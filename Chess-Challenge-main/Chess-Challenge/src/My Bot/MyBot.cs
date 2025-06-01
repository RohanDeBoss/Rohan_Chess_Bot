using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Buffers;

// v2.5 Optimised LMR + New move ordering bonuses and tweaks + Corrected Mate Score Handling and console finally! + Cleanup
public class MyBot : IChessBot
{
    // Time management flags
    private static readonly bool ConstantDepth = false;
    private static readonly short MaxDepth = 12; // Used when ConstantDepth is true

    private static readonly bool UseFixedTimePerMove = false;
    private static readonly int FixedTimePerMoveMs = 500;

    private static readonly bool PerDepthDebugging = false;

    // Search & Eval Constants
    private const short MaxSafetyDepth = 99; // Max search depth for internal Negamax calls
    private const int InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22;
    private const int MAX_KILLER_PLY = 256;

    // Move Ordering Bonuses
    private const int TT_MOVE_BONUS = 10_000_000;
    private const int PREVIOUS_BEST_MOVE_BONUS = 5_000_000; // For root moves from previous iteration
    private const int PROMOTION_BASE_BONUS = 1_100_000;
    private const int KILLER_MOVE_BONUS = 900_000;
    private const int HISTORY_MAX_BONUS = 800_000;
    private const int GOOD_CAPTURE_BONUS = 2_000_000; // For captures with SEE >= 0
    private const int LOSING_CAPTURE_BONUS = 100_000;  // For captures with SEE < 0

    // Time Management & Aspiration Window Constants
    private const int INITIAL_ASPIRATION_WINDOW = 150;
    private const int MAX_ASPIRATION_DEPTH = 4; // Depth to start using aspiration windows
    private const int CHECKMATE_SCORE_THRESHOLD = 25000; // abs(score) > this is considered a mate
    private const int SAFETY_MARGIN = 10; // Time buffer in ms

    private const int TIME_CHECK_NODES = 1024;
    private const int TIME_CHECK_MASK = TIME_CHECK_NODES - 1;

    // Static Fields
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = TT_SIZE - 1;
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 }; // P, N, B, R, Q, K

    // Instance Fields (reset per Think call)
    private long negamaxPositions = 0;
    private long qsearchPositions = 0;
    private int bestScoreRoot; // Best score found for the current move, from current player's POV
    private Move[,] killerMoves = new Move[MAX_KILLER_PLY, 2];
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private int completedSearchDepth; // Max depth fully completed in ID for logging
    private Timer currentTimer;
    private volatile bool timeIsUp;
    private long absoluteTimeLimit;

    private static readonly DescendingIntComparer _descendingIntComparer = new DescendingIntComparer();
    private class DescendingIntComparer : IComparer<int>
    {
        public int Compare(int x, int y) => y.CompareTo(x);
    }

    private void CheckTime()
    {
        if (ConstantDepth) return;

        // Check time every TIME_CHECK_NODES
        if (((negamaxPositions + qsearchPositions) & TIME_CHECK_MASK) == 0)
        {
            if (currentTimer.MillisecondsElapsedThisTurn >= absoluteTimeLimit)
            {
                timeIsUp = true;
            }
        }
    }

    private short GetTimeSpentFraction(Timer timer)
    {
        int t = timer.MillisecondsRemaining;
        // Formula aims for a balance between using a fraction of remaining time and being responsive
        int result = 20 + 99900 / (t + 1675);
        return (short)Math.Max(26, Math.Min(65, result)); // Clamp fraction
    }

    private int AllocateTime(Timer timer)
    {
        if (ConstantDepth)
            return int.MaxValue; // Effectively infinite time for constant depth search up to MaxDepth
        if (UseFixedTimePerMove)
            return Math.Max(1, Math.Min(FixedTimePerMoveMs, timer.MillisecondsRemaining - SAFETY_MARGIN));

        short timeFraction = Math.Max(GetTimeSpentFraction(timer), (short)1);
        int allocated = (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 2);
        allocated = Math.Max(10, allocated - SAFETY_MARGIN); // Ensure some minimum time, apply safety margin
        allocated = Math.Min(allocated, timer.MillisecondsRemaining - SAFETY_MARGIN); // Don't use more than available
        return Math.Max(1, allocated); // Ensure at least 1ms
    }

    public Move Think(Board board, Timer timer)
    {
        currentTimer = timer;
        timeIsUp = false;

        if (timer.MillisecondsRemaining <= 0 && !ConstantDepth)
        {
            var moves = board.GetLegalMoves();
            return moves.Length > 0 ? moves[0] : Move.NullMove;
        }

        // Initialize per-turn fields
        Array.Clear(killerMoves, 0, killerMoves.Length);
        Array.Clear(historyMoves, 0, historyMoves.Length);
        negamaxPositions = 0;
        qsearchPositions = 0;
        completedSearchDepth = 0;
        lastBoardHash = 0; // For IsEndgame cache
        cachedPieceCount = -1; // For IsEndgame cache
        this.bestScoreRoot = 0; // Score from current player's POV at root

        short currentIterativeDepth = 1;
        int scoreFromPrevIteration = 0;
        Move bestMoveFromPrevIteration = Move.NullMove;

        var legalMoves = board.GetLegalMoves();
        Move bestMoveOverall = legalMoves.Length > 0 ? legalMoves[0] : Move.NullMove;

        if (legalMoves.Length == 0)
        {
            // Mate in 0 ply (current position) if checkmated now. Score is from current player's POV.
            this.bestScoreRoot = board.IsInCheck() ? -InfiniteScore : 0; // Stalemate is 0
            return Move.NullMove;
        }
        if (legalMoves.Length == 1)
        {
            return HandleForcedMove(legalMoves[0], board, 0, true); // Depth 0 for logging, not a search depth
        }

        if (PerDepthDebugging)
        {
            Console.WriteLine("");
            if (ConstantDepth)
                DebugLog($"Starting constant depth search to {MaxDepth}:");
            else
                DebugLog($"Starting search for timed move:");
        }

        absoluteTimeLimit = timer.MillisecondsElapsedThisTurn + AllocateTime(timer);

        Move bestMoveThisIteration = bestMoveOverall; // Best move found in the current ID depth

        // --- Iterative Deepening Loop ---
        while (currentIterativeDepth <= MaxSafetyDepth && (ConstantDepth ? currentIterativeDepth <= MaxDepth : true))
        {
            if (timeIsUp || (!ConstantDepth && currentTimer.MillisecondsElapsedThisTurn >= absoluteTimeLimit - SAFETY_MARGIN * 2))
                break;

            Move bestMoveInAspiration = Move.NullMove;

            bool useAspiration = currentIterativeDepth > MAX_ASPIRATION_DEPTH && Math.Abs(scoreFromPrevIteration) < CHECKMATE_SCORE_THRESHOLD;
            int alpha = useAspiration ? scoreFromPrevIteration - INITIAL_ASPIRATION_WINDOW : -InfiniteScore;
            int beta = useAspiration ? scoreFromPrevIteration + INITIAL_ASPIRATION_WINDOW : InfiniteScore;
            int aspirationWindowSize = INITIAL_ASPIRATION_WINDOW;
            bool aspirationSearchFailed;
            int scoreThisAspirationLoop;

            // --- Aspiration Window Loop ---
            do
            {
                aspirationSearchFailed = false;
                scoreThisAspirationLoop = -InfiniteScore; // Score for the current aspiration search attempt

                // Initialize best move for this aspiration attempt with PV move or first legal move
                Move currentBestMoveInLoopAttempt = bestMoveFromPrevIteration;
                if (currentBestMoveInLoopAttempt.IsNull && legalMoves.Length > 0) currentBestMoveInLoopAttempt = legalMoves[0];


                Move[] movesToOrder = OrderMoves(legalMoves, board, 0, bestMoveFromPrevIteration); // ply 0 for root
                if (movesToOrder.Length > 0 && currentBestMoveInLoopAttempt.IsNull) currentBestMoveInLoopAttempt = movesToOrder[0];


                for (int i = 0; i < movesToOrder.Length; i++)
                {
                    Move move = movesToOrder[i];
                    board.MakeMove(move);
                    // depth-1 for search, ply 1 for killers/history, realPly 1 for game ply from root
                    int score = -Negamax(board, currentIterativeDepth - 1, -beta, -alpha, 1, 1);
                    board.UndoMove(move);

                    if (timeIsUp) goto EndRootMoveLoop_ID; // Exit this iteration's root move loop

                    if (score > scoreThisAspirationLoop)
                    {
                        scoreThisAspirationLoop = score;
                        currentBestMoveInLoopAttempt = move;
                        alpha = Math.Max(alpha, score);
                    }

                    if (alpha >= beta) // Beta cutoff
                    {
                        if (useAspiration) aspirationSearchFailed = true;
                        break;
                    }
                }

            EndRootMoveLoop_ID:;
                if (timeIsUp) break; // Exit aspiration loop if time is up

                if (aspirationSearchFailed)
                {
                    // Aspiration failed, widen window and re-search
                    if (scoreThisAspirationLoop <= (scoreFromPrevIteration - aspirationWindowSize)) // Failed low
                    {
                        alpha = -InfiniteScore;
                        beta = scoreThisAspirationLoop + aspirationWindowSize;
                    }
                    else // Failed high 
                    {
                        alpha = scoreThisAspirationLoop - aspirationWindowSize;
                        beta = InfiniteScore;
                    }
                    aspirationWindowSize *= 2;
                }
                else // Aspiration successful or not used
                {
                    scoreFromPrevIteration = scoreThisAspirationLoop;
                    this.bestScoreRoot = scoreThisAspirationLoop;
                    if (!currentBestMoveInLoopAttempt.IsNull)
                    {
                        bestMoveThisIteration = currentBestMoveInLoopAttempt;
                    }
                    else if (movesToOrder.Length > 0)
                    { // Fallback if something odd happened
                        bestMoveThisIteration = movesToOrder[0];
                    }
                    else if (legalMoves.Length > 0)
                    {
                        bestMoveThisIteration = legalMoves[0];
                    }
                }

            } while (aspirationSearchFailed && !timeIsUp && aspirationWindowSize < InfiniteScore / 2); // Prevent overly large/infinite windows

            if (timeIsUp) break; // Exit ID loop if time ran out during aspiration

            if (!bestMoveThisIteration.IsNull) // If this ID depth successfully found/confirmed a move
            {
                bestMoveOverall = bestMoveThisIteration;
                bestMoveFromPrevIteration = bestMoveOverall; // Use as PV hint for next iteration
                this.completedSearchDepth = currentIterativeDepth; // Log this depth as completed
                if (PerDepthDebugging)
                {
                    string timeDisplay = currentTimer.MillisecondsElapsedThisTurn <= 9999 ? $"{currentTimer.MillisecondsElapsedThisTurn}ms" : $"{(currentTimer.MillisecondsElapsedThisTurn / 1000.0):F1}s";
                    long totalNodes = negamaxPositions + qsearchPositions;
                    string nodesDisplay = totalNodes < 10000 ? $"{totalNodes}" : totalNodes < 10000000 ? $"{(totalNodes / 1000.0):F1}k" : $"{(totalNodes / 1000000.0):F1}m";
                    DebugLog($"Depth {currentIterativeDepth}, Score {this.bestScoreRoot}, BestMove {bestMoveOverall}, Nodes {nodesDisplay}, Time {timeDisplay}");
                }
            }
            else
            {
                // Iteration failed to find any move (likely due to time out before first root move completed)
                // Rely on bestMoveOverall from the previous successful iteration.
                break;
            }
            currentIterativeDepth++;
        } // --- End Iterative Deepening Loop ---

        // Fallback if no move was ever properly selected (e.g., instant timeout on first depth)
        if (bestMoveOverall.IsNull && legalMoves.Length > 0)
            bestMoveOverall = legalMoves[0];

        // If search completed no depth (e.g. very fast exit but not timeout on d=1), get a basic eval for logging.
        if (this.completedSearchDepth == 0 && legalMoves.Length > 0 && !timeIsUp && this.bestScoreRoot == 0)
        {
            this.bestScoreRoot = Evaluate(board) * (board.IsWhiteToMove ? 1 : -1);
        }

        return LogEval(board, this.completedSearchDepth, false, bestMoveOverall);
    }

    private void DebugLog(string message)
    {
        Console.WriteLine($"{GetType().Name} {message}");
    }

    private Move LogEval(Board board, int depthCompleted, bool isForcedMove, Move moveForThisTurn)
    {
        if (!isForcedMove && currentTimer != null)
        {
            Console.WriteLine();
            // bestScoreRoot is from the perspective of the player whose turn it was at the start of Think().
            // For consistent display (e.g. positive for White winning), adjust if Black made the move.
            int evalForDisplay = board.IsWhiteToMove ? this.bestScoreRoot : -this.bestScoreRoot;
            string mateInfo = GetMateInMoves(this.bestScoreRoot); // Pass score from current player's POV
            string npsDisplay = currentTimer.MillisecondsElapsedThisTurn > 0 ? $"{((negamaxPositions + qsearchPositions) / (currentTimer.MillisecondsElapsedThisTurn / 1000.0) / 1000):F0}knps" : "0knps";

            DebugLog($"Depth: {depthCompleted}");
            DebugLog(mateInfo ?? "No mate found");
            DebugLog($"Eval: {evalForDisplay}"); // Display from White's perspective
            DebugLog($"Nodes: {negamaxPositions + qsearchPositions:N0}");
            DebugLog($"NPS: {npsDisplay}");
        }
        else if (isForcedMove)
        {
            Console.WriteLine($"\n{GetType().Name}: FORCED MOVE! ({moveForThisTurn})");
        }
        return moveForThisTurn;
    }

    // Interprets an internal mate score (e.g., +Inf - P*50) into "Mate in P ply".
    // Score is from the perspective of the current player at the root.
    private string GetMateInMoves(int score)
    {
        if (Math.Abs(score) <= CHECKMATE_SCORE_THRESHOLD) // Not a mate score
        {
            return null;
        }
        int sign = Math.Sign(score);
        // Internal score format: sign * (InfiniteScore - game_ply_of_mate_from_root * 50)
        // abs(score) = InfiniteScore - game_ply_of_mate_from_root * 50
        // game_ply_of_mate_from_root * 50 = InfiniteScore - abs(score)
        // game_ply_of_mate_from_root = (InfiniteScore - abs(score)) / 50
        // Add 49 for robust integer division to get ceiling for P from (Inf - P*50) type scores.
        int pliesToMate = (InfiniteScore - Math.Abs(score) + 49) / 50;

        return $"{(sign > 0 ? "Winning" : "Losing")} Mate in {pliesToMate} ply";
    }

    private Move[] OrderMoves(Move[] moves, Board board, int ply, Move? pvMoveHint = null)
    {
        if (moves.Length <= 1) return moves;

        int[] scores = ArrayPool<int>.Shared.Rent(moves.Length);
        try
        {
            TTEntry ttEntry = tt[GetTTIndex(board.ZobristKey)];
            Move ttMove = (ttEntry.Key == board.ZobristKey) ? ttEntry.BestMove : Move.NullMove;

            for (int i = 0; i < moves.Length; i++)
            {
                Move move = moves[i];
                int moveScore = 0;

                if (!ttMove.IsNull && move == ttMove)
                    moveScore += TT_MOVE_BONUS;
                else if (ply == 0 && pvMoveHint.HasValue && move == pvMoveHint.Value) // Only use pvMoveHint at root
                    moveScore += PREVIOUS_BEST_MOVE_BONUS;

                if (move.IsCapture)
                {
                    int seeScoreVal = CalculateSEE(board, move);
                    if (seeScoreVal >= 0) // Good or equal capture
                    {
                        moveScore += GOOD_CAPTURE_BONUS + seeScoreVal;
                    }
                    else // Losing capture
                    {
                        moveScore += LOSING_CAPTURE_BONUS + seeScoreVal; // seeScoreVal is negative
                    }
                }
                else // Quiet moves
                {
                    if (IsKillerMove(move, ply))
                        moveScore += KILLER_MOVE_BONUS;
                    moveScore += Math.Min(historyMoves[move.StartSquare.Index, move.TargetSquare.Index], HISTORY_MAX_BONUS);
                }

                if (move.IsPromotion) // Promotion bonus stacks
                    moveScore += PROMOTION_BASE_BONUS + GetSeeValue(move.PromotionPieceType);

                scores[i] = moveScore;
            }

            Array.Sort(scores, moves, 0, moves.Length, _descendingIntComparer);
            return moves;
        }
        finally
        {
            ArrayPool<int>.Shared.Return(scores);
        }
    }

    private bool IsKillerMove(Move move, int ply)
    {
        if (ply < 0 || ply >= MAX_KILLER_PLY) // Bounds check
            return false;
        return move == killerMoves[ply, 0] || move == killerMoves[ply, 1];
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        // Only for quiet moves that cause a beta cutoff, within supported ply range
        if (move.IsCapture || move.IsPromotion || ply < 0 || ply >= MAX_KILLER_PLY)
            return;

        if (move != killerMoves[ply, 0])
        {
            killerMoves[ply, 1] = killerMoves[ply, 0]; // Shift killer 1 to slot 2
            killerMoves[ply, 0] = move;                // New killer in slot 1
        }
    }

    private const int HISTORY_SCORE_CAP = 1_000_000;

    private void UpdateHistoryMove(Move move, int bonus)
    {
        if (move.IsCapture || move.IsPromotion) return; // Only for quiet moves causing cutoff
        int startIdx = move.StartSquare.Index;
        int targetIdx = move.TargetSquare.Index;
        // Bonus is typically depth^2 or similar
        historyMoves[startIdx, targetIdx] = Math.Min(historyMoves[startIdx, targetIdx] + bonus, HISTORY_SCORE_CAP);

        // Periodically decay history scores (e.g., every time check)
        if (((negamaxPositions + qsearchPositions) & TIME_CHECK_MASK) == 0)
            DecayHistory();
    }

    private void DecayHistory()
    {
        // Simple linear decay; other schemes (e.g., multiplicative) exist
        for (int i = 0; i < 64; i++)
            for (int j = 0; j < 64; j++)
                historyMoves[i, j] /= 2;
    }

    // realPly: Number of plies from the root of the *current search invocation* (Think call).
    // ply: Number of plies from the current Negamax node (used for killer/history table indexing).
    private int Negamax(Board board, int depth, int alpha, int beta, int ply, int realPly)
    {
        CheckTime();
        if (timeIsUp) return 0; // Return a neutral score if time is up

        negamaxPositions++;
        if (board.IsDraw()) return 0; // Draw scores 0

        // Mate distance pruning: scores are defined as InfiniteScore - game_ply_of_mate.
        // A mate at current realPly is the soonest possible.
        alpha = Math.Max(alpha, -InfiniteScore + realPly * 50);
        beta = Math.Min(beta, InfiniteScore - realPly * 50);
        if (alpha >= beta) return alpha; // Pruning based on mate distance

        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];
        bool ttHit = ttEntry.Key == key;
        Move ttMove = ttHit ? ttEntry.BestMove : Move.NullMove;

        if (ttHit && ttEntry.Depth >= depth)
        {
            // TT scores are stored as absolute game_ply_of_mate.
            // AdjustMateScoreFromTT now simply returns the score as Negamax bounds expect this.
            short scoreFromTT = AdjustMateScoreFromTT(ttEntry.Score, realPly);
            if (ttEntry.Flag == EXACT) return scoreFromTT;
            if (ttEntry.Flag == ALPHA && scoreFromTT <= alpha) return alpha;
            if (ttEntry.Flag == BETA && scoreFromTT >= beta) return beta;
        }

        if (depth <= 0) // Reached max depth for this search branch, enter quiescence
            return Quiescence(board, alpha, beta, ply, 0, realPly);

        Move[] moves = board.GetLegalMoves();
        if (moves.Length == 0) // Checkmate or stalemate
        {
            // Mate occurs at current 'realPly'. Score is from current player's perspective.
            return board.IsInCheck() ? (-InfiniteScore + realPly * 50) : 0;
        }

        int standPat = 0;
        bool inCheck = board.IsInCheck();
        if (!inCheck) standPat = Evaluate(board); // Evaluate only if not in check for NMP/Futility

        // Null Move Pruning (NMP)
        if (!inCheck && depth >= 3 && ply > 0 && !IsEndgame(board) && Math.Abs(standPat) < CHECKMATE_SCORE_THRESHOLD)
        {
            board.ForceSkipTurn();
            int R = depth > 6 ? 3 : 2; // Reduction factor
            int nullScore = -Negamax(board, depth - R - 1, -beta, -beta + 1, ply + 1, realPly + 1);
            board.UndoSkipTurn();
            if (timeIsUp) return 0;
            if (nullScore >= beta) return beta; // Null move cutoff
        }

        // Razoring (at depth 1)
        if (depth == 1 && !inCheck && standPat + 200 < alpha)
            return Quiescence(board, alpha, beta, ply, 0, realPly);

        // Futility Pruning (at shallow depths)
        bool inMateZone = Math.Abs(standPat) > CHECKMATE_SCORE_THRESHOLD;
        if (depth <= 2 && !inCheck && !inMateZone && standPat + 150 * depth <= alpha)
            return Quiescence(board, alpha, beta, ply, 0, realPly);

        moves = OrderMoves(moves, board, ply, ttMove); // ttMove acts as PV hint if available
        int originalAlpha = alpha;
        Move bestMoveCurrentNode = Move.NullMove;
        int localBestScore = -InfiniteScore;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();

            int newDepth = depth - 1;
            // Check extension
            if (givesCheck && newDepth < MaxSafetyDepth - 1) newDepth = Math.Min(MaxSafetyDepth - 1, newDepth + 1);

            int score;
            bool isQuiet = !move.IsCapture && !move.IsPromotion;
            // Late Move Reductions (LMR), but not for killer moves
            bool useLMR = depth > 2 && i >= 2 && isQuiet && !givesCheck && !inMateZone && !IsKillerMove(move, ply);

            if (useLMR)
            {
                int reduction = (int)(0.75 + Math.Log(depth) * Math.Log(i + 1) / 2.0);
                // Reduce less for historically good moves
                if (historyMoves[move.StartSquare.Index, move.TargetSquare.Index] > HISTORY_SCORE_CAP / 4)
                    reduction = Math.Max(reduction - 1, 0);
                int reducedDepth = Math.Max(newDepth - reduction, 1); // Ensure depth doesn't go <= 0

                score = -Negamax(board, reducedDepth, -alpha - 1, -alpha, ply + 1, realPly + 1); // Null window search
                if (score > alpha && score < beta && !timeIsUp) // Re-search if it failed high
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }
            else // Full depth search (no LMR or not applicable)
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);

            board.UndoMove(move);
            if (timeIsUp) return 0;

            if (score > localBestScore)
            {
                localBestScore = score;
                bestMoveCurrentNode = move;
                alpha = Math.Max(alpha, score);

                if (alpha >= beta) // Beta cutoff
                {
                    if (isQuiet) // Update killers/history only for quiet moves causing cutoff
                    {
                        UpdateKillerMoves(move, ply);
                        UpdateHistoryMove(move, depth * depth); // Bonus based on depth
                    }
                    // Scores (beta) are already absolute game_ply_of_mate based.
                    AddTT(key, depth, AdjustMateScoreForTTStorage(beta, realPly), BETA, move);
                    return beta;
                }
            }
        }

        byte flag = localBestScore <= originalAlpha ? ALPHA : EXACT;
        // Scores (localBestScore) are already absolute game_ply_of_mate based.
        AddTT(key, depth, AdjustMateScoreForTTStorage(localBestScore, realPly), flag, bestMoveCurrentNode);
        return localBestScore;
    }

    private int Quiescence(Board board, int alpha, int beta, int ply, int qDepth, int realPly)
    {
        qsearchPositions++;
        if (timeIsUp) return 0;

        int standPat = Evaluate(board); // Static evaluation of the current position

        if (standPat >= beta) return beta; // Fail-high
        if (standPat > alpha) alpha = standPat; // Update alpha

        Move[] captures = board.GetLegalMoves(true); // Only consider captures in q-search
        Move[] orderedMoves = OrderMoves(captures, board, ply); // Order captures by SEE, etc.

        foreach (Move move in orderedMoves)
        {
            // Static Exchange Evaluation (SEE) check for non-promoting captures
            if (!move.IsPromotion)
            {
                int seeValue = CalculateSEE(board, move);
                if (seeValue < 0) // Skip captures that lose material straight away
                {
                    continue;
                }
            }

            board.MakeMove(move);
            // realPly is incremented as quiescence search goes deeper in game terms
            int score = -Quiescence(board, -beta, -alpha, ply + 1, qDepth + 1, realPly + 1);
            board.UndoMove(move);

            if (timeIsUp) return 0;
            if (score >= beta) return beta; // Fail-high
            if (score > alpha) alpha = score; // Update alpha
        }
        return alpha; // Return best score found
    }

    private static readonly int[] SeePieceValues = { 100, 300, 310, 500, 900, 20000 }; // P, N, B, R, Q, K (King high for SEE)

    private int GetSeeValue(PieceType pt)
    {
        if (pt == PieceType.None) return 0;
        return SeePieceValues[(int)pt - 1];
    }

    private (PieceType type, Square fromSquare) GetLeastValuableAttacker(Board board, Square targetSquare, bool attackerIsWhite, ulong occupiedHypothetical)
    {
        for (int pieceTypeId = 1; pieceTypeId <= 6; pieceTypeId++) // Iterate Pawn to King
        {
            PieceType currentPieceTypeToTest = (PieceType)pieceTypeId;
            ulong potentialAttackersOfThisType = board.GetPieceBitboard(currentPieceTypeToTest, attackerIsWhite) & occupiedHypothetical;
            if (potentialAttackersOfThisType == 0) continue; // No pieces of this type for this side

            ulong attackRaysToTarget;
            switch (currentPieceTypeToTest)
            {
                case PieceType.Pawn: attackRaysToTarget = BitboardHelper.GetPawnAttacks(targetSquare, !attackerIsWhite); break;
                case PieceType.Knight: attackRaysToTarget = BitboardHelper.GetKnightAttacks(targetSquare); break;
                case PieceType.Bishop: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Bishop, targetSquare, occupiedHypothetical); break;
                case PieceType.Rook: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Rook, targetSquare, occupiedHypothetical); break;
                case PieceType.Queen: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Queen, targetSquare, occupiedHypothetical); break;
                case PieceType.King: attackRaysToTarget = BitboardHelper.GetKingAttacks(targetSquare); break;
                default: continue; // Should not happen
            }

            ulong actualAttackers = attackRaysToTarget & potentialAttackersOfThisType;
            if (actualAttackers != 0)
            {
                // Return the first (least valuable) attacker found
                return (currentPieceTypeToTest, new Square(BitOperations.TrailingZeroCount(actualAttackers)));
            }
        }
        return (PieceType.None, default(Square)); // No attacker found
    }

    private int CalculateSEE(Board board, Move move)
    {
        if (!move.IsCapture) return 0; // SEE is 0 for non-captures

        Square targetSquare = move.TargetSquare;
        PieceType initialAttackerPieceType = move.MovePieceType;
        PieceType capturedPieceType = move.CapturePieceType;

        Span<int> gain = stackalloc int[32]; // Max possible captures in a sequence
        int d = 0; // Depth of SEE search

        ulong occupiedHypothetical = board.AllPiecesBitboard;
        bool currentSideToRecaptureIsWhite = !board.IsWhiteToMove; // Side whose turn it is after initial capture

        gain[d++] = GetSeeValue(capturedPieceType); // Value of initially captured piece
        occupiedHypothetical ^= (1UL << move.StartSquare.Index); // Remove initial attacker from board
        PieceType pieceOnSquareForNextCapture = initialAttackerPieceType; // Piece that just moved to targetSquare

        while (true)
        {
            (PieceType lvaType, Square lvaFromSquare) =
                GetLeastValuableAttacker(board, targetSquare, currentSideToRecaptureIsWhite, occupiedHypothetical);

            if (lvaType == PieceType.None) break; // No more attackers for current side

            occupiedHypothetical ^= (1UL << lvaFromSquare.Index); // Remove this attacker
            gain[d++] = GetSeeValue(pieceOnSquareForNextCapture); // Add value of piece currently on targetSquare to gain list
            pieceOnSquareForNextCapture = lvaType; // This attacker is now on the target square
            currentSideToRecaptureIsWhite = !currentSideToRecaptureIsWhite; // Switch sides
            if (d >= 32) break; // Safety break for very long sequences
        }

        // Calculate SEE score from the gain list
        int seeScore = 0;
        for (int k = d - 1; k >= 0; --k)
        {
            // score = piece_value_captured - best_opponent_reply_score
            // If opponent has no good reply (score < 0), their reply score is 0.
            int netGainIfThisCaptureIsMade = gain[k] - seeScore;
            if (k == 0) // This is the value of the initial capture sequence for the side to move
            {
                seeScore = netGainIfThisCaptureIsMade;
            }
            else // These are subsequent captures in the hypothetical sequence
            {
                // If the side to move for this part of sequence can get a positive outcome, they take it.
                // Otherwise, they wouldn't make this part of the sequence, value is 0 for them.
                // Since seeScore is from opponent's perspective in `val - seeScore`,
                // we want to maximize our gain `val - seeScore` vs `0` (not continuing sequence).
                seeScore = Math.Max(0, netGainIfThisCaptureIsMade);
            }
        }
        return seeScore;
    }

    private int Evaluate(Board board)
    {
        if (board.IsDraw()) return 0;

        Square whiteKingSquare = board.GetKingSquare(true);
        Square blackKingSquare = board.GetKingSquare(false);
        bool isEndgame = IsEndgame(board);

        int score = 0;
        int whiteBishopCount = 0;
        int blackBishopCount = 0;

        foreach (PieceList list in board.GetAllPieceLists())
        {
            int pieceTypeIndex = (int)list.TypeOfPieceInList - 1;
            int baseVal = PieceValues[pieceTypeIndex];
            int pieceSign = list.IsWhitePieceList ? 1 : -1;

            if (list.TypeOfPieceInList == PieceType.Bishop)
            {
                if (list.IsWhitePieceList) whiteBishopCount += list.Count; else blackBishopCount += list.Count;
            }

            int[] pstForPieceType;
            if (list.TypeOfPieceInList == PieceType.King)
            {
                pstForPieceType = isEndgame ? KingEndGamePST : KingMiddleGamePST;
            }
            else
            {
                pstForPieceType = PiecePSTs[pieceTypeIndex];
            }

            int xorMask = list.IsWhitePieceList ? 0 : 56; // Flips square index for Black's perspective

            foreach (Piece p in list)
            {
                score += pieceSign * (baseVal + pstForPieceType[p.Square.Index ^ xorMask]);

                // Endgame Pawn Advancement Bonus (simple version)
                if (isEndgame && p.PieceType == PieceType.Pawn)
                {
                    // Rank from piece's perspective (0=8th rank for white, 7=1st rank for white)
                    int rankFromPromotion = p.IsWhite ? (7 - p.Square.Rank) : p.Square.Rank;
                    // Bonus for how far pawn has advanced (more advanced = higher bonus)
                    int advancement = p.IsWhite ? p.Square.Rank : (7 - p.Square.Rank);
                    score += pieceSign * advancement * 5; // Smaller bonus
                }
            }
        }

        // Bishop Pair Bonus
        const int BISHOP_PAIR_BONUS = 30;
        if (whiteBishopCount >= 2) score += BISHOP_PAIR_BONUS;
        if (blackBishopCount >= 2) score -= BISHOP_PAIR_BONUS;

        // Endgame King Proximity Bonus (if clearly winning, push king towards opponent's king)
        if (isEndgame && Math.Abs(EvaluateMaterialOnly(board)) > 150) // Check raw material advantage
        {
            int kingFileDist = Math.Abs(whiteKingSquare.File - blackKingSquare.File);
            int kingRankDist = Math.Abs(whiteKingSquare.Rank - blackKingSquare.Rank);
            int kingDist = kingFileDist + kingRankDist; // Manhattan distance
            int proximityBonus = (14 - kingDist) * 5; // Closer kings = higher bonus for winning side

            // Add to winning side based on full eval score, not just material
            if (score > 0) score += proximityBonus;
            else if (score < 0) score -= proximityBonus;
        }

        // Tempo Bonus (small bonus for side to move)
        const int TEMPO_BONUS = 10;
        score += board.IsWhiteToMove ? TEMPO_BONUS : -TEMPO_BONUS;

        // Return score relative to current player
        return board.IsWhiteToMove ? score : -score;
    }

    // Helper to get a rough material evaluation, used for endgame king proximity condition
    private int EvaluateMaterialOnly(Board board)
    {
        int materialScore = 0;
        for (int i = 0; i < 5; i++)
        { // Iterate P, N, B, R, Q (King value is 0 in PieceValues)
            materialScore += PieceValues[i] * (board.GetPieceList((PieceType)(i + 1), true).Count - board.GetPieceList((PieceType)(i + 1), false).Count);
        }
        return materialScore;
    }

    private bool IsEndgame(Board board)
    {
        // Cache piece count as it's expensive to count PopCount repeatedly
        ulong currentBoardHash = board.ZobristKey;
        if (currentBoardHash != lastBoardHash)
        {
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = currentBoardHash;
        }
        // Endgame if 11 or fewer total pieces (including kings) remain
        const int endgameTotalPieceThreshold = 11;
        return cachedPieceCount <= endgameTotalPieceThreshold;
    }

    private Move HandleForcedMove(Move move, Board board, int completedDepthForLog, bool isForcedMove)
    {
        // For forced moves, 'bestScoreRoot' can be a simple evaluation or 0.
        // It's mainly for logging consistency.
        this.bestScoreRoot = Evaluate(board) * (board.IsWhiteToMove ? 1 : -1);
        this.completedSearchDepth = completedDepthForLog;
        return LogEval(board, completedDepthForLog, isForcedMove, move);
    }

    private struct TTEntry
    {
        public ulong Key;    // Zobrist key
        public short Depth;  // Depth of the search that stored this entry
        public short Score;  // Score (absolute game-ply mate score if mate)
        public byte Flag;    // EXACT, ALPHA (lower bound), or BETA (upper bound)
        public Move BestMove; // Best move found from this position
    }

    private const byte EXACT = 0;
    private const byte ALPHA = 1; // Score is a lower bound (actual score >= entry.Score)
    private const byte BETA = 2;  // Score is an upper bound (actual score <= entry.Score)

    private int GetTTIndex(ulong key) => (int)(key & ttMask);

    // scoreForTT is already an absolute game-ply mate score if it's a mate.
    private void AddTT(ulong key, int depth, short scoreForTT, byte flag, Move bestMove)
    {
        int index = GetTTIndex(key);
        ref TTEntry entry = ref tt[index];

        // Replacement strategy:
        // - Always replace if new entry is deeper.
        // - At same depth: EXACT replaces anything. BETA replaces ALPHA. Don't replace EXACT/BETA with ALPHA.
        bool replace = entry.Key == 0 || depth > entry.Depth ||
                       (depth == entry.Depth && (flag == EXACT || (flag == BETA && entry.Flag == ALPHA)));

        if (replace)
        {
            entry.Key = key;
            entry.Depth = (short)depth;
            entry.Score = scoreForTT;
            entry.Flag = flag;
            // Store best move for EXACT or BETA nodes.
            // For ALPHA nodes, move is a refutation, but storing it can be useful as a TT move.
            // Avoid overwriting a good move with NullMove if new is ALPHA and new_move is null.
            if (flag == EXACT || flag == BETA || !bestMove.IsNull)
            {
                entry.BestMove = bestMove;
            }
            else if (flag == ALPHA && bestMove.IsNull && entry.BestMove.IsNull)
            {
                // If new is ALPHA with no move, and old also had no move (or was overwritten), store NullMove.
                entry.BestMove = Move.NullMove;
            }
            // else: if new is ALPHA with NullMove but old had a move, keep old move.
        }
    }

    // scoreFromNode is already sign * (InfiniteScore - game_ply_of_mating_move * 50)
    // This function primarily clamps it for TT storage if it's a mate.
    private short AdjustMateScoreForTTStorage(int scoreFromNode, int currentRealPly)
    {
        if (Math.Abs(scoreFromNode) > CHECKMATE_SCORE_THRESHOLD)
        {
            // Clamp to ensure game_ply_of_mating_move is at least 1 (as realPly >= 1 for children)
            // and score fits in short.
            // A score of (+/-) (InfiniteScore - 50) corresponds to mate at ply 1 from root.
            // Smallest storable mate value should be mate in MAX_KILLER_PLY.
            return (short)Math.Clamp(scoreFromNode, -(InfiniteScore - MAX_KILLER_PLY * 50), InfiniteScore - MAX_KILLER_PLY * 50);
        }
        return (short)scoreFromNode;
    }

    // ttScore is sign * (InfiniteScore - game_ply_of_mating_move_stored * 50)
    // currentRealPly is the ply of the node retrieving from TT.
    // Returns the score in the same absolute game-ply format, as Negamax bounds expect this.
    private short AdjustMateScoreFromTT(short ttScore, int currentRealPly)
    {
        // No adjustment needed based on currentRealPly if TT scores are stored
        // as absolute game_ply_of_mate and Negamax bounds expect this format.
        return ttScore;
    }

    // -- Piece Square Tables (Perspective of White, Black's are flipped via XOR 56) --
    private static readonly int[] PawnPST = {
          0,   0,   0,   0,   0,   0,   0,   0,
          5,  10,  10, -20, -20,  10,  11,   5,
          5,  -1, -10,   1,   3, -10,   0,   5,
          1,   3,   6,  21,  22,   0,   0,   0,
          5,   5,  10,  25,  25,  10,   5,   5,
         12,  10,  20,  30,  30,  20,  11,  10,
         50,  50,  50,  50,  50,  50,  50,  50,
          0,   0,   0,   0,   0,   0,   0,   0
    };
    private static readonly int[] KnightPST = {
        -50, -40, -30, -30, -30, -30, -40, -50,
        -40, -20,   0,   5,   5,   0, -20, -40,
        -30,   5,  10,  15,  15,  10,   5, -30,
        -30,   0,  15,  20,  20,  15,   0, -30,
        -30,   5,  15,  20,  20,  15,   5, -30,
        -30,   0,  10,  15,  15,  10,   0, -30,
        -40, -20,  -3,   0,   0,  -3, -20, -40,
        -50, -40, -30, -30, -30, -30, -40, -50
    };
    private static readonly int[] BishopPST = {
        -20, -10, -10, -10, -10, -10, -10, -20,
        -10,   5,   0,   0,   0,   0,   5, -10,
        -10,  10,  10,  10,  10,  10,  10, -10,
        -10,   0,  10,  10,  10,  10,   0, -10,
        -10,   5,   5,  10,  10,   5,   5, -10,
        -10,   0,   5,  10,  10,   5,   0, -10,
        -10,   0,   0,   0,   0,   0,   0, -10,
        -20, -10, -10, -10, -10, -10, -10, -20
    };
    private static readonly int[] RookPST = {
          0,   0,   0,   5,   5,   0,   0,  -4,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
          0,  10,  10,  10,  10,  10,  10,   5,
          0,   0,   0,   0,   0,   0,   0,   0
    };
    private static readonly int[] QueenPST = {
        -20, -10, -10,  -5,  -5, -10, -10, -20,
        -10,   0,   5,   0,   0,   0,   0, -10,
        -10,   5,   5,   5,   5,   5,   0, -10,
          0,   0,   5,   5,   5,   5,   0,  -5,
         -5,   0,   5,   5,   5,   5,   0,  -5,
        -10,   0,   5,   5,   5,   5,   0, -10,
        -10,   0,   0,   0,   0,   0,   0, -10,
        -20, -10, -10,  -5,  -5, -10, -10, -20
    };
    private static readonly int[] KingMiddleGamePST = {
         20,  30,  10,   0,   0,  10,  30,  20,
         20,  20,   0,   0,   0,   0,  20,  20,
        -10, -20, -20, -20, -20, -20, -20, -10,
        -20, -30, -30, -40, -40, -30, -30, -20,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30
    };
    private static readonly int[] KingEndGamePST = {
        -30, -20, -20, -20, -20, -20, -20, -30,
        -20, -15, -10,   0,   0, -10, -10, -20,
        -20, -10,  15,  20,  15,  15, -10, -20,
        -20, -10,  15,  18,  18,  15, -10, -20,
        -20, -10,  15,  18,  18,  15, -10, -20,
        -20, -10,  10,  15,  15,  15, -10, -20,
        -20, -15, -10,  -5,  -5, -10, -15, -20,
        -30, -25, -20, -15, -15, -20, -25, -30
    };

    private static readonly int[][] PiecePSTs = {
        PawnPST, KnightPST, BishopPST, RookPST, QueenPST, KingMiddleGamePST // KingMiddleGamePST is default for non-King PST lookup
    };
}