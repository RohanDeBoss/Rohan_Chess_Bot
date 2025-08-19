using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Buffers;

//v3.0 New tunable settings at the top, Ply-Corrected Mate Score Handling + Tweaks and value changes
public class EvilBot : IChessBot
{
    // --- Configuration ---
    private static readonly bool PerMoveDebugging = true;
    private static readonly bool PerDepthDebugging = false;
    private static readonly bool ConstantDepth = false;
    private static readonly short MaxDepth = 12;
    private static readonly bool UseFixedTimePerMove = false;
    private static readonly int FixedTimePerMoveMs = 500;

    // --- Core Constants ---
    private const short MaxSafetyDepth = 999;
    private const int InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22;
    private const int MAX_KILLER_PLY = 256;
    private const int MATE_FOUND_SCORE = 29000;

    // --- Time Management & Aspiration Windows ---
    private const int INITIAL_ASPIRATION_WINDOW = 150;
    private const int MAX_ASPIRATION_DEPTH = 4;
    private const int SAFETY_MARGIN = 10;
    private const int TIME_CHECK_NODES = 1024;
    private const int TIME_CHECK_MASK = TIME_CHECK_NODES - 1;


    // -- TUNABLE SEARCH & EVAL PARAMETERS --

    // Piece Values (P, N, B, R, Q, K)
    private static readonly int[] PieceValues = { 100, 305, 320, 500, 900, 0 };      // High impact, high risk.                                     // Best: ?
    private static readonly int[] SeePieceValues = { 100, 305, 320, 500, 900, 20000 };// Affects capture aggression. High impact, high risk.        // Best: ?

    // Move Ordering Bonuses (Relative values matter most)
    private const int TT_MOVE_BONUS = 10_000_000;            // UP: Prioritizes TT move more. Low risk.           // Best: ?
    private const int PREVIOUS_BEST_MOVE_BONUS = 5_000_000;  // UP: Follows previous iteration more. Low risk.    // Best: ?
    private const int PROMOTION_BASE_BONUS = 1_100_000;      // UP: Explores promotions earlier. Low risk.        // Best: ?
    private const int KILLER_MOVE_BONUS = 900_000;           // UP: Prioritizes killers more. Low risk.           // Best: ?
    private const int HISTORY_MAX_BONUS = 800_000;           // UP: History heuristic is stronger. Low risk.      // Best: ?
    private const int GOOD_CAPTURE_BONUS = 2_000_000;        // UP: Prioritizes winning captures. Low risk.       // Best: ?
    private const int LOSING_CAPTURE_BONUS = 100_000;        // UP: Prioritizes losing captures. Low risk.        // Best: ?

    // --- Search Heuristics (Inside Negamax/Quiescence) ---
    // 1. Null Move Pruning (NMP)
    private const int NMP_MIN_DEPTH = 3;                     // UP: Less aggressive pruning (safer). DOWN: More aggressive. Medium impact, medium risk. // Best: ?
    private const int NMP_R_BASE = 2;                        // UP: More aggressive pruning (riskier). DOWN: Less aggressive. High impact, high risk.   // Best: ?
    private const int NMP_R_DEEP_DEPTH = 6;                  // UP: Delays deep reduction (safer). DOWN: Activates sooner. Low impact, low risk.        // Best: ?
    private const int NMP_R_DEEP_REDUCTION = 3;              // UP: More aggressive deep pruning. DOWN: Less aggressive. Medium impact, medium risk.    // Best: ?

    // 2. Late Move Reductions (LMR)
    private const int LMR_MIN_DEPTH = 3;                     // UP: Less LMR (safer). DOWN: More LMR (riskier). Medium impact, medium risk.             // Best: ?
    private const int LMR_MIN_MOVE_COUNT = 2;                // UP: Reduces later moves (safer). DOWN: Reduces earlier. Medium impact, medium risk.     // Best: ?
    private const double LMR_LOG_DIVISOR = 2.0;              // UP: Less aggressive reduction (safer). DOWN: More aggressive. High impact, high risk.   // Best: ?

    // 3. Late Move Extensions (LME)
    private const int LME_AMOUNT = 1;                        // Changing this from 1 is generally not recommended. Low impact, high risk. // Best: 1

    // 4. Futility Pruning
    private const int FUTILITY_PRUNING_MAX_DEPTH_1 = 1;      // UP: Less pruning (safer). DOWN: More pruning. Low impact, medium risk.          // Best: ?
    private const int FUTILITY_PRUNING_MARGIN_1 = 200;       // UP: Less aggressive pruning. DOWN: More aggressive. Medium impact, medium risk. // Best: ?
    private const int FUTILITY_PRUNING_MAX_DEPTH_2 = 2;      // UP: Less pruning (safer). DOWN: More pruning. Low impact, medium risk.          // Best: ?
    private const int FUTILITY_MARGIN_PER_PLY_2 = 150;       // UP: Less aggressive pruning. DOWN: More aggressive. Medium impact, medium risk. // Best: ?

    // 5. SEE (Static Exchange Evaluation) Pruning/Reductions
    private const int Q_SEE_PRUNING_MARGIN = -30;            // UP(less neg): Less sacrifice-friendly. DOWN: More sacs. High impact, medium risk. // Best: ?
    private const int SEE_PRUNING_MARGIN = -20;              // UP(less neg): Reduces fewer captures. DOWN: Reduces more. Medium impact, medium risk. // Best: ?
    private const bool ENABLE_SEE_REDUCTIONS = true;         // ON/OFF switch for the below parameters. High impact, medium risk. // Best: ?
    private const int SEE_REDUCTION_MIN_DEPTH = 3;           // UP: Reduces less often (safer). DOWN: Reduces more. Low impact, low risk. // Best: ?
    private const int SEE_REDUCTION_AMOUNT = 3;              // UP: Reduces more aggressively (riskier). DOWN: Less. Medium impact, medium risk. // Best: ?

    // -- END OF TUNABLES --


    // Static Fields
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = TT_SIZE - 1;
    private int lastGamePlyCount = -1; //For measuring start of game

    // Instance Fields
    private long negamaxPositions, qsearchPositions;
    private int bestScoreRoot;
    private Move[,] killerMoves = new Move[MAX_KILLER_PLY, 2];
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private int completedSearchDepth;
    private Timer currentTimer;
    private volatile bool timeIsUp;
    private long absoluteTimeLimit;
    private bool isWhitePlayer; // Flag to remember starting perspective for logging

    private static readonly DescendingIntComparer _descendingIntComparer = new DescendingIntComparer();
    private class DescendingIntComparer : IComparer<int>
    {
        public int Compare(int x, int y) => y.CompareTo(x);
    }

    public Move Think(Board board, Timer timer)
    {
        // Game Start Detection & TT Clear (So no overflow onto next game)
        if (board.PlyCount < lastGamePlyCount)
        {
            Array.Clear(tt, 0, TT_SIZE); // Clear the TT only at the start of a new game
        }
        lastGamePlyCount = board.PlyCount;

        currentTimer = timer;
        timeIsUp = false;
        isWhitePlayer = board.IsWhiteToMove;

        if (timer.MillisecondsRemaining <= 0 && !ConstantDepth)
        {
            var moves = board.GetLegalMoves();
            return moves.Length > 0 ? moves[0] : Move.NullMove;
        }

        Array.Clear(killerMoves, 0, killerMoves.Length);
        Array.Clear(historyMoves, 0, historyMoves.Length);
        negamaxPositions = 0; qsearchPositions = 0; completedSearchDepth = 0;
        lastBoardHash = 0; cachedPieceCount = -1; bestScoreRoot = 0;

        short currentIterativeDepth = 1;
        int scoreFromPrevIteration = 0;
        Move bestMoveFromPrevIteration = Move.NullMove;

        var legalMoves = board.GetLegalMoves();
        if (legalMoves.Length == 0)
        {
            bestScoreRoot = board.IsInCheck() ? -InfiniteScore : 0;
            completedSearchDepth = MaxSafetyDepth;
            return LogEval(board, completedSearchDepth, false, Move.NullMove);
        }
        Move bestMoveOverall = legalMoves[0];
        if (legalMoves.Length == 1)
        {
            return HandleForcedMove(legalMoves[0], board, 0, true);
        }

        if (PerDepthDebugging)
        {
            Console.WriteLine("");
            DebugLog(ConstantDepth ? $"Starting constant depth search to {MaxDepth}:" : "Starting timed search:");
        }

        absoluteTimeLimit = timer.MillisecondsElapsedThisTurn + AllocateTime(timer);
        Move bestMoveThisIteration = bestMoveOverall;

        while (currentIterativeDepth <= MaxSafetyDepth && (ConstantDepth ? currentIterativeDepth <= MaxDepth : true))
        {
            if (timeIsUp || (!ConstantDepth && currentTimer.MillisecondsElapsedThisTurn >= absoluteTimeLimit - SAFETY_MARGIN * 2)) break;

            bool useAspiration = currentIterativeDepth > MAX_ASPIRATION_DEPTH && Math.Abs(scoreFromPrevIteration) < MATE_FOUND_SCORE;
            int alpha = useAspiration ? scoreFromPrevIteration - INITIAL_ASPIRATION_WINDOW : -InfiniteScore;
            int beta = useAspiration ? scoreFromPrevIteration + INITIAL_ASPIRATION_WINDOW : InfiniteScore;
            int aspirationWindowSize = INITIAL_ASPIRATION_WINDOW;
            bool aspirationSearchFailed;
            int scoreThisAspirationLoop;

            do
            {
                aspirationSearchFailed = false;
                scoreThisAspirationLoop = -InfiniteScore;
                Move currentBestMoveInLoopAttempt = bestMoveFromPrevIteration;
                if (currentBestMoveInLoopAttempt.IsNull) currentBestMoveInLoopAttempt = legalMoves[0];
                Move[] movesToOrder = OrderMoves(legalMoves, board, 0, bestMoveFromPrevIteration);
                if (movesToOrder.Length > 0 && currentBestMoveInLoopAttempt.IsNull) currentBestMoveInLoopAttempt = movesToOrder[0];

                for (int i = 0; i < movesToOrder.Length; i++)
                {
                    Move move = movesToOrder[i];
                    board.MakeMove(move);
                    int score = -Negamax(board, currentIterativeDepth - 1, -beta, -alpha, 1, 1);
                    board.UndoMove(move);
                    if (timeIsUp) goto EndRootMoveLoop_ID;
                    if (score > scoreThisAspirationLoop)
                    {
                        scoreThisAspirationLoop = score;
                        currentBestMoveInLoopAttempt = move;
                        alpha = Math.Max(alpha, score);
                    }
                    if (alpha >= beta)
                    {
                        if (useAspiration) aspirationSearchFailed = true;
                        break;
                    }
                }
            EndRootMoveLoop_ID:;
                if (timeIsUp) break;
                if (aspirationSearchFailed)
                {
                    if (scoreThisAspirationLoop <= (scoreFromPrevIteration - aspirationWindowSize)) { alpha = -InfiniteScore; beta = scoreThisAspirationLoop + aspirationWindowSize; }
                    else { alpha = scoreThisAspirationLoop - aspirationWindowSize; beta = InfiniteScore; }
                    aspirationWindowSize *= 2;
                }
                else
                {
                    scoreFromPrevIteration = scoreThisAspirationLoop;
                    bestScoreRoot = scoreThisAspirationLoop;
                    if (!currentBestMoveInLoopAttempt.IsNull) bestMoveThisIteration = currentBestMoveInLoopAttempt;
                    else if (movesToOrder.Length > 0) bestMoveThisIteration = movesToOrder[0];
                    else bestMoveThisIteration = legalMoves[0];
                }
            } while (aspirationSearchFailed && !timeIsUp && aspirationWindowSize < InfiniteScore / 2);

            if (timeIsUp) break;

            if (!bestMoveThisIteration.IsNull)
            {
                bestMoveOverall = bestMoveThisIteration;
                bestMoveFromPrevIteration = bestMoveOverall;
                completedSearchDepth = currentIterativeDepth;
                if (PerDepthDebugging)
                {
                    long totalNodes = negamaxPositions + qsearchPositions;
                    string timeDisplay = currentTimer.MillisecondsElapsedThisTurn <= 9999 ? $"{currentTimer.MillisecondsElapsedThisTurn}ms" : $"{(currentTimer.MillisecondsElapsedThisTurn / 1000.0):F1}s";
                    string nodesDisplay = totalNodes < 10000 ? $"{totalNodes}" : totalNodes < 10000000 ? $"{(totalNodes / 1000.0):F1}k" : $"{(totalNodes / 1000000.0):F1}m";
                    DebugLog($"Depth {currentIterativeDepth}, Score {bestScoreRoot}, BestMove {bestMoveOverall}, Nodes {nodesDisplay}, Time {timeDisplay}");
                }
            }
            else { break; }
            currentIterativeDepth++;
        }

        if (bestMoveOverall.IsNull && legalMoves.Length > 0) bestMoveOverall = legalMoves[0];

        if (Math.Abs(bestScoreRoot) >= MATE_FOUND_SCORE)
        {
            int pliesToMate = InfiniteScore - Math.Abs(bestScoreRoot);
            completedSearchDepth = MaxSafetyDepth - pliesToMate;
        }

        return LogEval(board, completedSearchDepth, false, bestMoveOverall);
    }

    private Move LogEval(Board board, int depthCompleted, bool isForcedMove, Move moveForThisTurn)
    {
        if (PerMoveDebugging)
        {
            if (isForcedMove)
            {
                Console.WriteLine($"\n{GetType().Name}: FORCED MOVE! ({moveForThisTurn})");
            }
            else if (currentTimer != null)
            {
                Console.WriteLine();
                string mateInfo = GetMateInMoves(bestScoreRoot);
                int evalForDisplay = isWhitePlayer ? bestScoreRoot : -bestScoreRoot;
                string npsDisplay = currentTimer.MillisecondsElapsedThisTurn > 0 ? $"{((negamaxPositions + qsearchPositions) / (currentTimer.MillisecondsElapsedThisTurn / 1000.0) / 1000):F0}knps" : "0knps";

                DebugLog($"Depth: {depthCompleted}");
                DebugLog(mateInfo ?? "No mate found");
                DebugLog($"Eval: {evalForDisplay}");
                DebugLog($"Nodes: {negamaxPositions + qsearchPositions:N0}");
                DebugLog($"NPS: {npsDisplay}");
            }
        }
        return moveForThisTurn;
    }

    private short GetTimeSpentFraction(Timer timer) //Tuning needed
    {
        int t = timer.MillisecondsRemaining;
        int result = 20 + 99900 / (t + 1675);
        return (short)Math.Max(26, Math.Min(65, result));
    }

    private int AllocateTime(Timer timer)
    {
        if (ConstantDepth) return int.MaxValue;
        if (UseFixedTimePerMove) return Math.Max(1, Math.Min(FixedTimePerMoveMs, timer.MillisecondsRemaining - SAFETY_MARGIN));

        short timeFraction = Math.Max(GetTimeSpentFraction(timer), (short)1);
        int allocated = (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 2);
        allocated = Math.Max(10, allocated - SAFETY_MARGIN);
        allocated = Math.Min(allocated, timer.MillisecondsRemaining - SAFETY_MARGIN);
        return Math.Max(1, allocated);
    }

    private string GetMateInMoves(int score)
    {
        if (Math.Abs(score) < MATE_FOUND_SCORE) return null;

        int pliesToMate = InfiniteScore - Math.Abs(score);
        int movesToMate = (pliesToMate + 1) / 2;
        return $"{(Math.Sign(score) > 0 ? "Winning" : "Losing")} Mate in {movesToMate} moves ({pliesToMate} ply)";
    }

    private int Negamax(Board board, int depth, int alpha, int beta, int ply, int realPly)
    {
        // -- Tunable parameters for this function are now at the top of the class --

        CheckTime();
        if (timeIsUp) return 0;
        negamaxPositions++;
        if (board.IsDraw()) return 0;

        alpha = Math.Max(alpha, -InfiniteScore + realPly);
        beta = Math.Min(beta, InfiniteScore - realPly);
        if (alpha >= beta) return alpha;

        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];
        bool ttHit = ttEntry.Key == key;
        Move ttMove = ttHit ? ttEntry.BestMove : Move.NullMove;

        if (ttHit && ttEntry.Depth >= depth)
        {
            // The critical mate score adjustment happens here when retrieving from TT
            short scoreFromTT = AdjustMateScoreFromTT(ttEntry.Score, realPly);
            if (ttEntry.Flag == EXACT) return scoreFromTT;
            if (ttEntry.Flag == ALPHA && scoreFromTT <= alpha) return alpha;
            if (ttEntry.Flag == BETA && scoreFromTT >= beta) return beta;
        }

        if (depth <= 0)
        {
            return Quiescence(board, alpha, beta, ply, 0, realPly);
        }

        Move[] moves = board.GetLegalMoves();
        if (moves.Length == 0)
        {
            return board.IsInCheck() ? (-InfiniteScore + realPly) : 0;
        }

        int standPat = 0;
        bool inCheck = board.IsInCheck();
        if (!inCheck) standPat = Evaluate(board);
        bool inMateZone = Math.Abs(standPat) >= MATE_FOUND_SCORE;

        // Null Move Pruning
        if (!inCheck && depth >= NMP_MIN_DEPTH && ply > 0 && !IsEndgame(board) && !inMateZone)
        {
            board.ForceSkipTurn();
            int R = depth > NMP_R_DEEP_DEPTH ? NMP_R_DEEP_REDUCTION : NMP_R_BASE;
            int nullScore = -Negamax(board, depth - R - 1, -beta, -beta + 1, ply + 1, realPly + 1);
            board.UndoSkipTurn();
            if (timeIsUp) return 0;
            if (nullScore >= beta) return beta;
        }

        // Futility Pruning
        if (depth <= FUTILITY_PRUNING_MAX_DEPTH_1 && !inCheck && !inMateZone && standPat + FUTILITY_PRUNING_MARGIN_1 < alpha)
        {
            return Quiescence(board, alpha, beta, ply, 0, realPly);
        }
        if (depth <= FUTILITY_PRUNING_MAX_DEPTH_2 && !inCheck && !inMateZone && standPat + FUTILITY_MARGIN_PER_PLY_2 * depth <= alpha)
        {
            return Quiescence(board, alpha, beta, ply, 0, realPly);
        }

        moves = OrderMoves(moves, board, ply, ttMove);
        int originalAlpha = alpha;
        Move bestMoveCurrentNode = Move.NullMove;
        int localBestScore = -InfiniteScore;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];

            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();
            int newDepth = depth - 1;

            // Extensions
            bool isPawnPushTo7th = board.IsWhiteToMove && move.MovePieceType == PieceType.Pawn && move.TargetSquare.Rank == 6;
            bool isPawnPushTo2nd = !board.IsWhiteToMove && move.MovePieceType == PieceType.Pawn && move.TargetSquare.Rank == 1;
            if (givesCheck || isPawnPushTo7th || isPawnPushTo2nd)
            {
                newDepth += LME_AMOUNT;
            }

            int score;
            bool isQuiet = !move.IsCapture && !move.IsPromotion;

            // SEE-based Reductions
            if (ENABLE_SEE_REDUCTIONS && depth >= SEE_REDUCTION_MIN_DEPTH && move.IsCapture && !move.IsPromotion && !inCheck)
            {
                if (CalculateSEE(board, move) < SEE_PRUNING_MARGIN)
                {
                    int reducedDepth = Math.Max(newDepth - SEE_REDUCTION_AMOUNT, 1);
                    score = -Negamax(board, reducedDepth, -alpha - 1, -alpha, ply + 1, realPly + 1);
                    if (score > alpha && !timeIsUp)
                    {
                        score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
                    }
                    goto AfterSearch;
                }
            }

            // Late Move Reductions (LMR)
            bool useLMR = depth >= LMR_MIN_DEPTH && i >= LMR_MIN_MOVE_COUNT && isQuiet && !givesCheck && !inMateZone && !IsKillerMove(move, ply);
            if (useLMR)
            {
                int reduction = (int)(0.75 + Math.Log(depth) * Math.Log(i + 1) / LMR_LOG_DIVISOR);
                if (historyMoves[move.StartSquare.Index, move.TargetSquare.Index] > HISTORY_SCORE_CAP / 4)
                {
                    reduction = Math.Max(reduction - 1, 0);
                }
                int reducedDepth = Math.Max(newDepth - reduction, 1);
                score = -Negamax(board, reducedDepth, -alpha - 1, -alpha, ply + 1, realPly + 1);
                if (score > alpha && score < beta && !timeIsUp)
                {
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
                }
            }
            else
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }

        AfterSearch:
            board.UndoMove(move);
            if (timeIsUp) return 0;

            if (score > localBestScore)
            {
                localBestScore = score;
                bestMoveCurrentNode = move;
                alpha = Math.Max(alpha, score);
                if (alpha >= beta)
                {
                    if (isQuiet)
                    {
                        UpdateKillerMoves(move, ply);
                        UpdateHistoryMove(move, depth * depth);
                    }
                    AddTT(key, depth, AdjustMateScoreForTTStorage(beta, realPly), BETA, move);
                    return beta;
                }
            }
        }

        byte flag = localBestScore <= originalAlpha ? ALPHA : EXACT;
        AddTT(key, depth, AdjustMateScoreForTTStorage(localBestScore, realPly), flag, bestMoveCurrentNode);
        return localBestScore;
    }

    private int Quiescence(Board board, int alpha, int beta, int ply, int qDepth, int realPly)
    {
        qsearchPositions++;
        if (timeIsUp) return 0;
        int standPat = Evaluate(board);
        if (standPat >= beta) return beta;
        if (standPat > alpha) alpha = standPat;

        Move[] captures = board.GetLegalMoves(true);
        Move[] orderedMoves = OrderMoves(captures, board, ply);

        foreach (Move move in orderedMoves)
        {
            if (!move.IsPromotion)
            {
                // --- DYNAMIC MARGIN LOGIC TO TEST ---
                // (Using the Q_SEE_PRUNING_MARGIN from the tunable parameters section)

                // 1. If we're already doing well, be very strict.
                // If standPat is 100 points better than alpha, don't allow any losing captures.
                if (standPat > alpha + 100)
                {
                    if (CalculateSEE(board, move) < 0) continue;
                }
                // 2. Otherwise, use our standard small margin.
                else
                {
                    if (CalculateSEE(board, move) < Q_SEE_PRUNING_MARGIN) continue;
                }
            }
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, ply + 1, qDepth + 1, realPly + 1);
            board.UndoMove(move);
            if (timeIsUp) return 0;
            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }
        return alpha;
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
                {
                    moveScore += TT_MOVE_BONUS;
                }
                else if (ply == 0 && pvMoveHint.HasValue && move == pvMoveHint.Value)
                {
                    moveScore += PREVIOUS_BEST_MOVE_BONUS;
                }
                if (move.IsCapture)
                {
                    int seeScoreVal = CalculateSEE(board, move);
                    if (seeScoreVal >= 0) moveScore += GOOD_CAPTURE_BONUS + seeScoreVal;
                    else moveScore += LOSING_CAPTURE_BONUS + seeScoreVal;
                }
                else
                {
                    if (IsKillerMove(move, ply)) moveScore += KILLER_MOVE_BONUS;
                    moveScore += Math.Min(historyMoves[move.StartSquare.Index, move.TargetSquare.Index], HISTORY_MAX_BONUS);
                }
                if (move.IsPromotion) moveScore += PROMOTION_BASE_BONUS + GetSeeValue(move.PromotionPieceType);
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

    private int Evaluate(Board board)
    {
        if (board.IsDraw()) return 0;
        int score = 0;
        bool isEndgame = IsEndgame(board);
        int whiteBishopCount = 0, blackBishopCount = 0;
        const int BISHOP_PAIR_BONUS = 25; // Tunable eval term
        const int TEMPO_BONUS = 10; // Tunable eval term

        for (int pieceTypeIndex = 0; pieceTypeIndex < 6; pieceTypeIndex++)
        {
            PieceType pt = (PieceType)(pieceTypeIndex + 1);
            int baseVal = PieceValues[pieceTypeIndex];
            int[] pstForPieceType = pt == PieceType.King ? (isEndgame ? KingEndGamePST : KingMiddleGamePST) : PiecePSTs[pieceTypeIndex];
            ulong whiteBitboard = board.GetPieceBitboard(pt, true);
            if (pt == PieceType.Bishop) whiteBishopCount = BitOperations.PopCount(whiteBitboard);
            while (whiteBitboard != 0)
            {
                int squareIndex = BitOperations.TrailingZeroCount(whiteBitboard);
                score += baseVal + pstForPieceType[squareIndex];
                if (isEndgame && pt == PieceType.Pawn) score += new Square(squareIndex).Rank * 5;
                whiteBitboard &= whiteBitboard - 1;
            }
            ulong blackBitboard = board.GetPieceBitboard(pt, false);
            if (pt == PieceType.Bishop) blackBishopCount = BitOperations.PopCount(blackBitboard);
            while (blackBitboard != 0)
            {
                int squareIndex = BitOperations.TrailingZeroCount(blackBitboard);
                score -= baseVal + pstForPieceType[squareIndex ^ 56];
                if (isEndgame && pt == PieceType.Pawn) score -= (7 - new Square(squareIndex).Rank) * 5;
                blackBitboard &= blackBitboard - 1;
            }
        }

        if (whiteBishopCount >= 2) score += BISHOP_PAIR_BONUS;
        if (blackBishopCount >= 2) score -= BISHOP_PAIR_BONUS;

        if (isEndgame && Math.Abs(EvaluateMaterialOnly(board)) > 150)
        {
            Square whiteKingSquare = board.GetKingSquare(true);
            Square blackKingSquare = board.GetKingSquare(false);
            int kingDist = Math.Abs(whiteKingSquare.File - blackKingSquare.File) + Math.Abs(whiteKingSquare.Rank - blackKingSquare.Rank);
            int proximityBonus = (14 - kingDist) * 5;
            if (score > 0) score += proximityBonus; else if (score < 0) score -= proximityBonus;
        }

        score += board.IsWhiteToMove ? TEMPO_BONUS : -TEMPO_BONUS;
        return board.IsWhiteToMove ? score : -score;
    }

    // --- Helper Functions ---

    private int GetSeeValue(PieceType pt)
    {
        if (pt == PieceType.None) return 0;
        return SeePieceValues[(int)pt - 1];
    }

    private (PieceType type, Square fromSquare) GetLeastValuableAttacker(Board board, Square targetSquare, bool attackerIsWhite, ulong occupiedHypothetical)
    {
        for (int pieceTypeId = 1; pieceTypeId <= 6; pieceTypeId++)
        {
            PieceType currentPieceTypeToTest = (PieceType)pieceTypeId;
            ulong potentialAttackersOfThisType = board.GetPieceBitboard(currentPieceTypeToTest, attackerIsWhite) & occupiedHypothetical;
            if (potentialAttackersOfThisType == 0) continue;

            ulong attackRaysToTarget;
            switch (currentPieceTypeToTest)
            {
                case PieceType.Pawn: attackRaysToTarget = BitboardHelper.GetPawnAttacks(targetSquare, !attackerIsWhite); break;
                case PieceType.Knight: attackRaysToTarget = BitboardHelper.GetKnightAttacks(targetSquare); break;
                case PieceType.Bishop: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Bishop, targetSquare, occupiedHypothetical); break;
                case PieceType.Rook: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Rook, targetSquare, occupiedHypothetical); break;
                case PieceType.Queen: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Queen, targetSquare, occupiedHypothetical); break;
                case PieceType.King: attackRaysToTarget = BitboardHelper.GetKingAttacks(targetSquare); break;
                default: continue;
            }

            ulong actualAttackers = attackRaysToTarget & potentialAttackersOfThisType;
            if (actualAttackers != 0)
            {
                return (currentPieceTypeToTest, new Square(BitOperations.TrailingZeroCount(actualAttackers)));
            }
        }
        return (PieceType.None, default(Square));
    }

    private int CalculateSEE(Board board, Move move)
    {
        if (!move.IsCapture) return 0;
        Square targetSquare = move.TargetSquare;
        Span<int> gain = stackalloc int[32];
        int d = 0;
        ulong occupiedHypothetical = board.AllPiecesBitboard;
        bool currentSideToRecaptureIsWhite = !board.IsWhiteToMove;
        gain[d++] = GetSeeValue(move.CapturePieceType);
        occupiedHypothetical ^= (1UL << move.StartSquare.Index);
        PieceType pieceOnSquareForNextCapture = move.MovePieceType;

        while (true)
        {
            (PieceType lvaType, Square lvaFromSquare) = GetLeastValuableAttacker(board, targetSquare, currentSideToRecaptureIsWhite, occupiedHypothetical);
            if (lvaType == PieceType.None) break;
            occupiedHypothetical ^= (1UL << lvaFromSquare.Index);
            gain[d++] = GetSeeValue(pieceOnSquareForNextCapture);
            pieceOnSquareForNextCapture = lvaType;
            currentSideToRecaptureIsWhite = !currentSideToRecaptureIsWhite;
            if (d >= 32) break;
        }

        for (int k = d - 1; k > 0; k--)
        {
            gain[k - 1] = -Math.Max(-gain[k - 1], gain[k] - gain[k - 1]);
        }
        return gain[0];
    }

    private int EvaluateMaterialOnly(Board board)
    {
        int materialScore = 0;
        for (int i = 0; i < 5; i++)
        {
            materialScore += PieceValues[i] * (board.GetPieceList((PieceType)(i + 1), true).Count - board.GetPieceList((PieceType)(i + 1), false).Count);
        }
        return materialScore;
    }

    private bool IsEndgame(Board board)
    {
        if (board.ZobristKey != lastBoardHash)
        {
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = board.ZobristKey;
        }
        const int endgameTotalPieceThreshold = 11;
        return cachedPieceCount <= endgameTotalPieceThreshold;
    }

    private void CheckTime()
    {
        if (ConstantDepth) return;
        if (((negamaxPositions + qsearchPositions) & TIME_CHECK_MASK) == 0)
        {
            if (currentTimer.MillisecondsElapsedThisTurn >= absoluteTimeLimit)
            {
                timeIsUp = true;
            }
        }
    }

    private bool IsKillerMove(Move move, int ply)
    {
        if (ply < 0 || ply >= MAX_KILLER_PLY) return false;
        return move == killerMoves[ply, 0] || move == killerMoves[ply, 1];
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        if (move.IsCapture || move.IsPromotion || ply < 0 || ply >= MAX_KILLER_PLY) return;
        if (move != killerMoves[ply, 0])
        {
            killerMoves[ply, 1] = killerMoves[ply, 0];
            killerMoves[ply, 0] = move;
        }
    }

    private const int HISTORY_SCORE_CAP = 1_000_000;
    private void UpdateHistoryMove(Move move, int bonus)
    {
        if (move.IsCapture || move.IsPromotion) return;
        int startIdx = move.StartSquare.Index;
        int targetIdx = move.TargetSquare.Index;
        historyMoves[startIdx, targetIdx] = Math.Min(historyMoves[startIdx, targetIdx] + bonus, HISTORY_SCORE_CAP);
        if (((negamaxPositions + qsearchPositions) & TIME_CHECK_MASK) == 0) DecayHistory();
    }

    private void DecayHistory()
    {
        for (int i = 0; i < 64; i++) for (int j = 0; j < 64; j++) historyMoves[i, j] /= 2;
    }

    private Move HandleForcedMove(Move move, Board board, int completedDepthForLog, bool isForcedMove)
    {
        this.bestScoreRoot = Evaluate(board) * (board.IsWhiteToMove ? 1 : -1);
        this.completedSearchDepth = completedDepthForLog;
        return LogEval(board, completedDepthForLog, isForcedMove, move);
    }

    private struct TTEntry { public ulong Key; public short Depth; public short Score; public byte Flag; public Move BestMove; }

    private const byte EXACT = 0, ALPHA = 1, BETA = 2;
    private int GetTTIndex(ulong key) => (int)(key & ttMask);

    private void AddTT(ulong key, int depth, short scoreForTT, byte flag, Move bestMove)
    {
        int index = GetTTIndex(key);
        ref TTEntry entry = ref tt[index];
        bool replace = entry.Key == 0 || depth >= entry.Depth;
        if (replace)
        {
            entry.Key = key;
            entry.Depth = (short)depth;
            entry.Score = scoreForTT;
            entry.Flag = flag;
            entry.BestMove = bestMove;
        }
    }

    private short AdjustMateScoreForTTStorage(int scoreFromNode, int currentRealPly)
    {
        if (Math.Abs(scoreFromNode) >= MATE_FOUND_SCORE)
        {
            int sign = Math.Sign(scoreFromNode);
            return (short)(scoreFromNode + (sign * currentRealPly));
        }
        return (short)scoreFromNode;
    }

    private short AdjustMateScoreFromTT(short ttScore, int currentRealPly)
    {
        if (Math.Abs(ttScore) >= MATE_FOUND_SCORE)
        {
            int sign = Math.Sign(ttScore);
            return (short)(ttScore - (sign * currentRealPly));
        }
        return ttScore;
    }

    private void DebugLog(string message)
    {
        Console.WriteLine($"{GetType().Name} {message}");
    }

    // -- Piece Square Tables (Perspective of White, Black's are flipped via XOR 56) --
    // Keep as actual squares
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
        PawnPST, KnightPST, BishopPST, RookPST, QueenPST, KingMiddleGamePST
    };
}