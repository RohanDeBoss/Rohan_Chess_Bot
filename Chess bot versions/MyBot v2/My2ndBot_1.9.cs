using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

// v1.8.3 (Time Management Refactor)
public class MyBot : IChessBot
{
    // Search Parameters
    private const bool ConstantDepth = false;
    private const short MaxDepth = 5; // Used when ConstantDepth is true
    private const short MaxSafetyDepth = 99;
    private const int InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22; // Approx 4 million entries

    // Move Ordering Bonuses
    private const int TT_MOVE_BONUS = 10_000_000;
    private const int PREVIOUS_BEST_MOVE_BONUS = 5_000_000;
    private const int CAPTURE_BASE_BONUS = 1_000_000;
    private const int PROMOTION_BASE_BONUS = 900_000;
    private const int KILLER_MOVE_BONUS = 800_000;
    private const int MVV_LVA_MULTIPLIER = 5; // Multiplier for MVV-LVA scoring
    private const int HISTORY_MAX_BONUS = 700_000;

    // Time Management
    private const int INITIAL_ASPIRATION_WINDOW = 150;
    private const int MAX_ASPIRATION_DEPTH = 3;
    private const int CHECKMATE_SCORE_THRESHOLD = 25000; // Eval cutoff for mate scores
    private const int SAFETY_MARGIN = 15; // Small time buffer in ms
    private const int TIME_CHECK_NODES = 2048; // How often to check the time in nodes

    // Static Fields
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = (ulong)(TT_SIZE - 1);
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 }; // Pawn, Knight, Bishop, Rook, Queen, King(0)

    // Instance Fields
    private long negamaxPositions = 0;
    private long qsearchPositions = 0;
    private int bestScore;
    private List<Move> killerMoves = new List<Move>();
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private int currentDepth; // Actual depth being searched in ID
    private Timer currentTimer;
    private volatile bool timeIsUp; // Flag to signal time expiration globally
    private long absoluteTimeLimit; // The absolute time limit for the current move in ms

    // Helper to check time limit frequently but not excessively
    private void CheckTime()
    {
        if ((negamaxPositions + qsearchPositions) % TIME_CHECK_NODES == 0)
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
        int result = 23 + 99900 / (t + 1675);
        return (short)Math.Max(26, Math.Min(65, result)); // Clamp between 26 and 65
    }

    public Move Think(Board board, Timer timer)
    {
        currentTimer = timer;
        timeIsUp = false; // Reset time flag for the new turn

        if (timer.MillisecondsRemaining <= 0)
        {
            var moves = board.GetLegalMoves();
            return moves.Length > 0 ? moves[0] : Move.NullMove;
        }

        // --- Initialization ---
        killerMoves.Clear();
        Array.Clear(historyMoves, 0, historyMoves.Length);
        negamaxPositions = 0;
        qsearchPositions = 0;
        currentDepth = 0;
        lastBoardHash = 0; // Reset board hash cache
        cachedPieceCount = -1;

        short depth = 1;
        int previousBestScore = 0; // Score from previous completed depth
        Move previousBestMove = Move.NullMove; // Best move from previous completed depth
        var legalMoves = board.GetLegalMoves();
        Move bestMove = legalMoves.Length > 0 ? legalMoves[0] : Move.NullMove; // Overall best move found
        Move bestMoveThisIteration = bestMove; // Best move for the current depth being searched

        // --- Handle Trivial Cases ---
        if (legalMoves.Length == 0)
        {
            bestScore = board.IsInCheck() ? -InfiniteScore + 50 : 0; // Checkmate or Stalemate
            return Move.NullMove;
        }
        if (legalMoves.Length == 1)
        {
            return HandleForcedMove(legalMoves[0], board, 1, true); // Only one move possible
        }
        foreach (Move move in legalMoves) // Check for immediate checkmate
        {
            if (IsCheckmateMove(move, board))
            {
                return HandleForcedMove(move, board, 1, false, InfiniteScore - 50);
            }
        }

        // --- Time Allocation ---
        short timeFraction = Math.Max(GetTimeSpentFraction(timer), (short)1);
        int allocatedTime = ConstantDepth
            ? int.MaxValue
            : Math.Max(10, (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 4) - SAFETY_MARGIN);
        absoluteTimeLimit = timer.MillisecondsElapsedThisTurn + allocatedTime;

        // --- Iterative Deepening Loop ---
        while (depth <= MaxSafetyDepth && (ConstantDepth ? depth <= MaxDepth : true))
        {
            // Check time before starting a new depth. If time ran out during the previous search, stop.
            if (timeIsUp) break;
            if (!ConstantDepth && currentTimer.MillisecondsRemaining <= SAFETY_MARGIN * 2) break;

            currentDepth = depth;
            bestMoveThisIteration = Move.NullMove; // Reset for this depth

            bool useAspiration = depth > MAX_ASPIRATION_DEPTH && Math.Abs(previousBestScore) < CHECKMATE_SCORE_THRESHOLD;
            int alpha = -InfiniteScore;
            int beta = InfiniteScore;
            int aspirationWindow = INITIAL_ASPIRATION_WINDOW;
            bool aspirationFailed;
            int currentBestScore = -InfiniteScore; // Track score for this iteration

            if (useAspiration)
            {
                alpha = previousBestScore - aspirationWindow;
                beta = previousBestScore + aspirationWindow;
            }

            // --- Aspiration Window Loop ---
            do
            {
                aspirationFailed = false;
                currentBestScore = -InfiniteScore; // Reset score for this aspiration attempt
                Move currentBestMoveAspiration = Move.NullMove; // Track best move within this attempt

                Move[] movesToOrder = OrderMoves(legalMoves, board, 0, previousBestMove);
                if (movesToOrder.Length > 0) currentBestMoveAspiration = movesToOrder[0];

                // --- Root Move Loop ---
                for (int i = 0; i < movesToOrder.Length; i++)
                {
                    Move move = movesToOrder[i];

                    board.MakeMove(move);
                    int score = -Negamax(board, depth - 1, -beta, -alpha, 1, 1);
                    board.UndoMove(move);

                    // Check time immediately after the call returns
                    if (timeIsUp) goto EndRootMoveLoop; // Exit root move loop if time ran out during search

                    if (score > currentBestScore)
                    {
                        currentBestScore = score;
                        currentBestMoveAspiration = move;
                        alpha = Math.Max(alpha, score); // Update alpha
                    }

                    // Handle Beta Cutoff / Aspiration Failure
                    if (alpha >= beta)
                    {
                        if (useAspiration)
                        {
                            // If score >= beta inside an aspiration window, it failed high.
                            aspirationFailed = true;
                            alpha = currentBestScore - aspirationWindow; // Reset alpha for re-search
                            beta = InfiniteScore; // Widen beta to infinity for re-search
                        }
                        // If aspiration failed, don't break yet, continue re-search with wider bounds.
                        // If it didn't fail (normal beta cutoff), break the loop.
                        if (!aspirationFailed) break;
                    }
                } // --- End Root Move Loop ---

            EndRootMoveLoop:; // Target for time-up break

                // Check time again after finishing the loop over root moves
                if (timeIsUp) break; // Exit aspiration loop

                // Handle Aspiration Window Re-search
                if (aspirationFailed)
                {
                    // Aspiration failed high (score >= beta), beta was reset to Inf.
                    // Or aspiration failed low (all moves <= alpha), alpha needs reset.
                    if (currentBestScore <= alpha) // Check if it failed low
                    {
                        alpha = -InfiniteScore; // Widen alpha to -infinity
                        beta = currentBestScore + aspirationWindow; // Reset beta based on best score found
                    }
                    // Widen window for next attempt if needed (usually only re-search once)
                    aspirationWindow *= 3; // Can adjust widening factor
                }
                else
                {
                    // Aspiration successful (or not used), update results for this iteration
                    previousBestScore = currentBestScore;
                    bestScore = currentBestScore;
                    if (!currentBestMoveAspiration.IsNull)
                    {
                        bestMoveThisIteration = currentBestMoveAspiration;
                    }
                }

            } while (aspirationFailed && !timeIsUp); // Repeat if aspiration failed AND time permits

            // --- Iteration Completion ---
            if (timeIsUp) break; // Exit ID loop if time ran out during aspiration/search

            // If this iteration completed and found a valid move, update the overall best move
            if (!bestMoveThisIteration.IsNull)
            {
                bestMove = bestMoveThisIteration;
                previousBestMove = bestMove; // Use this move for ordering next iteration
            }
            else
            {
                // If iteration completed but no move was found (e.g., time ran out exactly after last Negamax call)
                // break and use the result from the previous iteration.
                break;
            }

            // Optional: Stop early if a checkmate is found
            if (Math.Abs(bestScore) > CHECKMATE_SCORE_THRESHOLD && !ConstantDepth)
            {
                break;
            }

            depth++; // Go to the next depth

        } // --- End Iterative Deepening Loop ---

        // Fallback if no move was ever selected (e.g., time out on depth 1)
        if (bestMove.IsNull && legalMoves.Length > 0)
        {
            bestMove = legalMoves[0];
        }

        if (!ConstantDepth) LogEval(board, currentDepth, false);
        return bestMove;
    }

    private void DebugLog(string message)
    {
        Console.WriteLine($"{GetType().Name} {message}");
    }

    private void LogEval(Board board, int depth, bool isForcedMove)
    {
        if (currentTimer != null && currentTimer.MillisecondsRemaining <= 0 && !isForcedMove) return; // Don't log if time is up unless forced

        if (isForcedMove)
        {
            Console.WriteLine($"\n{GetType().Name}: FORCED MOVE!");
        }
        else
        {
            Console.WriteLine();
            DebugLog($"Depth: {depth}");
            string mateInfo = GetMateInMoves(bestScore) ?? string.Empty;
            DebugLog(!string.IsNullOrEmpty(mateInfo) ? mateInfo : "No mate found");
            // Display eval from white's perspective
            DebugLog($"Eval: {bestScore * (board.IsWhiteToMove ? 1 : -1)}");
            DebugLog($"Nodes: {negamaxPositions + qsearchPositions:N0}");
        }
    }

    private string? GetMateInMoves(int score)
    {
        // Check if the score indicates a mate
        if (Math.Abs(score) > CHECKMATE_SCORE_THRESHOLD)
        {
            // Calculate plies to mate, rounding up
            int sign = Math.Sign(score);
            int matePly = (InfiniteScore - Math.Abs(score) + 49) / 50;
            return $"{(sign > 0 ? "Winning" : "Losing")} Mate in {matePly} ply";
        }
        return null;
    }

    private Move[] OrderMoves(Move[] moves, Board board, int ply, Move? previousBestMove = null)
    {
        if (moves.Length <= 1) return moves; // No need to order 0 or 1 move

        int[] scores = new int[moves.Length];
        TTEntry ttEntry = tt[GetTTIndex(board.ZobristKey)];
        Move ttMove = (ttEntry.Key == board.ZobristKey) ? ttEntry.BestMove : Move.NullMove;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            int score = 0;

            if (!ttMove.IsNull && move == ttMove)
                score += TT_MOVE_BONUS;
            else if (previousBestMove.HasValue && move == previousBestMove.Value)
                score += PREVIOUS_BEST_MOVE_BONUS;

            if (move.IsCapture)
            {
                Piece capturedPiece = board.GetPiece(move.TargetSquare);
                int capturedValue; // Declare here

                // --- FIX for En Passant ---
                if (capturedPiece.PieceType == PieceType.None)
                {
                    // Must be En Passant capture, captured piece is a Pawn
                    capturedValue = PieceValues[(int)PieceType.Pawn - 1]; // Index 0
                }
                else
                {
                    // Standard capture
                    capturedValue = PieceValues[(int)capturedPiece.PieceType - 1];
                }
                // --- End Fix ---

                // Attacker value should be safe as start square always has a piece
                int attackerValue = PieceValues[(int)board.GetPiece(move.StartSquare).PieceType - 1];
                score += CAPTURE_BASE_BONUS + capturedValue * MVV_LVA_MULTIPLIER - attackerValue;
            }
            else // Non-captures
            {
                if (IsKillerMove(move, ply))
                    score += KILLER_MOVE_BONUS;

                int historyScore = historyMoves[move.StartSquare.Index, move.TargetSquare.Index];
                score += Math.Min(historyScore, HISTORY_MAX_BONUS);
            }

            if (move.IsPromotion)
                score += PROMOTION_BASE_BONUS + PieceValues[(int)move.PromotionPieceType - 1];


            scores[i] = score;
        }

        Array.Sort(scores, moves, Comparer<int>.Create((a, b) => b.CompareTo(a)));
        return moves;
    }

    private bool IsKillerMove(Move move, int ply)
    {
        EnsureKillerMovesSize(ply); // Ensure list is large enough
        int index0 = ply * 2;
        int index1 = ply * 2 + 1;
        return (killerMoves.Count > index0 && move == killerMoves[index0]) ||
               (killerMoves.Count > index1 && move == killerMoves[index1]);
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        // Only update for quiet moves (non-captures, non-promotions)
        if (move.IsCapture || move.IsPromotion) return;

        EnsureKillerMovesSize(ply);
        int index0 = ply * 2;
        int index1 = ply * 2 + 1;

        // If the move is not already the first killer, shift the first to second and insert new move as first
        if (move != killerMoves[index0])
        {
            killerMoves[index1] = killerMoves[index0];
            killerMoves[index0] = move;
        }
    }

    // Helper for dynamic killer move list resizing
    private void EnsureKillerMovesSize(int ply)
    {
        int requiredSize = (ply * 2) + 2;
        while (killerMoves.Count < requiredSize)
        {
            killerMoves.Add(Move.NullMove);
        }
    }

    private const int HISTORY_SCORE_CAP = 1_000_000; // Cap history score to prevent overflow/dominance

    private void UpdateHistoryMove(Move move, int bonus) // Pass bonus directly (e.g., depth^2)
    {
        // Only update for quiet moves that cause a beta cutoff
        if (move.IsCapture || move.IsPromotion) return;
        int startIdx = move.StartSquare.Index;
        int targetIdx = move.TargetSquare.Index;
        historyMoves[startIdx, targetIdx] = Math.Min(historyMoves[startIdx, targetIdx] + bonus, HISTORY_SCORE_CAP);

        // Periodically decay history scores to prioritize recent information
        if ((negamaxPositions + qsearchPositions) % 1024 == 0) // Decay slightly more often
            DecayHistory();
    }

    private void DecayHistory()
    {
        // Simple linear decay (e.g., divide by 2 or multiply by 0.5)
        for (int i = 0; i < 64; i++)
            for (int j = 0; j < 64; j++)
                historyMoves[i, j] /= 2; // Or historyMoves[i, j] = (historyMoves[i, j] * 3) / 4; etc.
    }


    private int Negamax(Board board, int depth, int alpha, int beta, int ply, int realPly)
    {
        CheckTime();
        if (timeIsUp) return 0; // Return neutral value if time is up

        negamaxPositions++;
        bool isDraw = board.IsDraw();
        if (isDraw) return 0;

        // Mate distance pruning: Adjust bounds based on distance to root
        int mateScore = InfiniteScore - realPly * 50;
        alpha = Math.Max(alpha, -mateScore);
        beta = Math.Min(beta, mateScore);
        if (alpha >= beta) return alpha; // Prune if bounds cross due to mate distance

        // Transposition Table Lookup
        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];
        bool ttHit = ttEntry.Key == key;
        Move ttMove = Move.NullMove;

        if (ttHit && ttEntry.Depth >= depth)
        {
            short ttScore = AdjustMateScore(ttEntry.Score, ply, realPly); // Adjust stored mate score to current ply
            if (ttEntry.Flag == EXACT) return ttScore;
            if (ttEntry.Flag == ALPHA && ttScore <= alpha) return alpha;
            if (ttEntry.Flag == BETA && ttScore >= beta) return beta;
        }
        if (ttHit) ttMove = ttEntry.BestMove;

        // Base Case: Enter Quiescence Search
        if (depth <= 0)
        {
            return Quiescence(board, alpha, beta, ply, 0);
        }

        // Generate legal moves
        Move[] moves = board.GetLegalMoves();

        // Check for Checkmate / Stalemate
        if (moves.Length == 0)
        {
            return board.IsInCheck() ? -InfiniteScore + realPly * 50 : 0;
        }

        // Static Evaluation for Pruning (calculate only if needed)
        int standPat = 0; // Initialize lazy eval
        // Conditions for NMP/Futility/Razor: in check, depth, endgame status
        bool inCheck = board.IsInCheck();
        bool needEvalForPruning = (!inCheck && depth <= 3) || (!inCheck && depth >= 3); // Simplified: needed if not in check and depth allows NMP/Futility/Razor
        if (needEvalForPruning) standPat = Evaluate(board);


        // --- Pruning Techniques ---
        // Null Move Pruning (NMP)
        if (!inCheck && depth >= 3 && ply > 0 && !IsEndgame(board) && Math.Abs(standPat) < CHECKMATE_SCORE_THRESHOLD)
        {
            board.ForceSkipTurn();
            int reduction = (depth > 6) ? 3 : 2; // R = 2 or 3
            int nullScore = -Negamax(board, depth - reduction - 1, -beta, -beta + 1, ply + 1, realPly + 1);
            board.UndoSkipTurn();

            if (timeIsUp) return 0; // Check time after NMP search
            if (nullScore >= beta) return beta; // Prune if null move proves sufficient
        }

        // Razoring (at depth 1)
        if (depth == 1 && !inCheck && standPat + 200 < alpha) // Threshold tunable
        {
            // --- Reverted Change ---
            return Quiescence(board, alpha, beta, ply, 0); // Call QSearch
                                                           // --- End Reverted Change ---
        }

        // Futility Pruning (at shallow depths)
        bool inMateZone = Math.Abs(standPat) > CHECKMATE_SCORE_THRESHOLD; // Don't prune near mate
        if (depth <= 2 && !inCheck && !inMateZone)
        {
            int futilityMargin = 150 * depth; // Tunable margin
            if (standPat + futilityMargin <= alpha)
            {
                // --- Reverted Change ---
                return Quiescence(board, alpha, beta, ply, 0); // Call QSearch
                                                               // --- End Reverted Change ---
            }
        }
        // --- End Pruning ---


        // Order Moves
        moves = OrderMoves(moves, board, ply, ttMove);
        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int localBestScore = -InfiniteScore;

        // --- Search Moves Loop ---
        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();

            int newDepth = depth - 1;
            // Extensions: Check extension (limited depth)
            if (givesCheck && newDepth < MaxSafetyDepth - 1) newDepth = Math.Min(MaxSafetyDepth, newDepth + 1);

            // Late Move Reductions (LMR)
            int score;
            bool isQuiet = !move.IsCapture && !move.IsPromotion;
            bool useLMR = depth > 2 && i >= 2 && isQuiet && !givesCheck && !inMateZone;

            if (useLMR)
            {
                int reduction = (int)(0.75 + Math.Log(depth) * Math.Log(i + 1) / 2.0); // Basic LMR formula
                int historyScore = historyMoves[move.StartSquare.Index, move.TargetSquare.Index];
                if (historyScore > HISTORY_SCORE_CAP / 4) reduction = Math.Max(reduction - 1, 0); // Reduce less for good history
                int reducedDepth = Math.Max(newDepth - reduction, 1);

                // Search with Null Window
                score = -Negamax(board, reducedDepth, -alpha - 1, -alpha, ply + 1, realPly + 1);

                // Re-search if LMR failed high
                if (score > alpha && score < beta && !timeIsUp) // Check time before potential re-search
                {
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
                }
            }
            else // Full Depth Search (No LMR or PVS search)
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }
            board.UndoMove(move);

            if (timeIsUp) return 0; // Check time after recursive call returns

            // Update Best Score and Alpha
            if (score > localBestScore)
            {
                localBestScore = score;
                bestMove = move;
                alpha = Math.Max(alpha, score);

                // Beta Cutoff Check
                if (alpha >= beta)
                {
                    if (isQuiet) // Update heuristics only for quiet moves causing cutoff
                    {
                        UpdateKillerMoves(move, ply);
                        UpdateHistoryMove(move, depth * depth); // Bonus based on depth squared
                    }
                    AddTT(key, depth, AdjustMateScoreForStorage(beta, ply, realPly), BETA, move);
                    return beta; // Fail high
                }
            }
        } // --- End Search Moves Loop ---

        // Store result in Transposition Table
        byte flag = localBestScore <= originalAlpha ? ALPHA : EXACT;
        AddTT(key, depth, AdjustMateScoreForStorage(localBestScore, ply, realPly), flag, bestMove);
        return localBestScore;
    }

    private int Quiescence(Board board, int alpha, int beta, int ply, int qDepth)
    {
        CheckTime();
        if (timeIsUp) return 0;

        qsearchPositions++;

        int standPat = Evaluate(board);
        if (standPat >= beta) return beta;
        if (standPat > alpha) alpha = standPat;

        // Use pseudolegal moves and filter for captures / relevant checks
        Move[] allMoves = board.GetLegalMoves(true);
        List<Move> relevantMoves = new List<Move>();

        bool inCheck = board.IsInCheck();
        bool includeChecks = (inCheck || Math.Abs(standPat) > CHECKMATE_SCORE_THRESHOLD) && qDepth <= 2; // Include checks if needed

        foreach (Move move in allMoves)
        {
            if (move.IsCapture)
            {
                // Basic Delta Pruning: If capture likely won't raise alpha, skip deeper search
                // Requires piece values readily available. Example:
                // int capturedVal = PieceValues[(int)board.GetPiece(move.TargetSquare).PieceType - 1];
                // if (standPat + capturedVal + 200 < alpha && !move.IsPromotion) continue; // 200 is safety margin

                relevantMoves.Add(move);
            }
            else if (includeChecks) // Only consider quiet moves if including checks
            {
                // Make/Undo is simplest way to check if it's a check, though potentially slow
                board.MakeMove(move);
                bool givesCheck = board.IsInCheck();
                board.UndoMove(move);
                if (givesCheck)
                {
                    relevantMoves.Add(move);
                }
            }
        }

        // Order relevant moves (captures prioritized by OrderMoves logic)
        Move[] orderedMoves = OrderMoves(relevantMoves.ToArray(), board, ply);

        foreach (Move move in orderedMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, ply + 1, qDepth + 1);
            board.UndoMove(move);

            if (timeIsUp) return 0; // Check time after recursive call

            if (score >= beta) return beta; // Beta cutoff
            if (score > alpha) alpha = score; // Update alpha
        }

        return alpha;
    }

    private int Evaluate(Board board)
    {
        if (board.IsDraw()) return 0;

        Square whiteKingSquare = board.GetKingSquare(true);
        Square blackKingSquare = board.GetKingSquare(false);
        bool isEndgame = IsEndgame(board);

        // Use appropriate PSTs based on game phase
        int[][][] adjustmentTables = new int[][][] {
            PawnTable, KnightTable, BishopTable, RookTable, QueenTable,
            isEndgame ? KingEndGame : KingMiddleGame // Select King table
        };

        int score = 0;
        int whiteBishopCount = 0;
        int blackBishopCount = 0;

        // Evaluate material and piece-square tables
        foreach (PieceList list in board.GetAllPieceLists())
        {
            int pieceTypeIndex = (int)list.TypeOfPieceInList - 1; // 0-5 for P,N,B,R,Q,K
            if (pieceTypeIndex < 0 || pieceTypeIndex > 5) continue; // Skip if invalid index

            int baseVal = PieceValues[pieceTypeIndex];
            int[][] table = adjustmentTables[pieceTypeIndex];
            int pieceSign = list.IsWhitePieceList ? 1 : -1;

            if (list.TypeOfPieceInList == PieceType.Bishop)
            {
                if (list.IsWhitePieceList) whiteBishopCount += list.Count;
                else blackBishopCount += list.Count;
            }

            foreach (Piece p in list)
            {
                // Get PST value based on piece color (flip rank for white)
                int rank = p.IsWhite ? 7 - p.Square.Rank : p.Square.Rank;
                int file = p.Square.File;
                int pstValue = table[rank][file];
                score += pieceSign * (baseVal + pstValue);

                // Add endgame pawn advancement bonus
                if (isEndgame && p.PieceType == PieceType.Pawn)
                {
                    int advancementBonus = p.IsWhite ? p.Square.Rank : (7 - p.Square.Rank);
                    score += pieceSign * advancementBonus * 5; // Bonus of 5 per rank advanced
                }
            }
        }

        // Add Bishop Pair Bonus
        const int BISHOP_PAIR_BONUS = 50;
        if (whiteBishopCount >= 2) score += BISHOP_PAIR_BONUS;
        if (blackBishopCount >= 2) score -= BISHOP_PAIR_BONUS;

        // Add King Proximity Bonus in Endgame when winning significantly
        if (isEndgame && Math.Abs(score) > 300) // Only apply if one side has a clear advantage
        {
            int fileDist = Math.Abs(whiteKingSquare.File - blackKingSquare.File);
            int rankDist = Math.Abs(whiteKingSquare.Rank - blackKingSquare.Rank);
            int kingDist = fileDist + rankDist; // Manhattan distance
            int proximityBonus = (14 - kingDist) * 5; // Max bonus 70 (dist 0), min bonus 0 (dist 14)
            score += (score > 0) ? proximityBonus : -proximityBonus; // Add bonus to winning side
        }

        // Add Tempo Bonus (small bonus for the side to move)
        const int TEMPO_BONUS = 10;
        score += board.IsWhiteToMove ? TEMPO_BONUS : -TEMPO_BONUS;

        // Return score relative to the side whose turn it is
        return board.IsWhiteToMove ? score : -score;
    }

    private bool IsEndgame(Board board)
    {
        // Cache piece count if board hash changes
        ulong currentBoardHash = board.ZobristKey;
        if (currentBoardHash != lastBoardHash)
        {
            // Consider queens as more valuable for endgame determination
            int queenCount = BitOperations.PopCount(board.GetPieceBitboard(PieceType.Queen, true)) +
                             BitOperations.PopCount(board.GetPieceBitboard(PieceType.Queen, false));
            int minorPieceCount = BitOperations.PopCount(board.GetPieceBitboard(PieceType.Knight, true)) +
                                 BitOperations.PopCount(board.GetPieceBitboard(PieceType.Knight, false)) +
                                 BitOperations.PopCount(board.GetPieceBitboard(PieceType.Bishop, true)) +
                                 BitOperations.PopCount(board.GetPieceBitboard(PieceType.Bishop, false)) +
                                 BitOperations.PopCount(board.GetPieceBitboard(PieceType.Rook, true)) +
                                 BitOperations.PopCount(board.GetPieceBitboard(PieceType.Rook, false));

            // Simple heuristic: Endgame if no queens or few minor pieces remain
            cachedPieceCount = queenCount * 3 + minorPieceCount; // Weight queens higher
            lastBoardHash = currentBoardHash;
        }
        const int endgameMaterialThreshold = 8; // Tunable threshold
        return cachedPieceCount <= endgameMaterialThreshold;
    }

    private Move HandleForcedMove(Move move, Board board, int forcedDepth, bool isForcedMove, int? overrideScore = null)
    {
        // Used for single legal moves or immediate checkmates found at root
        bestScore = overrideScore ?? -Evaluate(board); // Use provided score or evaluate
        currentDepth = forcedDepth;
        LogEval(board, forcedDepth, isForcedMove); // Log this forced move situation
        return move;
    }

    private bool IsCheckmateMove(Move move, Board board)
    {
        board.MakeMove(move);
        bool isCheckmate = board.IsInCheckmate();
        board.UndoMove(move);
        return isCheckmate;
    }

    // --- Transposition Table Logic ---
    private struct TTEntry
    {
        public ulong Key;    // Zobrist key
        public short Depth;  // Depth searched from this position
        public short Score;  // Score relative to side to move, adjusted for mate distance from root
        public byte Flag;    // EXACT, ALPHA (upper bound), or BETA (lower bound)
        public Move BestMove; // Best move found at this node
    }

    private const byte EXACT = 0;
    private const byte ALPHA = 1; // Score is an upper bound (score <= alpha)
    private const byte BETA = 2;  // Score is a lower bound (score >= beta)

    private int GetTTIndex(ulong key) => (int)(key & ttMask);

    private void AddTT(ulong key, int depth, short score, byte flag, Move bestMove)
    {
        int index = GetTTIndex(key);
        ref TTEntry entry = ref tt[index]; // Use ref for potential minor optimization

        if (entry.Key == 0 || depth > entry.Depth || (depth == entry.Depth && flag == EXACT))
        {
            entry.Key = key;
            entry.Depth = (short)depth;
            entry.Score = score; // Score should be adjusted for mate distance before storing
            entry.Flag = flag;
            // Only store a best move if it's valid and leads to an EXACT score or a BETA cutoff
            entry.BestMove = (flag == EXACT || flag == BETA) ? bestMove : Move.NullMove;
        }
    }

    // Helper to adjust mate scores based on ply distance
    private short AdjustMateScore(short score, int currentPly, int rootPly)
    {
        if (Math.Abs(score) > CHECKMATE_SCORE_THRESHOLD)
        {
            int sign = Math.Sign(score);
            // Adjust score relative to the *current* ply from the root ply it was stored at
            return (short)(score - sign * (currentPly - rootPly) * 50);
        }
        return score;
    }

    // Helper to adjust mate scores for storage (relative to root)
    private short AdjustMateScoreForStorage(int score, int currentPly, int rootPly)
    {
        if (Math.Abs(score) > CHECKMATE_SCORE_THRESHOLD)
        {
            int sign = Math.Sign(score);
            // Store mate score relative to the root ply
            return (short)(score + sign * (currentPly - rootPly) * 50);
        }
        return (short)score;
    }


    // -- Piece Square Tables --

    private static readonly int[][] PawnTable = {
        new[] {0,  0,  0,  0,  0,  0,  0,  0},
        new[] {50, 50, 50, 50, 50, 50, 50, 50},
        new[] {12, 10, 20, 30, 30, 20, 11, 10},
        new[] {5,  5, 10, 25, 25, 10,  5,  5},
        new[] {1,  3,  6, 21, 22,  0,  0,  0},
        new[] {5, -1,-10,  1,  3,-10, -5,  5},
        new[] {5, 10, 10,-20,-20, 10, 11,  5},
        new[] {0,  0,  0,  0,  0,  0,  0,  0}
    };

    private static readonly int[][] KnightTable = {
        new[] {-50,-40,-30,-30,-30,-30,-40,-50},
        new[] {-40,-20,  0,  0,  0,  0,-20,-40},
        new[] {-30,  0, 10, 15, 15, 10,  0,-30},
        new[] {-30,  5, 15, 20, 20, 15,  5,-30},
        new[] {-30,  0, 15, 20, 20, 15,  0,-30},
        new[] {-30,  5, 10, 15, 15, 10,  5,-30},
        new[] {-40,-20,  0,  5,  5,  0,-20,-40},
        new[] {-50,-40,-30,-30,-30,-30,-40,-50}
    };

    private static readonly int[][] BishopTable = {
        new[] {-20,-10,-10,-10,-10,-10,-10,-20},
        new[] {-10,  0,  0,  0,  0,  0,  0,-10},
        new[] {-10,  0,  5, 10, 10,  5,  0,-10},
        new[] {-10,  5,  5, 10, 10,  5,  5,-10},
        new[] {-10,  0, 10, 10, 10, 10,  0,-10},
        new[] {-10, 10, 10, 10, 10, 10, 10,-10},
        new[] {-10,  5,  0,  0,  0,  0,  5,-10},
        new[] {-20,-10,-10,-10,-10,-10,-10,-20}
    };

    private static readonly int[][] RookTable = {
        new[] {0,   0,  0,  0,  0,  0,  0,  0},
        new[] {0,  10, 10, 10, 10, 10, 10,  5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {0,  0,  0,  5,  5,  0,  0,  -4}
    };

    private static readonly int[][] QueenTable = {
        new[] {-20,-10,-10, -5, -5,-10,-10,-20},
        new[] {-10,  0,  0,  0,  0,  0,  0,-10},
        new[] {-10,  0,  5,  5,  5,  5,  0,-10},
        new[] {-5,  0,  5,  5,  5,  5,  0, -5},
        new[] {0,  0,  5,  5,  5,  5,  0, -5},
        new[] {-10,  5,  5,  5,  5,  5,  0,-10},
        new[] {-10,  0,  5,  0,  0,  0,  0,-10},
        new[] {-20,-10,-10, -5, -5,-10,-10,-20}
    };

    private static readonly int[][] KingMiddleGame = {
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-20,-30,-30,-40,-40,-30,-30,-20},
        new[] {-10,-20,-20,-20,-20,-20,-20,-10},
        new[] {20, 20,  0,  0,  0,  0, 20, 20},
        new[] {20, 30, 10,  0,  0, 10, 30, 20}
    };

    private static readonly int[][] KingEndGame = {
        new[] {-30,-25,-20,-15,-15,-20,-25,-30},
        new[] {-20,-15,-10,-5, -5, -10,-15,-20},
        new[] {-20,-10, 10, 15, 15, 15,-10,-20},
        new[] {-20,-10, 15, 18, 18, 15,-10,-20},
        new[] {-20,-10, 15, 18, 18, 15,-10,-20},
        new[] {-20,-10, 15, 20, 15, 15,-10,-20},
        new[] {-20,-15,-10,  0,  0,-10,-10,-20},
        new[] {-30,-20,-20,-20,-20,-20,-20,-30}
    };
}