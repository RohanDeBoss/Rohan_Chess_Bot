using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

// v2.0.3 Small improvements / Cleanup
public class EvilBot : IChessBot
{
    // Time management flags
    private static readonly bool ConstantDepth = false;
    private static readonly short MaxDepth = 5; // Used when ConstantDepth is true

    private static readonly bool UseFixedTimePerMove = false; // Flag to enable fixed time per move
    private static readonly int FixedTimePerMoveMs = 150;   // Fixed time if flag is true (Don't set below 15ms)

    // More constants
    private const short MaxSafetyDepth = 99;
    private const int InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22; // Approx 4 million entries
    private const int MAX_KILLER_PLY = 200; // Define max ply for killer moves array

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
    private const int TIME_CHECK_NODES = 200; // How often to check the time

    // Static Fields
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = TT_SIZE - 1;
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 }; // P, N, B, R, Q, K

    // Instance Fields
    private long negamaxPositions = 0;
    private long qsearchPositions = 0;
    private int bestScore;
    private Move[,] killerMoves = new Move[MAX_KILLER_PLY, 2];
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private int currentDepth;
    private Timer currentTimer;
    private volatile bool timeIsUp; // Global flag for time expiration
    private long absoluteTimeLimit; // Absolute time limit for the current move

    private void CheckTime()
    {
        // Check time limit frequently but not excessively based on node count
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
        int result = 23 + 99900 / (t + 1675); // Formula for time allocation fraction
        return (short)Math.Max(26, Math.Min(65, result));
    }

    public Move Think(Board board, Timer timer)
    {
        currentTimer = timer;
        timeIsUp = false;

        if (timer.MillisecondsRemaining <= 0)
        {
            var moves = board.GetLegalMoves();
            return moves.Length > 0 ? moves[0] : Move.NullMove;
        }

        // Initialization per turn
        Array.Clear(killerMoves, 0, killerMoves.Length);
        Array.Clear(historyMoves, 0, historyMoves.Length);
        negamaxPositions = 0;
        qsearchPositions = 0;
        currentDepth = 0;
        lastBoardHash = 0;
        cachedPieceCount = -1;

        short depth = 1;
        int previousBestScore = 0;
        Move previousBestMove = Move.NullMove;
        var legalMoves = board.GetLegalMoves();
        Move bestMove = legalMoves.Length > 0 ? legalMoves[0] : Move.NullMove;
        Move bestMoveThisIteration = bestMove;

        if (legalMoves.Length == 0)
        {
            bestScore = board.IsInCheck() ? -InfiniteScore + 50 : 0;
            return Move.NullMove;
        }
        if (legalMoves.Length == 1)
        {
            return HandleForcedMove(legalMoves[0], board, 1, true);
        }

        // --- Time Allocation ---
        int allocatedTime;
        if (UseFixedTimePerMove)
        {
            allocatedTime = Math.Min(FixedTimePerMoveMs, timer.MillisecondsRemaining - SAFETY_MARGIN);
            allocatedTime = Math.Max(1, allocatedTime); // Keep: Ensure minimum 1ms
        }
        else if (ConstantDepth)
        {
            allocatedTime = int.MaxValue;
        }
        else
        {
            short timeFraction = Math.Max(GetTimeSpentFraction(timer), (short)1);
            allocatedTime = (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 3);
            allocatedTime = Math.Max(10, allocatedTime - SAFETY_MARGIN);
            allocatedTime = Math.Min(allocatedTime, timer.MillisecondsRemaining - SAFETY_MARGIN);
            allocatedTime = Math.Max(1, allocatedTime); // Keep: Ensure minimum 1ms
        }
        absoluteTimeLimit = timer.MillisecondsElapsedThisTurn + allocatedTime;
        // --- End Time Allocation ---

        // --- Iterative Deepening Loop ---
        while (depth <= MaxSafetyDepth && (ConstantDepth ? depth <= MaxDepth : true))
        {
            // Check time before starting a new depth
            if (timeIsUp) break;
            if (!ConstantDepth && !UseFixedTimePerMove && currentTimer.MillisecondsElapsedThisTurn >= absoluteTimeLimit - SAFETY_MARGIN * 2) break;

            currentDepth = depth;
            bestMoveThisIteration = Move.NullMove;

            bool useAspiration = depth > MAX_ASPIRATION_DEPTH && Math.Abs(previousBestScore) < CHECKMATE_SCORE_THRESHOLD;
            int alpha = -InfiniteScore;
            int beta = InfiniteScore;
            int aspirationWindow = INITIAL_ASPIRATION_WINDOW;
            bool aspirationFailed;
            int currentBestScore = -InfiniteScore;

            if (useAspiration)
            {
                alpha = previousBestScore - aspirationWindow;
                beta = previousBestScore + aspirationWindow;
            }

            // --- Aspiration Window Loop ---
            do
            {
                aspirationFailed = false;
                currentBestScore = -InfiniteScore;
                Move currentBestMoveAspiration = Move.NullMove;

                Move[] movesToOrder = OrderMoves(legalMoves, board, 0, previousBestMove);
                if (movesToOrder.Length > 0) currentBestMoveAspiration = movesToOrder[0];

                for (int i = 0; i < movesToOrder.Length; i++)
                {
                    Move move = movesToOrder[i];

                    board.MakeMove(move);
                    int score = -Negamax(board, depth - 1, -beta, -alpha, 1, 1);
                    board.UndoMove(move);

                    if (timeIsUp) goto EndRootMoveLoop; // Exit loop if Negamax ran out of time

                    if (score > currentBestScore)
                    {
                        currentBestScore = score;
                        currentBestMoveAspiration = move;
                        alpha = Math.Max(alpha, score);
                    }

                    if (alpha >= beta)
                    {
                        if (useAspiration)
                        {
                            aspirationFailed = true;
                            alpha = currentBestScore - aspirationWindow; // Keep current score, widen bounds later
                            beta = InfiniteScore; // Widen beta for re-search
                        }
                        if (!aspirationFailed) break; // Normal beta cutoff
                    }
                } // --- End Root Move Loop ---

            EndRootMoveLoop:;

                if (timeIsUp) break; // Exit aspiration loop

                // Handle Aspiration Window Re-search (Keep v2.1 logic)
                if (aspirationFailed)
                {
                    // If score <= original alpha (failed low)
                    if (currentBestScore <= previousBestScore - aspirationWindow)
                    {
                        alpha = -InfiniteScore; // Widen alpha significantly
                        beta = currentBestScore + aspirationWindow; // Re-center beta around actual score
                    }
                    else // Failed high (score >= original beta)
                    {
                        alpha = currentBestScore - aspirationWindow; // Re-center alpha
                        beta = InfiniteScore; // Widen beta significantly
                    }
                    aspirationWindow *= 3; // Increase window size for re-search
                }
                else // Aspiration successful (or not used)
                {
                    previousBestScore = currentBestScore;
                    bestScore = currentBestScore;
                    if (!currentBestMoveAspiration.IsNull)
                    {
                        bestMoveThisIteration = currentBestMoveAspiration;
                    }
                }

            } while (aspirationFailed && !timeIsUp); // Repeat if aspiration failed and time permits

            if (timeIsUp) break;

            if (!bestMoveThisIteration.IsNull)
            {
                bestMove = bestMoveThisIteration;
                previousBestMove = bestMove;
            }
            else
            {
                // If iteration failed to find a move (likely due to time out), use previous best
                break;
            }

            // Optional: Stop early if a checkmate is found
            if (Math.Abs(bestScore) > CHECKMATE_SCORE_THRESHOLD && !ConstantDepth)
            {
                break;
            }

            depth++;

        } // --- End Iterative Deepening Loop ---

        // Fallback if no move was ever selected
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
        if (currentTimer != null && currentTimer.MillisecondsElapsedThisTurn > absoluteTimeLimit && !isForcedMove && depth <= 1) return;
        if (currentTimer != null && currentTimer.MillisecondsRemaining <= 0 && !isForcedMove) return;

        if (isForcedMove)
        {
            Console.WriteLine($"\n{GetType().Name}: FORCED MOVE!");
        }
        else
        {
            Console.WriteLine();
            DebugLog($"Depth: {depth}"); // Keep: Log completed depth
            string mateInfo = GetMateInMoves(bestScore) ?? "No mate found";
            DebugLog(mateInfo);
            DebugLog($"Eval: {bestScore * (board.IsWhiteToMove ? 1 : -1)}"); // Eval from white's perspective
            DebugLog($"Nodes: {negamaxPositions + qsearchPositions:N0}");
        }
    }

    private string? GetMateInMoves(int score)
    {
        if (Math.Abs(score) > CHECKMATE_SCORE_THRESHOLD)
        {
            int sign = Math.Sign(score);
            int matePly = (InfiniteScore - Math.Abs(score) + 49) / 50; // Calculate plies to mate
            return $"{(sign > 0 ? "Winning" : "Losing")} Mate in {matePly} ply";
        }
        return null;
    }

    private Move[] OrderMoves(Move[] moves, Board board, int ply, Move? previousBestMove = null)
    {
        if (moves.Length <= 1) return moves;

        int[] scores = new int[moves.Length];
        TTEntry ttEntry = tt[GetTTIndex(board.ZobristKey)];
        Move ttMove = (ttEntry.Key == board.ZobristKey) ? ttEntry.BestMove : Move.NullMove;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            int score = 0;

            // Prioritize TT move and previous best move
            if (!ttMove.IsNull && move == ttMove)
                score += TT_MOVE_BONUS;
            else if (previousBestMove.HasValue && move == previousBestMove.Value)
                score += PREVIOUS_BEST_MOVE_BONUS;

            if (move.IsCapture)
            {
                Piece capturedPiece = board.GetPiece(move.TargetSquare);
                int capturedValue = 0; // Initialize

                if (move.IsEnPassant) // Handle En Passant explicitly
                {
                    capturedValue = PieceValues[(int)PieceType.Pawn - 1];
                }
                else if (capturedPiece.PieceType != PieceType.None)
                {
                    capturedValue = PieceValues[(int)capturedPiece.PieceType - 1];
                }
                // Removed redundant else { capturedValue = 0; }

                int attackerValue = PieceValues[(int)board.GetPiece(move.StartSquare).PieceType - 1];
                score += CAPTURE_BASE_BONUS + capturedValue * MVV_LVA_MULTIPLIER - attackerValue; // MVV-LVA
            }
            else // Non-captures use Killer and History heuristics
            {
                if (IsKillerMove(move, ply))
                    score += KILLER_MOVE_BONUS;

                int historyScore = historyMoves[move.StartSquare.Index, move.TargetSquare.Index];
                score += Math.Min(historyScore, HISTORY_MAX_BONUS);
            }

            // Promotion bonus
            if (move.IsPromotion)
                score += PROMOTION_BASE_BONUS + PieceValues[(int)move.PromotionPieceType - 1];

            scores[i] = score;
        }

        Array.Sort(scores, moves, Comparer<int>.Create((a, b) => b.CompareTo(a))); // Sort descending
        return moves;
    }

    private bool IsKillerMove(Move move, int ply)
    {
        // Check if ply is within the bounds of the killer move array
        if (ply < 0 || ply >= MAX_KILLER_PLY)
        {
            return false; // Ply is out of supported range
        }
        // Check if move matches either killer slot for the current ply
        return move == killerMoves[ply, 0] || move == killerMoves[ply, 1];
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        // Only update for quiet moves and within supported ply range
        if (move.IsCapture || move.IsPromotion || ply < 0 || ply >= MAX_KILLER_PLY)
        {
            return;
        }

        // Shift killers if new move is different from the first killer
        if (move != killerMoves[ply, 0])
        {
            killerMoves[ply, 1] = killerMoves[ply, 0]; // Shift killer 1 to slot 2
            killerMoves[ply, 0] = move;                // Put new killer in slot 1
        }
    }

    private const int HISTORY_SCORE_CAP = 1_000_000;

    private void UpdateHistoryMove(Move move, int bonus)
    {
        if (move.IsCapture || move.IsPromotion) return; // Only for quiet moves causing cutoff
        int startIdx = move.StartSquare.Index;
        int targetIdx = move.TargetSquare.Index;
        historyMoves[startIdx, targetIdx] = Math.Min(historyMoves[startIdx, targetIdx] + bonus, HISTORY_SCORE_CAP);

        // Periodically decay history scores
        if ((negamaxPositions + qsearchPositions) % 1024 == 0)
            DecayHistory();
    }

    private void DecayHistory()
    {
        // Simple linear decay
        for (int i = 0; i < 64; i++)
            for (int j = 0; j < 64; j++)
                historyMoves[i, j] /= 2;
    }

    private int Negamax(Board board, int depth, int alpha, int beta, int ply, int realPly)
    {
        CheckTime();
        if (timeIsUp) return 0;

        negamaxPositions++;
        if (board.IsDraw()) return 0;

        // Mate distance pruning
        int mateScore = InfiniteScore - realPly * 50;
        alpha = Math.Max(alpha, -mateScore);
        beta = Math.Min(beta, mateScore);
        if (alpha >= beta) return alpha;

        // Transposition Table Lookup
        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];
        bool ttHit = ttEntry.Key == key;
        Move ttMove = Move.NullMove;

        if (ttHit && ttEntry.Depth >= depth)
        {
            short ttScore = AdjustMateScore(ttEntry.Score, ply, realPly);
            if (ttEntry.Flag == EXACT) return ttScore;
            if (ttEntry.Flag == ALPHA && ttScore <= alpha) return alpha;
            if (ttEntry.Flag == BETA && ttScore >= beta) return beta;
        }
        if (ttHit) ttMove = ttEntry.BestMove;

        // Base Case: Quiescence Search
        if (depth <= 0)
        {
            return Quiescence(board, alpha, beta, ply, 0);
        }

        Move[] moves = board.GetLegalMoves();

        // Checkmate / Stalemate
        if (moves.Length == 0)
        {
            return board.IsInCheck() ? -InfiniteScore + realPly * 50 : 0;
        }

        // Static Evaluation for Pruning (calculated lazily)
        int standPat = 0;
        bool inCheck = board.IsInCheck();
        bool needEvalForPruning = !inCheck; // Simpler: eval always needed for NMP/Futility/Razoring if not in check
        if (needEvalForPruning) standPat = Evaluate(board);

        if (!inCheck && depth >= 3 && ply > 0 && !IsEndgame(board) && Math.Abs(standPat) < CHECKMATE_SCORE_THRESHOLD)
        {
            board.ForceSkipTurn();
            int reduction = (depth > 6) ? 3 : 2;
            int nullScore = -Negamax(board, depth - reduction - 1, -beta, -beta + 1, ply + 1, realPly + 1);
            board.UndoSkipTurn();

            if (timeIsUp) return 0;
            if (nullScore >= beta) return beta;
        }

        // Razoring
        if (depth == 1 && !inCheck && standPat + 200 < alpha)
        {
            return Quiescence(board, alpha, beta, ply, 0); // Fall back to QSearch
        }

        // Futility Pruning
        bool inMateZone = Math.Abs(standPat) > CHECKMATE_SCORE_THRESHOLD;
        if (depth <= 2 && !inCheck && !inMateZone)
        {
            int futilityMargin = 150 * depth;
            if (standPat + futilityMargin <= alpha)
            {
                return Quiescence(board, alpha, beta, ply, 0); // Fall back to QSearch
            }
        }

        moves = OrderMoves(moves, board, ply, ttMove); // Order moves using heuristics
        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int localBestScore = -InfiniteScore;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();

            int newDepth = depth - 1;
            // Check Extension
            if (givesCheck && newDepth < MaxSafetyDepth - 1) newDepth = Math.Min(MaxSafetyDepth - 1, newDepth + 1); // Corrected MaxSafetyDepth

            // Late Move Reductions (LMR)
            int score;
            bool isQuiet = !move.IsCapture && !move.IsPromotion;
            bool useLMR = depth > 2 && i >= 2 && isQuiet && !givesCheck && !inMateZone;

            if (useLMR)
            {
                int reduction = (int)(0.75 + Math.Log(depth) * Math.Log(i + 1) / 2.0);
                // Reduce reduction slightly for moves with good history scores
                if (historyMoves[move.StartSquare.Index, move.TargetSquare.Index] > HISTORY_SCORE_CAP / 4)
                    reduction = Math.Max(reduction - 1, 0);
                int reducedDepth = Math.Max(newDepth - reduction, 1);

                score = -Negamax(board, reducedDepth, -alpha - 1, -alpha, ply + 1, realPly + 1); // Null window search

                // Re-search if LMR potentially found a better move
                if (score > alpha && score < beta && !timeIsUp)
                {
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1); // Full window re-search
                }
            }
            else // Full Depth Search (No LMR or not applicable)
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }
            board.UndoMove(move);

            if (timeIsUp) return 0; // Check time after recursive call

            // Update Best Score and Alpha
            if (score > localBestScore)
            {
                localBestScore = score;
                bestMove = move;
                alpha = Math.Max(alpha, score);

                if (alpha >= beta)
                {
                    if (isQuiet) // Update killers/history only for quiet moves causing cutoff
                    {
                        UpdateKillerMoves(move, ply);
                        UpdateHistoryMove(move, depth * depth);
                    }
                    AddTT(key, depth, AdjustMateScoreForStorage(beta, ply, realPly), BETA, move);
                    return beta;
                }
            }
        }

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

        Move[] captures = board.GetLegalMoves(true);
        Move[] orderedMoves = OrderMoves(captures, board, ply);

        foreach (Move move in orderedMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, ply + 1, qDepth + 1);
            board.UndoMove(move);

            if (timeIsUp) return 0;

            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }

        return alpha;
    }

    private int Evaluate(Board board)
    {
        if (board.IsDraw()) return 0;

        Square whiteKingSquare = board.GetKingSquare(true);
        Square blackKingSquare = board.GetKingSquare(false);
        bool isEndgame = IsEndgame(board);

        int[][][] adjustmentTables = { PawnTable, KnightTable, BishopTable, RookTable, QueenTable, isEndgame ? KingEndGame : KingMiddleGame };

        int score = 0;
        int whiteBishopCount = 0;
        int blackBishopCount = 0;

        foreach (PieceList list in board.GetAllPieceLists())
        {
            int pieceTypeIndex = (int)list.TypeOfPieceInList - 1;
            if (pieceTypeIndex < 0 || pieceTypeIndex > 5) continue;

            int baseVal = PieceValues[pieceTypeIndex];
            int[][] table = adjustmentTables[pieceTypeIndex];
            int pieceSign = list.IsWhitePieceList ? 1 : -1;

            if (list.TypeOfPieceInList == PieceType.Bishop)
            {
                if (list.IsWhitePieceList) whiteBishopCount += list.Count; else blackBishopCount += list.Count;
            }

            foreach (Piece p in list)
            {
                int rank = p.IsWhite ? 7 - p.Square.Rank : p.Square.Rank; // Rank from perspective of color
                int file = p.Square.File;
                score += pieceSign * (baseVal + table[rank][file]); // Material + PST

                // Endgame Pawn Advancement Bonus
                if (isEndgame && p.PieceType == PieceType.Pawn)
                {
                    int advancementBonus = p.IsWhite ? rank : (7 - rank);
                    score += pieceSign * advancementBonus * 5;
                }
            }
        }

        // Bishop Pair Bonus
        const int BISHOP_PAIR_BONUS = 50;
        if (whiteBishopCount >= 2) score += BISHOP_PAIR_BONUS;
        if (blackBishopCount >= 2) score -= BISHOP_PAIR_BONUS;

        // Endgame King Proximity Bonus (when clearly winning)
        if (isEndgame && Math.Abs(score) > 300)
        {
            int kingDist = Math.Abs(whiteKingSquare.File - blackKingSquare.File) + Math.Abs(whiteKingSquare.Rank - blackKingSquare.Rank);
            int proximityBonus = (14 - kingDist) * 5; // Closer kings = higher bonus for winning side
            score += (score > 0) ? proximityBonus : -proximityBonus;
        }

        // Tempo Bonus
        const int TEMPO_BONUS = 10;
        score += board.IsWhiteToMove ? TEMPO_BONUS : -TEMPO_BONUS;

        return board.IsWhiteToMove ? score : -score; // Return score relative to current player
    }

    private bool IsEndgame(Board board)
    {
        // Use cached piece count if possible
        ulong currentBoardHash = board.ZobristKey;
        if (currentBoardHash != lastBoardHash)
        {
            // Calculate total number of pieces on the board directly
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = currentBoardHash;
        }
        const int endgameTotalPieceThreshold = 11; // Endgame if 11 or fewer total pieces (including kings) remain

        return cachedPieceCount <= endgameTotalPieceThreshold;
    }

    private Move HandleForcedMove(Move move, Board board, int forcedDepth, bool isForcedMove)
    {
        // Handle single legal moves or immediate checkmates
        bestScore = -Evaluate(board);
        currentDepth = forcedDepth;
        LogEval(board, forcedDepth, isForcedMove);
        return move;
    }

    private struct TTEntry
    {
        public ulong Key;
        public short Depth;
        public short Score;
        public byte Flag;
        public Move BestMove;
    }

    private const byte EXACT = 0;
    private const byte ALPHA = 1;
    private const byte BETA = 2;

    private int GetTTIndex(ulong key) => (int)(key & ttMask);

    private void AddTT(ulong key, int depth, short score, byte flag, Move bestMove)
    {
        int index = GetTTIndex(key);
        ref TTEntry entry = ref tt[index];

        // Replacement Strategy: Deeper search, or same depth with EXACT flag, replaces existing entry
        if (entry.Key == 0 || depth > entry.Depth || (depth == entry.Depth && flag == EXACT))
        {
            entry.Key = key;
            entry.Depth = (short)depth;
            entry.Score = score; // Assumes score is already adjusted for storage
            entry.Flag = flag;
            entry.BestMove = (flag == EXACT || flag == BETA) ? bestMove : Move.NullMove; // Store move only if useful
        }
    }

    // Adjust TT mate score based on current ply vs stored ply (relative to root)
    private short AdjustMateScoreForStorage(int score, int currentPly, int rootPly)
    {
        if (Math.Abs(score) > CHECKMATE_SCORE_THRESHOLD)
        {
            return (short)Math.Clamp(score, -InfiniteScore + 50, InfiniteScore - 50);
        }
        return (short)score;
    }

    private short AdjustMateScore(short score, int currentPly, int rootPly)
    {
        return score;
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