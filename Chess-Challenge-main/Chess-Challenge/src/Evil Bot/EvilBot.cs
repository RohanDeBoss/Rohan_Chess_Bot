using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

// v1.9.1 Check Bonus
public class EvilBot : IChessBot
{

    // Search Parameters
    private const bool ConstantDepth = false;
    private const short MaxDepth = 6;         // Used when ConstantDepth is true
    private const short MaxSafetyDepth = 99;
    private const int InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22;

    // Move Ordering Bonuses
    private const int TT_MOVE_BONUS = 10_000_000;
    private const int PREVIOUS_BEST_MOVE_BONUS = 5_000_000;
    private const int CAPTURE_BASE_BONUS = 1_000_000;
    private const int PROMOTION_BASE_BONUS = 900_000;
    private const int KILLER_MOVE_BONUS = 800_000;
    private const int MVV_LVA_MULTIPLIER = 10;
    private const int HISTORY_MAX_BONUS = 700_000;

    // New bonus for moves that give check
    private const int CHECK_BONUS = 300_000;

    // Time Management
    private const int INITIAL_ASPIRATION_WINDOW = 125;
    private const int MAX_ASPIRATION_DEPTH = 3;
    private const int CHECKMATE_SCORE_THRESHOLD = 25000;
    private const int SAFETY_MARGIN = 10;


    // --- Static Fields ---

    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = (ulong)(TT_SIZE - 1);

    // --- Instance Fields ---

    private int negamaxPositions = 0;
    private int qsearchPositions = 0;
    private int bestScore;
    private List<Move> killerMoves = new List<Move>();
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private int currentDepth;

    // --- Debugging Methods ---

    private void DebugLog(string message)
    {
        Console.WriteLine($"{GetType().Name}: {message}");
    }

    private string? GetMateInMoves(int score)
    {
        // Check if the score is in the mate range
        if (score > InfiniteScore - 1500)  // We're winning with mate
        {
            int matePly = (InfiniteScore - score + 49) / 50; // Round up to next ply
            return $"Winning Mate in {matePly} ply! :)";
        }
        else if (score < -InfiniteScore + 1500)  // We're losing to mate
        {
            int matePly = (InfiniteScore + score + 49) / 50; // Round up to next ply
            return $"Losing Mate in {matePly} ply! :(";
        }

        return null;
    }

    private void LogEval(Board board, int depth, bool isForcedMove)
    {
        if (isForcedMove)
        {
            Console.WriteLine();
            Console.WriteLine($"{GetType().Name}: FORCED MOVE!");
        }
        else
        {
            Console.WriteLine();
            DebugLog($"Depth: {depth}");
            string mateInfo = GetMateInMoves(bestScore) ?? string.Empty;
            DebugLog(!string.IsNullOrEmpty(mateInfo) ? mateInfo : "No mate found");
            DebugLog($"Eval: {bestScore * (board.IsWhiteToMove ? 1 : -1)}");
            DebugLog($"Total: {negamaxPositions + qsearchPositions:N0}");
        }
    }


    private Move[] OrderMoves(Move[] moves, Board board, int ply, Move? previousBestMove = null)
    {
        int[] scores = new int[moves.Length];
        TTEntry ttEntry = tt[GetTTIndex(board.ZobristKey)];

        for (int i = 0; i < moves.Length; i++)
        {
            int score = 0;
            Move move = moves[i];

            if (move == ttEntry.BestMove)
                score += TT_MOVE_BONUS;
            if (previousBestMove.HasValue && move == previousBestMove.Value)
                score += PREVIOUS_BEST_MOVE_BONUS;
            if (move.IsCapture)
            {
                var capturedPiece = board.GetPiece(move.TargetSquare);
                int capturedValue = GetPieceValue(capturedPiece.PieceType);
                int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
                score += CAPTURE_BASE_BONUS + capturedValue * MVV_LVA_MULTIPLIER - attackerValue;
            }
            if (move.IsPromotion)
            {
                score += PROMOTION_BASE_BONUS + GetPieceValue(move.PromotionPieceType);
            }
            if (IsKillerMove(move, ply))
            {
                score += KILLER_MOVE_BONUS;
            }

            // New bonus
            if (board.IsInCheck())
            {
                score += CHECK_BONUS;
            }

            int historyScore = historyMoves[move.StartSquare.Index, move.TargetSquare.Index];
            score += Math.Min(historyScore, HISTORY_MAX_BONUS);

            scores[i] = score;
        }

        Array.Sort(scores, moves, Comparer<int>.Create((a, b) => b.CompareTo(a)));
        return moves;
    }


    private bool IsKillerMove(Move move, int ply)
    {
        int killerIndex0 = ply * 2;
        int killerIndex1 = ply * 2 + 1;
        return (killerMoves.Count > killerIndex0 && move == killerMoves[killerIndex0]) ||
               (killerMoves.Count > killerIndex1 && move == killerMoves[killerIndex1]);
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        if (move.CapturePieceType != PieceType.None) return;
        EnsureKillerMovesSize(ply);
        int killerIndex = ply * 2;
        if (move != killerMoves[killerIndex])
        {
            killerMoves[killerIndex + 1] = killerMoves[killerIndex];
            killerMoves[killerIndex] = move;
        }
    }

    private const int HISTORY_SCORE_CAP = 1_000_000; // Maximum history score, adjustable

    private void UpdateHistoryMove(Move move, int depth)
    {
        if (move.CapturePieceType != PieceType.None) return;
        int increment = depth * depth;
        int idx1 = move.StartSquare.Index, idx2 = move.TargetSquare.Index;
        historyMoves[idx1, idx2] = Math.Min(historyMoves[idx1, idx2] + increment, HISTORY_SCORE_CAP);
        if ((negamaxPositions + qsearchPositions) % 512 == 0)
            DecayHistory();
    }

    private void DecayHistory()
    {
        for (int i = 0; i < 64; i++)
            for (int j = 0; j < 64; j++)
                historyMoves[i, j] = (historyMoves[i, j] * 4) / 5;
    }

    private void EnsureKillerMovesSize(int ply)
    {
        int requiredSize = (ply * 2) + 2;
        while (killerMoves.Count < requiredSize)
        {
            killerMoves.Add(Move.NullMove);
        }
    }

    private short GetTimeSpentFraction(Timer timer)
    {
        if (timer.MillisecondsRemaining <= 1_000) return 60;
        if (timer.MillisecondsRemaining <= 5_000) return 42;
        else if (timer.MillisecondsRemaining < 20_000) return 30;
        else return 25;
    }

    public Move Think(Board board, Timer timer)
    {
        // Reset state between moves
        killerMoves.Clear();
        Array.Clear(historyMoves, 0, historyMoves.Length);
        negamaxPositions = 0;
        qsearchPositions = 0;
        currentDepth = 0;

        short depth = 1;
        int previousBestScore = 0;
        Move previousBestMove = Move.NullMove;
        var legalMoves = board.GetLegalMoves();
        Move bestMove = legalMoves.Length > 0 ? legalMoves[0] : Move.NullMove;

        // No legal moves => game over
        if (legalMoves.Length == 0)
        {
            bestScore = board.IsInCheck() ? -InfiniteScore + 50 : 0;
            return Move.NullMove;
        }

        // Forced move: only one legal move
        if (legalMoves.Length == 1)
        {
            return HandleForcedMove(legalMoves[0], board, 1, true);
        }

        // Immediate checkmate check
        foreach (Move move in legalMoves)
        {
            if (IsCheckmateMove(move, board))
            {
                return HandleForcedMove(move, board, 1, false, InfiniteScore - 50);
            }
        }

        short timeFraction = Math.Max(GetTimeSpentFraction(timer), (short)1);
        int maxTimeForTurn = ConstantDepth
            ? int.MaxValue
            : (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 4);

        // Iterative deepening loop with MaxSafetyDepth cap
        while (depth <= MaxSafetyDepth &&
               (ConstantDepth && depth <= MaxDepth ||
                !ConstantDepth && timer.MillisecondsElapsedThisTurn - SAFETY_MARGIN < maxTimeForTurn))
        {
            currentDepth = depth;
            bool useAspiration = depth > MAX_ASPIRATION_DEPTH && Math.Abs(previousBestScore) < CHECKMATE_SCORE_THRESHOLD;

            int alpha = -InfiniteScore;
            int beta = InfiniteScore;
            int aspirationWindow = INITIAL_ASPIRATION_WINDOW;
            bool aspirationFailed;

            do
            {
                aspirationFailed = false;
                int currentBestScore = -InfiniteScore;
                bestMove = legalMoves[0];

                Move[] movesToOrder = OrderMoves(legalMoves, board, 0, previousBestMove);

                foreach (Move move in movesToOrder)
                {
                    if (!ConstantDepth && timer.MillisecondsElapsedThisTurn >= maxTimeForTurn)
                    {
                        LogEval(board, currentDepth, false);
                        return bestMove;
                    }

                    board.MakeMove(move);
                    int score = -Negamax(board, depth - 1, -beta, -alpha, 1, 1);
                    board.UndoMove(move);

                    if (score > currentBestScore)
                    {
                        currentBestScore = score;
                        bestMove = move;
                    }

                    if (score >= beta)
                    {
                        aspirationFailed = useAspiration;
                        beta = Math.Min(InfiniteScore, beta + aspirationWindow);
                        break;
                    }
                    alpha = Math.Max(alpha, score);
                }

                if (aspirationFailed)
                {
                    aspirationWindow *= 3;
                    alpha = currentBestScore - aspirationWindow;
                    beta = currentBestScore + aspirationWindow;
                }
                else
                {
                    previousBestScore = currentBestScore;
                    bestScore = currentBestScore;
                }
            } while (aspirationFailed);

            previousBestMove = bestMove;
            depth++;
        }

        LogEval(board, currentDepth, false);
        return bestMove;
    }

    // Call this with realPly = 0 at the root.
    private int Negamax(Board board, int depth, int alpha, int beta, int ply, int realPly)
    {
        negamaxPositions++;

        // Immediate game-ending positions
        if (board.IsDraw()) return 0;
        if (board.IsInCheckmate())
            // Use realPly here so extensions don’t inflate the mate score.
            return -InfiniteScore + realPly * 50;

        // Transposition table lookup
        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];
        if (ttEntry.Key == key && ttEntry.Depth >= depth)
        {
            if (ttEntry.Flag == EXACT) return ttEntry.Score;
            if (ttEntry.Flag == ALPHA && ttEntry.Score <= alpha) return alpha;
            if (ttEntry.Flag == BETA && ttEntry.Score >= beta) return beta;
        }

        // Horizon and quiescence search
        if (depth <= 0) return Quiescence(board, alpha, beta, ply);

        // Null move pruning
        if (!board.IsInCheck() && depth > 3)
        {
            board.ForceSkipTurn();
            int reduction = Math.Min(3, 1 + depth / 4);
            int nullScore = -Negamax(board, depth - reduction - 1, -beta, -beta + 1, ply + 1, realPly + 1);
            board.UndoSkipTurn();
            if (nullScore >= beta) return beta;
        }

        int standPat = Evaluate(board);
        Move[] moves = OrderMoves(board.GetLegalMoves(), board, ply);

        // No legal moves -> checkmate (or stalemate, but here we treat as mate)
        if (moves.Length == 0) return -InfiniteScore + realPly * 50;

        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int localBestScore = -InfiniteScore;

        // Mate zone detection
        bool inMateZone = Math.Abs(standPat) > InfiniteScore - 1000;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();

            int newDepth = depth - 1;

            // Extensions for check and mate zone still applied for search quality…
            if (givesCheck) newDepth += 1;
            if (inMateZone) newDepth += 1;

            // Late move reduction only when safe
            bool useLMR = !inMateZone && depth > 2 && i >= 2 && !move.IsCapture &&
                          !move.IsPromotion && !givesCheck && !board.IsInCheck();

            if (useLMR)
            {
                int reduction = (int)(0.5 + Math.Log(depth) * Math.Log(i) / 2.0);
                newDepth = Math.Max(newDepth - reduction, 1);
            }

            int score;
            // Always increment both ply and realPly by 1.
            if (i == 0)
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }
            else
            {
                score = -Negamax(board, newDepth, -alpha - 1, -alpha, ply + 1, realPly + 1);
                if (score > alpha && score < beta)
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }
            board.UndoMove(move);

            if (score > localBestScore)
            {
                localBestScore = score;
                bestMove = move;
            }

            alpha = Math.Max(alpha, score);
            if (alpha >= beta)
            {
                if (!move.IsCapture)
                {
                    if (i < 2) UpdateKillerMoves(move, ply);
                    UpdateHistoryMove(move, depth);
                }
                AddTT(key, depth, (short)beta, BETA, move);
                return beta;
            }
        }

        byte flag = localBestScore <= originalAlpha ? ALPHA : localBestScore >= beta ? BETA : EXACT;
        AddTT(key, depth, (short)localBestScore, flag, bestMove);
        return localBestScore;
    }



    private int Quiescence(Board board, int alpha, int beta, int ply)
    {
        qsearchPositions++;
        int standPat = Evaluate(board);
        if (standPat >= beta) return beta;
        alpha = Math.Max(alpha, standPat);

        Move[] captureMoves = OrderMoves(board.GetLegalMoves(true), board, ply);
        foreach (Move move in captureMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, ply + 1);
            board.UndoMove(move);

            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }
        return alpha;
    }


    private int Evaluate(Board board)
    {
        if (board.IsDraw()) return 0;
        bool isEndgame = IsEndgame(board);
        int[][][] adjustmentTables = new int[][][]
        {
        PawnTable, KnightTable, BishopTable, RookTable, QueenTable,
        isEndgame ? KingEndGame : KingMiddleGame
        };

        int score = 0;
        foreach (PieceList list in board.GetAllPieceLists())
        {
            int baseVal = PieceValues[(int)list.TypeOfPieceInList - 1];
            int[][] table = adjustmentTables[(int)list.TypeOfPieceInList - 1];
            foreach (Piece p in list)
            {
                // For white, adjust rank from the bottom; for black, use the rank as-is.
                int r = p.IsWhite ? 7 - p.Square.Rank : p.Square.Rank;
                score += (p.IsWhite ? 1 : -1) * (baseVal + table[r][p.Square.File]);
            }
        }
        return board.IsWhiteToMove ? score : -score;
    }

    private bool IsEndgame(Board board)
    {
        ulong currentBoardHash = board.ZobristKey;
        if (currentBoardHash != lastBoardHash)
        {
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = currentBoardHash;
        }
        const int endgameThreshold = 12;
        return cachedPieceCount <= endgameThreshold;
    }

    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 }; // Pawn, Knight, Bishop, Rook, Queen, King

    private int GetPieceValue(PieceType pieceType)
    {
        if (pieceType == PieceType.None)
            return 0;
        int index = (int)pieceType - 1;
        if (index < 0 || index >= PieceValues.Length)
            return 0;
        return PieceValues[index];
    }

    // --- Helper Methods ---

    private Move HandleForcedMove(Move move, Board board, int forcedDepth, bool isForcedMove, int? overrideScore = null)
    {
        board.MakeMove(move);
        bestScore = overrideScore ?? -Evaluate(board);
        board.UndoMove(move);
        currentDepth = forcedDepth;
        LogEval(board, forcedDepth, isForcedMove);
        return move;
    }


    private bool IsCheckmateMove(Move move, Board board)
    {
        board.MakeMove(move);
        bool isCheckmate = board.IsInCheckmate();
        board.UndoMove(move);
        return isCheckmate;
    }

    // --- Transposition Table ---

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
        var existing = tt[index];
        if (existing.Key == 0 || depth > existing.Depth || (depth == existing.Depth && flag == EXACT))
            tt[index] = new TTEntry { Key = key, Depth = (short)depth, Score = score, Flag = flag, BestMove = bestMove };
    }

    // --- Piece Square Tables ---

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
        new[] {-50,-40,-30,-20,-20,-30,-40,-50},
        new[] {-30,-20,-10,  0,  0,-10,-20,-30},
        new[] {-30,-10, 20, 30, 30, 20,-10,-30},
        new[] {-30,-10, 30, 40, 40, 30,-10,-30},
        new[] {-30,-10, 30, 40, 40, 30,-10,-30},
        new[] {-30,-10, 20, 30, 30, 20,-10,-30},
        new[] {-30,-30,  0,  0,  0,  0,-30,-30},
        new[] {-50,-30,-30,-30,-30,-30,-30,-50}
    };
}