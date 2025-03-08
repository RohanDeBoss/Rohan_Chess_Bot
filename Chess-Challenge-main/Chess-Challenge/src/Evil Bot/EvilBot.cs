using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

// v1.7 Code refactor and Automatic MyBot/Evil Name debug switching
public class EvilBot : IChessBot
{
    // Constants
    private const bool ConstantDepth = false;
    private const short MaxDepth = 6; // Only does anything when Constant depth is true
    private const short MaxSafetyDepth = 99; // New absolute maximum safety depth
    private const short InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22;

    // Static Fields
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 };
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = (ulong)(TT_SIZE - 1);

    private int GetTTIndex(ulong key) => (int)(key & ttMask);

    // Instance Fields
    private int negamaxPositions = 0;
    private int qsearchPositions = 0;
    private int bestScore;
    private List<Move> killerMoves = new List<Move>();
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private int currentDepth;

    // Debugging
    private void DebugLog(string message)
    {
        Console.WriteLine($"{GetType().Name}: {message}");
    }


    private string? GetMateInMoves(int score)
    {
        int mateMoves = (InfiniteScore - Math.Abs(score) + 1) / 50;
        if (Math.Abs(score) >= InfiniteScore - 1500 && mateMoves <= currentDepth)
        {
            return score > 0
                ? $"Mate in {mateMoves} ply! :)"
                : $"Mated in {mateMoves} ply :(";
        }
        return null;
    }

    private void LogEval(Board board, int depth, bool isForcedMove)
    {
        if (isForcedMove)
        {
            Console.WriteLine();
            Console.WriteLine($"{GetType().Name}: I must play a FORCED MOVE!");
        }
        else
        {
            Console.WriteLine();
            DebugLog($"Depth: {depth}");
            string mateInfo = GetMateInMoves(bestScore) ?? string.Empty;
            DebugLog(!string.IsNullOrEmpty(mateInfo) ? mateInfo : "No forced mate found");
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
            if (moves[i] == ttEntry.BestMove)
                score += 10_000_000;
            if (previousBestMove.HasValue && moves[i] == previousBestMove.Value)
                score += 5_000_000;
            score += MoveOrdering(moves[i], board, ply);
            scores[i] = score;
        }

        Array.Sort(scores, moves, Comparer<int>.Create((a, b) => b.CompareTo(a)));
        return moves;
    }

    private Move HandleForcedMove(Move move, Board board, int forcedDepth, bool isForcedMove, int? overrideScore = null)
    {
        board.MakeMove(move);
        bestScore = overrideScore ?? -Evaluate(board);
        board.UndoMove(move);
        currentDepth = forcedDepth;
        LogEval(board, forcedDepth, isForcedMove);
        return move;
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

        // Aspiration search constants
        const int InitialAspirationWindow = 125;
        const int MaxAspirationDepth = 4;
        const int CheckmateScoreThreshold = 25000;
        const int SafetyMargin = 10;

        short timeFraction = Math.Max(GetTimeSpentFraction(timer), (short)1);
        int maxTimeForTurn = ConstantDepth
            ? int.MaxValue
            : (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 4);

        // Iterative deepening loop with MaxSafetyDepth cap
        while (depth <= MaxSafetyDepth &&
               (ConstantDepth && depth <= MaxDepth ||
                !ConstantDepth && timer.MillisecondsElapsedThisTurn - SafetyMargin < maxTimeForTurn))
        {
            currentDepth = depth;
            bool useAspiration = depth > MaxAspirationDepth && Math.Abs(previousBestScore) < CheckmateScoreThreshold;

            int alpha = -InfiniteScore;
            int beta = InfiniteScore;
            int aspirationWindow = InitialAspirationWindow;
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
                    int score = -Negamax(board, depth - 1, -beta, -alpha, 1);
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
                    aspirationWindow *= 4;
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

        return bestMove;
    }

    // --- Killer moves & History management ---
    private void EnsureKillerMovesSize(int ply)
    {
        int requiredSize = (ply * 2) + 2;
        while (killerMoves.Count < requiredSize)
        {
            killerMoves.Add(Move.NullMove);
        }
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

    private void UpdateHistoryMove(Move move, int depth)
    {
        if (move.CapturePieceType != PieceType.None) return;
        historyMoves[move.StartSquare.Index, move.TargetSquare.Index] += depth * depth;
        if ((negamaxPositions + qsearchPositions) % 512 == 0)
            DecayHistory();
    }

    private void DecayHistory()
    {
        for (int i = 0; i < 64; i++)
            for (int j = 0; j < 64; j++)
                historyMoves[i, j] = (historyMoves[i, j] * 4) / 5;
    }

    private bool IsCheckmateMove(Move move, Board board)
    {
        board.MakeMove(move);
        bool isCheckmate = board.IsInCheckmate();
        board.UndoMove(move);
        return isCheckmate;
    }

    // --- Move ordering helper ---
    private int MoveOrdering(Move move, Board board, int ply = 0)
    {
        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        if (tt[index].Key == key && tt[index].BestMove == move)
            return 1000000;

        int score = historyMoves[move.StartSquare.Index, move.TargetSquare.Index];
        var capturedPiece = board.GetPiece(move.TargetSquare);
        if (capturedPiece.PieceType != PieceType.None)
            score += 100000 + GetPieceValue(capturedPiece.PieceType) * 10 -
                     GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
        if (move.IsPromotion)
            score += 80000 + GetPieceValue(move.PromotionPieceType);

        int killerIndex0 = ply * 2;
        int killerIndex1 = ply * 2 + 1;
        if ((killerMoves.Count > killerIndex0 && move == killerMoves[killerIndex0]) ||
            (killerMoves.Count > killerIndex1 && move == killerMoves[killerIndex1]))
        {
            score += 90000;
        }
        return score;
    }

    private int Negamax(Board board, int depth, int alpha, int beta, int ply)
    {
        negamaxPositions++;

        if (board.IsDraw()) return 0;
        if (board.IsInCheckmate()) return -InfiniteScore + ply * 50;

        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];

        if (ttEntry.Key == key && ttEntry.Depth >= depth)
        {
            if (ttEntry.Flag == EXACT) return ttEntry.Score;
            if (ttEntry.Flag == ALPHA && ttEntry.Score <= alpha) return alpha;
            if (ttEntry.Flag == BETA && ttEntry.Score >= beta) return beta;
        }

        if (depth <= 0) return Quiescence(board, alpha, beta, ply);

        if (!board.IsInCheck() && depth > 2)
        {
            board.ForceSkipTurn();
            int reduction = Math.Min(3, 1 + depth / 4);
            int nullScore = -Negamax(board, depth - reduction - 1, -beta, -beta + 1, ply + 1);
            board.UndoSkipTurn();
            if (nullScore >= beta) return beta;
        }

        int standPat = Evaluate(board);
        Move[] moves = OrderMoves(board.GetLegalMoves(), board, ply);

        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int localBestScore = -InfiniteScore;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            if (depth <= 3 && !board.IsInCheck() && !move.IsCapture && !move.IsPromotion &&
                standPat + 150 * depth < alpha)
            {
                continue;
            }

            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();
            int newDepth = depth - 1;

            if (givesCheck)
                newDepth += 1;
            if (depth > 2 && !move.IsCapture && !move.IsPromotion && !givesCheck)
            {
                int reduction = 1 + (i / 5);
                newDepth = Math.Max(newDepth - reduction, 0);
            }

            int score;
            if (i == 0)
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1);
            }
            else
            {
                score = -Negamax(board, newDepth, -alpha - 1, -alpha, ply + 1);
                if (score > alpha)
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1);
            }
            board.UndoMove(move);

            if (score <= -InfiniteScore + ply)
            {
                newDepth -= 1;
            }

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
            PawnTable,
            KnightTable,
            BishopTable,
            RookTable,
            QueenTable,
            isEndgame ? KingEndGame : KingMiddleGame
        };

        int score = 0;
        foreach (PieceList pieceList in board.GetAllPieceLists())
        {
            var pieceType = pieceList.TypeOfPieceInList;
            int pieceValue = PieceValues[(int)pieceType - 1];
            int[][] adjustmentTable = adjustmentTables[(int)pieceType - 1];
            foreach (Piece piece in pieceList)
            {
                int rank = piece.IsWhite ? 7 - piece.Square.Rank : piece.Square.Rank;
                int adjustment = adjustmentTable[rank][piece.Square.File];
                score += (piece.IsWhite ? 1 : -1) * (pieceValue + adjustment);
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

    private int GetPieceValue(PieceType pieceType) =>
        pieceType <= PieceType.King ? PieceValues[(int)pieceType - 1] : 0;

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

    private void AddTT(ulong key, int depth, short score, byte flag, Move bestMove)
    {
        int index = GetTTIndex(key);
        if (tt[index].Key == 0 || tt[index].Depth <= depth)
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