using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

//My2ndBot v0.4 TT is now an array, and code is much cleaner!
public class EvilBot : IChessBot
{
    private const bool ConstantDepth = true;
    private const int MaxDepth = 1;
    private const int InfiniteScore = 1000000;
    private const int TT_SIZE = 500000 * MaxDepth;

    private const int R = 2;
    private const int LMR_THRESHOLD = 2;
    private Move[] killerMoves = new Move[MaxDepth * 2];
    private int[,] historyMoves = new int[64, 64];

    private int positionsSearched = 0;
    private int ttHits = 0;
    private int ttCollisions = 0;
    public int bestScore;
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 };
    private static TTEntry[] tt = new TTEntry[TT_SIZE];

    public Move Think(Board board, Timer timer)
    {
        Move bestMove = Move.NullMove;
        positionsSearched = 0;
        ttHits = 0;
        ttCollisions = 0;
        int depth = 1;

        var legalMoves = board.GetLegalMoves();
        if (legalMoves.Length == 1) return legalMoves[0]; // Return immediately if only one move is possible

        // Iterative Deepening with time management when ConstantDepth is false
        int maxTimeForTurn = ConstantDepth ? int.MaxValue :
            (Math.Min(1000, timer.MillisecondsRemaining / 28) + timer.IncrementMilliseconds) / 4;

        while (depth <= MaxDepth && (ConstantDepth || timer.MillisecondsElapsedThisTurn < maxTimeForTurn))
        {
            bool foundLegalMove = false;
            var orderedMoves = legalMoves.OrderByDescending(move => MoveOrdering(move, board)).ToList();

            foreach (Move move in orderedMoves)
            {
                if (IsCheckmateMove(move, board)) return move; // Immediate return on checkmate

                board.MakeMove(move);
                int score = -Negamax(board, depth - 1, -InfiniteScore, InfiniteScore, 1);
                board.UndoMove(move);

                if (score > bestScore || !foundLegalMove)
                {
                    bestScore = score;
                    bestMove = move;
                    foundLegalMove = true;
                }
            }

            if (!foundLegalMove) break; // Exit if no moves were valid at this depth
            depth++; // Increase depth for the next iteration
        }

        if (bestMove == Move.NullMove && legalMoves.Length > 0)
            bestMove = legalMoves[0];

        Console.WriteLine(" ");
        Console.WriteLine($"Evil Depth: {depth - 1}");
        Console.WriteLine($"Evil eval: {(board.IsWhiteToMove ? bestScore : -bestScore)}");
        Console.WriteLine($"Evil Positions searched: {positionsSearched:N0}");
        //PrintTTStats();
        return bestMove;
    }

    private void PrintTTStats()
    {
        int usedEntries = tt.Count(entry => entry.Key != 0);
        double fillPercentage = (usedEntries * 100.0) / TT_SIZE;
        double hitRate = positionsSearched > 0 ? (ttHits * 100.0) / positionsSearched : 0;
        double collisionRate = ttCollisions > 0 ? (ttCollisions * 100.0) / usedEntries : 0;

        Console.WriteLine($"Evil TT Stats:");
        Console.WriteLine($"  Size: {usedEntries:N0} / {TT_SIZE:N0} ({fillPercentage:F2}% full)");
        Console.WriteLine($"  Hits: {ttHits:N0} ({hitRate:F2}% of positions)");
        Console.WriteLine($"  Collisions: {ttCollisions:N0} ({collisionRate:F2}% of entries)");
    }

    private int MoveOrdering(Move move, Board board, int ply = 0)
    {
        int score = 0;
        ulong key = board.ZobristKey;
        int index = (int)(key % TT_SIZE);

        if (tt[index].Key == key && tt[index].BestMove == move)
            return 1000000;

        PieceType capturedPieceType = board.GetPiece(move.TargetSquare).PieceType;
        if (capturedPieceType != PieceType.None)
        {
            int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
            int victimValue = GetPieceValue(capturedPieceType);
            score += 100000 + (victimValue * 10 - attackerValue);
        }

        if (move == killerMoves[ply * 2] || move == killerMoves[ply * 2 + 1])
            score += 90000;

        score += historyMoves[move.StartSquare.Index, move.TargetSquare.Index];

        if (move.IsPromotion)
            score += 80000 + GetPieceValue(move.PromotionPieceType);

        return score;
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        if (move.CapturePieceType != PieceType.None) return;
        if (move != killerMoves[ply * 2])
        {
            killerMoves[ply * 2 + 1] = killerMoves[ply * 2];
            killerMoves[ply * 2] = move;
        }
    }

    private void UpdateHistoryMove(Move move, int depth)
    {
        if (move.CapturePieceType != PieceType.None) return;
        historyMoves[move.StartSquare.Index, move.TargetSquare.Index] += depth * depth;
        if (positionsSearched % 1000 == 0)
            for (int from = 0; from < 64; from++)
                for (int to = 0; to < 64; to++)
                    historyMoves[from, to] = historyMoves[from, to] * 3 / 4;
    }

    private bool IsCheckmateMove(Move move, Board board)
    {
        board.MakeMove(move);
        bool isCheckmate = board.IsInCheckmate();
        board.UndoMove(move);
        return isCheckmate;
    }

    private int Quiescence(Board board, int alpha, int beta, int depth)
    {
        positionsSearched++;
        int stand_pat = Evaluate(board, depth);
        if (stand_pat >= beta) return beta;
        if (alpha < stand_pat) alpha = stand_pat;

        var captureMoves = board.GetLegalMoves(true).OrderByDescending(move => MoveOrdering(move, board)).ToList();
        foreach (Move move in captureMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, depth - 1);
            board.UndoMove(move);
            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }
        return alpha;
    }

    private int Negamax(Board board, int depth, int alpha, int beta, int ply)
    {
        positionsSearched++;
        if (board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        ulong key = board.ZobristKey;
        int index = (int)(key % TT_SIZE);
        if (tt[index].Key == key && tt[index].Depth >= depth)
        {
            ttHits++;
            if (tt[index].Flag == EXACT) return tt[index].Score;
            if (tt[index].Flag == ALPHA && tt[index].Score <= alpha) return alpha;
            if (tt[index].Flag == BETA && tt[index].Score >= beta) return beta;
        }

        if (depth == 0) return Quiescence(board, alpha, beta, 0);

        if (depth > R && !board.IsInCheck())
        {
            board.ForceSkipTurn();
            int nullMoveScore = -Negamax(board, depth - R - 1, -beta, -beta + 1, ply + 1);
            board.UndoSkipTurn();
            if (nullMoveScore >= beta) return beta;
        }

        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int bestScore = -InfiniteScore;
        List<Move> moves = board.GetLegalMoves().OrderByDescending(move => MoveOrdering(move, board)).ToList();

        int moveCount = 0;
        foreach (Move move in moves)
        {
            board.MakeMove(move);
            int newDepth = depth - 1;
            if (moveCount >= LMR_THRESHOLD && depth > 2 && !move.IsCapture && !board.IsInCheck())
                newDepth--;

            int score = -Negamax(board, newDepth, -beta, -alpha, ply + 1);
            board.UndoMove(move);

            if (score > bestScore)
            {
                bestScore = score;
                bestMove = move;
            }

            alpha = Math.Max(alpha, score);
            if (alpha >= beta)
            {
                if (move.CapturePieceType == PieceType.None)
                {
                    UpdateKillerMoves(move, ply);
                    UpdateHistoryMove(move, depth);
                    AddTT(key, depth, beta, BETA, move);
                }
                return beta;
            }
            moveCount++;
        }

        byte flag = bestScore <= originalAlpha ? ALPHA : bestScore >= beta ? BETA : EXACT;
        AddTT(key, depth, bestScore, flag, bestMove);
        return bestScore;
    }

    private int Evaluate(Board board, int depth)
    {
        if (board.IsInCheckmate())
            return -InfiniteScore - depth;
        if (board.IsDraw())
            return -40;

        int score = 0;
        bool isEndgame = IsEndgame(board);

        foreach (PieceList pieceList in board.GetAllPieceLists())
        {
            int pieceValue = GetPieceValue(pieceList.TypeOfPieceInList);
            int[,] adjustmentTable = GetAdjustmentTable(pieceList.TypeOfPieceInList, isEndgame);
            foreach (Piece piece in pieceList)
            {
                int rank = piece.IsWhite ? 7 - piece.Square.Rank : piece.Square.Rank;
                score += (piece.IsWhite ? 1 : -1) * (adjustmentTable[rank, piece.Square.File] + pieceValue);
            }
        }
        return board.IsWhiteToMove ? score : -score;
    }

    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private bool IsEndgame(Board board)
    {
        ulong currentBoardHash = board.ZobristKey; // Unique identifier for board state

        // Update cached piece count only if the board has changed
        if (currentBoardHash != lastBoardHash)
        {
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = currentBoardHash;
        }

        return cachedPieceCount <= 10; // Threshold can be adjusted as needed
    }

    private int GetPieceValue(PieceType pieceType)
    {
        return pieceType switch
        {
            PieceType.Pawn => PieceValues[0],
            PieceType.Knight => PieceValues[1],
            PieceType.Bishop => PieceValues[2],
            PieceType.Rook => PieceValues[3],
            PieceType.Queen => PieceValues[4],
            PieceType.King => PieceValues[5],
            _ => 0
        };
    }

    private int[,] GetAdjustmentTable(PieceType pieceType, bool isEndgame) =>
        pieceType switch
        {
            PieceType.Pawn => PawnTable,
            PieceType.Knight => KnightTable,
            PieceType.Bishop => BishopTable,
            PieceType.Rook => RookTable,
            PieceType.Queen => QueenTable,
            PieceType.King => isEndgame ? KingEndGame : KingMiddleGame,
            _ => new int[8, 8]
        };

    private struct TTEntry
    {
        public ulong Key;
        public short Depth;
        public int Score;
        public byte Flag;
        public Move BestMove;
    }

    private const byte EXACT = 0;
    private const byte ALPHA = 1;
    private const byte BETA = 2;

    private void AddTT(ulong key, int depth, int score, byte flag, Move bestMove)
    {
        int index = (int)(key % TT_SIZE);
        if (tt[index].Key != key && tt[index].Key != 0) ttCollisions++;
        if (tt[index].Key == 0 || tt[index].Depth <= depth)
            tt[index] = new TTEntry { Key = key, Depth = (short)depth, Score = score, Flag = flag, BestMove = bestMove };
    }

    private static readonly int[,] PawnTable = {
        {0,  0,  0,  0,  0,  0,  0,  0},
        {50, 50, 50, 50, 50, 50, 50, 50},
        {10, 10, 20, 30, 30, 20, 10, 10},
        {5,  5, 10, 25, 25, 10,  5,  5},
        {0,  0,  0, 20, 20,  0,  0,  0},
        {5, -5,-10,  0,  0,-10, -5,  5},
        {5, 10, 10,-20,-20, 10, 10,  5},
        {0,  0,  0,  0,  0,  0,  0,  0}
    };

    private static readonly int[,] KnightTable = {
        {-50,-40,-30,-30,-30,-30,-40,-50},
        {-40,-20,  0,  0,  0,  0,-20,-40},
        {-30,  0, 10, 15, 15, 10,  0,-30},
        {-30,  5, 15, 20, 20, 15,  5,-30},
        {-30,  0, 15, 20, 20, 15,  0,-30},
        {-30,  5, 10, 15, 15, 10,  5,-30},
        {-40,-20,  0,  5,  5,  0,-20,-40},
        {-50,-40,-30,-30,-30,-30,-40,-50}
    };

    private static readonly int[,] BishopTable = {
        {-20,-10,-10,-10,-10,-10,-10,-20},
        {-10,  0,  0,  0,  0,  0,  0,-10},
        {-10,  0,  5, 10, 10,  5,  0,-10},
        {-10,  5,  5, 10, 10,  5,  5,-10},
        {-10,  0, 10, 10, 10, 10,  0,-10},
        {-10, 10, 10, 10, 10, 10, 10,-10},
        {-10,  5,  0,  0,  0,  0,  5,-10},
        {-20,-10,-10,-10,-10,-10,-10,-20}
    };

    private static readonly int[,] RookTable = {
        {0,  0,  0,  0,  0,  0,  0,  0},
        {5, 10, 10, 10, 10, 10, 10,  5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {0,  0,  0,  5,  5,  0,  0,  0}
    };

    private static readonly int[,] QueenTable = {
        {-20,-10,-10, -5, -5,-10,-10,-20},
        {-10,  0,  0,  0,  0,  0,  0,-10},
        {-10,  0,  5,  5,  5,  5,  0,-10},
        {-5,  0,  5,  5,  5,  5,  0, -5},
        {0,  0,  5,  5,  5,  5,  0, -5},
        {-10,  5,  5,  5,  5,  5,  0,-10},
        {-10,  0,  5,  0,  0,  0,  0,-10},
        {-20,-10,-10, -5, -5,-10,-10,-20}
    };

    private static readonly int[,] KingMiddleGame = {
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-20,-30,-30,-40,-40,-30,-30,-20},
        {-10,-20,-20,-20,-20,-20,-20,-10},
        {20, 20,  0,  0,  0,  0, 20, 20},
        {20, 30, 10,  0,  0, 10, 30, 20}
    };

    private static readonly int[,] KingEndGame = {
        {-50,-40,-30,-20,-20,-30,-40,-50},
        {-30,-20,-10,  0,  0,-10,-20,-30},
        {-30,-10, 20, 30, 30, 20,-10,-30},
        {-30,-10, 30, 40, 40, 30,-10,-30},
        {-30,-10, 30, 40, 40, 30,-10,-30},
        {-30,-10, 20, 30, 30, 20,-10,-30},
        {-30,-30,  0,  0,  0,  0,-30,-30},
        {-50,-30,-30,-30,-30,-30,-30,-50}
    };
}