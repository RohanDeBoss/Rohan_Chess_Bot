using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

//My2ndBot v0.2 TT Added so a lot faster + bot is now stronger!
public class EvilBot : IChessBot
{
    private const int MaxDepth = 1;
    private const int QuiescenceDepthLimit = 5;
    private const int InfiniteScore = 1000000;
    private const int MaxTTSize = 1000000;

    private int positionsSearched = 0;
    private int ttHits = 0;
    private int ttCollisions = 0;
    public int bestScore;
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 };

    private const byte EXACT = 0;
    private const byte ALPHA = 1;
    private const byte BETA = 2;

    private class TTEntry
    {
        public ulong Key;
        public int Depth;
        public int Score;
        public byte Flag;
        public Move BestMove;
    }

    private Dictionary<ulong, TTEntry> transpositionTable = new Dictionary<ulong, TTEntry>();

    private void AddToTranspositionTable(ulong key, int depth, int score, byte flag, Move bestMove)
    {
        if (transpositionTable.ContainsKey(key))
        {
            ttCollisions++;
            // Only replace if new position was searched to greater or equal depth
            if (transpositionTable[key].Depth <= depth)
            {
                transpositionTable[key] = new TTEntry
                {
                    Key = key,
                    Depth = depth,
                    Score = score,
                    Flag = flag,
                    BestMove = bestMove
                };
            }
            return;
        }

        if (transpositionTable.Count >= MaxTTSize)
        {
            // Remove a random entry if table is full
            var keyToRemove = transpositionTable.Keys.First();
            transpositionTable.Remove(keyToRemove);
        }

        transpositionTable[key] = new TTEntry
        {
            Key = key,
            Depth = depth,
            Score = score,
            Flag = flag,
            BestMove = bestMove
        };
    }

    private void PrintTTStats()
    {
        double fillPercentage = (transpositionTable.Count * 100.0) / MaxTTSize;
        double hitRate = positionsSearched > 0 ? (ttHits * 100.0) / positionsSearched : 0;
        double collisionRate = ttCollisions > 0 ? (ttCollisions * 100.0) / transpositionTable.Count : 0;

        Console.WriteLine($"TT Stats:");
        Console.WriteLine($"  Size: {transpositionTable.Count:N0} / {MaxTTSize:N0} ({fillPercentage:F2}% full)");
        Console.WriteLine($"  Hits: {ttHits:N0} ({hitRate:F2}% of positions)");
        Console.WriteLine($"  Collisions: {ttCollisions:N0} ({collisionRate:F2}% of entries)");
    }

    public Move Think(Board board, Timer timer)
    {
        Move bestMove = Move.NullMove;
        int depth = 1;
        bestScore = -InfiniteScore;
        positionsSearched = 0;
        ttHits = 0;
        ttCollisions = 0;

        var legalMoves = board.GetLegalMoves();
        if (legalMoves.Length == 1)
            return legalMoves[0];

        while (depth <= MaxDepth)
        {
            bool foundLegalMove = false;
            var orderedMoves = legalMoves.OrderByDescending(move => MoveOrdering(move, board)).ToList();
            foreach (Move move in orderedMoves)
            {
                if (IsCheckmateMove(move, board))
                    return move;

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

            if (!foundLegalMove)
                break;

            depth++;
        }

        if (bestMove == Move.NullMove && legalMoves.Length > 0)
            bestMove = legalMoves[0];

        Console.WriteLine(" ");
        Console.WriteLine($"EvilBot Depth: {depth - 1}");
        

        return bestMove;
    }


    private Move[] killerMoves = new Move[MaxDepth * 2]; // Two killer moves per ply
    private int[,] historyMoves = new int[64, 64]; // From square -> To square history table

    private int MoveOrdering(Move move, Board board, int ply = 0)
    {
        int score = 0;

        // 1. TT moves (highest priority)
        ulong positionKey = board.ZobristKey;
        if (transpositionTable.TryGetValue(positionKey, out TTEntry ttEntry) &&
            ttEntry.BestMove == move)
        {
            return 1000000;
        }

        // 2. Captures with MVV/LVA scoring
        PieceType capturedPieceType = board.GetPiece(move.TargetSquare).PieceType;
        if (capturedPieceType != PieceType.None)
        {
            int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
            int victimValue = GetPieceValue(capturedPieceType);
            score += 100000 + (victimValue * 10 - attackerValue);
        }

        // 3. Killer moves
        if (move == killerMoves[ply * 2] || move == killerMoves[ply * 2 + 1])
        {
            score += 90000;
        }

        // 4. History moves
        score += historyMoves[move.StartSquare.Index, move.TargetSquare.Index];

        // 5. Promotions
        if (move.IsPromotion)
        {
            score += 80000 + GetPieceValue(move.PromotionPieceType);
        }

        return score;
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        // Don't store captures as killer moves
        if (move.CapturePieceType != PieceType.None) return;

        // Shift killer moves
        if (move != killerMoves[ply * 2])
        {
            killerMoves[ply * 2 + 1] = killerMoves[ply * 2];
            killerMoves[ply * 2] = move;
        }
    }

    private void UpdateHistoryMove(Move move, int depth)
    {
        // Don't store captures in history table
        if (move.CapturePieceType != PieceType.None) return;

        // Update history score with depth squared bonus
        historyMoves[move.StartSquare.Index, move.TargetSquare.Index] += depth * depth;

        // Periodically reduce history scores to prevent overflow
        if (positionsSearched % 1000 == 0)
        {
            for (int from = 0; from < 64; from++)
                for (int to = 0; to < 64; to++)
                    historyMoves[from, to] = historyMoves[from, to] * 3 / 4;
        }
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

        if (depth <= 0)
            return Evaluate(board, depth);

        int stand_pat = Evaluate(board, depth);
        if (stand_pat >= beta)
            return beta;
        if (alpha < stand_pat)
            alpha = stand_pat;
        var captureMoves = board.GetLegalMoves(true).OrderByDescending(move => MoveOrdering(move, board)).ToList();
        foreach (Move move in captureMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, depth - 1);
            board.UndoMove(move);

            if (score >= beta)
                return beta;
            if (score > alpha)
                alpha = score;
        }
        return alpha;
    }

    private int Negamax(Board board, int depth, int alpha, int beta, int ply)
    {
        positionsSearched++;

        if (board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        // Check transposition table
        ulong positionKey = board.ZobristKey;
        if (transpositionTable.TryGetValue(positionKey, out TTEntry ttEntry))
        {
            if (ttEntry.Depth >= depth)
            {
                ttHits++;
                if (ttEntry.Flag == EXACT)
                    return ttEntry.Score;
                if (ttEntry.Flag == ALPHA && ttEntry.Score <= alpha)
                    return alpha;
                if (ttEntry.Flag == BETA && ttEntry.Score >= beta)
                    return beta;
            }
        }

        if (depth == 0)
            return Quiescence(board, alpha, beta, QuiescenceDepthLimit);

        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int bestScore = -InfiniteScore;
        List<Move> moves = board.GetLegalMoves().OrderByDescending(move => MoveOrdering(move, board)).ToList();

        foreach (Move move in moves)
        {
            board.MakeMove(move);
            int score = -Negamax(board, depth - 1, -beta, -alpha, ply + 1);
            board.UndoMove(move);

            if (score > bestScore)
            {
                bestScore = score;
                bestMove = move;
            }

            alpha = Math.Max(alpha, score);
            if (alpha >= beta)
            {
                // Update killer moves on beta cutoff
                UpdateKillerMoves(move, ply);
                // Update history moves on beta cutoff
                UpdateHistoryMove(move, depth);

                AddToTranspositionTable(positionKey, depth, beta, BETA, move);
                return beta;
            }
        }

        byte flag = bestScore <= originalAlpha ? ALPHA :
                   bestScore >= beta ? BETA : EXACT;
        AddToTranspositionTable(positionKey, depth, bestScore, flag, bestMove);

        return bestScore;
    }

    private int Evaluate(Board board, int depth)
    {
        if (board.IsInCheckmate())
            return -InfiniteScore - depth;

        if (board.IsDraw())
            return 0;

        int score = 0;
        bool isEndgame = IsEndgame(board);
        PieceList[] pieceLists = board.GetAllPieceLists();

        foreach (PieceList pieceList in pieceLists)
        {
            int pieceValue = GetPieceValue(pieceList.TypeOfPieceInList);
            int[,] adjustmentTable = GetAdjustmentTable(pieceList.TypeOfPieceInList, isEndgame);

            foreach (Piece piece in pieceList)
            {
                Square square = piece.Square;
                int file = square.File;
                int rank = piece.IsWhite ? 7 - square.Rank : square.Rank;

                int value = adjustmentTable[rank, file] + pieceValue;
                score += piece.IsWhite ? value : -value;
            }
        }

        return board.IsWhiteToMove ? score : -score;
    }


    private int GetPieceValue(PieceType pieceType)
    {
        switch (pieceType)
        {
            case PieceType.Pawn:
                return PieceValues[0];
            case PieceType.Knight:
                return PieceValues[1];
            case PieceType.Bishop:
                return PieceValues[2];
            case PieceType.Rook:
                return PieceValues[3];
            case PieceType.Queen:
                return PieceValues[4];
            case PieceType.King:
                return PieceValues[5];
            default:
                Console.WriteLine($"Warning: Unknown piece type {pieceType}");
                return 0;
        }
    }

    private int[,] GetAdjustmentTable(PieceType pieceType, bool isEndgame)
    {
        switch (pieceType)
        {
            case PieceType.Pawn:
                return PawnTable;
            case PieceType.Knight:
                return KnightTable;
            case PieceType.Bishop:
                return BishopTable;
            case PieceType.Rook:
                return RookTable;
            case PieceType.Queen:
                return QueenTable;
            case PieceType.King:
                return isEndgame ? KingEndGame : KingMiddleGame;
            default:
                return new int[8, 8];
        }
    }

    private bool IsEndgame(Board board)
    {
        int pieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
        return pieceCount <= 10; // You can adjust this threshold as needed
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