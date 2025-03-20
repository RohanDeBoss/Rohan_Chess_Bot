using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

//My2ndBot v0.2 Added lots of features, including a Transposition table, Null move pruning and LMR
public class MyBot : IChessBot
{
    private const int MaxDepth = 3;
    private const int InfiniteScore = 1000000;
    private const int MaxTTSize = 1000000 * MaxDepth;

    private int positionsSearched = 0;
    public int bestScore;
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 };

    private const byte EXACT = 0;
    private const byte ALPHA = 1;
    private const byte BETA = 2;

    private class TTEntry
    {
        public ulong Key;
        public short Depth;
        public int Score;
        public byte Flag;
        public Move BestMove;
    }

    private Dictionary<ulong, TTEntry> transpositionTable = new Dictionary<ulong, TTEntry>();

    private void AddToTranspositionTable(ulong key, int depth, int score, byte flag, Move bestMove)
    {
        if (transpositionTable.ContainsKey(key))
        {
            // Only replace if new position was searched to greater or equal depth
            if (transpositionTable[key].Depth <= depth)
            {
                transpositionTable[key] = new TTEntry
                {
                    Key = key,
                    Depth = (short)depth,
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
            Depth = (short)depth,
            Score = score,
            Flag = flag,
            BestMove = bestMove
        };
    }

    public Move Think(Board board, Timer timer)
    {
        Move bestMove = Move.NullMove;
        int depth = 1;
        bestScore = -InfiniteScore;
        positionsSearched = 0;

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
        Console.WriteLine($"MyBot Depth: {depth - 1}");
        Console.WriteLine($"MyBot eval: {(board.IsWhiteToMove ? bestScore : -bestScore)}");
        Console.WriteLine($"MyBot Positions searched: {positionsSearched:N0}");

        return bestMove;
    }


    private Move[] killerMoves = new Move[MaxDepth * 2]; // Two killer moves per ply
    private int[,] historyMoves = new int[64, 64]; // From square -> To square history table

    private int MoveOrdering(Move move, Board board, int ply = 0)
    {
        int score = 0;

        // 1. TT moves (highest priority)
        ulong positionKey = board.ZobristKey;
        if (transpositionTable.TryGetValue(positionKey, out TTEntry? ttEntry) &&
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

        // Evaluate the position at the current depth
        int stand_pat = Evaluate(board, depth);

        // Beta cut-off
        if (stand_pat >= beta)
            return beta;

        // Update alpha if the stand-pat score is better
        if (alpha < stand_pat)
            alpha = stand_pat;

        // Get capture moves ordered by their potential value
        var captureMoves = board.GetLegalMoves(true).OrderByDescending(move => MoveOrdering(move, board)).ToList();

        // Explore capturing moves
        foreach (Move move in captureMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, depth - 1); // Recur with reduced depth
            board.UndoMove(move);

            // Beta cut-off
            if (score >= beta)
                return beta;

            // Update alpha based on the score
            if (score > alpha)
                alpha = score;
        }
        return alpha; // Return the best score found
    }


    private const int R = 2; // Reduction for null move pruning
    private const int LMR_THRESHOLD = 2;  // Depth threshold to apply LMR

    private int Negamax(Board board, int depth, int alpha, int beta, int ply)
    {
        positionsSearched++;

        if (board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        // Transposition Table lookup
        ulong positionKey = board.ZobristKey;
        if (transpositionTable.TryGetValue(positionKey, out TTEntry? ttEntry))
        {
            if (ttEntry.Depth >= depth)
            {
                if (ttEntry.Flag == EXACT)
                    return ttEntry.Score;
                if (ttEntry.Flag == ALPHA && ttEntry.Score <= alpha)
                    return alpha;
                if (ttEntry.Flag == BETA && ttEntry.Score >= beta)
                    return beta;
            }
        }

        if (depth == 0)
            return Quiescence(board, alpha, beta, 0);

        // Null Move Pruning
        if (depth > R && !board.IsInCheck())
        {
            board.ForceSkipTurn();
            int nullMoveScore = -Negamax(board, depth - R - 1, -beta, -beta + 1, ply + 1);
            board.UndoSkipTurn();

            if (nullMoveScore >= beta)
                return beta;
        }

        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int bestScore = -InfiniteScore;
        List<Move> moves = board.GetLegalMoves().OrderByDescending(move => MoveOrdering(move, board)).ToList();

        int moveCount = 0;
        foreach (Move move in moves)
        {
            board.MakeMove(move);

            // Late Move Reduction check
            int newDepth = depth - 1;
            bool canReduce = moveCount >= LMR_THRESHOLD && depth > 2 && !move.IsCapture && !board.IsInCheck();
            if (canReduce)
                newDepth--; // Reduce depth for late moves

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
                    AddToTranspositionTable(positionKey, depth, beta, BETA, move);
                }
                return beta;
            }
            moveCount++;
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

        foreach (PieceList pieceList in board.GetAllPieceLists())
        {
            int pieceValue = GetPieceValue(pieceList.TypeOfPieceInList);
            int[,] adjustmentTable = GetAdjustmentTable(pieceList.TypeOfPieceInList, isEndgame);

            foreach (Piece piece in pieceList)
            {
                int rank = piece.IsWhite ? 7 - piece.Square.Rank : piece.Square.Rank;
                score += (piece.IsWhite ? 1 : -1) *
                        (adjustmentTable[rank, piece.Square.File] + pieceValue);
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