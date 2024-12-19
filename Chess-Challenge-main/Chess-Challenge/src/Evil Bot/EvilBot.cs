using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

//My2ndBot v0.6 Bug fixes and experimental features removed draw has to be 0 now!
public class EvilBot : IChessBot
{
    private const bool ConstantDepth = true;
    private const short MaxDepth = 3;
    private const short InfiniteScore = 30000; //less than 32k so that it fits into short!
    private const int TT_SIZE = 1048576;
    private const short TimeSpentFractionofTotal = 18;

    private const byte R = 2;
    private const byte LMR_THRESHOLD = 2;

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
        short safetymaxdepth = 150;
        short depth = 1;

        var legalMoves = board.GetLegalMoves();
        if (legalMoves.Length == 1) return legalMoves[0]; // Return immediately if only one legal move

        // Iterative Deepening with time management when ConstantDepth is false
        int maxTimeForTurn = ConstantDepth ? int.MaxValue :
            (Math.Min(1000, timer.MillisecondsRemaining / TimeSpentFractionofTotal) + timer.IncrementMilliseconds) / 4;

        while ((ConstantDepth && depth <= MaxDepth) || (!ConstantDepth && timer.MillisecondsElapsedThisTurn < maxTimeForTurn))
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

            if (!foundLegalMove || depth >= safetymaxdepth) break; // Exit if no moves were found or depth>=150
            depth++; // Increase depth for the next iteration
        }

        if (bestMove == Move.NullMove && legalMoves.Length > 0)
            bestMove = legalMoves[0];

        //TT loop
        int usedEntries = tt.Count(entry => entry.Key != 0);
        double fillPercentage = (usedEntries * 100.0) / TT_SIZE;

        Console.WriteLine(" ");
        Console.WriteLine($"Evil Depth: {depth - 1}");
        Console.WriteLine($"Evil eval: {(board.IsWhiteToMove ? bestScore : -bestScore)}");
        Console.WriteLine($"Evil Positions: {positionsSearched:N0}");
        Console.WriteLine($"Evil TT Size: ({fillPercentage:F2}%)");
        return bestMove;
    }

    private int MoveOrdering(Move move, Board board, int ply = 0)
    {
        ulong key = board.ZobristKey;
        int index = (int)(key % TT_SIZE);

        // Prioritize transposition table moves.
        if (tt[index].Key == key && tt[index].BestMove == move)
            return 1000000;

        int score = historyMoves[move.StartSquare.Index, move.TargetSquare.Index];

        // Captures: MVV-LVA (Most Valuable Victim - Least Valuable Attacker)
        var capturedPiece = board.GetPiece(move.TargetSquare);
        if (capturedPiece.PieceType != PieceType.None)
        {
            score += 100000 + GetPieceValue(capturedPiece.PieceType) * 10 -
                     GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
        }

        // Promotion moves.
        if (move.IsPromotion)
            score += 80000 + GetPieceValue(move.PromotionPieceType);

        // Killer moves.
        if (move == killerMoves[ply * 2] || move == killerMoves[ply * 2 + 1])
            score += 90000;

        return score;
    }

    private Move[] killerMoves = new Move[100 * 2];
    private int[,] historyMoves = new int[64, 64];

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

        if (board.IsDraw())
            return 0; //Always 0
        if (board.IsInCheckmate())
            return -InfiniteScore - depth;

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
        short bestScore = -InfiniteScore;
        List<Move> moves = board.GetLegalMoves().OrderByDescending(move => MoveOrdering(move, board)).ToList();

        int moveCount = 0;
        foreach (Move move in moves)
        {
            board.MakeMove(move);
            short newDepth = (short)(depth - 1);
            if (moveCount >= LMR_THRESHOLD && depth > 2 && !move.IsCapture && !board.IsInCheck())
                newDepth--;

            int score;
            if (moveCount == 0) // First move, full search window
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1);
            }
            else
            {
                // PVS: Perform a null window search on non-primary moves
                score = -Negamax(board, newDepth, -alpha - 1, -alpha, ply + 1);
                // If it fails within the alpha-beta window, re-search with the full window
                if (score > alpha && score < beta)
                {
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1);
                }
            }

            board.UndoMove(move);

            if (score > bestScore)
            {
                bestScore = (short)score;
                bestMove = move;
            }

            alpha = Math.Max(alpha, score);
            if (alpha >= beta)
            {
                if (move.CapturePieceType == PieceType.None)
                {
                    UpdateKillerMoves(move, ply);
                    UpdateHistoryMove(move, depth);
                    AddTT(key, depth, (short)beta, BETA, move);
                }
                return beta;
            }
            moveCount++;
        }

        byte flag = bestScore <= originalAlpha ? ALPHA : bestScore >= beta ? BETA : EXACT;
        AddTT(key, depth, (short)bestScore, flag, bestMove);
        return bestScore;
    }

    private int Evaluate(Board board, int depth)
    {
        int score = 0;
        bool isEndgame = IsEndgame(board);

        if (board.IsDraw())
            return 0; //Always 0

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
        ulong currentBoardHash = board.ZobristKey;

        // Update cached data if the board state has changed
        if (currentBoardHash != lastBoardHash)
        {
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = currentBoardHash;
        }

        // Check if the game is in an endgame phase
        const int endgameThreshold = 12;
        return cachedPieceCount <= endgameThreshold;
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
        public short Score;
        public byte Flag;
        public Move BestMove;
    }

    private const byte EXACT = 0;
    private const byte ALPHA = 1;
    private const byte BETA = 2;

    private void AddTT(ulong key, int depth, short score, byte flag, Move bestMove)
    {
        int index = (int)(key % TT_SIZE);
        if (tt[index].Key != key && tt[index].Key != 0) ttCollisions++;
        if (tt[index].Key == 0 || tt[index].Depth <= depth)
            tt[index] = new TTEntry { Key = key, Depth = (short)depth, Score = score, Flag = flag, BestMove = bestMove };
    }

    //Piece square table bitboards
    private static readonly int[,] PawnTable = {
        {0,  0,  0,  0,  0,  0,  0,  0},
        {50, 50, 50, 50, 50, 50, 50, 50},
        {12, 10, 20, 30, 30, 20, 11, 10},
        {5,  5, 10, 25, 25, 10,  5,  5},
        {1,  3 ,  6, 21, 22,  0,  0,  0},
        {5, -1,-10,  1,  3,-10, -5,  5},
        {5, 10, 10,-20,-20, 10, 11,  5},
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
        {0,   0,  0,  0,  0,  0,  0,  0},
        {0,  10, 10, 10, 10, 10, 10,  5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {0,  0,  0,  5,  5,  0,  0,  -4}
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