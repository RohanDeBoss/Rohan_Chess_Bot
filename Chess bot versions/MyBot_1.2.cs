﻿using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

public class MyBot : IChessBot
{
    private const int SEARCH_DEPTH = 4;
    private Move? chosenMove;

    // Data structures for move ordering
    private Dictionary<Move, int> killerMoves = new Dictionary<Move, int>();
    private Dictionary<Move, int> history = new Dictionary<Move, int>();

    // Bitboards
    private ulong whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings;
    private ulong blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings;

    private ulong[] bitboards = new ulong[12]; // 0-5: White pieces, 6-11: Black pieces

    public Move Think(Board board, Timer timer)
    {
        InitializeBitboards(board);
        Minimax(board, SEARCH_DEPTH, int.MinValue, int.MaxValue, board.IsWhiteToMove, true);
        return chosenMove ?? new Move(); // Return an empty move if no move is chosen
    }

    private void InitializeBitboards(Board board)
    {
        Array.Clear(bitboards, 0, bitboards.Length);

        for (int i = 0; i < 64; i++)
        {
            Piece piece = board.GetPiece(new Square(i));
            if (piece.PieceType == PieceType.None) continue;

            int index = GetBitboardIndex(piece);
            bitboards[index] |= (1UL << i);
        }

        whitePawns = bitboards[0];
        whiteKnights = bitboards[1];
        whiteBishops = bitboards[2];
        whiteRooks = bitboards[3];
        whiteQueens = bitboards[4];
        whiteKings = bitboards[5];
        blackPawns = bitboards[6];
        blackKnights = bitboards[7];
        blackBishops = bitboards[8];
        blackRooks = bitboards[9];
        blackQueens = bitboards[10];
        blackKings = bitboards[11];
    }

    private int GetBitboardIndex(Piece piece)
    {
        return piece.IsWhite
            ? piece.PieceType switch
            {
                PieceType.Pawn => 0,
                PieceType.Knight => 1,
                PieceType.Bishop => 2,
                PieceType.Rook => 3,
                PieceType.Queen => 4,
                PieceType.King => 5,
                _ => throw new ArgumentException("Invalid piece type")
            }
            : piece.PieceType switch
            {
                PieceType.Pawn => 6,
                PieceType.Knight => 7,
                PieceType.Bishop => 8,
                PieceType.Rook => 9,
                PieceType.Queen => 10,
                PieceType.King => 11,
                _ => throw new ArgumentException("Invalid piece type")
            };
    }
    private int EvaluatePieceSquareTables(ulong bitboard, int[] table, bool isWhite)
    {
        int score = 0;
        while (bitboard != 0)
        {
            int square = BitOperations.TrailingZeroCount(bitboard);
            score += isWhite ? table[square] : table[63 - square];
            bitboard &= bitboard - 1; // Clear the least significant bit
        }
        return score;
    }

    // Piece-square tables
    private static readonly int[] PawnTable = {
    0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
    5,  5, 10, 25, 25, 10,  5,  5,
    0,  0,  0, 20, 20,  0,  0,  0,
    5, -5,-10,  0,  0,-10, -5,  5,
    5, 10, 10,-20,-20, 10, 10,  5,
    0,  0,  0,  0,  0,  0,  0,  0
};

    private static readonly int[] KnightTable = {
    -50,-40,-30,-30,-30,-30,-40,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 10, 15, 15, 10,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 10, 15, 15, 10,  5,-30,
    -40,-20,  0,  5,  5,  0,-20,-40,
    -50,-40,-30,-30,-30,-30,-40,-50
};

    private static readonly int[] BishopTable = {
    -20,-10,-10,-10,-10,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5, 10, 10,  5,  0,-10,
    -10,  5,  5, 10, 10,  5,  5,-10,
    -10,  0, 10, 10, 10, 10,  0,-10,
    -10, 10, 10, 10, 10, 10, 10,-10,
    -10,  5,  0,  0,  0,  0,  5,-10,
    -20,-10,-10,-10,-10,-10,-10,-20
};

    private static readonly int[] RookTable = {
    0,  0,  0,  0,  0,  0,  0,  0,
    5, 10, 10, 10, 10, 10, 10,  5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    0,  0,  0,  5,  5,  0,  0,  0
};

    private static readonly int[] QueenTable = {
    -20,-10,-10, -5, -5,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5,  5,  5,  5,  0,-10,
    -5,  0,  5,  5,  5,  5,  0, -5,
    0,  0,  5,  5,  5,  5,  0, -5,
    -10,  5,  5,  5,  5,  5,  0,-10,
    -10,  0,  5,  0,  0,  0,  0,-10,
    -20,-10,-10, -5, -5,-10,-10,-20
};

    private static readonly int[] KingMiddleGameTable = {
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -20,-30,-30,-40,-40,-30,-30,-20,
    -10,-20,-20,-20,-20,-20,-20,-10,
    20, 20,  0,  0,  0,  0, 20, 20,
    20, 30, 10,  0,  0, 10, 30, 20
};
    int Evaluate(Board board, int depth)
    {
        if (board.IsInCheckmate())
        {
            return board.IsWhiteToMove ? -1000000 - depth : 1000000 + depth;
        }

        if (board.IsDraw())
        {
            return 0;
        }

        int material = 0;
        int positional = 0;

        material += CountBits(whitePawns) * 100;
        material += CountBits(whiteKnights) * 320;
        material += CountBits(whiteBishops) * 330;
        material += CountBits(whiteRooks) * 500;
        material += CountBits(whiteQueens) * 900;
        material -= CountBits(blackPawns) * 100;
        material -= CountBits(blackKnights) * 320;
        material -= CountBits(blackBishops) * 330;
        material -= CountBits(blackRooks) * 500;
        material -= CountBits(blackQueens) * 900;

        // Positional evaluation using piece-square tables
        positional += EvaluatePieceSquareTables(whitePawns, PawnTable, true);
        positional += EvaluatePieceSquareTables(whiteKnights, KnightTable, true);
        positional += EvaluatePieceSquareTables(whiteBishops, BishopTable, true);
        positional += EvaluatePieceSquareTables(whiteRooks, RookTable, true);
        positional += EvaluatePieceSquareTables(whiteQueens, QueenTable, true);
        positional += EvaluatePieceSquareTables(whiteKings, KingMiddleGameTable, true);

        positional -= EvaluatePieceSquareTables(blackPawns, PawnTable, false);
        positional -= EvaluatePieceSquareTables(blackKnights, KnightTable, false);
        positional -= EvaluatePieceSquareTables(blackBishops, BishopTable, false);
        positional -= EvaluatePieceSquareTables(blackRooks, RookTable, false);
        positional -= EvaluatePieceSquareTables(blackQueens, QueenTable, false);
        positional -= EvaluatePieceSquareTables(blackKings, KingMiddleGameTable, false);

        if (board.IsInCheck())
        {
            material += board.IsWhiteToMove ? -5 : 5;
        }

        return material + positional;
    }

    private int CountBits(ulong bitboard)
    {
        return (int)BitOperations.PopCount(bitboard);
    }

    private int CountPositionalBonus(ulong bitboard, int minRank, int maxRank)
    {
        int bonus = 0;
        for (int i = 0; i < 64; i++)
        {
            if ((bitboard & (1UL << i)) != 0)
            {
                int rank = i / 8 + 1;
                if (rank >= minRank && rank <= maxRank)
                    bonus += 2; // Positional bonus for center control
            }
        }
        return bonus;
    }

    private int EvaluateEndgame(Board board)
    {
        int whiteMaterial = CountMaterial(board, true);
        int blackMaterial = CountMaterial(board, false);

        int endgameScore = 0;

        if (whiteMaterial < 1800 || blackMaterial < 1800) // Arbitrary endgame threshold
        {
            endgameScore += CountEndgameKingSafety(whiteKings, true) - CountEndgameKingSafety(blackKings, false);
            endgameScore += CountEndgamePawnStructure(whitePawns, true) - CountEndgamePawnStructure(blackPawns, false);
        }

        return endgameScore;
    }

    private int CountMaterial(Board board, bool isWhite)
    {
        int material = 0;
        ulong[] pieces = isWhite ? new[] { whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings } :
                                    new[] { blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings };

        material += CountBits(pieces[0]) * 10;  // Pawns
        material += CountBits(pieces[1]) * 30;  // Knights
        material += CountBits(pieces[2]) * 35;  // Bishops
        material += CountBits(pieces[3]) * 55;  // Rooks
        material += CountBits(pieces[4]) * 100; // Queens
        material += CountBits(pieces[5]) * 900; // Kings

        return material;
    }

    private int CountEndgameKingSafety(ulong kingBitboard, bool isWhite)
    {
        int safety = 0;

        // Check if the king is near the center or near the edges
        ulong centralSquares = 0x0000001818000000UL; // Central 4 squares
        if ((kingBitboard & centralSquares) != 0)
        {
            safety += isWhite ? 10 : -10;
        }
        else
        {
            safety += isWhite ? -10 : 10;
        }

        return safety;
    }

    private int CountEndgamePawnStructure(ulong pawnsBitboard, bool isWhite)
    {
        int structureScore = 0;

        // Penalty for isolated or doubled pawns
        ulong isolatedPawnsMask = 0x0001010101010101UL; // File masks for isolated pawns
        for (int i = 0; i < 8; i++)
        {
            ulong filePawns = pawnsBitboard & (isolatedPawnsMask << i);
            if (CountBits(filePawns) > 1) // Doubled pawns
            {
                structureScore -= isWhite ? 5 : -5;
            }
            else if (filePawns == 0) // Isolated pawns
            {
                structureScore -= isWhite ? 5 : -5;
            }
        }

        return structureScore;
    }

    int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing, bool isRoot)
    {
        if (depth == 0 || board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        int bestEvaluation;
        Move? bestMove = null;
        List<Move> moves = new List<Move>(board.GetLegalMoves());

        // Order moves based on previous success and captures
        moves.Sort((m1, m2) =>
        {
            int score1 = history.ContainsKey(m1) ? history[m1] : 0;
            int score2 = history.ContainsKey(m2) ? history[m2] : 0;

            // Prioritize killer moves
            if (killerMoves.ContainsKey(m1))
                score1 += 5000;
            if (killerMoves.ContainsKey(m2))
                score2 += 5000;

            // Return captures first
            if (m1.IsCapture && !m2.IsCapture)
                return -1;
            if (m2.IsCapture && !m1.IsCapture)
                return 1;

            return score2.CompareTo(score1);
        });

        if (isMaximizing)
        {
            bestEvaluation = int.MinValue;

            foreach (Move move in moves)
            {
                board.MakeMove(move);
                InitializeBitboards(board);
                int evaluation = Minimax(board, depth - 1, alpha, beta, false, false);
                board.UndoMove(move);
                InitializeBitboards(board);

                if (evaluation > bestEvaluation)
                {
                    bestEvaluation = evaluation;
                    bestMove = move;
                }

                alpha = Math.Max(alpha, evaluation);
                if (beta <= alpha)
                    break;
            }
        }
        else
        {
            bestEvaluation = int.MaxValue;

            foreach (Move move in moves)
            {
                board.MakeMove(move);
                InitializeBitboards(board);
                int evaluation = Minimax(board, depth - 1, alpha, beta, true, false);
                board.UndoMove(move);
                InitializeBitboards(board);

                if (evaluation < bestEvaluation)
                {
                    bestEvaluation = evaluation;
                    bestMove = move;
                }

                beta = Math.Min(beta, evaluation);
                if (beta <= alpha)
                    break;
            }
        }

        if (isRoot && bestMove.HasValue)
            chosenMove = bestMove.Value;

        // Update history and killer moves
        if (bestMove.HasValue)
        {
            Move move = bestMove.Value;
            if (history.ContainsKey(move))
                history[move]++;
            else
                history[move] = 1;

            if (isRoot)
                killerMoves[move] = 1; // Assign a value to killer move
        }

        return bestEvaluation;
    }
}