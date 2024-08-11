using ChessChallenge.API;
using Raylib_cs;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Numerics;

//v1.5.1
public class EvilBot : IChessBot
{
    private const int SEARCH_DEPTH = 3;
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
    10, 10, 10, 10, 10, 10, 10, 10,
    5,  5, 10, 20, 20, 10,  5,  5,
    0,  0,  0, 15, 15,  0,  0,  0,
    0,  0,  0, 10, 10,  0,  0,  0,
    5, -5,-10,  0,  0,-10, -5,  5,
    5, 10, 10,-20,-20, 10, 10,  5,
    0,  0,  0,  0,  0,  0,  0,  0
};

    private static readonly int[] KnightTable = {
    -50,-40,-30,-30,-30,-30,-40,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 15, 15, 15, 15,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 15, 15, 15, 15,  5,-30,
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
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  0,  0,  0,  0,  0,  0
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
            return -50;
        }

        int material = 0;
        int positional = 0;

        material += CountBits(whitePawns) * 100;
        material += CountBits(whiteKnights) * 315;
        material += CountBits(whiteBishops) * 330;
        material += CountBits(whiteRooks) * 500;
        material += CountBits(whiteQueens) * 900;
        material -= CountBits(blackPawns) * 100;
        material -= CountBits(blackKnights) * 315;
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
        positional += CountPositionalBonus(whiteKings, 1, 1); // Bonus for king on 1st rank for White

        positional -= EvaluatePieceSquareTables(blackPawns, PawnTable, false);
        positional -= EvaluatePieceSquareTables(blackKnights, KnightTable, false);
        positional -= EvaluatePieceSquareTables(blackBishops, BishopTable, false);
        positional -= EvaluatePieceSquareTables(blackRooks, RookTable, false);
        positional -= EvaluatePieceSquareTables(blackQueens, QueenTable, false);
        positional -= EvaluatePieceSquareTables(blackKings, KingMiddleGameTable, false);
        positional -= CountPositionalBonus(blackKings, 8, 8); // Bonus for king on 8th rank for Black

        if (board.IsInCheck())
        {
            material += board.IsWhiteToMove ? -15 : 15;
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
                    bonus += 2; // Positional bonus for the king
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

        material += CountBits(pieces[0]) * 100;  // Pawns
        material += CountBits(pieces[1]) * 320;  // Knights
        material += CountBits(pieces[2]) * 330;  // Bishops
        material += CountBits(pieces[3]) * 500;  // Rooks
        material += CountBits(pieces[4]) * 900;  // Queens

        return material;
    }

    private struct TTEntry
    {
        public ulong ZobristKey;
        public int Depth;
        public int Score;
        public Move BestMove;
        public byte Flag; // 0 = exact, 1 = lower bound, 2 = upper bound
    }
    private const int TT_SIZE = 1 << 24; // 16 million entries
    private TTEntry[] transpositionTable = new TTEntry[TT_SIZE];
    private ulong[,] zobristTable = new ulong[12, 64];
    private ulong sideToMove;

    private void InitializeZobristTable()
    {
        Random rand = new Random(1234); // Use a fixed seed for reproducibility
        for (int piece = 0; piece < 12; piece++)
        {
            for (int square = 0; square < 64; square++)
            {
                zobristTable[piece, square] = (ulong)rand.NextInt64();
            }
        }
        sideToMove = (ulong)rand.NextInt64();
    }

    private ulong ComputeZobristKey(Board board)
    {
        ulong key = 0;
        for (int square = 0; square < 64; square++)
        {
            Piece piece = board.GetPiece(new Square(square));
            if (piece.PieceType != PieceType.None)
            {
                int pieceIndex = GetBitboardIndex(piece);
                key ^= zobristTable[pieceIndex, square];
            }
        }
        if (board.IsWhiteToMove)
            key ^= sideToMove;
        return key;
    }
    private int CountEndgameKingSafety(ulong kingBitboard, bool isWhite)
    {
        int safety = 0;

        // Define masks for central and edge squares
        ulong centralSquares = 0x0000001818000000UL; // Central 4 squares
        ulong edgeSquares = 0x00FF000000FF00FFUL;    // Edge squares

        // Check if the king is on the central squares
        if ((kingBitboard & centralSquares) != 0)
        {
            safety += isWhite ? 10 : -10;
        }

        // Check if the king is on the edge squares
        if ((kingBitboard & edgeSquares) != 0)
        {
            safety += isWhite ? -20 : 20;
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
                structureScore -= isWhite ? 15 : -15;
            }
            else if (filePawns == 0) // Isolated pawns
            {
                structureScore -= isWhite ? 15 : -15;
            }
        }

        return structureScore;
    }
    private int GetMVVLVAScore(Move move, Board board)
    {
        if (!move.IsCapture) return 0;

        int victimValue = GetPieceValue(board.GetPiece(move.TargetSquare).PieceType);
        int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);

        return victimValue * 10 - attackerValue;
    }

    private int GetPieceValue(PieceType pieceType)
    {
        return pieceType switch
        {
            PieceType.Pawn => 1,
            PieceType.Knight => 3,
            PieceType.Bishop => 3,
            PieceType.Rook => 5,
            PieceType.Queen => 9,
            PieceType.King => 1000,
            _ => 0
        };
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

            // MVV-LVA scoring for captures
            score1 += GetMVVLVAScore(m1, board);
            score2 += GetMVVLVAScore(m2, board);

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