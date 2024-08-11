using ChessChallenge.API;
using System.Collections.Generic;
using System.Numerics;
using System;
using System.Linq;

public class MyBot : IChessBot
{
    private const int SEARCH_DEPTH = 4;
    private Move? chosenMove;
    private Dictionary<Move, int> killerMoves = new Dictionary<Move, int>();
    private Dictionary<Move, int> history = new Dictionary<Move, int>();

    private ulong whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings;
    private ulong blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings;

    private ulong[] bitboards = new ulong[12];

    private Move[] principalVariation;

    public MyBot()
    {
        principalVariation = new Move[SEARCH_DEPTH + 1];
    }

    public Move Think(Board board, Timer timer)
    {
        InitializeBitboards(board);
        chosenMove = null;
        Minimax(board, SEARCH_DEPTH, int.MinValue, int.MaxValue, board.IsWhiteToMove, true);
        return chosenMove ?? new Move();
    }

    // Initialize the bitboards
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
            bitboard &= bitboard - 1;
        }
        return score;
    }

    // Piece-square tables
    private static readonly int[] PawnTable = {
    0,  0,  0,  0,  0,  0,  0,  0,
    10, 10, 15, 30, 30, 15, 10, 10,
    5,  5, 10, 20, 20, 10,  5,  5,
    0,  0,  0, 15, 15,  0,  0,  0,
    0,  0,  10, 20, 20,  0,  0,  0,
    5, -5,-10, 10, 10,-10, -5,  5,
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

    private int Evaluate(Board board, int depth)
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
        material += CountBits(whiteKnights) * 320;
        material += CountBits(whiteBishops) * 330;
        material += CountBits(whiteRooks) * 500;
        material += CountBits(whiteQueens) * 910;
        material -= CountBits(blackPawns) * 100;
        material -= CountBits(blackKnights) * 320;
        material -= CountBits(blackBishops) * 330;
        material -= CountBits(blackRooks) * 500;
        material -= CountBits(blackQueens) * 910;

        positional += EvaluatePieceSquareTables(whitePawns, PawnTable, true);
        positional += EvaluatePieceSquareTables(whiteKnights, KnightTable, true);
        positional += EvaluatePieceSquareTables(whiteBishops, BishopTable, true);
        positional += EvaluatePieceSquareTables(whiteRooks, RookTable, true);
        positional += EvaluatePieceSquareTables(whiteQueens, QueenTable, true);
        positional += EvaluatePieceSquareTables(whiteKings, KingMiddleGameTable, true);
        positional += CountPositionalBonus(whiteKings, 1, 1);

        positional -= EvaluatePieceSquareTables(blackPawns, PawnTable, false);
        positional -= EvaluatePieceSquareTables(blackKnights, KnightTable, false);
        positional -= EvaluatePieceSquareTables(blackBishops, BishopTable, false);
        positional -= EvaluatePieceSquareTables(blackRooks, RookTable, false);
        positional -= EvaluatePieceSquareTables(blackQueens, QueenTable, false);
        positional -= EvaluatePieceSquareTables(blackKings, KingMiddleGameTable, false);
        positional -= CountPositionalBonus(blackKings, 8, 8);

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
                    bonus += 2;
            }
        }
        return bonus;
    }

    private int EvaluateEndgame(Board board)
    {
        int whiteMaterial = CountMaterial(board, true);
        int blackMaterial = CountMaterial(board, false);

        int endgameScore = 0;

        if (whiteMaterial < 1800 || blackMaterial < 1800)
        {
            endgameScore += CountEndgameKingSafety(whiteKings, true) - CountEndgameKingSafety(blackKings, false);
            endgameScore += CountEndgamePawnStructure(whitePawns, true) - CountEndgamePawnStructure(blackPawns, false);

            // Add king proximity evaluation
            endgameScore += EvaluateKingProximity(board, whiteMaterial + blackMaterial);
        }

        return endgameScore;
    }

    private int EvaluateKingProximity(Board board, int totalMaterial)
    {
        // Return a default score if total material is 1700 or more
        if (totalMaterial >= 1700)
        {
            return 0; // or any other default score
        }

        // Get bitboards for white and black kings
        ulong whiteKingBitboard = board.GetPieceBitboard(PieceType.King, true); // Replace with your actual method
        ulong blackKingBitboard = board.GetPieceBitboard(PieceType.King, false); // Replace with your actual method


        // Get positions of the kings
        ulong whiteKingPosition = GetKingPosition(whiteKingBitboard);
        ulong blackKingPosition = GetKingPosition(blackKingBitboard);

        // Convert positions to row and column
        int whiteKingRow = (int)(whiteKingPosition / 8);
        int whiteKingCol = (int)(whiteKingPosition % 8);
        int blackKingRow = (int)(blackKingPosition / 8);
        int blackKingCol = (int)(blackKingPosition % 8);

        // Calculate Manhattan distance
        int distance = Math.Abs(whiteKingRow - blackKingRow) + Math.Abs(whiteKingCol - blackKingCol);

        // Calculate a scaling factor based on the total material
        int scalingFactor = 5000 / Math.Max(totalMaterial / 100, 1); // Ensure divisor is at least 1

        // Reward closer proximity with increased bonus as pieces decrease
        int proximityScore = -scalingFactor * distance; // Adjust the multiplier as needed

        return proximityScore;
    }

    // Method to get the position of the king from its bitboard
    private ulong GetKingPosition(ulong kingBitboard)
    {
        // Find the position of the king (assuming only one king per bitboard)
        ulong position = 0;
        for (int i = 0; i < 64; i++)
        {
            if ((kingBitboard & (1UL << i)) != 0)
            {
                position = 1UL << i;
                break; // Assuming only one king, so break after finding it
            }
        }
        return position;
    }



    private int CountMaterial(Board board, bool isWhite)
    {
        int material = 0;
        ulong[] pieces = isWhite ? new[] { whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings } :
                                    new[] { blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings };

        material += CountBits(pieces[0]) * 100;
        material += CountBits(pieces[1]) * 320;
        material += CountBits(pieces[2]) * 330;
        material += CountBits(pieces[3]) * 500;
        material += CountBits(pieces[4]) * 900;
        material += CountBits(pieces[5]) * 1000;

        return material;
    }

    private int CountEndgameKingAggression(ulong kingBitboard, bool isWhite)
    {
        int aggression = 0;

        // Define bitboards for central squares and edge squares
        ulong centralSquares = 0x0000001818000000UL;
        ulong edgeSquares = 0x00FF000000FF00FFUL;

        // Reward king for being in central squares (more active)
        if ((kingBitboard & centralSquares) != 0)
        {
            aggression += isWhite ? 20 : -20;
        }

        // Penalize king for being on the edges (less active)
        if ((kingBitboard & edgeSquares) != 0)
        {
            aggression += isWhite ? -15 : 15;
        }

        // Reward king for being closer to the center (more aggressive positioning)
        ulong kingPosition = kingBitboard;
        int squareIndex = BitOperations.TrailingZeroCount(kingPosition);
        int row = squareIndex / 8;
        int col = squareIndex % 8;

        int centerDistance = Math.Max(Math.Abs(row - 3), Math.Abs(col - 3)); // Calculate distance from center (3,3)

        aggression -= 5 * centerDistance; // Penalize distance from center

        return aggression;
    }
    private int CountEndgameKingSafety(ulong kingBitboard, bool isWhite)
    {
        int safetyScore = 0;

        // Define a bitboard for squares around the king
        ulong kingSafetyZone = 0x000007E0000000E0UL; // Adjust if needed for different board representations

        // Check if the king is in a safe zone
        if ((kingBitboard & kingSafetyZone) != 0)
        {
            safetyScore += isWhite ? 10 : -10;
        }

        // Penalize if the king is on the edge or corner (less safe)
        ulong edgeAndCornerSquares = 0x00FF000000FF00FFUL; // Edge and corner squares
        if ((kingBitboard & edgeAndCornerSquares) != 0)
        {
            safetyScore += isWhite ? -20 : 20;
        }

        // Add more safety evaluations as needed

        return safetyScore;
    }


    private int CountEndgamePawnStructure(ulong pawnsBitboard, bool isWhite)
    {
        int pawnStructure = 0;
        int[] pawnFileCounts = new int[8];

        while (pawnsBitboard != 0)
        {
            int square = BitOperations.TrailingZeroCount(pawnsBitboard);
            pawnFileCounts[square % 8]++;
            pawnsBitboard &= pawnsBitboard - 1;
        }

        foreach (int count in pawnFileCounts)
        {
            if (count > 1)
            {
                pawnStructure += isWhite ? 10 : -10;
            }
        }

        return pawnStructure;
    }

    private int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing, bool isRoot)
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

            if (killerMoves.ContainsKey(m1))
                score1 += 5000;
            if (killerMoves.ContainsKey(m2))
                score2 += 5000;

            if (m1.IsCapture && !m2.IsCapture)
                return -1;
            if (m2.IsCapture && !m1.IsCapture)
                return 1;

            return score2.CompareTo(score1);
        });

        bool isInCheck = board.IsInCheck();
        if (isMaximizing)
        {
            bestEvaluation = int.MinValue;

            foreach (Move move in moves)
            {
                board.MakeMove(move);
                InitializeBitboards(board);

                // Search the move
                int evaluation = Minimax(board, depth - 1, alpha, beta, false, false);

                // If in check, search an extra move
                if (isInCheck)
                {
                    evaluation = Math.Max(evaluation, Minimax(board, depth - 1, alpha, beta, false, false));
                }

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

                // Search the move
                int evaluation = Minimax(board, depth - 1, alpha, beta, true, false);

                // If in check, search an extra move
                if (isInCheck)
                {
                    evaluation = Math.Min(evaluation, Minimax(board, depth - 1, alpha, beta, true, false));
                }

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

        // Update principal variation list
        if (bestMove.HasValue && depth < principalVariation.Length)
        {
            principalVariation[depth] = bestMove.Value; // Unwrap the nullable Move
        }

        return bestEvaluation;
    }
}