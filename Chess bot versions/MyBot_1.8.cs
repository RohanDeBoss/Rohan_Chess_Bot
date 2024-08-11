using ChessChallenge.API;
using System.Collections.Generic;
using System.Numerics;
using System;
using System.Diagnostics;
using System.Net.NetworkInformation;

public class MyBot : IChessBot
{
    private const int SEARCH_DEPTH = 6;
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
    private static readonly int[] KingEndgameTable = {
    -50,-40,-30,-20,-20,-30,-40,-50,
    -40,-20,-10,  0,  0,-10,-20,-40,
    -30,  0, 10, 20, 20, 10,  0,-30,
    -20, 10, 20, 30, 30, 20, 10,-20,
    -20,  5, 10, 20, 20, 10,  5,-20,
    -30,-10,  0,  5,  5,  0,-10,-30,
    -40,-20,-10, -5, -5,-10,-20,-40,
    -50,-40,-30,-20,-20,-30,-40,-50
};

    private int EvaluatePassedPawns(Board board, bool isWhite)
    {
        int score = 0;
        ulong[] pawnBitboards = isWhite
            ? new[] { whitePawns }
            : new[] { blackPawns };

        foreach (ulong pawnBitboard in pawnBitboards)
        {
            // Check each pawn on the board
            ulong bitboard = pawnBitboard;
            while (bitboard != 0)
            {
                int square = BitOperations.TrailingZeroCount(bitboard);
                int file = square % 8;
                int rank = square / 8;

                bool isPassedPawn = true;
                // Check if the pawn is passed (i.e., no opponent pawns blocking it)
                for (int i = Math.Max(0, file - 1); i <= Math.Min(7, file + 1); i++)
                {
                    for (int j = rank + 1; j <= 7; j++)
                    {
                        if (isWhite)
                        {
                            if ((blackPawns & (1UL << (i + j * 8))) != 0)
                            {
                                isPassedPawn = false;
                                break;
                            }
                        }
                        else
                        {
                            if ((whitePawns & (1UL << (i + j * 8))) != 0)
                            {
                                isPassedPawn = false;
                                break;
                            }
                        }
                    }
                    if (!isPassedPawn) break;
                }

                if (isPassedPawn)
                {
                    // Reward passed pawns based on their rank
                    score += (rank - (isWhite ? 0 : 7)) * 9; // Pawns closer to promotion get a higher reward
                }

                bitboard &= bitboard - 1; // Move to the next pawn
            }
        }
        return score;
    }

    private int Evaluate(Board board, int depth)
    {
        if (board.IsInCheckmate()) return board.IsWhiteToMove ? -1000000 - depth : 1000000 + depth;
        if (board.IsDraw()) return 0;

        int material = 0;
        int positional = 0;

        // Material evaluation
        material += CountBits(bitboards[0]) * 100 - CountBits(bitboards[6]) * 100;
        material += CountBits(bitboards[1]) * 320 - CountBits(bitboards[7]) * 320;
        material += CountBits(bitboards[2]) * 330 - CountBits(bitboards[8]) * 330;
        material += CountBits(bitboards[3]) * 500 - CountBits(bitboards[9]) * 500;
        material += CountBits(bitboards[4]) * 900 - CountBits(bitboards[10]) * 900;

        // Positional evaluation
        positional += EvaluatePieceSquareTables(bitboards[0], PawnTable, true) - EvaluatePieceSquareTables(bitboards[6], PawnTable, false);
        positional += EvaluatePieceSquareTables(bitboards[1], KnightTable, true) - EvaluatePieceSquareTables(bitboards[7], KnightTable, false);
        positional += EvaluatePieceSquareTables(bitboards[2], BishopTable, true) - EvaluatePieceSquareTables(bitboards[8], BishopTable, false);
        positional += EvaluatePieceSquareTables(bitboards[3], RookTable, true) - EvaluatePieceSquareTables(bitboards[9], RookTable, false);
        positional += EvaluatePieceSquareTables(bitboards[4], QueenTable, true) - EvaluatePieceSquareTables(bitboards[10], QueenTable, false);
        positional += EvaluatePieceSquareTables(bitboards[5], KingMiddleGameTable, true) - EvaluatePieceSquareTables(bitboards[11], KingMiddleGameTable, false);

        positional += CountEndgameKingSafety(whiteKings, true) - CountEndgameKingSafety(blackKings, false);

        positional += EvaluateCastling(board);

        if (board.IsInCheck())
        {
            material += board.IsWhiteToMove ? -15 : 15;
        }

        positional += EvaluateKingEdge(board, true);
        positional -= EvaluateKingEdge(board, false);

        // Add king distance influence
        int kingDistance = CalculateKingDistance(board);
        positional += board.IsWhiteToMove ? -kingDistance : kingDistance;


        return material + positional;
    }
    private int EvaluateCastling(Board board)
    {
        int castlingBonus = 0;

        // White castling
        if (board.HasKingsideCastleRight(true))
        {
            castlingBonus += 25; // Encourage kingside castling
        }

        if (board.HasQueensideCastleRight(true))
        {
            castlingBonus += 20; // Encourage queenside castling
        }

        // Black castling
        if (board.HasKingsideCastleRight(false))
        {
            castlingBonus -= 25; // Encourage kingside castling
        }

        if (board.HasQueensideCastleRight(false))
        {
            castlingBonus -= 20; // Encourage queenside castling
        }

        return castlingBonus;
    }
    private int EvaluateKingEdge(Board board, bool isWhite)
    {
        ulong kingBitboard = isWhite ? whiteKings : blackKings;
        int kingPosition = GetKingPosition(kingBitboard);
        int row = kingPosition / 8;
        int col = kingPosition % 8;

        // Check if the king is on the edge of the board
        bool isOnEdge = row == 0 || row == 7 || col == 0 || col == 7;

        return isOnEdge ? (isWhite ? -20 : 20) : 0; // Adjust the value based on your preference
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
        int totalMaterial = whiteMaterial + blackMaterial;
        int materialDifference = whiteMaterial - blackMaterial;

        // Apply full endgame evaluation as soon as either player has less than 1800 material
        if (whiteMaterial < 2000 || blackMaterial < 2000)
        {
            int endgameScore = 0;

            // King safety and pawn structure evaluation
            endgameScore += CountEndgameKingSafety(whiteKings, true) - CountEndgameKingSafety(blackKings, false);
            endgameScore += CountEndgamePawnStructure(whitePawns, true) - CountEndgamePawnStructure(blackPawns, false);

            // King proximity evaluation, considering the material difference
            endgameScore += EvaluateKingProximity(board, totalMaterial, materialDifference);

            return endgameScore;
        }

        return 0; // No endgame evaluation applied if material is above the threshold
    }

    private int EvaluateKingProximity(Board board, int totalMaterial, int materialDifference)
    {
        // Get positions of the kings
        int whiteKingPosition = GetKingPosition(whiteKings);
        int blackKingPosition = GetKingPosition(blackKings);

        // Convert positions to row and column
        int whiteKingRow = whiteKingPosition / 8;
        int whiteKingCol = whiteKingPosition % 8;
        int blackKingRow = blackKingPosition / 8;
        int blackKingCol = blackKingPosition % 8;

        // Debug output for king positions
        Debug.WriteLine($"White King Position: {whiteKingPosition} (Row: {whiteKingRow}, Col: {whiteKingCol})");
        Debug.WriteLine($"Black King Position: {blackKingPosition} (Row: {blackKingRow}, Col: {blackKingCol})");

        // Calculate Manhattan distance between the kings
        int distance = Math.Abs(whiteKingRow - blackKingRow) + Math.Abs(whiteKingCol - blackKingCol);

        // Encourage king proximity without scaling factor
        int proximityScore = -1000 * distance; // Adjust the multiplier as needed

        return proximityScore;
    }
    private int CalculateKingDistance(Board board)
    {
        int whiteKingPosition = GetKingPosition(whiteKings);
        int blackKingPosition = GetKingPosition(blackKings);

        // Convert positions to row and column
        int whiteKingRow = whiteKingPosition / 8;
        int whiteKingCol = whiteKingPosition % 8;
        int blackKingRow = blackKingPosition / 8;
        int blackKingCol = blackKingPosition % 8;

        // Calculate Manhattan distance between the kings
        return Math.Abs(whiteKingRow - blackKingRow) + Math.Abs(whiteKingCol - blackKingCol);
    }



    private int GetKingPosition(ulong kingBitboard)
    {
        // Find the position of the king on the board
        return BitOperations.TrailingZeroCount(kingBitboard); // Assumes only one king per bitboard
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
        material += CountBits(pieces[5]) * 200;

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