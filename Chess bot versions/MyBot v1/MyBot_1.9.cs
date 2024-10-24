using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Data;
using System.Numerics;

//v1.9 (Time management + cleanup)
//I need to fix the mate in thing.
public class MyBot : IChessBot
{
    public int bestEvaluation { get; private set; }

    private int defultSearch = 5; //recomended 5
    public int searchDepth;
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

        // Adjust search depth based on time remaining
        if (defultSearch > 4)
        {
            if (timer.MillisecondsRemaining <= 800)
            {
                searchDepth = 1;
            }
            else if (timer.MillisecondsRemaining <= 4000)
            {
                searchDepth = 2;
            }
            else if (timer.MillisecondsRemaining <= 14000)
            {
                searchDepth = defultSearch - 2;
            }
            else if (timer.MillisecondsRemaining <= 35000)
            {
                searchDepth = defultSearch - 1;
            }
            else if (timer.MillisecondsRemaining >= 58000)
            {
                searchDepth = defultSearch - 1; //first few moves done quickly
            }
            else
            {
                searchDepth = defultSearch;
            }
        }
        else
        {
            if (timer.MillisecondsRemaining >= 55000)
            {
                searchDepth = defultSearch + 1;
            }
            else
            {
                searchDepth = defultSearch;
            }
        }
        Minimax(board, searchDepth, int.MinValue, int.MaxValue, board.IsWhiteToMove, true);


        // Evaluation debugging - Uncomment the next line to see evaluation
        EvaluationDebugger debugger = new(this);
        debugger.PrintEvaluation(board); // This will output the evaluation
        debugger.PrintDepth(board); // Same for depth


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
    -50,-45,-30,-30,-30,-30,-45,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 15, 15, 15, 15,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 15, 15, 15, 15,  5,-30,
    -40,-20,  0,  5,  5,  0,-20,-40,
    -50,-45,-30,-30,-30,-30,-45,-50
};

    private static readonly int[] BishopTable = {
    -20,-10,-15,-10,-10,-15,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5, 10, 10,  5,  0,-10,
    -10,  5,  5, 10, 10,  5,  5,-10,
    -10,  0, 10, 10, 10, 10,  0,-10,
    -10, 10, 10, 10, 10, 10, 10,-10,
    -10,  5,  0,  0,  0,  0,  5,-10,
    -20,-10,-15,-10,-10,-15,-10,-20
};

    private static readonly int[] RookTable = {
    -1, 0,  5, 9,  9,   5,  0, -1,
    5,  10, 10, 15, 15, 10, 10, 5,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  0,  5, 10, 10,  5,  0,  0,
    0,  5,  5, 10, 10,  5,  5,  0,
    -10, 0,  0,  0,  0,  0,  0, -10
};

    private static readonly int[] QueenTable = {
    -20,-10,-10, -5, -5,-10,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5,  5,  5,  5,  0,-10,
    -5,   0,  5,  5,  5,  5,  0, -5,
     0,   0,  5,  5,  5,  5,  0, -5,
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
    20, 30,  0,  0,  0,  0, 30, 20
};
    private static readonly int[] KingEndGameTable = {
     0,  5,  5,  5,  5,  5,  5,  0,
     0, 10, 10, 10, 10, 10, 10,  0,
     0, 10, 20, 20, 20, 20, 10,  0,
     0, 10, 20, 19, 19, 20, 10,  0,
     0, 10, 20, 19, 19, 20, 10,  0,
     5, 10, 20, 20, 20, 20, 10,  5,
     5, 10, 10, 10, 10, 10, 10,  5,
     0,  5,  5,  5,  5,  5,  5,  0
    };

    public int Evaluate(Board board, int depth)
    {
        // Checkmate and draw evaluations
        if (board.IsInCheckmate())
        {
            return board.IsWhiteToMove ? -1000000 - depth : 1000000 + depth;
        }
        if (board.IsDraw())
        {
            return -40; // Negative score for draw
        }

        int material = 0;
        int positional = 0;

        // Material evaluation
        material += CountBits(whitePawns) * 100;
        material += CountBits(whiteKnights) * 305;
        material += CountBits(whiteBishops) * 320;
        material += CountBits(whiteRooks) * 500;
        material += CountBits(whiteQueens) * 900;
        material -= CountBits(blackPawns) * 100;
        material -= CountBits(blackKnights) * 305;
        material -= CountBits(blackBishops) * 320;
        material -= CountBits(blackRooks) * 500;
        material -= CountBits(blackQueens) * 900;

        // Positional evaluation using piece-square tables
        positional += EvaluatePieceSquareTables(whitePawns, PawnTable, true);
        positional += EvaluatePieceSquareTables(whiteKnights, KnightTable, true);
        positional += EvaluatePieceSquareTables(whiteBishops, BishopTable, true);
        positional += EvaluatePieceSquareTables(whiteRooks, RookTable, true);
        positional += EvaluatePieceSquareTables(whiteQueens, QueenTable, true);
        positional -= EvaluatePieceSquareTables(blackPawns, PawnTable, false);
        positional -= EvaluatePieceSquareTables(blackKnights, KnightTable, false);
        positional -= EvaluatePieceSquareTables(blackBishops, BishopTable, false);
        positional -= EvaluatePieceSquareTables(blackRooks, RookTable, false);
        positional -= EvaluatePieceSquareTables(blackQueens, QueenTable, false);

        // King evaluation based on game phase
        int whiteMaterial = CountMaterial(board, true);
        int blackMaterial = CountMaterial(board, false);


        if (whiteMaterial < 1750 || blackMaterial < 1750) // Endgame
        {
            positional += EvaluatePieceSquareTables(whiteKings, KingEndGameTable, true);
            positional -= EvaluatePieceSquareTables(blackKings, KingEndGameTable, false);
        }
        else // Middle game
        {
            positional += EvaluatePieceSquareTables(whiteKings, KingMiddleGameTable, true);
            positional -= EvaluatePieceSquareTables(blackKings, KingMiddleGameTable, false);
        }

        // Passed pawn evaluation
        positional += EvaluatePassedPawns(whitePawns, blackPawns, true);
        positional -= EvaluatePassedPawns(blackPawns, whitePawns, false);

        // Adjust for check status
        if (board.IsInCheck())
        {
            material += board.IsWhiteToMove ? -20 : 20;
        }

        // Return the total evaluation score
        return material + positional;
    }


    int EvaluatePassedPawns(ulong myPawns, ulong opponentPawns, bool isWhite)
    {
        int passedPawnBonus = 0;
        ulong passedPawns = GetPassedPawns(myPawns, opponentPawns, isWhite);

        while (passedPawns != 0)
        {
            int pawnSquare = BitOperations.TrailingZeroCount(passedPawns);
            int rank = isWhite ? pawnSquare / 8 + 1 : 8 - pawnSquare / 8;
            passedPawnBonus += (rank - 1) * 10;
            passedPawns &= passedPawns - 1; // Remove the lowest set bit
        }

        return passedPawnBonus;
    }

    ulong GetPassedPawns(ulong myPawns, ulong opponentPawns, bool isWhite)
    {
        ulong passedPawns = 0;
        ulong fileMask = 0x0101010101010101UL; // Mask to isolate files

        for (int i = 0; i < 8; i++)
        {
            ulong myFilePawns = myPawns & (fileMask << i);
            ulong opponentFilePawns = opponentPawns & (fileMask << i);
            ulong noOpponentAhead = isWhite ? ~(opponentFilePawns >> 8) : ~(opponentFilePawns << 8);
            passedPawns |= myFilePawns & noOpponentAhead;
        }

        return passedPawns;
    }

    int GetPawnRank(ulong pawn, bool isWhite)
    {
        int rank = 0;
        int squareIndex = BitOperations.TrailingZeroCount(pawn);
        rank = (squareIndex / 8) + 1;
        return isWhite ? rank : 9 - rank; // Flip rank for black
    }

    IEnumerable<ulong> GetPawnBitboards(ulong pawns)
    {
        // Convert bitboard to individual pawn bitboards
        List<ulong> pawnList = new List<ulong>();

        while (pawns != 0)
        {
            ulong lsb = pawns & (~pawns + 1);
            pawnList.Add(lsb);
            pawns &= pawns - 1; // Clear LSB
        }

        return pawnList;
    }



    private int CountBits(ulong bitboard)
    {
        return (int)BitOperations.PopCount(bitboard);
    }

    private int EvaluateEndgame(Board board)
    {
        int whiteMaterial = CountMaterial(board, true);
        int blackMaterial = CountMaterial(board, false);

        int endgameScore = 0;

        if (whiteMaterial < 1750 || blackMaterial < 1750) // Arbitrary endgame threshold
        {
            endgameScore += CountEndgameKingSafety(whiteKings, true) - CountEndgameKingSafety(blackKings, false);
            endgameScore += CountEndgamePawnStructure(whitePawns, true) - CountEndgamePawnStructure(blackPawns, false);
        }

        return endgameScore;
    }

    private int CountMaterial(Board board, bool isWhite)
    {
        int material = 0;
        ulong[] pieces = isWhite ? new[] { whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens } :
                                    new[] { blackPawns, blackKnights, blackBishops, blackRooks, blackQueens };

        material += CountBits(pieces[0]) * 100;  // Pawns
        material += CountBits(pieces[1]) * 305;  // Knights
        material += CountBits(pieces[2]) * 320;  // Bishops
        material += CountBits(pieces[3]) * 500;  // Rooks
        material += CountBits(pieces[4]) * 900;  // Queens

        return material;
    }

    private int CountEndgameKingSafety(ulong kingBitboard, bool isWhite)
    {
        int safety = 0;

        // Define masks for central and edge squares
        ulong edgeSquares = 0x00FF000000FF00FFUL; // Edge squares

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
                structureScore -= isWhite ? 14 : -14;
            }
            else if (filePawns == 0) // Isolated pawns
            {
                structureScore -= isWhite ? 20 : -20;
            }
        }

        return structureScore;
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
            PieceType.King => 999,
            _ => 0
        };
    }
    public int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing, bool isRoot)
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

        if (isRoot)
        {
            this.bestEvaluation = bestEvaluation; // Store the best evaluation at the root level
            if (bestMove.HasValue)
                chosenMove = bestMove.Value;
        }

        // Update history and killer moves
        if (bestMove.HasValue)
        {
            Move move = bestMove.Value;
            if (history.ContainsKey(move))
                history[move]++;
            else
                history[move] = 1;

            if (isRoot)
                killerMoves[move] = 2;
        }

        return bestEvaluation;
    }
}
public class EvaluationDebugger
{
    private MyBot bot;
    public EvaluationDebugger(MyBot bot)
    {
        this.bot = bot;
    }
    public void PrintEvaluation(Board board)
    {
        //Attempt at writing mate in:

        if (bot.bestEvaluation >= 1000003)
            Console.WriteLine($"White mate in: {(Double)bot.bestEvaluation - 1000002}!");
        else if (bot.bestEvaluation >= 1000001)
            Console.WriteLine($"White mate in: {(Double)bot.bestEvaluation - 999999}!");
        else if (bot.bestEvaluation <= -1000002)
            Console.WriteLine($"Black mate in: {(Double)bot.bestEvaluation + 1000003}!");
        else if (bot.bestEvaluation <= -1000000)
            Console.WriteLine($"Black mate in: {(Double)bot.bestEvaluation + 1000002}!");

        else
        {
            Console.WriteLine($"Evaluation: {(Double)bot.bestEvaluation / 100}");
        }
        Console.WriteLine($"EvaluationAlways: {(Double)bot.bestEvaluation}");
    }

    public void PrintDepth(Board board)
    {
        Console.WriteLine($"Searched Depth: {bot.searchDepth}");
    }
}