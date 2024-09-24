using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Data;
using System.Numerics;

//v2.6.1 Clean
//I still need to fix the mate in thing.
public class EvilBot : IChessBot
{
    public int bestEvaluation { get; private set; }

    private int defultSearch = 5; //recomended 5
    public int searchDepth;
    public int transpotitionsize = 2000000;
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
        transpositionTable.Clear(); // Clear the table at the start of each new move
        // Adjust search depth based on time remaining
        if (defultSearch > 4)
        {
            if (timer.MillisecondsRemaining <= 800)
            {
                searchDepth = 1;
            }
            else if (timer.MillisecondsRemaining <= 3200)
            {
                searchDepth = 2;
            }
            else if (timer.MillisecondsRemaining <= 10500)
            {
                searchDepth = defultSearch - 2;
            }
            else if (timer.MillisecondsRemaining <= 29000)
            {
                searchDepth = defultSearch - 1;
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

        return chosenMove ?? new Move(); // Return an empty move if no move is chosen
    }

    // Transpotition table
    private class TranspositionEntry
    {
        public int Depth;
        public int Score;
        public Move BestMove;
        public int NodeType; // 0: Exact, 1: Lower Bound, 2: Upper Bound
    }

    private Dictionary<ulong, TranspositionEntry> transpositionTable = new Dictionary<ulong, TranspositionEntry>();

    private void StoreInTranspositionTable(Board board, int depth, int score, Move bestMove, int nodeType)
    {
        if (transpositionTable.Count >= transpotitionsize) // Limit table size
            return;

        transpositionTable[board.ZobristKey] = new TranspositionEntry
        {
            Depth = depth,
            Score = score,
            BestMove = bestMove,
            NodeType = nodeType
        };
    }

    private bool ProbeTranspositionTable(Board board, int depth, ref int alpha, ref int beta, out int score, out Move bestMove)
    {
        score = 0;
        bestMove = default;

        if (transpositionTable.TryGetValue(board.ZobristKey, out var entry) && entry.Depth >= depth)
        {
            score = entry.Score;
            bestMove = entry.BestMove;

            if (entry.NodeType == 0) // Exact score
                return true;
            if (entry.NodeType == 1 && score >= beta) // Lower bound
                return true;
            if (entry.NodeType == 2 && score <= alpha) // Upper bound
                return true;

            // Adjust alpha or beta
            if (entry.NodeType == 1)
                alpha = Math.Max(alpha, score);
            else if (entry.NodeType == 2)
                beta = Math.Min(beta, score);
        }

        return false;
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
    20, 20,  0,  0, -15,-10, 20, 20,
    20, 30,  0,  0,  0,  -10, 50, 20
};
    private static readonly int[] KingEndGameTable = {
     0,  5,  5,  5,  5,  5,  5,  0,
     0, 10, 10, 10, 10, 10, 10,  0,
     0, 10, 20, 20, 20, 20, 10,  0,
     0, 10, 21, 19, 19, 21, 10,  0,
     0, 10, 20, 16, 16, 20, 10,  0,
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
            return -35; // Negative score for draw
        }
        if (board.IsRepeatedPosition())
        {
            return -10;
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
            material += board.IsWhiteToMove ? -16 : 16;
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

            // Bonus for the rank of the pawn
            passedPawnBonus += (rank - 1) * 10;

            // Additional bonus based on distance to promotion
            passedPawnBonus += (isWhite ? 8 - rank : rank - 1) * 5;

            // Check for potential blockers (simplified)
            // More complex blocker checks can be implemented as needed
            ulong pawnMask = 1UL << pawnSquare;
            if ((opponentPawns & (pawnMask >> 8)) != 0) // Pawn blocked by opponent's pawn directly ahead
            {
                passedPawnBonus -= 20;
            }

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
    private void OrderMoves(Board board, List<Move> moves)
    {
        moves.Sort((m1, m2) => ScoreMove(board, m2) - ScoreMove(board, m1));
    }

    private int ScoreMove(Board board, Move move)
    {
        int score = 0;
        // If it's a capture move, prioritize based on MVV-LVA (Most Valuable Victim - Least Valuable Attacker)
        if (move.IsCapture)
        {
            int victimValue = GetPieceValue(board.GetPiece(move.TargetSquare).PieceType);
            int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
            score += victimValue - attackerValue + 1000000; // High value to prioritize captures
        }

        // Prioritize killer moves
        if (killerMoves.ContainsKey(move))
        {
            score += 5000; // Arbitrary bonus for killer moves
        }

        // Use history heuristic (assign a bonus based on move frequency)
        if (history.ContainsKey(move))
        {
            score += history[move];
        }

        return score;
    }

    public int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing, bool isRoot)
    {
        Move ttMove = default; // Initialize ttMove with a default value

        // Transposition table lookup
        if (!isRoot && ProbeTranspositionTable(board, depth, ref alpha, ref beta, out int ttScore, out ttMove))
        {
            return ttScore;
        }

        if (depth == 0 || board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        int bestEvaluation;
        Move? bestMove = null;

        List<Move> moves = new List<Move>(board.GetLegalMoves());
        OrderMoves(board, moves);

        // Use ttMove if available
        if (ttMove.RawValue != 0)
        {
            moves.Remove(ttMove);
            moves.Insert(0, ttMove);
        }

        int nodeType = 1; // Assume lower bound initially

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
                {
                    nodeType = 1; // Lower bound
                    break;
                }
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
                    break; //Alpha cutoff
            }
        }

        // Store position in transposition table
        if (bestMove.HasValue)
        {
            if (bestEvaluation <= alpha)
                nodeType = 2; // Upper bound
            else if (bestEvaluation >= beta)
                nodeType = 1; // Lower bound
            else
                nodeType = 0; // Exact score

            StoreInTranspositionTable(board, depth, bestEvaluation, bestMove.Value, nodeType);
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