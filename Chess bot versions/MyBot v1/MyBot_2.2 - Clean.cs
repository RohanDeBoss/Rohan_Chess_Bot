using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

//v2.2 Clean
public class MyBot : IChessBot
{
    public int bestEvaluation { get; private set; }

    // Search parameters
    private int defaultSearch = 3; //recomended 5
    public int transpotitionsize = 2000000;
    private const int CHECKMATE_SCORE = 1000000;
    private const int DRAW_SCORE = -35;
    private const int REPEATED_POSITION_SCORE = -5;

    // Search parameters
    public int searchDepth;
    private Move? chosenMove;

    // Evaluation and search optimization
    private int[] killerMoves = new int[538]; // Assuming max 1000 plies
    private int[,] history = new int[64, 64]; // From-To square history heuristic

    // Bitboards
    private ulong whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings;
    private ulong blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings;

    private ulong[] bitboards = new ulong[12]; // 0-5: White pieces, 6-11: Black pieces

    // Transposition Table structure to handle collisions
    private Dictionary<ulong, List<TranspositionEntry>> transpositionTable = new Dictionary<ulong, List<TranspositionEntry>>();

    public Move Think(Board board, Timer timer)
    {
        InitializeBitboards(board);
        transpositionTable.Clear(); // Clear the table at the start of each new move

        // Adjust search depth based on time remaining
        searchDepth = CalculateSearchDepth(timer);

        Minimax(board, searchDepth, int.MinValue, int.MaxValue, board.IsWhiteToMove, true);
        return chosenMove ?? new Move(); // Return an empty move if no move is chosen
    }

    private int CalculateSearchDepth(Timer timer)
    {
        if (defaultSearch > 4)
        {
            if (timer.MillisecondsRemaining <= 800) return 1;
            if (timer.MillisecondsRemaining <= 3200) return 2;
            if (timer.MillisecondsRemaining <= 10500) return defaultSearch - 2;
            if (timer.MillisecondsRemaining <= 29000) return defaultSearch - 1;
            return defaultSearch;
        }
        else
        {
            if (timer.MillisecondsRemaining >= 55000) return defaultSearch + 1;
            return defaultSearch;
        }
    }

    // Transpotition table
    private class TranspositionEntry
    {
        public int Depth;
        public int Score;
        public Move BestMove;
        public int NodeType; // 0: Exact, 1: Lower Bound, 2: Upper Bound
    }

    // Improved StoreInTranspositionTable method
    private void StoreInTranspositionTable(Board board, int depth, int score, Move bestMove, int nodeType)
    {
        ulong zobristKey = board.ZobristKey;

        if (!transpositionTable.TryGetValue(zobristKey, out var entries))
        {
            entries = new List<TranspositionEntry>();
            transpositionTable[zobristKey] = entries;
        }

        // Remove existing entries that are not useful anymore
        entries.RemoveAll(entry => entry.Depth < depth);

        // Add or update the entry
        entries.Add(new TranspositionEntry
        {
            Depth = depth,
            Score = score,
            BestMove = bestMove,
            NodeType = nodeType
        });

        // Optionally, enforce a maximum number of entries
        if (entries.Count > transpotitionsize)
        {
            entries.RemoveRange(0, entries.Count - transpotitionsize);
        }
    }

    // Modified ProbeTranspositionTable to handle multiple entries
    private bool ProbeTranspositionTable(Board board, int depth, ref int alpha, ref int beta, out int score, out Move bestMove)
    {
        score = 0;
        bestMove = default;

        ulong zobristKey = board.ZobristKey;

        if (transpositionTable.TryGetValue(zobristKey, out var entries))
        {
            foreach (var entry in entries)
            {
                if (entry.Depth >= depth)
                {
                    score = entry.Score;
                    bestMove = entry.BestMove;

                    if (entry.NodeType == 0 || (entry.NodeType == 1 && score >= beta) || (entry.NodeType == 2 && score <= alpha))
                        return true;

                    if (entry.NodeType == 1)
                        alpha = Math.Max(alpha, score);
                    else if (entry.NodeType == 2)
                        beta = Math.Min(beta, score);
                }
            }
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
            bitboards[index] |= 1UL << i;
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
        return piece.PieceType switch
        {
            PieceType.Pawn => 0,
            PieceType.Knight => 1,
            PieceType.Bishop => 2,
            PieceType.Rook => 3,
            PieceType.Queen => 4,
            PieceType.King => 5,
            _ => throw new ArgumentException("Invalid piece type")
        } + (piece.IsWhite ? 0 : 6);
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
    10, 10,10, 15, 15, 10, 10, 10,
    5,  5, 10, 20, 20, 10,  5,  5,
    0,  0,  0, 15, 15,  0,  0,  0,
    0,  0,  5, 20, 19,-16,  0,  0,
    5, -5,-10,  0,  0,-10,  5,  5,
    5, 10, 10,-20,-20, 10, 20, 15,
    0,  0,  0,  0,  0,  0,  0,  0
};
    private static readonly int[] KnightTable = {
    -50,-45,-30,-30,-30,-30,-45,-50,
    -40,-20,  0,  0,  0,  0,-20,-40,
    -30,  0, 15, 15, 15, 15,  0,-30,
    -30,  5, 15, 20, 20, 15,  5,-30,
    -30,  0, 15, 20, 20, 15,  0,-30,
    -30,  5, 20, 15, 15, 20,  5,-30,
    -40,-20,  0,  5,  5,  0,-20,-40,
    -50,-20,-30,-30,-30,-30,-20,-50
};
    private static readonly int[] BishopTable = {
    -20,-10,-15,-10,-10,-15,-10,-20,
    -10,  0,  0,  0,  0,  0,  0,-10,
    -10,  0,  5, 10, 10,  5,  0,-10,
    -10,  15, 5, 10, 10,  5, 15,-10,
    -10,  0, 15, 10, 10, 15,  0,-10,
    -10, 10, 10,  0,  0, 10, 10,-10,
    -10, 15,  0,  0,  0,  0, 15,-10,
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
    -20,-10,-10,  0, -5,-10,-10,-20
};
    private static readonly int[] KingMiddleGameTable = {
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -30,-40,-40,-50,-50,-40,-40,-30,
    -20,-30,-30,-40,-40,-30,-30,-20,
    -10,-20,-20,-20,-20,-20,-20,-10,
    20, 20,  0,  0, -15,-10, 20, 20,
    20, 30,  0,  0,  0, -15, 50, 20
};
    private static readonly int[] KingEndGameTable = {
     0,  5,  5,  5,  5,  5,  5,  0,
     0, 10, 10, 10, 10, 10, 10,  0,
     0, 10, 20, 20, 20, 20, 10,  0,
     0, 10, 20, 19, 19, 20, 10,  0,
     0, 10, 20, 16, 16, 20, 10,  0,
     5, 10, 20, 20, 20, 20, 10,  5,
     5, 10, 10, 10, 10, 10, 10,  5,
     0,  5,  5,  5,  5,  5,  5,  0
    };

    public int Evaluate(Board board, int depth)
    {
        int material = 0;
        int positional = 0;

        // Checkmate and draw evaluations
        if (board.IsInCheckmate())
            return board.IsWhiteToMove ? -CHECKMATE_SCORE - depth : CHECKMATE_SCORE + depth;

        if (board.IsDraw())
            return DRAW_SCORE;

        if (board.IsRepeatedPosition())
            return REPEATED_POSITION_SCORE;

        if (board.IsInCheck())
        {
            material += board.IsWhiteToMove ? -16 : 16;
        }

        // Group the piece bitboards and values into arrays
        ulong[] whitePieces = { whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens };
        ulong[] blackPieces = { blackPawns, blackKnights, blackBishops, blackRooks, blackQueens };
        int[] pieceValues = { 100, 305, 320, 500, 900 };

        // Calculate material evaluation for white pieces
        for (int i = 0; i < whitePieces.Length; i++)
        {
            int whitePieceCount = BitOperations.PopCount(whitePieces[i]);
            int blackPieceCount = BitOperations.PopCount(blackPieces[i]);
            material += (whitePieceCount - blackPieceCount) * pieceValues[i];
        }

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

        // Side material calculation for king bitboard change
        int whiteMaterial = CountSideMaterial(board, true);
        int blackMaterial = CountSideMaterial(board, false);

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

    private int CountBits(ulong bitboard)
    {
        return (int)BitOperations.PopCount(bitboard);
    }

    private int CountSideMaterial(Board board, bool isWhite)
    {
        int material = 0;
        ulong[] pieces = isWhite ? new[] { whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens } : new[] { blackPawns, blackKnights, blackBishops, blackRooks, blackQueens };

        material += CountBits(pieces[0]) * 100;  // Pawns
        material += CountBits(pieces[1]) * 305;  // Knights
        material += CountBits(pieces[2]) * 320;  // Bishops
        material += CountBits(pieces[3]) * 500;  // Rooks
        material += CountBits(pieces[4]) * 900;  // Queens

        return material;
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

        // Most Valuable Victim - Least Valuable Attacker (MVV-LVA)
        if (move.IsCapture)
        {
            int victimValue = GetPieceValue(board.GetPiece(move.TargetSquare).PieceType);
            int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
            score += victimValue - attackerValue + 1000000; // High value for captures
        }

        score += killerMoves[board.PlyCount] == move.RawValue ? 5000 : 0;
        score += history[move.StartSquare.Index, move.TargetSquare.Index];

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
            history[bestMove.Value.StartSquare.Index, bestMove.Value.TargetSquare.Index]++;
            if (isRoot)
                killerMoves[board.PlyCount] = bestMove.Value.RawValue;
        }

        return bestEvaluation;
    }
}