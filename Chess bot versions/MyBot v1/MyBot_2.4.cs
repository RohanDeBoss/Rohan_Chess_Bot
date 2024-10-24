using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

//v2.4 Added PVS and improved TT and more!
//I still need to fix the mate in thing.
public class MyBot : IChessBot
{
    // Search parameters
    private const int MaxDepth = 4;
    private bool ConstantDepth = true;
    private const int CHECKMATE_SCORE = 1000000;
    private const int DRAW_SCORE = -35;

    public int BestEvaluation { get; private set; }
    private int positionsSearched;
    private Move? chosenMove;
    public Move? previousBestMove;
    public int currentDepth;

    // Evaluation and search optimization
    private int[] killerMoves = new int[400]; // Assuming max 200 moves each per game
    private int[,] history = new int[64, 64]; // From-To square history heuristic

    // Bitboards
    private ulong whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings;
    private ulong blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings;

    private ulong[] bitboards = new ulong[12]; // 0-5: White pieces, 6-11: Black pieces

    // Transposition Table with a fixed size
    private const int TranspositionTableSize = (1 << 18) * MaxDepth; // ~1.3m entries for depth 5
    private Dictionary<ulong, TranspositionEntry> transpositionTable = new Dictionary<ulong, TranspositionEntry>();
    private Queue<ulong> transpositionQueue = new Queue<ulong>(); // To track the keys for eviction

    public Move Think(Board board, Timer timer)
    {
        positionsSearched = 0;  // Reset the counter at the start of each search
        InitializeBitboards(board);
        int alpha = int.MinValue;
        int beta = int.MaxValue;
        Move bestMove = previousBestMove ?? new Move(); // Use previous best move if available


        // Calculate time cap
        int remainingTime = timer.MillisecondsRemaining; // Get remaining time in Ms
        int timeCap = (remainingTime / 62 - 100); // Time limit for the search but will finish current depth
        int Gametime = timer.GameStartTimeMilliseconds;
        long startTime = DateTime.Now.Ticks; // Start time for the search
        int currentDepth = 1; // Start from depth 1

        while (true) // Continue searching until time runs out or break
        {
            // Perform the minimax search
            int eval = Minimax(board, currentDepth, alpha, beta, board.IsWhiteToMove, true);

            // Store the best move found at this depth
            if (chosenMove.HasValue)
            {
                bestMove = chosenMove.Value;
                previousBestMove = chosenMove.Value; // Store this as the previous best move for the next iteration
            }

            // Check if the time limit has been reached
            long currentTime = DateTime.Now.Ticks;
            long elapsedTime = (currentTime - startTime) / TimeSpan.TicksPerMillisecond; // Convert to milliseconds
            if (currentDepth > 1)
            {
                if (remainingTime > 10000000 && currentDepth >= MaxDepth)
                {
                    break;
                }
                if (ConstantDepth == true)
                {
                    if (currentDepth >= MaxDepth)
                    {
                        break;
                    }
                }
                else if (elapsedTime > Gametime / 11 || elapsedTime >= timeCap - 30)
                {
                    break;
                }
            }

            currentDepth++; // Increase depth for the next iteration
        }

        EvaluationDebugger evaluationDebugger = new EvaluationDebugger(this);
        evaluationDebugger.PrintEvaluation(board);
        Console.WriteLine($"Depth: {currentDepth}");
        Console.WriteLine($"Positions searched: {positionsSearched / 1000}k");  // Total positions searched
        Console.WriteLine($"Transposition Table size: ({(transpositionTable.Count * 100) / TranspositionTableSize}%) {transpositionTable.Count} / {TranspositionTableSize}"); // Print TT size
        Console.WriteLine(" ");

        return bestMove; // Return the best move found
    }

    // Transposition Table entry structure
    public struct TranspositionEntry
    {
        public int Score;      // 32-bit
        public Move BestMove;  // 32-bit
        public byte Depth;    // 16-bit
        public byte NodeType;  // 8-bit
    }

    private void StoreInTranspositionTable(Board board, int depth, int score, Move bestMove, int nodeType)
    {
        ulong zobristKey = board.ZobristKey; // Use full Zobrist key for uniqueness

        // If the table exceeds its size limit, evict the oldest entry (FIFO strategy)
        if (transpositionTable.Count >= TranspositionTableSize)
        {
            ulong oldestKey = transpositionQueue.Dequeue();
            transpositionTable.Remove(oldestKey);
        }

        // Check if an entry exists and replace it based on depth (replace if new depth is greater or equal)
        if (!transpositionTable.TryGetValue(zobristKey, out var existingEntry) || depth >= existingEntry.Depth)
        {
            // Store the new entry
            transpositionTable[zobristKey] = new TranspositionEntry
            {
                Depth = (byte)depth,  // Store depth
                Score = (short)score,  // Store score
                BestMove = bestMove,   // Store best move
                NodeType = (byte)nodeType   // Store node type
            };

            // Add the key to the queue for future eviction
            transpositionQueue.Enqueue(zobristKey);
        }
    }

    private bool ProbeTranspositionTable(Board board, int depth, ref int alpha, ref int beta, out int score, out Move bestMove)
    {
        score = 0;
        bestMove = default;

        ulong zobristKey = board.ZobristKey;

        // Try to get the existing entry
        if (transpositionTable.TryGetValue(zobristKey, out var entry) && entry.Depth >= depth)
        {
            score = entry.Score;
            bestMove = entry.BestMove;

            // Check node type and adjust alpha or beta accordingly
            if (entry.NodeType == 0 || (entry.NodeType == 1 && score >= beta) || (entry.NodeType == 2 && score <= alpha))
                return true;

            if (entry.NodeType == 1)
                alpha = Math.Max(alpha, score);
            else if (entry.NodeType == 2)
                beta = Math.Min(beta, score);
        }
        return false;
    }

    private void InitializeBitboards(Board board)
    {
        // Clear bitboards
        Array.Clear(bitboards, 0, bitboards.Length);

        for (int square = 0; square < 64; square++)
        {
            Piece piece = board.GetPiece(new Square(square));
            if (piece.PieceType == PieceType.None) continue;

            int pieceIndex = (int)piece.PieceType - 1; // Maps Pawn to 0, Knight to 1, etc.
            int bitboardIndex = piece.IsWhite ? pieceIndex : pieceIndex + 6;

            bitboards[bitboardIndex] |= 1UL << square;
        }

        // Bulk assigning bitboards
        (whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings) = (bitboards[0], bitboards[1], bitboards[2], bitboards[3], bitboards[4], bitboards[5]);
        (blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings) = (bitboards[6], bitboards[7], bitboards[8], bitboards[9], bitboards[10], bitboards[11]);
    }

    private static int EvaluatePieceSquareTables(ulong bitboard, int[] table, bool isWhite)
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
    8,  8,  8, 10, 10,  8,  8,  8,
    4,  4,  8, 12, 12,  8,  4,  4,
    0,  0,  0, 10, 10,  0,  0,  0,
    0,  0,  4, 12, 12,  4,  0,  0,
    4, -4, -8,  0,  0, -8, -4,  4,
    4,  8,  8,-16,-16,  8, 12, 10,
    0,  0,  0,  0,  0,  0,  0,  0
};

    private static readonly int[] KnightTable = {
    -40,-36,-24,-24,-24,-24,-36,-40,
    -32,-16,  0,  0,  0,  0,-16,-32,
    -24,  0, 12, 12, 12, 12,  0,-24,
    -24,  4, 12, 16, 16, 12,  4,-24,
    -24,  0, 12, 16, 16, 12,  0,-24,
    -24,  4, 16, 12, 12, 16,  4,-24,
    -32,-16,  0,  4,  4,  0,-16,-32,
    -40,-16,-24,-24,-24,-24,-16,-40
};

    private static readonly int[] BishopTable = {
    -16, -8,-12, -8, -8,-12, -8,-16,
    -8,   0,  0,  0,  0,  0,  0, -8,
    -8,   0,  4,  8,  8,  4,  0, -8,
    -8,  12,  4,  8,  8,  4, 12, -8,
    -8,   0, 12,  8,  8, 12,  0, -8,
    -8,   8,  8,  0,  0,  8,  8, -8,
    -8,  12,  0,  0,  0,  0, 12, -8,
    -16, -8,-12, -8, -8,-12, -8,-16
};

    private static readonly int[] RookTable = {
    -1,  0,  4,  8,  8,  4,  0, -1,
    4,   8,  8, 12, 12,  8,  8,  4,
    0,   0,  4,  8,  8,  4,  0,  0,
    0,   0,  4,  8,  8,  4,  0,  0,
    0,   0,  4,  8,  8,  4,  0,  0,
    0,   0,  4,  8,  8,  4,  0,  0,
    0,   4,  4,  8,  8,  4,  4,  0,
    -8,  0,  0,  0,  0,  0,  0, -8
};

    private static readonly int[] QueenTable = {
    -16, -8, -8, -4, -4, -8, -8,-16,
    -8,   0,  0,  0,  0,  0,  0, -8,
    -8,   0,  4,  4,  4,  4,  0, -8,
    -4,   0,  4,  4,  4,  4,  0, -4,
     0,   0,  4,  4,  4,  4,  0, -4,
    -8,   4,  4,  4,  4,  4,  0, -8,
    -8,   0,  4,  0,  0,  0,  0, -8,
    -16, -8, -8,  0, -4, -8, -8,-16
};

    private static readonly int[] KingMiddleGameTable = {
    -24,-32,-32,-40,-40,-32,-32,-24,
    -24,-32,-32,-40,-40,-32,-32,-24,
    -24,-32,-32,-40,-40,-32,-32,-24,
    -24,-32,-32,-40,-40,-32,-32,-24,
    -16,-24,-24,-32,-32,-24,-24,-16,
     -8,-16,-16,-16,-16,-16,-16, -8,
    16, 16,  0,  0, -12, -8, 16, 16,
    16, 24, -10,  0,  0,-15, 40, 16
};

    private static readonly int[] KingEndGameTable = {
     0,  4,  4,  4,  4,  4,  4,  0,
     0,  8,  8,  8,  8,  8,  8,  0,
     0,  8, 16, 16, 16, 16,  8,  0,
     0,  8, 16, 15, 15, 16,  8,  0,
     0,  8, 16, 13, 13, 16,  8,  0,
     4,  8, 16, 16, 16, 16,  8,  4,
     4,  8,  8,  8,  8,  8,  8,  4,
     0,  4,  4,  4,  4,  4,  4,  0
};
    public int Evaluate(Board board, int depth)
    {
        int material = 0;
        int positional = 0;

        // Evaluate material
        ulong[] whitePieces = { whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens };
        ulong[] blackPieces = { blackPawns, blackKnights, blackBishops, blackRooks, blackQueens };
        int[] pieceValues = { 100, 300, 310, 500, 900 };

        for (int i = 0; i < whitePieces.Length; i++)
            material += (BitOperations.PopCount(whitePieces[i]) - BitOperations.PopCount(blackPieces[i])) * pieceValues[i];

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


        // King evaluation based on game stage
        if (CountSideMaterial(board, true) < 1750 || CountSideMaterial(board, false) < 1750) // Endgame
        {
            positional += EvaluatePieceSquareTables(whiteKings, KingEndGameTable, true);
            positional -= EvaluatePieceSquareTables(blackKings, KingEndGameTable, false);
        }
        else // Middle game
        {
            positional += EvaluatePieceSquareTables(whiteKings, KingMiddleGameTable, true);
            positional -= EvaluatePieceSquareTables(blackKings, KingMiddleGameTable, false);
        }

        // Evaluate passed pawns
        positional += EvaluatePassedPawns(whitePawns, blackPawns, true);
        positional -= EvaluatePassedPawns(blackPawns, whitePawns, false);

        // Check for checkmate, draw, or repeated position
        if (board.IsInCheckmate())
            positional = board.IsWhiteToMove ? -CHECKMATE_SCORE - depth : CHECKMATE_SCORE + depth;

        if (board.IsDraw())
            positional = DRAW_SCORE;

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

            // Rank-based bonus
            passedPawnBonus += (rank - 1) * 10 + (isWhite ? 8 - rank : rank - 1) * 5;

            // Check for blockers
            ulong pawnMask = 1UL << pawnSquare;
            if ((opponentPawns & (pawnMask >> 8)) != 0) // Blocked directly ahead
            {
                passedPawnBonus -= 20;
            }

            // Check adjacent files for potential blockers
            if ((opponentPawns & ((pawnMask >> 7) | (pawnMask >> 9))) != 0) // Blocked on diagonals
            {
                passedPawnBonus -= 10;
            }

            // Clear the processed pawn
            passedPawns &= passedPawns - 1; // Remove the least significant bit
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
        material += CountBits(pieces[1]) * 300;  // Knights
        material += CountBits(pieces[2]) * 310;  // Bishops
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
    private void OrderMoves(Board board, ref Move[] moves, Move ttMove)
    {
        // Sort moves based on their score using Array.Sort and a custom comparison function
        Array.Sort(moves, (m1, m2) => ScoreMove(board, m2) - ScoreMove(board, m1));

        // If the TT move exists, prioritize it by moving it to the front of the array
        if (ttMove.RawValue != 0)
        {
            int ttIndex = Array.FindIndex(moves, m => m.RawValue == ttMove.RawValue);
            if (ttIndex >= 0)
            {
                // Move the TT move to the front of the array
                Move temp = moves[ttIndex];
                for (int i = ttIndex; i > 0; i--)
                {
                    moves[i] = moves[i - 1]; // Shift all elements to the right
                }
                moves[0] = temp; // Place the TT move at the front
            }
        }
    }
    private int ScoreMove(Board board, Move move)
    {
        int score = 0;

        // MVV-LVA (Most Valuable Victim - Least Valuable Attacker)
        if (move.IsCapture)
        {
            int victimValue = GetPieceValue(board.GetPiece(move.TargetSquare).PieceType);
            int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
            score += (victimValue - attackerValue) * 1000 + 200000; // Pretty heavily prioritize captures
        }

        // Promotion: prioritize pawn promotion moves
        if (move.IsPromotion)
        {
            score += GetPieceValue(move.PromotionPieceType) * 10000; // Favor promotions, higher for queens
        }

        // Prioritize moves that give check
        if (board.IsInCheck())
        {
            score += 100000; // High value for moves that give check
        }

        // Killer move heuristic
        if (board.PlyCount < killerMoves.Length) // Check bounds
        {
            score += killerMoves[board.PlyCount] == move.RawValue ? 5000 : 0;
        }

        // History heuristic
        score += history[move.StartSquare.Index, move.TargetSquare.Index];

        return score;
    }

    public int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing, bool isRoot)
    {
        Move ttMove = default; // Initialize ttMove with a default value
        positionsSearched++;

        // Try probing the transposition table
        if (ProbeTranspositionTable(board, depth, ref alpha, ref beta, out int ttScore, out Move ttBestMove))
        {
            chosenMove = ttBestMove;
            return ttScore;
        }

        // Base case: terminal node
        if (depth == 0 || board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        int bestEvaluation;
        Move? bestMove = null;

        // Change GetLegalMoves() to return an array
        Move[] moves = board.GetLegalMoves();

        // Prioritize previous best move (from transposition table or previous iteration)
        OrderMoves(board, ref moves, previousBestMove.HasValue ? previousBestMove.Value : ttMove);  // Adjusted for arrays

        int nodeType = 1; // Assume lower bound initially (for transposition table entry)
        bool pvFound = false; // For principal variation

        if (isMaximizing)
        {
            bestEvaluation = int.MinValue;

            for (int i = 0; i < moves.Length; i++)
            {
                Move move = moves[i];
                board.MakeMove(move);
                InitializeBitboards(board); // Ensure bitboards are updated after the move

                int evaluation;
                if (pvFound)
                {
                    // Late move reduction (for moves beyond the first one)
                    if (i >= 1 && depth > 1)
                    {
                        // Perform a shallow search
                        evaluation = Minimax(board, depth - 1, alpha, alpha + 1, false, false);

                        // If shallow search improves alpha, re-search with full window
                        if (evaluation > alpha && evaluation < beta)
                        {
                            evaluation = Minimax(board, depth - 1, alpha, beta, false, false);
                        }
                    }
                    else
                    {
                        // First move is searched with full window
                        evaluation = Minimax(board, depth - 1, alpha, beta, false, false);
                        pvFound = true; // Principal variation move found
                    }
                }
                else
                {
                    // First move is searched with full window
                    evaluation = Minimax(board, depth - 1, alpha, beta, false, false);
                    pvFound = true; // Principal variation move found
                }

                board.UndoMove(move);
                InitializeBitboards(board); // Revert bitboards after undoing the move

                if (evaluation > bestEvaluation)
                {
                    bestEvaluation = evaluation;
                    bestMove = move;
                }

                alpha = Math.Max(alpha, evaluation);
                if (alpha >= beta)
                {
                    nodeType = 1; // Lower bound (beta cutoff)
                    break; // Pruning
                }
            }
        }
        else
        {
            bestEvaluation = int.MaxValue;

            for (int i = 0; i < moves.Length; i++)
            {
                Move move = moves[i];
                board.MakeMove(move);
                InitializeBitboards(board); // Ensure bitboards are updated after the move

                int evaluation;
                if (pvFound)
                {
                    // Late move reduction (for moves beyond the first one)
                    if (i >= 1 && depth > 1)
                    {
                        // Perform a shallow search
                        evaluation = Minimax(board, depth - 1, beta - 1, beta, true, false);

                        // If shallow search decreases beta, re-search with full window
                        if (evaluation < beta && evaluation > alpha)
                        {
                            evaluation = Minimax(board, depth - 1, alpha, beta, true, false);
                        }
                    }
                    else
                    {
                        // First move is searched with full window
                        evaluation = Minimax(board, depth - 1, alpha, beta, true, false);
                        pvFound = true; // Principal variation move found
                    }
                }
                else
                {
                    // First move is searched with full window
                    evaluation = Minimax(board, depth - 1, alpha, beta, true, false);
                    pvFound = true; // Principal variation move found
                }

                board.UndoMove(move);
                InitializeBitboards(board); // Revert bitboards after undoing the move

                if (evaluation < bestEvaluation)
                {
                    bestEvaluation = evaluation;
                    bestMove = move;
                }

                beta = Math.Min(beta, evaluation);
                if (alpha >= beta)
                {
                    nodeType = 2; // Upper bound (alpha cutoff)
                    break; // Pruning
                }
            }
        }

        // Store the evaluated position in the transposition table
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

        // If it's the root node, update the best move and evaluation
        if (isRoot)
        {
            this.BestEvaluation = bestEvaluation;
            if (bestMove.HasValue)
                chosenMove = bestMove.Value;
        }

        // Update history and killer moves for move ordering
        if (bestMove.HasValue)
        {
            Move move = bestMove.Value;
            history[move.StartSquare.Index, move.TargetSquare.Index]++; // Increment history score
            if (isRoot)
                killerMoves[board.PlyCount] = move.RawValue; // Update killer move for the current ply
        }

        return bestEvaluation;
    }
}
public class EvaluationDebugger
{

    private const int WhiteMateThreshold = 1000000;
    private const int BlackMateThreshold = -1000000;
    private const int MateValue = 1000000;
    private MyBot bot;

    public EvaluationDebugger(MyBot bot)
    {
        this.bot = bot;
    }

    public void PrintEvaluation(Board board)
    {
        int evaluation = bot.BestEvaluation;

        if (evaluation >= WhiteMateThreshold)
        {
            Console.WriteLine($"White mate in: {(evaluation - WhiteMateThreshold) / 100}!");
        }
        else if (evaluation <= BlackMateThreshold)
        {
            Console.WriteLine($"Black mate in: {-(evaluation - BlackMateThreshold) / 100}!");
        }
        else
        {
            Console.WriteLine($"Evaluation: {evaluation / 100.0:F2}");
        }

        Console.WriteLine($"Evaluation Always: {evaluation}");
    }
}