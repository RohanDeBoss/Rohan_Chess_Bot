using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

//v2.5 Work in progress 3
//I still need to fix the mate in thing.
public class MyBot : IChessBot
{
    // Piece values: null, pawn, knight, bishop, rook, queen, king
    int[] pieceValues = { 0, 100, 300, 300, 500, 900, 10000 };

    // Search parameters
    private const int MaxDepth = 4;
    private bool ConstantDepth = true;

    public int BestEvaluation { get; private set; }
    private int positionsSearched;
    private Move? chosenMove;
    public Move? previousBestMove;
    public int currentDepth;

    // Evaluation and search optimization
    private int[] killerMoves = new int[512]; // Assuming max 256 moves each per game
    private int[,] history = new int[64, 64]; // From-To square history heuristic

    // Bitboards
    private ulong whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens, whiteKings;
    private ulong blackPawns, blackKnights, blackBishops, blackRooks, blackQueens, blackKings;

    private ulong[] bitboards = new ulong[12]; // 0-5: White pieces, 6-11: Black pieces

    public Move Think(Board board, Timer timer)
    {
        positionsSearched = 0;  // Reset the counter at the start of each search
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

            EvaluationDebugger evaluationDebugger = new EvaluationDebugger(this);
            evaluationDebugger.PrintEvaluation(board);
            Console.WriteLine($"Depth: {currentDepth}");
            Console.WriteLine($"Positions searched: {positionsSearched}");  // Total positions searched
            Console.WriteLine($"Transposition Table size: ({(transpositionTable.Count * 100) / TranspositionTableSize}%) {transpositionTable.Count} / {TranspositionTableSize}"); // Print TT size
            Console.WriteLine(" ");

            currentDepth++; // Increase depth for the next iteration
        }
        return bestMove; // Return the best move found
    }
    // Transposition Table with a fixed size
    private const int TranspositionTableSize = (1 << 17) * MaxDepth ^ 2; // ~2m+ entries
    private Dictionary<ulong, TranspositionEntry> transpositionTable = new Dictionary<ulong, TranspositionEntry>();
    private Queue<ulong> transpositionQueue = new Queue<ulong>(); // To track the keys for eviction


    // Transposition Table entry structure
    public struct TranspositionEntry
    {
        public int Score;      // 32-bit
        public Move BestMove;  // 32-bit
        public byte Depth;     // 8-bit
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
    0,  0,  4, 12, 12, -4, -5,  0,
    4, -4, -8,  0,  0, -8, -4,  4,
    4, 18,  8,-16,-16,  18, 20, 14,
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
    -8,   0, 13,  8,  8, 13,  0, -8,
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
    -8,  0,  0,  4,  4,  0,  0, -8
};
    private static readonly int[] QueenTable = {
    -16, -8, -8, -4, -4, -8, -8,-16,
    -8,   0,  0,  0,  0,  0,  0, -8,
    -8,   0,  4,  4,  4,  4,  0, -8,
    -4,   0,  4,  4,  4,  4,  0, -4,
     0,   0,  4,  4,  4,  4,  0, -4,
    -8,   4, -4,  4,  4, -4,  0, -8,
    -8,   0,  4,  0,  0,  0,  0, -8,
    -16, -8, -8,  1,  0, -8, -8,-16
};
    private static readonly int[] KingMiddleGameTable = {
    -24,-32,-32,-40,-40,-32,-32,-24,
    -24,-32,-32,-40,-40,-32,-32,-24,
    -24,-32,-32,-40,-40,-32,-32,-24,
    -24,-32,-32,-40,-40,-32,-32,-24,
    -16,-24,-24,-32,-32,-24,-24,-16,
     -8,-16,-16,-16,-16,-16,-16, -8,
    16, 16,  0,  0, -12, -8, 16, 16,
    16, 24, -10,  0,  0,-15, 30, 16
};
    private static readonly int[] KingEndGameTable = {
     0,  4,  4,  4,  4,  4,  4,  0,
     0,  8,  8,  8,  8,  8,  8,  0,
     0,  8, 11, 11, 11, 11,  8,  0,
     0,  8, 11, 15, 15, 11,  8,  0,
     0,  8, 11, 13, 13, 11,  8,  0,
     4,  8, 11, 11, 11, 11,  8,  4,
     4,  8,  8,  8,  8,  8,  8,  4,
     0,  4,  4,  4,  4,  4,  4,  0
};
    public int Evaluate(Board board, int depth)
    {
        int material = 0;
        int positional = 0;
        int CHECKMATE_SCORE = 1000000;
        int DRAW_SCORE = -30;

        // Check for checkmate, draw, or repeated position
        if (board.IsInCheckmate())
            return board.IsWhiteToMove ? -CHECKMATE_SCORE - depth : CHECKMATE_SCORE + depth;

        if (board.IsDraw())
            return DRAW_SCORE;

        // Evaluate material
        ulong[] whitePieces = { whitePawns, whiteKnights, whiteBishops, whiteRooks, whiteQueens };
        ulong[] blackPieces = { blackPawns, blackKnights, blackBishops, blackRooks, blackQueens };

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

        if (IsEndGame(board)) // Pass the board reference
        {
            positional += EvaluatePieceSquareTables(whiteKings, KingEndGameTable, true);
            positional -= EvaluatePieceSquareTables(blackKings, KingEndGameTable, false);
        }
        else // Middle game & Opening
        {
            positional += EvaluatePieceSquareTables(whiteKings, KingMiddleGameTable, true);
            positional -= EvaluatePieceSquareTables(blackKings, KingMiddleGameTable, false);
        }

        // Evaluate passed pawns
        positional += EvaluatePassedPawns(whitePawns, blackPawns, true);
        positional -= EvaluatePassedPawns(blackPawns, whitePawns, false);

        return material + positional;
    }

    int EvaluatePassedPawns(ulong myPawns, ulong opponentPawns, bool isWhite)
    {
        int passedPawnBonus = 0;
        ulong passedPawns = 0;
        ulong fileMask = 0x0101010101010101UL; // Mask to isolate files

        // Determine passed pawns and calculate their bonuses
        for (int i = 0; i < 8; i++)
        {
            ulong myFilePawns = myPawns & (fileMask << i);
            ulong opponentFilePawns = opponentPawns & (fileMask << i);
            ulong noOpponentAhead = isWhite ? ~(opponentFilePawns >> 8) : ~(opponentFilePawns << 8);
            passedPawns |= myFilePawns & noOpponentAhead;
        }

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
                passedPawnBonus -= 15;
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

    bool IsEndGame(Board boardRef) //Endgame if No Queens or 1 Queen and 1 Minor Piece
    {
        bool[] sides = { true, false };
        var GetPieces = boardRef.GetPieceList;
        foreach (bool side in sides)
        {
            int queenCount = GetPieces(PieceType.Queen, side).Count;
            int minorPieceCount = GetPieces(PieceType.Rook, side).Count + GetPieces(PieceType.Bishop, side).Count + GetPieces(PieceType.Knight, side).Count;
            if ((queenCount == 0 && minorPieceCount > 2) || (queenCount == 1 && minorPieceCount > 1))
                return false;
        }
        return true;
    }

    private void OrderMoves(Board board, ref Move[] moves, Move ttMove)
    {
        // Sort moves using a custom scoring function
        Array.Sort(moves, (m1, m2) => ScoreMove(board, m2).CompareTo(ScoreMove(board, m1)));

        // If the TT move exists, move it to the front
        if (ttMove.RawValue != 0)
        {
            int ttIndex = Array.FindIndex(moves, m => m.RawValue == ttMove.RawValue);
            if (ttIndex >= 0)
            {
                Move ttTemp = moves[ttIndex]; // Move the TT move to the front and shift other moves
                for (int i = ttIndex; i > 0; i--)
                {
                    moves[i] = moves[i - 1];
                }
                moves[0] = ttTemp; // Place the TT move at the front
            }
        }
    }

    private int ScoreMove(Board board, Move move)
    {
        int score = 0;
        int movePieceType = (int)move.MovePieceType;

        // MVV-LVA (Most Valuable Victim - Least Valuable Attacker)
        if (move.IsCapture)
            score = 10000 * pieceValues[(int)move.CapturePieceType] - pieceValues[movePieceType];

        if (move.IsPromotion)
            score += pieceValues[(int)move.PromotionPieceType];

        if (move.IsCastles)
            score += 1000;

        // Prioritize moves that give check
        if (board.IsInCheck())
        {
            score += 50000; // High value for check moves
        }

        // Killer move heuristic
        if (board.PlyCount < killerMoves.Length && killerMoves[board.PlyCount] == move.RawValue)
        {
            score += 5000; // Reward killer move
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
        Move[] moves = board.GetLegalMoves();

        // Prioritize previous best move (from transposition table or previous iteration)
        OrderMoves(board, ref moves, previousBestMove.HasValue ? previousBestMove.Value : ttMove);  // Adjusted for arrays

        int nodeType = 1; // Assume lower bound initially (for transposition table entry)
        bool pvFound = false; // For principal variation

        // Set initial best evaluation based on maximizing or minimizing
        bestEvaluation = isMaximizing ? int.MinValue : int.MaxValue;

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
                    evaluation = Minimax(board, depth - 1, isMaximizing ? alpha : beta - 1, isMaximizing ? alpha + 1 : beta, !isMaximizing, false);

                    // If shallow search improves alpha or decreases beta, re-search with full window
                    if ((isMaximizing && evaluation > alpha && evaluation < beta) ||
                        (!isMaximizing && evaluation < beta && evaluation > alpha))
                    {
                        evaluation = Minimax(board, depth - 1, alpha, beta, !isMaximizing, false);
                    }
                }
                else
                {
                    // First move is searched with full window
                    evaluation = Minimax(board, depth - 1, alpha, beta, !isMaximizing, false);
                    pvFound = true; // Principal variation move found
                }
            }
            else
            {
                // First move is searched with full window
                evaluation = Minimax(board, depth - 1, alpha, beta, !isMaximizing, false);
                pvFound = true; // Principal variation move found
            }

            board.UndoMove(move);
            InitializeBitboards(board); // Revert bitboards after undoing the move

            if (isMaximizing)
            {
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
            else
            {
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

            // Update history and killer moves for move ordering
            Move move = bestMove.Value;
            history[move.StartSquare.Index, move.TargetSquare.Index]++; // Increment history score
            if (isRoot) killerMoves[board.PlyCount] = move.RawValue; // Update killer move for the current ply

            StoreInTranspositionTable(board, depth, bestEvaluation, bestMove.Value, nodeType);
        }

        // If it's the root node, update the best move and evaluation
        if (isRoot)
        {
            this.BestEvaluation = bestEvaluation;
            if (bestMove.HasValue) chosenMove = bestMove.Value;
        }

        return bestEvaluation;
    }
}
public class EvaluationDebugger
{
    private const int MateValue = 1000000;
    private MyBot bot;
    public EvaluationDebugger(MyBot bot)
    {
        this.bot = bot;
    }
    public void PrintEvaluation(Board board)
    {
        int evaluation = bot.BestEvaluation;

        if (evaluation >= MateValue)
        {
            Console.WriteLine($"White mate in: {(evaluation - MateValue) / 100}!");
        }
        else if (evaluation <= -MateValue)
        {
            Console.WriteLine($"Black mate in: {-(evaluation + MateValue) / 100}!");
        }
        else
        {
            Console.WriteLine($"Evaluation: {evaluation / 100.0:F2}");
        }
        Console.WriteLine($"Evaluation Always: {evaluation}");
    }
}