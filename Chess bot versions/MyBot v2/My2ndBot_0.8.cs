using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

// My2ndBot v0.8 Time management with tsfot = variable , LMR and NMP tweaks + Bug fixes!
public class MyBot : IChessBot
{
    // Constants
    private const bool ConstantDepth = false;
    private const short MaxDepth = 4;
    private const short InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22;

    // Static Fields
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 };
    private TTEntry[] tt = new TTEntry[TT_SIZE]; // Remove 'static'
    private readonly ulong ttMask = (ulong)(TT_SIZE - 1); // Precomputed mask

    // Instance Fields
    private int positionsSearched = 0;
    public int bestScore;
    private Move[] killerMoves = new Move[200 * 2];
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
    private int currentDepthPositions;
    private int currentDepth;

    private short GetTimeSpentFraction(Timer timer)
    {
        if (timer.MillisecondsRemaining <= 5_000) // Less than or equal to 5 seconds
            return 40; // Use 1/40 of remaining time
        else if (timer.MillisecondsRemaining < 20_000) // Less than 20 seconds
            return 30; // Use 1/30 of remaining time
        else if (timer.MillisecondsRemaining > 60_000) // More than 1 minute
            return 22; // Use 1/22 of remaining time
        else
            return 25; // Default to 1/25 of remaining time
    }

    private string GetMateInMoves(int score)
    {
        if (Math.Abs(score) >= InfiniteScore - MaxDepth * 50)
        {
            int mateMoves = (InfiniteScore - Math.Abs(score) + 1) / 50;
            return score > 0 ? $"Mate in {mateMoves} ply! :)" : $"Mated in {mateMoves} ply :(";
        }
        return null;
    }

    private Move EvalLog(Move moveToReturn, Board board, int depth)
    {
        Console.WriteLine(" ");
        Console.WriteLine($"MyBot Depth: {depth}");

        // Check for forced mate and log
        string mateInfo = GetMateInMoves(bestScore);
        if (!string.IsNullOrEmpty(mateInfo))
        {
            Console.WriteLine(mateInfo);
        }
        else
        {
            Console.WriteLine($"MyBot eval: {(board.IsWhiteToMove ? bestScore : -bestScore)}");
        }

        Console.WriteLine($"MyBot Positions: {positionsSearched:N0}");

        return moveToReturn;
    }

    public Move Think(Board board, Timer timer)
    {
        positionsSearched = 0;
        currentDepth = 0;
        short depth = 1;
        int previousBestScore = 0;
        Move previousBestMove = Move.NullMove;
        var legalMoves = board.GetLegalMoves();
        Move bestMove = legalMoves.Length > 0 ? legalMoves[0] : Move.NullMove; // Initialize bestMove with a valid move

        // Immediate checkmate check
        foreach (Move move in legalMoves)
        {
            if (IsCheckmateMove(move, board))
            {
                bestScore = InfiniteScore - 50; // Set bestScore for Mate in 1
                return EvalLog(move, board, 1);
            }
        }

        if (legalMoves.Length == 0) return legalMoves[0];

        // Aspiration search logic
        const int InitialAspirationWindow = 125;
        const int MaxAspirationDepth = 4;
        const int CheckmateScoreThreshold = 25000;

        // Calculate time fraction dynamically
        short timeFraction = GetTimeSpentFraction(timer);

        // Use the fraction to allocate time for this move
        int maxTimeForTurn = ConstantDepth ? int.MaxValue :
            (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 3);

        while ((ConstantDepth && depth <= MaxDepth) || (!ConstantDepth && timer.MillisecondsElapsedThisTurn < maxTimeForTurn))
        {
            currentDepth = depth;
            currentDepthPositions = 0;

            bool useAspiration = depth > MaxAspirationDepth &&
                                Math.Abs(previousBestScore) < CheckmateScoreThreshold;

            int alpha = -InfiniteScore;
            int beta = InfiniteScore;
            int aspirationWindow = InitialAspirationWindow;

            bool aspirationFailed;
            int searchCount = 0;

            do
            {
                aspirationFailed = false;
                int currentBestScore = -InfiniteScore;
                bestMove = legalMoves[0];

                // Manual move ordering
                Move[] movesToOrder = legalMoves;
                int[] moveScores = new int[movesToOrder.Length];
                TTEntry ttEntry = tt[GetTTIndex(board.ZobristKey)];

                for (int i = 0; i < movesToOrder.Length; i++)
                {
                    Move move = movesToOrder[i];
                    int score = 0;

                    if (move == ttEntry.BestMove) score += 10_000_000;
                    if (move == previousBestMove) score += 5_000_000;
                    score += MoveOrdering(move, board);
                    moveScores[i] = score;
                }

                Array.Sort(moveScores, movesToOrder, Comparer<int>.Create((a, b) => b.CompareTo(a)));

                foreach (Move move in movesToOrder)
                {
                    if (!ConstantDepth && timer.MillisecondsElapsedThisTurn >= maxTimeForTurn)
                        return EvalLog(bestMove, board, currentDepth); // Now returns a valid move

                    if (IsCheckmateMove(move, board))
                        return EvalLog(move, board, currentDepth);

                    board.MakeMove(move);
                    int score = -Negamax(board, depth - 1, -beta, -alpha, 1);
                    board.UndoMove(move);

                    if (score > currentBestScore)
                    {
                        currentBestScore = score;
                        bestMove = move;
                    }

                    if (score >= beta)
                    {
                        aspirationFailed = useAspiration;
                        beta = Math.Min(InfiniteScore, beta + aspirationWindow);
                        break;
                    }
                    alpha = Math.Max(alpha, score);
                }

                if (aspirationFailed && searchCount++ < 1)
                {
                    aspirationWindow *= 4;
                    alpha = currentBestScore - aspirationWindow;
                    beta = currentBestScore + aspirationWindow;
                }
                else
                {
                    previousBestScore = currentBestScore;
                    bestScore = currentBestScore;
                }
            } while (aspirationFailed);

            // Update global counter and log
            positionsSearched += currentDepthPositions;
            previousBestMove = bestMove;
            depth++;
        }
        return EvalLog(bestMove, board, currentDepth);
    }

    private int MoveOrdering(Move move, Board board, int ply = 0)
    {
        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);

        // Prioritize transposition table moves.
        if (tt[index].Key == key && tt[index].BestMove == move)
            return 1000000;

        int score = historyMoves[move.StartSquare.Index, move.TargetSquare.Index];

        // Captures: MVV-LVA (Most Valuable Victim - Least Valuable Attacker)
        var capturedPiece = board.GetPiece(move.TargetSquare);
        if (capturedPiece.PieceType != PieceType.None)
            score += 100000 + GetPieceValue(capturedPiece.PieceType) * 10 -
                  GetPieceValue(board.GetPiece(move.StartSquare).PieceType);

        // Promotion moves.
        if (move.IsPromotion)
            score += 80000 + GetPieceValue(move.PromotionPieceType);

        // Killer moves.
        if (move == killerMoves[ply * 2] || move == killerMoves[ply * 2 + 1])
            score += 90000;

        return score;
    }

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

        // Update history with depth weighting
        historyMoves[move.StartSquare.Index, move.TargetSquare.Index] += depth * depth;

        // Periodic decay (now in separate method)
        if (positionsSearched % 1024 == 0)
            DecayHistory();
    }
    private void DecayHistory()
    {
        for (int i = 0; i < 64; i++)
            for (int j = 0; j < 64; j++)
                historyMoves[i, j] = (historyMoves[i, j] * 3) / 4;
    }

    private bool IsCheckmateMove(Move move, Board board)
    {
        board.MakeMove(move);
        bool isCheckmate = board.IsInCheckmate();
        board.UndoMove(move);
        return isCheckmate;
    }

    private int Negamax(Board board, int depth, int alpha, int beta, int ply)
    {
        currentDepthPositions++;

        if (board.IsDraw()) return 0;
        if (board.IsInCheckmate()) return -InfiniteScore + ply * 50;

        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];

        if (ttEntry.Key == key && ttEntry.Depth >= depth)
        {
            if (ttEntry.Flag == EXACT) return ttEntry.Score;
            if (ttEntry.Flag == ALPHA && ttEntry.Score <= alpha) return alpha;
            if (ttEntry.Flag == BETA && ttEntry.Score >= beta) return beta;
        }

        if (depth <= 0) return Quiescence(board, alpha, beta, ply);

        // Null Move Pruning
        if (!board.IsInCheck() && depth > 2) //stars above depth 2
        {
            board.ForceSkipTurn();
            int reduction = 2; //Depth 2 reduction applied
            int nullScore = -Negamax(board, depth - reduction - 1, -beta, -beta + 1, ply + 1);
            board.UndoSkipTurn();
            if (nullScore >= beta) return beta;
        }

        // Manual move ordering
        Move[] moves = board.GetLegalMoves();
        int[] moveScores = new int[moves.Length];

        for (int i = 0; i < moves.Length; i++)
        {
            moveScores[i] = MoveOrdering(moves[i], board, ply);
        }

        Array.Sort(moveScores, moves, Comparer<int>.Create((a, b) => b.CompareTo(a)));

        int originalAlpha = alpha;
        Move bestMove = Move.NullMove;
        int bestScore = -InfiniteScore;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            board.MakeMove(move);

            // Apply LMR for non-capture, non-promotion, non-check moves at depth 3+
            int newDepth = depth - 1; // Default depth reduction of - 1
            if (depth > 2 && !move.IsCapture && !move.IsPromotion && !board.IsInCheck())
                newDepth -= 1; // Reduce depth further

            int score;
            if (i == 0)  // PV node (principal variation)
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1);
            }
            else
            {
                score = -Negamax(board, newDepth, -alpha - 1, -alpha, ply + 1);
                if (score > alpha)
                    score = -Negamax(board, newDepth, -beta, -alpha, ply + 1);
            }

            board.UndoMove(move);

            // Update best move and score if necessary
            if (score > bestScore)
            {
                bestScore = score;
                bestMove = move;
            }

            alpha = Math.Max(alpha, score);

            // Pruning
            if (alpha >= beta)
            {
                if (!move.IsCapture)
                {
                    if (i < 2) UpdateKillerMoves(move, ply);  // Update killer moves for early moves
                    UpdateHistoryMove(move, depth);  // Update history table
                }

                AddTT(key, depth, (short)beta, BETA, move);  // Store the result in transposition table
                return beta;  // Beta cutoff
            }
        }

        byte flag = bestScore <= originalAlpha ? ALPHA : bestScore >= beta ? BETA : EXACT;
        AddTT(key, depth, (short)bestScore, flag, bestMove);
        return bestScore;
    }

    private int Quiescence(Board board, int alpha, int beta, int ply)
    {
        currentDepthPositions++;
        int standPat = Evaluate(board, 0);
        if (standPat >= beta) return beta;
        alpha = Math.Max(alpha, standPat);

        // Manual capture ordering
        Move[] captureMoves = board.GetLegalMoves(true);
        int[] captureScores = new int[captureMoves.Length];

        for (int i = 0; i < captureMoves.Length; i++)
        {
            captureScores[i] = MoveOrdering(captureMoves[i], board, ply);
        }

        Array.Sort(captureScores, captureMoves, Comparer<int>.Create((a, b) => b.CompareTo(a)));

        foreach (Move move in captureMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, ply + 1);
            board.UndoMove(move);

            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }

        return alpha;
    }

    private int Evaluate(Board board, int depth)
    {
        if (board.IsDraw()) return 0;

        int score = 0;
        bool isEndgame = IsEndgame(board);

        foreach (PieceList pieceList in board.GetAllPieceLists())
        {
            int pieceValue = GetPieceValue(pieceList.TypeOfPieceInList);
            int[][] adjustmentTable = GetAdjustmentTable(pieceList.TypeOfPieceInList, isEndgame);

            foreach (Piece piece in pieceList)
            {
                int rank = piece.IsWhite ? 7 - piece.Square.Rank : piece.Square.Rank;
                score += (piece.IsWhite ? 1 : -1) *
                       (adjustmentTable[rank][piece.Square.File] + pieceValue);
            }
        }

        return board.IsWhiteToMove ? score : -score;
    }

    private int[][] GetAdjustmentTable(PieceType pieceType, bool isEndgame)
    {
        return pieceType switch
        {
            PieceType.Pawn => PawnTable,
            PieceType.Knight => KnightTable,
            PieceType.Bishop => BishopTable,
            PieceType.Rook => RookTable,
            PieceType.Queen => QueenTable,
            PieceType.King => isEndgame ? KingEndGame : KingMiddleGame,
            _ => new int[8][]
        };
    }

    private int GetTTIndex(ulong key) => (int)(key & ttMask); // Optimized calculation

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
        int index = GetTTIndex(key);
        if (tt[index].Key == 0 || tt[index].Depth <= depth)
            tt[index] = new TTEntry { Key = key, Depth = (short)depth, Score = score, Flag = flag, BestMove = bestMove };
    }

    // Piece Square Tables (Jagged Arrays)
    private static readonly int[][] PawnTable = {
        new[] {0,  0,  0,  0,  0,  0,  0,  0},
        new[] {50, 50, 50, 50, 50, 50, 50, 50},
        new[] {12, 10, 20, 30, 30, 20, 11, 10},
        new[] {5,  5, 10, 25, 25, 10,  5,  5},
        new[] {1,  3,  6, 21, 22,  0,  0,  0},
        new[] {5, -1,-10,  1,  3,-10, -5,  5},
        new[] {5, 10, 10,-20,-20, 10, 11,  5},
        new[] {0,  0,  0,  0,  0,  0,  0,  0}
    };

    private static readonly int[][] KnightTable = {
        new[] {-50,-40,-30,-30,-30,-30,-40,-50},
        new[] {-40,-20,  0,  0,  0,  0,-20,-40},
        new[] {-30,  0, 10, 15, 15, 10,  0,-30},
        new[] {-30,  5, 15, 20, 20, 15,  5,-30},
        new[] {-30,  0, 15, 20, 20, 15,  0,-30},
        new[] {-30,  5, 10, 15, 15, 10,  5,-30},
        new[] {-40,-20,  0,  5,  5,  0,-20,-40},
        new[] {-50,-40,-30,-30,-30,-30,-40,-50}
    };

    private static readonly int[][] BishopTable = {
        new[] {-20,-10,-10,-10,-10,-10,-10,-20},
        new[] {-10,  0,  0,  0,  0,  0,  0,-10},
        new[] {-10,  0,  5, 10, 10,  5,  0,-10},
        new[] {-10,  5,  5, 10, 10,  5,  5,-10},
        new[] {-10,  0, 10, 10, 10, 10,  0,-10},
        new[] {-10, 10, 10, 10, 10, 10, 10,-10},
        new[] {-10,  5,  0,  0,  0,  0,  5,-10},
        new[] {-20,-10,-10,-10,-10,-10,-10,-20}
    };

    private static readonly int[][] RookTable = {
        new[] {0,   0,  0,  0,  0,  0,  0,  0},
        new[] {0,  10, 10, 10, 10, 10, 10,  5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {-5,  0,  0,  0,  0,  0,  0, -5},
        new[] {0,  0,  0,  5,  5,  0,  0,  -4}
    };

    private static readonly int[][] QueenTable = {
        new[] {-20,-10,-10, -5, -5,-10,-10,-20},
        new[] {-10,  0,  0,  0,  0,  0,  0,-10},
        new[] {-10,  0,  5,  5,  5,  5,  0,-10},
        new[] {-5,  0,  5,  5,  5,  5,  0, -5},
        new[] {0,  0,  5,  5,  5,  5,  0, -5},
        new[] {-10,  5,  5,  5,  5,  5,  0,-10},
        new[] {-10,  0,  5,  0,  0,  0,  0,-10},
        new[] {-20,-10,-10, -5, -5,-10,-10,-20}
    };

    private static readonly int[][] KingMiddleGame = {
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-30,-40,-40,-50,-50,-40,-40,-30},
        new[] {-20,-30,-30,-40,-40,-30,-30,-20},
        new[] {-10,-20,-20,-20,-20,-20,-20,-10},
        new[] {20, 20,  0,  0,  0,  0, 20, 20},
        new[] {20, 30, 10,  0,  0, 10, 30, 20}
    };

    private static readonly int[][] KingEndGame = {
        new[] {-50,-40,-30,-20,-20,-30,-40,-50},
        new[] {-30,-20,-10,  0,  0,-10,-20,-30},
        new[] {-30,-10, 20, 30, 30, 20,-10,-30},
        new[] {-30,-10, 30, 40, 40, 30,-10,-30},
        new[] {-30,-10, 30, 40, 40, 30,-10,-30},
        new[] {-30,-10, 20, 30, 30, 20,-10,-30},
        new[] {-30,-30,  0,  0,  0,  0,-30,-30},
        new[] {-50,-30,-30,-30,-30,-30,-30,-50}
    };
}