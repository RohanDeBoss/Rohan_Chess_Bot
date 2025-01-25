using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

//My2ndBot v0.8.1 use null move reduction change over time again
public class EvilBot : IChessBot
{
    // Constants
    private const bool ConstantDepth = true;
    private const short MaxDepth = 6;
    private const short InfiniteScore = 30000; // Less than 32k to fit into short
    private const int TT_SIZE = 1 << 21; // 2097152 Max size
    private const short TimeSpentFractionofTotal = 25;
    private const byte LMR_THRESHOLD = 2;

    // Static Fields
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 };
    private static TTEntry[] tt = new TTEntry[TT_SIZE];

    // Instance Fields
    private int positionsSearched = 0;
    public int bestScore;
    private Move[] killerMoves = new Move[100 * 2];
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;

    private int GetNullMoveReduction(int depth, bool isEndgame)
    {
        return isEndgame ? 3 : 2;
    }
    private int GetTTIndex(ulong key) => (int)(key & (TT_SIZE - 1));

    private Move EvalLog(Move moveToReturn, Board board, int depth)
    {
        Console.WriteLine(" ");
        Console.WriteLine($"Evil Depth: {depth - 1}");
        Console.WriteLine($"Evil eval: {(board.IsWhiteToMove ? bestScore : -bestScore)}");
        Console.WriteLine($"Evil Positions: {positionsSearched:N0}");
        return moveToReturn;
    }

    public Move Think(Board board, Timer timer)
    {
        Move bestMove = Move.NullMove;
        positionsSearched = 0;
        short depth = 1;
        int previousBestScore = 0;
        Move previousBestMove = Move.NullMove;
        var legalMoves = board.GetLegalMoves();

        // Immediate checkmate check
        foreach (Move move in legalMoves)
        {
            if (IsCheckmateMove(move, board))
                return EvalLog(move, board, 1);
        }
        if (legalMoves.Length == 0) return Move.NullMove;

        const int InitialAspirationWindow = 125;
        const int MaxAspirationDepth = 4;
        const int CheckmateScoreThreshold = 25000;

        int maxTimeForTurn = ConstantDepth ? int.MaxValue :
            (timer.MillisecondsRemaining / TimeSpentFractionofTotal) + (timer.IncrementMilliseconds / 3);

        while ((ConstantDepth && depth <= MaxDepth) || (!ConstantDepth && timer.MillisecondsElapsedThisTurn < maxTimeForTurn))
        {
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

                // Manual move ordering start
                Move[] movesToOrder = legalMoves;
                int[] moveScores = new int[movesToOrder.Length];
                TTEntry ttEntry = tt[GetTTIndex(board.ZobristKey)];

                for (int i = 0; i < movesToOrder.Length; i++)
                {
                    Move move = movesToOrder[i];
                    int score = 0;

                    // Priority 1: TT best move
                    if (move == ttEntry.BestMove)
                        score += 10_000_000;

                    // Priority 2: Previous iteration's best move
                    if (move == previousBestMove)
                        score += 5_000_000;

                    // Regular move ordering score
                    score += MoveOrdering(move, board);
                    moveScores[i] = score;
                }

                // Sort moves by score in descending order
                Array.Sort(moveScores, movesToOrder, Comparer<int>.Create((a, b) => b.CompareTo(a)));
                // Manual move ordering end

                foreach (Move move in movesToOrder)
                {
                    if (!ConstantDepth && timer.MillisecondsElapsedThisTurn >= maxTimeForTurn)
                        return EvalLog(bestMove, board, depth);

                    if (IsCheckmateMove(move, board))
                        return EvalLog(move, board, depth);

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

            previousBestMove = bestMove;
            depth++;
        }

        return EvalLog(bestMove, board, depth);
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
        {
            score += 100000 + GetPieceValue(capturedPiece.PieceType) * 10 -
                     GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
        }

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
        if (positionsSearched % 512 == 0)
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
        positionsSearched++;

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

        // Null Move Pruning (added here)
        if (!board.IsInCheck() && depth > GetNullMoveReduction(depth, IsEndgame(board)))
        {
            board.ForceSkipTurn();
            int reduction = GetNullMoveReduction(depth, IsEndgame(board));
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

            int newDepth = depth - 1;
            if (i >= LMR_THRESHOLD && !move.IsCapture && !board.IsInCheck())
                newDepth -= 1;

            int score;
            if (i == 0) // PV node
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

            if (score > bestScore)
            {
                bestScore = score;
                bestMove = move;
            }

            alpha = Math.Max(alpha, score);
            if (alpha >= beta)
            {
                if (!move.IsCapture)
                {
                    if (i < 2) UpdateKillerMoves(move, ply);
                    UpdateHistoryMove(move, depth); // Restored history update call
                }
                AddTT(key, depth, (short)beta, BETA, move);
                return beta;
            }
        }

        byte flag = bestScore <= originalAlpha ? ALPHA : bestScore >= beta ? BETA : EXACT;
        AddTT(key, depth, (short)bestScore, flag, bestMove);
        return bestScore;
    }

    private int Quiescence(Board board, int alpha, int beta, int ply)
    {
        positionsSearched++;
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
        if (board.IsDraw()) return 0; //Always 0

        int score = 0;
        bool isEndgame = IsEndgame(board);

        foreach (PieceList pieceList in board.GetAllPieceLists())
        {
            int pieceValue = GetPieceValue(pieceList.TypeOfPieceInList);
            int[,] adjustmentTable = GetAdjustmentTable(pieceList.TypeOfPieceInList, isEndgame);
            foreach (Piece piece in pieceList)
            {
                int rank = piece.IsWhite ? 7 - piece.Square.Rank : piece.Square.Rank;
                score += (piece.IsWhite ? 1 : -1) * (adjustmentTable[rank, piece.Square.File] + pieceValue);
            }
        }

        return board.IsWhiteToMove ? score : -score;
    }

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

    private int[,] GetAdjustmentTable(PieceType pieceType, bool isEndgame) =>
        pieceType switch
        {
            PieceType.Pawn => PawnTable,
            PieceType.Knight => KnightTable,
            PieceType.Bishop => BishopTable,
            PieceType.Rook => RookTable,
            PieceType.Queen => QueenTable,
            PieceType.King => isEndgame ? KingEndGame : KingMiddleGame,
            _ => new int[8, 8]
        };

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

    //Piece square table bitboards
    private static readonly int[,] PawnTable = {
        {0,  0,  0,  0,  0,  0,  0,  0},
        {50, 50, 50, 50, 50, 50, 50, 50},
        {12, 10, 20, 30, 30, 20, 11, 10},
        {5,  5, 10, 25, 25, 10,  5,  5},
        {1,  3 ,  6, 21, 22,  0,  0,  0},
        {5, -1,-10,  1,  3,-10, -5,  5},
        {5, 10, 10,-20,-20, 10, 11,  5},
        {0,  0,  0,  0,  0,  0,  0,  0}
    };

    private static readonly int[,] KnightTable = {
        {-50,-40,-30,-30,-30,-30,-40,-50},
        {-40,-20,  0,  0,  0,  0,-20,-40},
        {-30,  0, 10, 15, 15, 10,  0,-30},
        {-30,  5, 15, 20, 20, 15,  5,-30},
        {-30,  0, 15, 20, 20, 15,  0,-30},
        {-30,  5, 10, 15, 15, 10,  5,-30},
        {-40,-20,  0,  5,  5,  0,-20,-40},
        {-50,-40,-30,-30,-30,-30,-40,-50}
    };

    private static readonly int[,] BishopTable = {
        {-20,-10,-10,-10,-10,-10,-10,-20},
        {-10,  0,  0,  0,  0,  0,  0,-10},
        {-10,  0,  5, 10, 10,  5,  0,-10},
        {-10,  5,  5, 10, 10,  5,  5,-10},
        {-10,  0, 10, 10, 10, 10,  0,-10},
        {-10, 10, 10, 10, 10, 10, 10,-10},
        {-10,  5,  0,  0,  0,  0,  5,-10},
        {-20,-10,-10,-10,-10,-10,-10,-20}
    };

    private static readonly int[,] RookTable = {
        {0,   0,  0,  0,  0,  0,  0,  0},
        {0,  10, 10, 10, 10, 10, 10,  5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {0,  0,  0,  5,  5,  0,  0,  -4}
    };

    private static readonly int[,] QueenTable = {
        {-20,-10,-10, -5, -5,-10,-10,-20},
        {-10,  0,  0,  0,  0,  0,  0,-10},
        {-10,  0,  5,  5,  5,  5,  0,-10},
        {-5,  0,  5,  5,  5,  5,  0, -5},
        {0,  0,  5,  5,  5,  5,  0, -5},
        {-10,  5,  5,  5,  5,  5,  0,-10},
        {-10,  0,  5,  0,  0,  0,  0,-10},
        {-20,-10,-10, -5, -5,-10,-10,-20}
    };

    private static readonly int[,] KingMiddleGame = {
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-30,-40,-40,-50,-50,-40,-40,-30},
        {-20,-30,-30,-40,-40,-30,-30,-20},
        {-10,-20,-20,-20,-20,-20,-20,-10},
        {20, 20,  0,  0,  0,  0, 20, 20},
        {20, 30, 10,  0,  0, 10, 30, 20}
    };

    private static readonly int[,] KingEndGame = {
        {-50,-40,-30,-20,-20,-30,-40,-50},
        {-30,-20,-10,  0,  0,-10,-20,-30},
        {-30,-10, 20, 30, 30, 20,-10,-30},
        {-30,-10, 30, 40, 40, 30,-10,-30},
        {-30,-10, 30, 40, 40, 30,-10,-30},
        {-30,-10, 20, 30, 30, 20,-10,-30},
        {-30,-30,  0,  0,  0,  0,-30,-30},
        {-50,-30,-30,-30,-30,-30,-30,-50}
    };
}