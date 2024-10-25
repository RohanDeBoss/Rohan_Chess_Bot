using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

//My2ndBot v0.2 Working on tt's.
public class EvilBot : IChessBot
{
    private const int MaxDepth = 4;
    private const int QuiescenceDepthLimit = 5; // Adjust this value as needed


    private const int InfiniteScore = 1000000;
    private int positionsSearched = 0;

    public int bestScore;
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 0 };

    public Move Think(Board board, Timer timer)
    {
        Move bestMove = Move.NullMove;
        int depth = 1;
        bestScore = -InfiniteScore;
        positionsSearched = 0;

        // Get legal moves count - if only one move, return it immediately
        var legalMoves = board.GetLegalMoves();
        if (legalMoves.Length == 1)
        {
            return legalMoves[0];
        }

        // Iterative deepening loop
        while (depth <= MaxDepth)
        {
            bool foundLegalMove = false;  // Track if we've found at least one legal move
            var orderedMoves = legalMoves.OrderByDescending(move => MoveOrdering(move, board)).ToList();
            foreach (Move move in orderedMoves)
            {
                if (IsCheckmateMove(move, board))
                {
                    // Play the checkmate move immediately
                    return move;
                }

                board.MakeMove(move);

                int score = -Negamax(board, depth - 1, -InfiniteScore, InfiniteScore);
                board.UndoMove(move);

                if (score > bestScore || !foundLegalMove)
                {
                    bestScore = score;
                    bestMove = move;
                    foundLegalMove = true;
                }

                // Time control
                if (timer.MillisecondsElapsedThisTurn >= timer.MillisecondsRemaining / 30)
                {
                    break;
                }
            }


            // If we're in checkmate or stalemate, stop searching
            if (!foundLegalMove)
            {
                break;
            }

            depth++;
        }

        // Final safety check - if the best move is null, pick any legal move
        if (bestMove == Move.NullMove && legalMoves.Length > 0)
        {
            bestMove = legalMoves[0];
        }

        Console.WriteLine(" ");
        Console.WriteLine($"EvilBot Depth: {depth - 1}");
        Console.WriteLine($"EvilBot eval: {(board.IsWhiteToMove ? bestScore : -bestScore)}");
        Console.WriteLine($"EvilBot Positions searched: {positionsSearched}");

        return bestMove;
    }

    private int[,] historyHeuristic = new int[64, 64]; // For history moves
    private Move[] killerMoves = new Move[2]; // For killer moves

    private int MoveOrdering(Move move, Board board)
    {
        int score = 0;

        //Best move no dought
        if (IsCheckmateMove(move, board))
        {
            return InfiniteScore; // or some very high value
        }

        // 1. MVV-LVA heuristic for captures
        PieceType capturedPieceType = board.GetPiece(move.TargetSquare).PieceType;
        if (capturedPieceType != PieceType.None)
        {
            int attackerValue = GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
            int victimValue = GetPieceValue(capturedPieceType);
            score += 10 * victimValue - attackerValue; // Higher value for capturing higher-value pieces
        }

        // 2. Promotion moves get a high score
        if (move.IsPromotion)
        {
            score += GetPieceValue(move.PromotionPieceType) + 1000; // Prioritize queen promotions
        }

        // 3. Killer moves heuristic
        if (move == killerMoves[0] || move == killerMoves[1])
        {
            score += 900; // Prioritize killer moves that caused beta cutoffs
        }

        // 4. History heuristic: prioritize frequently good moves
        score += historyHeuristic[move.StartSquare.Index, move.TargetSquare.Index];

        // 5. Penalize moves that move pieces to attacked squares
        if (board.SquareIsAttackedByOpponent(move.TargetSquare))
        {
            score -= GetPieceValue(board.GetPiece(move.StartSquare).PieceType);
        }

        return score;
    }

    private bool IsCheckmateMove(Move move, Board board)
    {
        board.MakeMove(move);
        bool isCheckmate = board.IsInCheckmate();
        board.UndoMove(move);
        return isCheckmate;
    }

    private int Quiescence(Board board, int alpha, int beta, int depth)
    {
        positionsSearched++;

        if (depth <= 0)
            return Evaluate(board, depth);

        int stand_pat = Evaluate(board, depth);
        if (stand_pat >= beta)
            return beta;
        if (alpha < stand_pat)
            alpha = stand_pat;
        var captureMoves = board.GetLegalMoves(true).OrderByDescending(move => MoveOrdering(move, board)).ToList();
        foreach (Move move in captureMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, depth - 1);
            board.UndoMove(move);

            if (score >= beta)
                return beta;
            if (score > alpha)
                alpha = score;
        }
        return alpha;
    }

    private int Negamax(Board board, int depth, int alpha, int beta)
    {
        positionsSearched++;  // Increment the positions counter

        if (board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        if (depth == 0)
            return Quiescence(board, alpha, beta, QuiescenceDepthLimit);


        int bestScore = -InfiniteScore;
        Move bestMove = Move.NullMove;
        List<Move> moves = board.GetLegalMoves().OrderByDescending(move => MoveOrdering(move, board)).ToList();

        foreach (Move move in moves)
        {
            if (IsCheckmateMove(move, board))
            {
                // Return immediately if checkmate is found
                return InfiniteScore;
            }

            board.MakeMove(move);
            int score = -Negamax(board, depth - 1, -beta, -alpha);
            board.UndoMove(move);

            if (score > bestScore)
            {
                bestScore = score;
                bestMove = move;
            }

            alpha = Math.Max(alpha, score);
            if (alpha >= beta)
            {
                // Store the killer move if beta cutoff occurs
                killerMoves[1] = killerMoves[0];
                killerMoves[0] = move;

                // Update the history heuristic
                historyHeuristic[move.StartSquare.Index, move.TargetSquare.Index] += depth * depth;

                break; // Beta cutoff
            }
        }

        return bestScore;
    }

    private int Evaluate(Board board, int depth)
    {
        if (board.IsInCheckmate())
            return -InfiniteScore - depth;

        if (board.IsDraw())
            return 0;

        int score = 0;
        bool isEndgame = IsEndgame(board);
        PieceList[] pieceLists = board.GetAllPieceLists();

        foreach (PieceList pieceList in pieceLists)
        {
            int pieceValue = GetPieceValue(pieceList.TypeOfPieceInList);
            int[,] adjustmentTable = GetAdjustmentTable(pieceList.TypeOfPieceInList, isEndgame);

            foreach (Piece piece in pieceList)
            {
                Square square = piece.Square;
                int file = square.File;
                int rank = piece.IsWhite ? 7 - square.Rank : square.Rank;

                int value = adjustmentTable[rank, file] + pieceValue;
                score += piece.IsWhite ? value : -value;
            }
        }

        return board.IsWhiteToMove ? score : -score;
    }


    private int GetPieceValue(PieceType pieceType)
    {
        switch (pieceType)
        {
            case PieceType.Pawn:
                return PieceValues[0];
            case PieceType.Knight:
                return PieceValues[1];
            case PieceType.Bishop:
                return PieceValues[2];
            case PieceType.Rook:
                return PieceValues[3];
            case PieceType.Queen:
                return PieceValues[4];
            case PieceType.King:
                return PieceValues[5];
            default:
                Console.WriteLine($"Warning: Unknown piece type {pieceType}");
                return 0;
        }
    }

    private int[,] GetAdjustmentTable(PieceType pieceType, bool isEndgame)
    {
        switch (pieceType)
        {
            case PieceType.Pawn:
                return PawnTable;
            case PieceType.Knight:
                return KnightTable;
            case PieceType.Bishop:
                return BishopTable;
            case PieceType.Rook:
                return RookTable;
            case PieceType.Queen:
                return QueenTable;
            case PieceType.King:
                return isEndgame ? KingEndGame : KingMiddleGame;
            default:
                return new int[8, 8];
        }
    }

    private bool IsEndgame(Board board)
    {
        int pieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
        return pieceCount <= 10; // You can adjust this threshold as needed
    }



    private static readonly int[,] PawnTable = {
        {0,  0,  0,  0,  0,  0,  0,  0},
        {50, 50, 50, 50, 50, 50, 50, 50},
        {10, 10, 20, 30, 30, 20, 10, 10},
        {5,  5, 10, 25, 25, 10,  5,  5},
        {0,  0,  0, 20, 20,  0,  0,  0},
        {5, -5,-10,  0,  0,-10, -5,  5},
        {5, 10, 10,-20,-20, 10, 10,  5},
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
        {0,  0,  0,  0,  0,  0,  0,  0},
        {5, 10, 10, 10, 10, 10, 10,  5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {-5,  0,  0,  0,  0,  0,  0, -5},
        {0,  0,  0,  5,  5,  0,  0,  0}
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