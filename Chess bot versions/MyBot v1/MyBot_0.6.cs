using ChessChallenge.API;
using System;
using System.Collections.Generic;
//v0.6
public class MyBot : IChessBot
{
    private const int SEARCH_DEPTH = 3;
    private Move? chosenMove;

    // Data structures for move ordering
    private Dictionary<Move, int> killerMoves = new Dictionary<Move, int>();
    private Dictionary<Move, int> history = new Dictionary<Move, int>();

    public Move Think(Board board, Timer timer)
    {
        Minimax(board, SEARCH_DEPTH, int.MinValue, int.MaxValue, board.IsWhiteToMove, true);
        return chosenMove ?? new Move(); // Return an empty move if no move is chosen
    }

    int Evaluate(Board board, int depth)
    {
        if (board.IsInCheckmate())
        {
            return board.IsWhiteToMove ? -1000000 - depth : 1000000 + depth;
        }

        if (board.IsDraw())
        {
            return 0;
        }

        int material = 0;

        for (int i = 0; i < 64; i++)
        {
            Piece piece = board.GetPiece(new Square(i));
            if (piece.PieceType == PieceType.None) continue;

            int colourMultiplier = piece.IsWhite ? 1 : -1;

            switch (piece.PieceType)
            {
                case PieceType.Pawn:
                    material += 10 * colourMultiplier;
                    break;
                case PieceType.Knight:
                    material += 30 * colourMultiplier;
                    break;
                case PieceType.Bishop:
                    material += 31 * colourMultiplier;
                    break;
                case PieceType.Rook:
                    material += 50 * colourMultiplier;
                    break;
                case PieceType.Queen:
                    material += 90 * colourMultiplier;
                    break;
                case PieceType.King:
                    material += 900 * colourMultiplier;
                    break;
            }

            // Positional bonus for central control
            if (piece.PieceType == PieceType.Pawn)
            {
                if (piece.Square.Rank >= 3 && piece.Square.Rank <= 4 && piece.Square.File >= 3 && piece.Square.File <= 4)
                    material += 2 * colourMultiplier;
            }
            else if (piece.PieceType == PieceType.Knight)
            {
                if (piece.Square.Rank >= 2 && piece.Square.Rank <= 5 && piece.Square.File >= 2 && piece.Square.File <= 5)
                    material += 2 * colourMultiplier;
            }
        }

        // Small bonus for checks
        if (board.IsInCheck())
        {
            material += board.IsWhiteToMove ? -5 : 5;
        }

        return material;
    }

    int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing, bool isRoot)
    {
        if (depth == 0 || board.IsInCheckmate() || board.IsDraw())
            return Evaluate(board, depth);

        int bestEvaluation;
        Move? bestMove = null;
        List<Move> moves = new List<Move>(board.GetLegalMoves());

        // Order moves based on previous success and captures
        moves.Sort((m1, m2) => {
            int score1 = history.ContainsKey(m1) ? history[m1] : 0;
            int score2 = history.ContainsKey(m2) ? history[m2] : 0;

            // Prioritize killer moves
            if (killerMoves.ContainsKey(m1))
                score1 += 5000;
            if (killerMoves.ContainsKey(m2))
                score2 += 5000;

            // Return captures first
            if (m1.IsCapture && !m2.IsCapture)
                return -1;
            if (m2.IsCapture && !m1.IsCapture)
                return 1;

            return score2.CompareTo(score1);
        });

        if (isMaximizing)
        {
            bestEvaluation = int.MinValue;

            foreach (Move move in moves)
            {
                board.MakeMove(move);
                int evaluation = Minimax(board, depth - 1, alpha, beta, false, false);
                board.UndoMove(move);

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
                int evaluation = Minimax(board, depth - 1, alpha, beta, true, false);
                board.UndoMove(move);

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

        return bestEvaluation;
    }
}