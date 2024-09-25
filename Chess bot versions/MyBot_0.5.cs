using ChessChallenge.API;
using System;
//v0.5
public class MyBot : IChessBot
{
    // Define a constant for the search depth
    private const int SEARCH_DEPTH = 4;
    bool playerAsWhite;
    Move chosenMove;

    public Move Think(Board board, Timer timer)
    {
        playerAsWhite = board.IsWhiteToMove;
        Minimax(board, SEARCH_DEPTH, int.MinValue, int.MaxValue, playerAsWhite, true);
        return chosenMove;
    }

    int Evaluate(Board board, int depth)
    {
        if (board.IsInCheckmate())
        {
            // Prioritize immediate checkmates
            return board.IsWhiteToMove ? -1000000 - depth : 1000000 + depth;
        }

        if (board.IsDraw())
        {
            // A draw is neutral, return 0
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

        if (isMaximizing)
        {
            bestEvaluation = int.MinValue;

            foreach (Move move in board.GetLegalMoves())
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

            foreach (Move move in board.GetLegalMoves())
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

        return bestEvaluation;
    }
}