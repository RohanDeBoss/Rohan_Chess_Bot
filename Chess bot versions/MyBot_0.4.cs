using ChessChallenge.API;
using System;
//v0.4
public class MyBot : IChessBot
{
    bool playerAsWhite;
    Move chosenMove;

    public Move Think(Board board, Timer timer)
    {
        Move[] moves = board.GetLegalMoves();
        playerAsWhite = board.IsWhiteToMove;

        Minimax(board, 3, int.MinValue, int.MaxValue, playerAsWhite);
        return chosenMove;
    }

    int Evaluate(Board board)
    {
        int material = 0;

        for (int i = 0; i < 64; i++)
        {
            Piece piece = board.GetPiece(new Square(i));
            int colourMultiplier = (piece.IsWhite) ? 1 : -1;

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

            if (piece.IsPawn && piece.Square.Rank >= 3 && piece.Square.Rank <= 4 && piece.Square.File >= 3 && piece.Square.File <= 4)
                material += 2 * colourMultiplier;

            if (piece.IsKnight && piece.Square.Rank >= 2 && piece.Square.Rank <= 5 && piece.Square.File >= 2 && piece.Square.File <= 5)
                material += 2 * colourMultiplier;

            // Adding positional value for the King
            if (piece.IsKing)
            {
                if (piece.IsWhite && piece.Square.Rank == 1)
                    material += 2 * colourMultiplier;
                else if (!piece.IsWhite && piece.Square.Rank == 8)
                    material += 2 * colourMultiplier;
            }
        }
        return material;
    }

    int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing)
    {
        if (depth == 0 || board.GetLegalMoves().Length == 0)
            return Evaluate(board);

        Move bestMove = board.GetLegalMoves()[0];
        if (isMaximizing)
        {
            int bestEvaluation = int.MinValue;

            foreach (Move move in board.GetLegalMoves())
            {
                board.MakeMove(move);
                int evaluation = Minimax(board, depth - 1, alpha, beta, false);
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
            chosenMove = bestMove;
            return bestEvaluation;
        }
        else
        {
            int bestEvaluation = int.MaxValue;

            foreach (Move move in board.GetLegalMoves())
            {
                board.MakeMove(move);
                int evaluation = Minimax(board, depth - 1, alpha, beta, true);
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
            chosenMove = bestMove;
            return bestEvaluation;
        }
    }
}