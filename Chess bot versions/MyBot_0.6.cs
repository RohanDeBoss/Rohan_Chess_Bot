using ChessChallenge.API;
using System;
//v0.6
public class MyBot : IChessBot
{
    bool playerAsWhite;
    Move chosenMove;

    public Move Think(Board board, Timer timer)
    {
        playerAsWhite = board.IsWhiteToMove;
        Minimax(board, 4, int.MinValue, int.MaxValue, playerAsWhite);
        return chosenMove;
    }

    int Evaluate(Board board)
    {
        if (IsCheckmate(board, playerAsWhite))
        {
            // Positive score for checkmating the opponent
            return int.MaxValue;
        }
        if (IsCheckmate(board, !playerAsWhite))
        {
            // Negative score for being checkmated
            return int.MinValue;
        }

        int material = 0;

        for (int i = 0; i < 64; i++)
        {
            Piece piece = board.GetPiece(new Square(i));
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
        }
        return material;
    }

    bool IsCheckmate(Board board, bool playerToCheck)
    {
        // Use the current player or the specified player
        bool isInCheck = board.IsInCheck();
        bool hasLegalMoves = board.GetLegalMoves().Length > 0;

        return isInCheck && !hasLegalMoves;
    }

    int Minimax(Board board, int depth, int alpha, int beta, bool isMaximizing)
    {
        if (depth == 0 || board.GetLegalMoves().Length == 0)
            return Evaluate(board);

        Move bestMove = board.GetLegalMoves()[0];  // Initialize with the first legal move

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