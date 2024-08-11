using ChessChallenge.API;
using System.Linq;
//v0.2
public class MyBot : IChessBot
{
    public Move Think(Board board, Timer timer)
    {
        // Get all legal moves
        Move[] moves = board.GetLegalMoves();

        // Ensure there are legal moves to choose from
        if (moves.Length == 0)
        {
            // Log or handle no available moves (this should be rare in a properly managed game)
            // For now, return a default move or throw an exception
            return Move.NullMove;
        }

        // Prioritize captures
        Move captureMove = moves.FirstOrDefault(m => m.IsCapture);
        if (captureMove != default(Move)) // Use default(Move) to check for a default value
        {
            return captureMove;
        }

        // Prioritize central control (moves towards center)
        Move centerMove = moves
            .OrderByDescending(m => EvaluateCenterControl(m))
            .FirstOrDefault();

        // If there's a move towards the center, return it, otherwise return the first legal move
        return centerMove != default(Move) ? centerMove : moves[0];
    }

    // Evaluate moves that control the center of the board
    private int EvaluateCenterControl(Move move)
    {
        int x = move.TargetSquare.File;
        int y = move.TargetSquare.Rank;

        // Center squares (e4, d4, e5, d5) are most valuable
        int[,] centerValues = new int[8, 8]
        {
            { 0, 0, 0, 0, 0, 0, 0, 0 },
            { 0, 1, 1, 1, 1, 1, 1, 0 },
            { 0, 1, 2, 2, 2, 2, 1, 0 },
            { 0, 1, 2, 3, 3, 2, 1, 0 },
            { 0, 1, 2, 3, 3, 2, 1, 0 },
            { 0, 1, 2, 2, 2, 2, 1, 0 },
            { 0, 1, 1, 1, 1, 1, 1, 0 },
            { 0, 0, 0, 0, 0, 0, 0, 0 }
        };

        // Ensure indexes are within bounds
        if (x < 0 || x >= 8 || y < 0 || y >= 8)
        {
            return 0;
        }
        return centerValues[y, x]; // Use [y, x] to match row/column in a 2D array
    }
}