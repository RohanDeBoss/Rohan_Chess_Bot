using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;

// MyBot v0.3 - Code Simplification & Optimization
// Changes:
// - Evaluate: Refactored main loop to reduce branching and optimize logic flow.
// - OrderMoves: Switched to stackalloc (Span<T>) to remove heap allocations.
// - IsEndgame: Simplified to intrinsic PopCount.

public class EvilBot : IChessBot
{
    // --- Configuration ---
    private static readonly bool PerMoveDebugging = true;
    private static readonly bool PerDepthDebugging = false;
    private static readonly bool ConstantDepth = true;
    private static readonly short MaxDepth = 5;
    private static readonly bool UseFixedTimePerMove = false;
    private static readonly int FixedTimePerMoveMs = 500;

    // --- Core Constants ---
    private const short MaxSafetyDepth = 999;
    private const int InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22;
    private const int MAX_KILLER_PLY = 256;
    private const int MATE_FOUND_SCORE = 29000;

    // --- Time Management & Aspiration Windows ---
    private const int INITIAL_ASPIRATION_WINDOW = 150;
    private const int MAX_ASPIRATION_DEPTH = 4;
    private const int SAFETY_MARGIN = 10;
    private const int TIME_CHECK_NODES = 2048;
    private const int TIME_CHECK_MASK = TIME_CHECK_NODES - 1;


    // -- TUNABLE SEARCH & EVAL PARAMETERS --

    // Piece Values (P, N, B, R, Q, K)
    private static readonly int[] MG_PieceValues = { 100, 305, 310, 500, 900, 0 };
    private static readonly int[] EG_PieceValues = { 120, 290, 305, 510, 950, 0 };

    // -- Piece Square Tables (Perspective of White, Black's are flipped via XOR 56) --
    private static readonly int[] PawnPST = {
          0,   0,   0,   0,   0,   0,   0,   0,
          5,  10,  10, -20, -20,  10,  11,   5,
          5,  -1, -10,   1,   3, -10,   0,   5,
          1,   3,   6,  21,  22,   0,   0,   0,
          5,   5,  10,  25,  25,  10,   5,   5,
         12,  10,  20,  30,  30,  20,  11,  10,
         50,  50,  50,  50,  50,  50,  50,  50,
          0,   0,   0,   0,   0,   0,   0,   0
    };
    private static readonly int[] KnightPST = {
        -50, -40, -30, -30, -30, -30, -40, -50,
        -40, -20,   0,   5,   5,   0, -20, -40,
        -30,   5,  10,  15,  15,  10,   5, -30,
        -30,   0,  15,  20,  20,  15,   0, -30,
        -30,   5,  15,  20,  20,  15,   5, -30,
        -30,   0,  10,  15,  15,  10,   0, -30,
        -40, -20,  -3,   0,   0,  -3, -20, -40,
        -50, -40, -30, -30, -30, -30, -40, -50
    };
    private static readonly int[] BishopPST = {
        -20, -10, -10, -10, -10, -10, -10, -20,
        -10,   5,   0,   0,   0,   0,   5, -10,
        -10,  10,  10,  10,  10,  10,  10, -10,
        -10,   0,  10,  10,  10,  10,   0, -10,
        -10,   5,   5,  10,  10,   5,   5, -10,
        -10,   0,   5,  10,  10,   5,   0, -10,
        -10,   0,   0,   0,   0,   0,   0, -10,
        -20, -10, -10, -10, -10, -10, -10, -20
    };
    private static readonly int[] RookPST = {
          0,   0,   0,   5,   5,   0,   0,  -4,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
         -5,   0,   0,   0,   0,   0,   0,  -5,
          0,  10,  10,  10,  10,  10,  10,   5,
          0,   0,   0,   0,   0,   0,   0,   0
    };
    private static readonly int[] QueenPST = {
        -20, -10, -10,  -5,  -5, -10, -10, -20,
        -10,   0,   5,   0,   0,   0,   0, -10,
        -10,   5,   5,   5,   5,   5,   0, -10,
          0,   0,   5,   5,   5,   5,   0,  -5,
         -5,   0,   5,   5,   5,   5,   0,  -5,
        -10,   0,   5,   5,   5,   5,   0, -10,
        -10,   0,   0,   0,   0,   0,   0, -10,
        -20, -10, -10,  -5,  -5, -10, -10, -20
    };
    private static readonly int[] KingMiddleGamePST = {
         20,  30,  10,   0,   0,  10,  30,  20,
         20,  20,   0,   0,   0,   0,  20,  20,
        -10, -20, -20, -20, -20, -20, -20, -10,
        -20, -30, -30, -40, -40, -30, -30, -20,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30
    };
    private static readonly int[] KingEndGamePST = {
        -30, -20, -20, -20, -20, -20, -20, -30,
        -20, -15, -10,   0,   0, -10, -10, -20,
        -20, -10,  15,  20,  15,  15, -10, -20,
        -20, -10,  15,  18,  18,  15, -10, -20,
        -20, -10,  15,  18,  18,  15, -10, -20,
        -20, -10,  10,  15,  15,  15, -10, -20,
        -20, -15, -10,  -5,  -5, -10, -15, -20,
        -30, -25, -20, -15, -15, -20, -25, -30
    };

    // Index via PieceType: None, Pawn, Knight, Bishop, Rook, Queen (King separate)
    private static readonly int[][] PiecePSTs = {
        Array.Empty<int>(), PawnPST, KnightPST, BishopPST, RookPST, QueenPST
    };

    // HCE Constants
    private const int KING_ATTACK_BASE_BONUS = 20;  // +0.2
    private const int KING_ATTACK_EXTRA_BONUS = 10; // +0.1
    private const int BISHOP_MOBILITY_BONUS = 3;

    // King Safety (MG Only)
    private const int KING_SAFETY_EXPOSURE_PENALTY = 1; // -0.01 per open pseudo-queen square

    // Rook HCE
    private const int ROOK_MOBILITY_EG = 2;
    private const int ROOK_OPEN_FILE_MG = 10;
    private const int ROOK_OPEN_FILE_EG = 25;
    private const int ROOK_SEMI_OPEN_FILE_MG = 5;
    private const int ROOK_SEMI_OPEN_FILE_EG = 15;

    // Endgame King Proximity
    private const int ENDGAME_MAT_THRESHOLD = 1000; // 10 points
    private const int KING_PROXIMITY_PENALTY = 4;   // -0.04 per dist

    // Phase weights for tapering
    private const int KnightPhase = 1;
    private const int BishopPhase = 1;
    private const int RookPhase = 2;
    private const int QueenPhase = 4;
    private const int TotalPhase = 24;
    private static readonly int[] SeePieceValues = { 100, 305, 310, 500, 900, 20000 };

    // Pawn Structure Evaluation
    private const int DOUBLED_PAWN_PENALTY = -10;
    private const int ISOLATED_PAWN_PENALTY = -15;
    private const int PASSED_PAWN_BASE_BONUS = 20;
    private const int PASSED_PAWN_RANK_BONUS = 15;

    // Move Ordering Bonuses 
    private const int TT_MOVE_BONUS = 10_000_000;
    private const int PREVIOUS_BEST_MOVE_BONUS = 5_000_000;
    private const int PROMOTION_BASE_BONUS = 1_100_000;
    private const int KILLER_MOVE_BONUS = 900_000;
    private const int HISTORY_MAX_BONUS = 800_000;
    private const int GOOD_CAPTURE_BONUS = 2_000_000;
    private const int LOSING_CAPTURE_BONUS = 100_000;

    // --- Search Heuristics ---
    private const int NMP_MIN_DEPTH = 3;
    private const int NMP_R_BASE = 2;
    private const int NMP_R_DEEP_DEPTH = 6;
    private const int NMP_R_DEEP_REDUCTION = 3;

    private const int LMR_MIN_DEPTH = 3;
    private const int LMR_MIN_MOVE_COUNT = 2;
    private const double LMR_LOG_DIVISOR = 2.0;

    private const int LME_AMOUNT = 1;

    private const int LATE_MOVE_PRUNING_COUNT = 3;
    private const int FUTILITY_PRUNING_MAX_DEPTH = 4;
    private const int FUTILITY_MARGIN_PER_PLY = 120;

    private const int Q_SEE_PRUNING_MARGIN = -30;
    private const int SEE_PRUNING_MARGIN = -30;
    private const bool ENABLE_SEE_REDUCTIONS = true;
    private const int SEE_REDUCTION_MIN_DEPTH = 3;
    private const int SEE_REDUCTION_DEEP = 3;
    private const int SEE_REDUCTION_SHALLOW = 2;

    // Static Fields
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = TT_SIZE - 1;
    private int lastGamePlyCount = -1;

    // Instance Fields
    private long negamaxPositions, qsearchPositions;
    private int bestScoreRoot;
    private Move[,] killerMoves = new Move[MAX_KILLER_PLY, 2];
    private int[,] historyMoves = new int[64, 64];
    private int completedSearchDepth;
    private Timer currentTimer;
    private volatile bool timeIsUp;
    private long absoluteTimeLimit;
    private bool isWhitePlayer;

    private static readonly DescendingIntComparer _descendingIntComparer = new DescendingIntComparer();
    private class DescendingIntComparer : IComparer<int>
    {
        public int Compare(int x, int y) => y.CompareTo(x);
    }

    public Move Think(Board board, Timer timer)
    {
        if (board.PlyCount < lastGamePlyCount)
        {
            Array.Clear(tt, 0, TT_SIZE);
        }
        lastGamePlyCount = board.PlyCount;

        currentTimer = timer;
        timeIsUp = false;
        isWhitePlayer = board.IsWhiteToMove;

        if (timer.MillisecondsRemaining <= 0 && !ConstantDepth)
        {
            var moves = board.GetLegalMoves();
            return moves.Length > 0 ? moves[0] : Move.NullMove;
        }

        Array.Clear(killerMoves, 0, killerMoves.Length);
        Array.Clear(historyMoves, 0, historyMoves.Length);
        negamaxPositions = 0; qsearchPositions = 0; completedSearchDepth = 0;
        bestScoreRoot = 0;

        short currentIterativeDepth = 1;
        int scoreFromPrevIteration = 0;
        Move bestMoveFromPrevIteration = Move.NullMove;

        var legalMoves = board.GetLegalMoves();
        if (legalMoves.Length == 0)
        {
            bestScoreRoot = board.IsInCheck() ? -InfiniteScore : 0;
            completedSearchDepth = MaxSafetyDepth;
            return LogEval(board, completedSearchDepth, false, Move.NullMove);
        }
        Move bestMoveOverall = legalMoves[0];
        if (legalMoves.Length == 1)
        {
            return HandleForcedMove(legalMoves[0], board, 0, true);
        }

        if (PerDepthDebugging)
        {
            Console.WriteLine("");
            DebugLog(ConstantDepth ? $"Starting constant depth search to {MaxDepth}:" : "Starting timed search:");
        }

        absoluteTimeLimit = timer.MillisecondsElapsedThisTurn + AllocateTime(timer);
        Move bestMoveThisIteration = bestMoveOverall;

        while (currentIterativeDepth <= MaxSafetyDepth && (ConstantDepth ? currentIterativeDepth <= MaxDepth : true))
        {
            if (timeIsUp || (!ConstantDepth && currentTimer.MillisecondsElapsedThisTurn >= absoluteTimeLimit - SAFETY_MARGIN * 2)) break;

            bool useAspiration = currentIterativeDepth > MAX_ASPIRATION_DEPTH && Math.Abs(scoreFromPrevIteration) < MATE_FOUND_SCORE;
            int alpha = useAspiration ? scoreFromPrevIteration - INITIAL_ASPIRATION_WINDOW : -InfiniteScore;
            int beta = useAspiration ? scoreFromPrevIteration + INITIAL_ASPIRATION_WINDOW : InfiniteScore;
            int aspirationWindowSize = INITIAL_ASPIRATION_WINDOW;
            bool aspirationSearchFailed;
            int scoreThisAspirationLoop;

            do
            {
                aspirationSearchFailed = false;
                scoreThisAspirationLoop = -InfiniteScore;
                Move currentBestMoveInLoopAttempt = bestMoveFromPrevIteration;
                if (currentBestMoveInLoopAttempt.IsNull) currentBestMoveInLoopAttempt = legalMoves[0];
                Move[] movesToOrder = OrderMoves(legalMoves, board, 0, bestMoveFromPrevIteration);
                if (movesToOrder.Length > 0 && currentBestMoveInLoopAttempt.IsNull) currentBestMoveInLoopAttempt = movesToOrder[0];

                for (int i = 0; i < movesToOrder.Length; i++)
                {
                    Move move = movesToOrder[i];
                    board.MakeMove(move);
                    int score = -Negamax(board, currentIterativeDepth - 1, -beta, -alpha, 1, 1);
                    board.UndoMove(move);
                    if (timeIsUp) goto EndRootMoveLoop_ID;
                    if (score > scoreThisAspirationLoop)
                    {
                        scoreThisAspirationLoop = score;
                        currentBestMoveInLoopAttempt = move;
                        alpha = Math.Max(alpha, score);
                    }
                    if (alpha >= beta)
                    {
                        if (useAspiration) aspirationSearchFailed = true;
                        break;
                    }
                }
            EndRootMoveLoop_ID:;
                if (timeIsUp) break;
                if (aspirationSearchFailed)
                {
                    if (scoreThisAspirationLoop <= (scoreFromPrevIteration - aspirationWindowSize)) { alpha = -InfiniteScore; beta = scoreThisAspirationLoop + aspirationWindowSize; }
                    else { alpha = scoreThisAspirationLoop - aspirationWindowSize; beta = InfiniteScore; }
                    aspirationWindowSize *= 2;
                }
                else
                {
                    scoreFromPrevIteration = scoreThisAspirationLoop;
                    bestScoreRoot = scoreThisAspirationLoop;
                    if (!currentBestMoveInLoopAttempt.IsNull) bestMoveThisIteration = currentBestMoveInLoopAttempt;
                    else if (movesToOrder.Length > 0) bestMoveThisIteration = movesToOrder[0];
                    else bestMoveThisIteration = legalMoves[0];
                }
            } while (aspirationSearchFailed && !timeIsUp && aspirationWindowSize < InfiniteScore / 2);

            if (timeIsUp) break;

            if (!bestMoveThisIteration.IsNull)
            {
                bestMoveOverall = bestMoveThisIteration;
                bestMoveFromPrevIteration = bestMoveOverall;
                completedSearchDepth = currentIterativeDepth;
                if (PerDepthDebugging)
                {
                    long totalNodes = negamaxPositions + qsearchPositions;
                    string timeDisplay = currentTimer.MillisecondsElapsedThisTurn <= 9999 ? $"{currentTimer.MillisecondsElapsedThisTurn}ms" : $"{(currentTimer.MillisecondsElapsedThisTurn / 1000.0):F1}s";
                    string nodesDisplay = totalNodes < 10000 ? $"{totalNodes}" : totalNodes < 10000000 ? $"{(totalNodes / 1000.0):F1}k" : $"{(totalNodes / 1000000.0):F1}m";
                    int displayScore = isWhitePlayer ? bestScoreRoot : -bestScoreRoot;
                    DebugLog($"Depth {currentIterativeDepth}, Score {displayScore}, BestMove {bestMoveOverall}, Nodes {nodesDisplay}, Time {timeDisplay}");
                }
            }
            else { break; }
            currentIterativeDepth++;
        }

        if (bestMoveOverall.IsNull && legalMoves.Length > 0) bestMoveOverall = legalMoves[0];

        if (Math.Abs(bestScoreRoot) >= MATE_FOUND_SCORE)
        {
            int pliesToMate = InfiniteScore - Math.Abs(bestScoreRoot);
            completedSearchDepth = MaxSafetyDepth - pliesToMate;
        }

        return LogEval(board, completedSearchDepth, false, bestMoveOverall);
    }

    private Move LogEval(Board board, int depthCompleted, bool isForcedMove, Move moveForThisTurn)
    {
        if (PerMoveDebugging)
        {
            if (isForcedMove)
            {
                Console.WriteLine($"\n{GetType().Name}: FORCED MOVE! ({moveForThisTurn})");
            }
            else if (currentTimer != null)
            {
                Console.WriteLine();
                string mateInfo = GetMateInMoves(bestScoreRoot);
                int evalForDisplay = isWhitePlayer ? bestScoreRoot : -bestScoreRoot;
                string npsDisplay = currentTimer.MillisecondsElapsedThisTurn > 0 ? $"{((negamaxPositions + qsearchPositions) / (currentTimer.MillisecondsElapsedThisTurn / 1000.0) / 1000):F0}knps" : "0knps";

                DebugLog($"Depth: {depthCompleted}");
                DebugLog(mateInfo ?? "No mate found");
                DebugLog($"Eval: {evalForDisplay}");
                DebugLog($"Nodes: {negamaxPositions + qsearchPositions:N0}");
                DebugLog($"NPS: {npsDisplay}");
            }
        }
        return moveForThisTurn;
    }

    private short GetTimeSpentFraction(Timer timer)
    {
        int t = timer.MillisecondsRemaining;
        int result = 20 + 99900 / (t + 1675);
        return (short)Math.Max(26, Math.Min(65, result));
    }

    private int AllocateTime(Timer timer)
    {
        if (ConstantDepth) return int.MaxValue;
        if (UseFixedTimePerMove) return Math.Max(1, Math.Min(FixedTimePerMoveMs, timer.MillisecondsRemaining - SAFETY_MARGIN));

        short timeFraction = Math.Max(GetTimeSpentFraction(timer), (short)1);
        int allocated = (timer.MillisecondsRemaining / timeFraction) + (timer.IncrementMilliseconds / 2);
        allocated = Math.Max(10, allocated - SAFETY_MARGIN);
        allocated = Math.Min(allocated, timer.MillisecondsRemaining - SAFETY_MARGIN);
        return Math.Max(1, allocated);
    }

    private string GetMateInMoves(int score)
    {
        if (Math.Abs(score) < MATE_FOUND_SCORE) return null;
        int pliesToMate = InfiniteScore - Math.Abs(score);
        int movesToMate = (pliesToMate + 1) / 2;
        return $"{(Math.Sign(score) > 0 ? "Winning" : "Losing")} Mate in {movesToMate} moves ({pliesToMate} ply)";
    }

    private int Negamax(Board board, int depth, int alpha, int beta, int ply, int realPly)
    {
        CheckTime();
        if (timeIsUp) return 0;
        negamaxPositions++;
        if (board.IsDraw()) return 0;

        alpha = Math.Max(alpha, -InfiniteScore + realPly);
        beta = Math.Min(beta, InfiniteScore - realPly);
        if (alpha >= beta) return alpha;

        ulong key = board.ZobristKey;
        int index = GetTTIndex(key);
        TTEntry ttEntry = tt[index];
        bool ttHit = ttEntry.Key == key;
        Move ttMove = ttHit ? ttEntry.BestMove : Move.NullMove;

        if (ttHit && ttEntry.Depth >= depth)
        {
            short scoreFromTT = AdjustMateScoreFromTT(ttEntry.Score, realPly);
            if (ttEntry.Flag == EXACT) return scoreFromTT;
            if (ttEntry.Flag == ALPHA && scoreFromTT <= alpha) return alpha;
            if (ttEntry.Flag == BETA && scoreFromTT >= beta) return beta;
        }

        if (depth <= 0)
        {
            return Quiescence(board, alpha, beta, ply, 0, realPly);
        }

        Move[] moves = board.GetLegalMoves();
        if (moves.Length == 0)
        {
            return board.IsInCheck() ? (-InfiniteScore + realPly) : 0;
        }

        int standPat = 0;
        bool inCheck = board.IsInCheck();
        if (!inCheck) standPat = Evaluate(board);
        bool inMateZone = Math.Abs(standPat) >= MATE_FOUND_SCORE;

        // --- HEURISTIC 1: REVERSE FUTILITY PRUNING ---
        if (!inCheck && !inMateZone && depth <= FUTILITY_PRUNING_MAX_DEPTH)
        {
            if (standPat - FUTILITY_MARGIN_PER_PLY * depth >= beta) return beta;
        }

        if (!inCheck && depth >= NMP_MIN_DEPTH && ply > 0 && !IsEndgame(board) && !inMateZone)
        {
            board.ForceSkipTurn();
            int R = depth > NMP_R_DEEP_DEPTH ? NMP_R_DEEP_REDUCTION : NMP_R_BASE;
            int nullScore = -Negamax(board, depth - R - 1, -beta, -beta + 1, ply + 1, realPly + 1);
            board.UndoSkipTurn();
            if (timeIsUp) return 0;
            if (nullScore >= beta) return beta;
        }

        moves = OrderMoves(moves, board, ply, ttMove);
        int originalAlpha = alpha;
        Move bestMoveCurrentNode = Move.NullMove;
        int localBestScore = -InfiniteScore;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            bool isQuiet = !move.IsCapture && !move.IsPromotion;

            // --- HEURISTIC 2: LATE MOVE PRUNING ---
            if (!inCheck && !inMateZone && isQuiet)
            {
                if (depth <= LATE_MOVE_PRUNING_COUNT && i >= LATE_MOVE_PRUNING_COUNT &&
                    alpha == originalAlpha && standPat + FUTILITY_MARGIN_PER_PLY * depth < alpha)
                {
                    continue;
                }
            }

            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();
            int newDepth = depth - 1;

            if (givesCheck || (move.MovePieceType == PieceType.Pawn && (move.TargetSquare.Rank is 1 or 6)))
            {
                newDepth += LME_AMOUNT;
            }

            int score;

            // SEE-based Reductions
            if (ENABLE_SEE_REDUCTIONS && depth >= SEE_REDUCTION_MIN_DEPTH && move.IsCapture && !isQuiet && !inCheck)
            {
                if (CalculateSEE(board, move) < SEE_PRUNING_MARGIN)
                {
                    int seeReduction = (depth > 5) ? SEE_REDUCTION_DEEP : SEE_REDUCTION_SHALLOW;
                    int reducedDepth = Math.Max(newDepth - seeReduction, 1);
                    score = -Negamax(board, reducedDepth, -alpha - 1, -alpha, ply + 1, realPly + 1);
                    if (score > alpha && !timeIsUp) score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
                    goto AfterSearch;
                }
            }

            // Late Move Reductions (LMR)
            bool useLMR = depth >= LMR_MIN_DEPTH && i >= LMR_MIN_MOVE_COUNT && isQuiet && !givesCheck && !inMateZone && !IsKillerMove(move, ply);
            if (useLMR)
            {
                int reduction = (int)(0.75 + Math.Log(depth) * Math.Log(i + 1) / LMR_LOG_DIVISOR);
                if (historyMoves[move.StartSquare.Index, move.TargetSquare.Index] > 0) reduction--;
                int reducedDepth = Math.Max(newDepth - Math.Max(0, reduction), 1);
                score = -Negamax(board, reducedDepth, -alpha - 1, -alpha, ply + 1, realPly + 1);
                if (score > alpha && score < beta && !timeIsUp) score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }
            else
            {
                score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);
            }

        AfterSearch:
            board.UndoMove(move);
            if (timeIsUp) return 0;

            if (score > localBestScore)
            {
                localBestScore = score;
                bestMoveCurrentNode = move;
                alpha = Math.Max(alpha, score);
                if (alpha >= beta)
                {
                    if (isQuiet) { UpdateKillerMoves(move, ply); UpdateHistoryMove(move, depth * depth); }
                    AddTT(key, depth, AdjustMateScoreForTTStorage(beta, realPly), BETA, move);
                    return beta;
                }
            }
        }

        byte flag = localBestScore <= originalAlpha ? ALPHA : EXACT;
        AddTT(key, depth, AdjustMateScoreForTTStorage(localBestScore, realPly), flag, bestMoveCurrentNode);
        return localBestScore;
    }

    private int Quiescence(Board board, int alpha, int beta, int ply, int qDepth, int realPly)
    {
        qsearchPositions++;
        if (timeIsUp) return 0;

        bool inCheck = board.IsInCheck();

        if (inCheck)
        {
            Move[] moves = OrderMoves(board.GetLegalMoves(), board, ply);
            if (moves.Length == 0) return -InfiniteScore + realPly;

            foreach (Move move in moves)
            {
                board.MakeMove(move);
                int score = -Quiescence(board, -beta, -alpha, ply + 1, qDepth + 1, realPly + 1);
                board.UndoMove(move);
                if (timeIsUp) return 0;
                if (score >= beta) return beta;
                if (score > alpha) alpha = score;
            }
            return alpha;
        }

        int standPat = Evaluate(board);
        if (standPat >= beta) return beta;
        if (standPat > alpha) alpha = standPat;

        var allTacticalMoves = new List<Move>(32);
        foreach (Move move in board.GetLegalMoves())
        {
            if (move.IsCapture || move.IsPromotion) allTacticalMoves.Add(move);
        }

        var movesToSearch = new List<Move>(allTacticalMoves.Count);
        int seeThreshold = (standPat > alpha + 100) ? 0 : Q_SEE_PRUNING_MARGIN;

        foreach (Move move in allTacticalMoves)
        {
            if (move.IsPromotion) { movesToSearch.Add(move); continue; }
            if (CalculateSEE(board, move) >= seeThreshold) movesToSearch.Add(move);
        }

        Move[] orderedMoves = OrderMoves(movesToSearch.ToArray(), board, ply);

        foreach (Move move in orderedMoves)
        {
            board.MakeMove(move);
            int score = -Quiescence(board, -beta, -alpha, ply + 1, qDepth + 1, realPly + 1);
            board.UndoMove(move);
            if (timeIsUp) return 0;
            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }

        return alpha;
    }

    private Move[] OrderMoves(Move[] moves, Board board, int ply, Move? pvMoveHint = null)
    {
        if (moves.Length <= 1) return moves;

        // stackalloc is faster and cleaner than ArrayPool for small arrays
        Span<int> scores = stackalloc int[moves.Length];

        TTEntry ttEntry = tt[GetTTIndex(board.ZobristKey)];
        Move ttMove = (ttEntry.Key == board.ZobristKey) ? ttEntry.BestMove : Move.NullMove;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            int moveScore = 0;

            if (!ttMove.IsNull && move == ttMove) moveScore += TT_MOVE_BONUS;
            else if (ply == 0 && pvMoveHint.HasValue && move == pvMoveHint.Value) moveScore += PREVIOUS_BEST_MOVE_BONUS;

            if (move.IsCapture)
            {
                int seeScoreVal = CalculateSEE(board, move);
                moveScore += (seeScoreVal >= 0 ? GOOD_CAPTURE_BONUS : LOSING_CAPTURE_BONUS) + seeScoreVal;
            }
            else
            {
                if (IsKillerMove(move, ply)) moveScore += KILLER_MOVE_BONUS;
                moveScore += Math.Min(historyMoves[move.StartSquare.Index, move.TargetSquare.Index], HISTORY_MAX_BONUS);
            }

            if (move.IsPromotion) moveScore += PROMOTION_BASE_BONUS + GetSeeValue(move.PromotionPieceType);
            scores[i] = moveScore;
        }

        // FIX: Use .AsSpan() on 'moves' so the compiler can infer types correctly
        scores.Sort(moves.AsSpan(), _descendingIntComparer);

        return moves;
    }

    private int Evaluate(Board board)
    {
        if (board.IsDraw()) return 0;

        int mgScore = 0;
        int egScore = 0;
        int gamePhase = 0;

        int whiteBishopCount = 0;
        int blackBishopCount = 0;

        // Material counters for endgame proximity logic
        int whiteMaterial = 0;
        int blackMaterial = 0;

        Square whiteKingSq = board.GetKingSquare(true);
        Square blackKingSq = board.GetKingSquare(false);

        // Pre-calculate data needed for loops
        ulong whiteKingRing = BitboardHelper.GetKingAttacks(whiteKingSq);
        ulong blackKingRing = BitboardHelper.GetKingAttacks(blackKingSq);
        ulong allPieces = board.AllPiecesBitboard;
        ulong whitePieces = board.WhitePiecesBitboard;
        ulong blackPieces = board.BlackPiecesBitboard;
        ulong whitePawns = board.GetPieceBitboard(PieceType.Pawn, true);
        ulong blackPawns = board.GetPieceBitboard(PieceType.Pawn, false);

        // Loop P(0), N(1), B(2), R(3), Q(4) - Handle King Separately
        for (int i = 0; i < 5; i++)
        {
            PieceType pt = (PieceType)(i + 1);
            ulong whiteBB = board.GetPieceBitboard(pt, true);
            ulong blackBB = board.GetPieceBitboard(pt, false);

            int count = BitOperations.PopCount(whiteBB | blackBB);

            // Phase Calculation
            if (i == 1) gamePhase += count * KnightPhase;       // Knight
            else if (i == 2) gamePhase += count * BishopPhase;  // Bishop
            else if (i == 3) gamePhase += count * RookPhase;    // Rook
            else if (i == 4) gamePhase += count * QueenPhase;   // Queen

            int[] currentPST = PiecePSTs[i + 1];
            int mgVal = MG_PieceValues[i];
            int egVal = EG_PieceValues[i];

            // --- WHITE PIECES ---
            ulong tempWhite = whiteBB;
            while (tempWhite != 0)
            {
                int sqIndex = BitOperations.TrailingZeroCount(tempWhite);

                // Material + PST
                int pstVal = currentPST[sqIndex];
                mgScore += mgVal + pstVal;
                egScore += egVal + pstVal;
                whiteMaterial += mgVal;

                // Piece Specific Logic
                switch (i)
                {
                    case 2: // Bishop
                        whiteBishopCount++;
                        ulong bMoves = BitboardHelper.GetSliderAttacks(PieceType.Bishop, new Square(sqIndex), allPieces) & ~whitePieces;
                        int bMob = BitOperations.PopCount(bMoves) * BISHOP_MOBILITY_BONUS;
                        mgScore += bMob; egScore += bMob;
                        break;
                    case 3: // Rook
                        int rFile = sqIndex & 7;
                        ulong rFileMask = FileMasks[rFile];
                        bool wBlocked = (whitePawns & rFileMask) != 0;
                        bool bBlocked = (blackPawns & rFileMask) != 0;

                        if (!wBlocked)
                        {
                            if (!bBlocked) { mgScore += ROOK_OPEN_FILE_MG; egScore += ROOK_OPEN_FILE_EG; }
                            else { mgScore += ROOK_SEMI_OPEN_FILE_MG; egScore += ROOK_SEMI_OPEN_FILE_EG; }
                        }

                        ulong rMoves = BitboardHelper.GetSliderAttacks(PieceType.Rook, new Square(sqIndex), allPieces) & ~whitePieces;
                        egScore += BitOperations.PopCount(rMoves) * ROOK_MOBILITY_EG;
                        break;
                }

                // King Attacks
                ulong attacks = 0;
                Square sq = new Square(sqIndex);
                if (pt == PieceType.Pawn) attacks = BitboardHelper.GetPawnAttacks(sq, true);
                else if (pt == PieceType.Knight) attacks = BitboardHelper.GetKnightAttacks(sq);
                else attacks = BitboardHelper.GetSliderAttacks(pt, sq, allPieces);

                int hits = BitOperations.PopCount(attacks & blackKingRing);
                if (hits > 0)
                {
                    int bonus = KING_ATTACK_BASE_BONUS + (hits > 1 ? KING_ATTACK_EXTRA_BONUS : 0);
                    mgScore += bonus; egScore += bonus;
                }

                tempWhite &= tempWhite - 1;
            }

            // --- BLACK PIECES ---
            ulong tempBlack = blackBB;
            while (tempBlack != 0)
            {
                int sqIndex = BitOperations.TrailingZeroCount(tempBlack);
                int pstVal = currentPST[sqIndex ^ 56]; // Flip for Black

                mgScore -= mgVal + pstVal;
                egScore -= egVal + pstVal;
                blackMaterial += mgVal;

                switch (i)
                {
                    case 2: // Bishop
                        blackBishopCount++;
                        ulong bMoves = BitboardHelper.GetSliderAttacks(PieceType.Bishop, new Square(sqIndex), allPieces) & ~blackPieces;
                        int bMob = BitOperations.PopCount(bMoves) * BISHOP_MOBILITY_BONUS;
                        mgScore -= bMob; egScore -= bMob;
                        break;
                    case 3: // Rook
                        int rFile = sqIndex & 7;
                        ulong rFileMask = FileMasks[rFile];
                        bool bBlocked = (blackPawns & rFileMask) != 0;
                        bool wBlocked = (whitePawns & rFileMask) != 0;

                        if (!bBlocked)
                        {
                            if (!wBlocked) { mgScore -= ROOK_OPEN_FILE_MG; egScore -= ROOK_OPEN_FILE_EG; }
                            else { mgScore -= ROOK_SEMI_OPEN_FILE_MG; egScore -= ROOK_SEMI_OPEN_FILE_EG; }
                        }

                        ulong rMoves = BitboardHelper.GetSliderAttacks(PieceType.Rook, new Square(sqIndex), allPieces) & ~blackPieces;
                        egScore -= BitOperations.PopCount(rMoves) * ROOK_MOBILITY_EG;
                        break;
                }

                // King Attacks
                ulong attacks = 0;
                Square sq = new Square(sqIndex);
                if (pt == PieceType.Pawn) attacks = BitboardHelper.GetPawnAttacks(sq, false);
                else if (pt == PieceType.Knight) attacks = BitboardHelper.GetKnightAttacks(sq);
                else attacks = BitboardHelper.GetSliderAttacks(pt, sq, allPieces);

                int hits = BitOperations.PopCount(attacks & whiteKingRing);
                if (hits > 0)
                {
                    int bonus = KING_ATTACK_BASE_BONUS + (hits > 1 ? KING_ATTACK_EXTRA_BONUS : 0);
                    mgScore -= bonus; egScore -= bonus;
                }

                tempBlack &= tempBlack - 1;
            }
        }

        // --- KINGS (Material is 0, just PSTs and Safety) ---
        int wKingIdx = whiteKingSq.Index;
        int bKingIdx = blackKingSq.Index;

        // King PSTs
        mgScore += KingMiddleGamePST[wKingIdx];
        egScore += KingEndGamePST[wKingIdx];

        mgScore -= KingMiddleGamePST[bKingIdx ^ 56];
        egScore -= KingEndGamePST[bKingIdx ^ 56];

        // King Safety (Mg Only)
        ulong wKingShield = BitboardHelper.GetSliderAttacks(PieceType.Queen, whiteKingSq, allPieces) & ~RankMasks[whiteKingSq.Rank] & ~whitePieces;
        mgScore -= BitOperations.PopCount(wKingShield) * KING_SAFETY_EXPOSURE_PENALTY;

        ulong bKingShield = BitboardHelper.GetSliderAttacks(PieceType.Queen, blackKingSq, allPieces) & ~RankMasks[blackKingSq.Rank] & ~blackPieces;
        mgScore += BitOperations.PopCount(bKingShield) * KING_SAFETY_EXPOSURE_PENALTY;

        // Endgame Proximity
        if (whiteMaterial < ENDGAME_MAT_THRESHOLD && blackMaterial > whiteMaterial)
        {
            int dist = Math.Abs(whiteKingSq.File - blackKingSq.File) + Math.Abs(whiteKingSq.Rank - blackKingSq.Rank);
            int penalty = Math.Max(0, (dist - 2) * KING_PROXIMITY_PENALTY);
            mgScore += penalty; egScore += penalty;
        }
        else if (blackMaterial < ENDGAME_MAT_THRESHOLD && whiteMaterial > blackMaterial)
        {
            int dist = Math.Abs(whiteKingSq.File - blackKingSq.File) + Math.Abs(whiteKingSq.Rank - blackKingSq.Rank);
            int penalty = Math.Max(0, (dist - 2) * KING_PROXIMITY_PENALTY);
            mgScore -= penalty; egScore -= penalty;
        }

        // Bishop Pair
        if (whiteBishopCount >= 2) { mgScore += 25; egScore += 35; }
        if (blackBishopCount >= 2) { mgScore -= 25; egScore -= 35; }

        // Pawns
        int pawnMg, pawnEg;
        CalculatePawnScore(board, out pawnMg, out pawnEg);
        mgScore += pawnMg;
        egScore += pawnEg;

        // Final Tapering
        int phase = Math.Min(gamePhase, TotalPhase);
        int finalScore = (mgScore * phase + egScore * (TotalPhase - phase)) / TotalPhase;

        finalScore += board.IsWhiteToMove ? 10 : -10;
        return board.IsWhiteToMove ? finalScore : -finalScore;
    }

    private void CalculatePawnScore(Board board, out int mg, out int eg)
    {
        mg = 0; eg = 0;
        ulong whitePawns = board.GetPieceBitboard(PieceType.Pawn, true);
        ulong blackPawns = board.GetPieceBitboard(PieceType.Pawn, false);

        // Process White Pawns
        ulong tempWhite = whitePawns;
        while (tempWhite != 0)
        {
            int sq = BitOperations.TrailingZeroCount(tempWhite);
            int file = sq & 7; int rank = sq >> 3;
            if ((whitePawns & AdjacentFilesMasks[file]) == 0) { mg += ISOLATED_PAWN_PENALTY; eg += ISOLATED_PAWN_PENALTY; }
            if ((whitePawns & FileMasks[file] & ~(1UL << sq)) != 0) { mg += DOUBLED_PAWN_PENALTY; eg += DOUBLED_PAWN_PENALTY; }
            if (((FileMasks[file] | AdjacentFilesMasks[file]) & WhiteForwardRankMasks[rank] & blackPawns) == 0)
            {
                mg += PASSED_PAWN_BASE_BONUS + (rank * 5);
                eg += PASSED_PAWN_BASE_BONUS + (rank * PASSED_PAWN_RANK_BONUS);
            }
            tempWhite &= tempWhite - 1;
        }

        // Process Black Pawns
        ulong tempBlack = blackPawns;
        while (tempBlack != 0)
        {
            int sq = BitOperations.TrailingZeroCount(tempBlack);
            int file = sq & 7; int rank = sq >> 3;
            if ((blackPawns & AdjacentFilesMasks[file]) == 0) { mg -= ISOLATED_PAWN_PENALTY; eg -= ISOLATED_PAWN_PENALTY; }
            if ((blackPawns & FileMasks[file] & ~(1UL << sq)) != 0) { mg -= DOUBLED_PAWN_PENALTY; eg -= DOUBLED_PAWN_PENALTY; }
            if (((FileMasks[file] | AdjacentFilesMasks[file]) & BlackForwardRankMasks[rank] & whitePawns) == 0)
            {
                mg -= (PASSED_PAWN_BASE_BONUS + ((7 - rank) * 5));
                eg -= (PASSED_PAWN_BASE_BONUS + ((7 - rank) * PASSED_PAWN_RANK_BONUS));
            }
            tempBlack &= tempBlack - 1;
        }
    }

    // --- Helper Functions ---

    private int GetSeeValue(PieceType pt)
    {
        if (pt == PieceType.None) return 0;
        return SeePieceValues[(int)pt - 1];
    }

    private (PieceType type, Square fromSquare) GetLeastValuableAttacker(Board board, Square targetSquare, bool attackerIsWhite, ulong occupiedHypothetical)
    {
        for (int pieceTypeId = 1; pieceTypeId <= 6; pieceTypeId++)
        {
            PieceType currentPieceTypeToTest = (PieceType)pieceTypeId;
            ulong potentialAttackersOfThisType = board.GetPieceBitboard(currentPieceTypeToTest, attackerIsWhite) & occupiedHypothetical;
            if (potentialAttackersOfThisType == 0) continue;

            ulong attackRaysToTarget;
            switch (currentPieceTypeToTest)
            {
                case PieceType.Pawn: attackRaysToTarget = BitboardHelper.GetPawnAttacks(targetSquare, !attackerIsWhite); break;
                case PieceType.Knight: attackRaysToTarget = BitboardHelper.GetKnightAttacks(targetSquare); break;
                case PieceType.Bishop: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Bishop, targetSquare, occupiedHypothetical); break;
                case PieceType.Rook: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Rook, targetSquare, occupiedHypothetical); break;
                case PieceType.Queen: attackRaysToTarget = BitboardHelper.GetSliderAttacks(PieceType.Queen, targetSquare, occupiedHypothetical); break;
                case PieceType.King: attackRaysToTarget = BitboardHelper.GetKingAttacks(targetSquare); break;
                default: continue;
            }

            ulong actualAttackers = attackRaysToTarget & potentialAttackersOfThisType;
            if (actualAttackers != 0)
            {
                return (currentPieceTypeToTest, new Square(BitOperations.TrailingZeroCount(actualAttackers)));
            }
        }
        return (PieceType.None, default(Square));
    }

    private int CalculateSEE(Board board, Move move)
    {
        if (!move.IsCapture) return 0;
        Square targetSquare = move.TargetSquare;
        Span<int> gain = stackalloc int[32];
        int d = 0;
        ulong occupiedHypothetical = board.AllPiecesBitboard;
        bool currentSideToRecaptureIsWhite = !board.IsWhiteToMove;
        gain[d++] = GetSeeValue(move.CapturePieceType);
        occupiedHypothetical ^= (1UL << move.StartSquare.Index);
        PieceType pieceOnSquareForNextCapture = move.MovePieceType;

        while (true)
        {
            (PieceType lvaType, Square lvaFromSquare) = GetLeastValuableAttacker(board, targetSquare, currentSideToRecaptureIsWhite, occupiedHypothetical);
            if (lvaType == PieceType.None) break;
            occupiedHypothetical ^= (1UL << lvaFromSquare.Index);
            gain[d++] = GetSeeValue(pieceOnSquareForNextCapture);
            pieceOnSquareForNextCapture = lvaType;
            currentSideToRecaptureIsWhite = !currentSideToRecaptureIsWhite;
            if (d >= 32) break;
        }

        for (int k = d - 1; k > 0; k--)
        {
            gain[k - 1] = -Math.Max(-gain[k - 1], gain[k] - gain[k - 1]);
        }
        return gain[0];
    }

    private bool IsEndgame(Board board)
    {
        // 11 pieces or fewer (kings included) is a safe endgame threshold
        return BitOperations.PopCount(board.AllPiecesBitboard) <= 11;
    }

    private void CheckTime()
    {
        if (ConstantDepth) return;
        if (((negamaxPositions + qsearchPositions) & TIME_CHECK_MASK) == 0)
        {
            if (currentTimer.MillisecondsElapsedThisTurn >= absoluteTimeLimit)
            {
                timeIsUp = true;
            }
        }
    }

    private bool IsKillerMove(Move move, int ply)
    {
        if (ply < 0 || ply >= MAX_KILLER_PLY) return false;
        return move == killerMoves[ply, 0] || move == killerMoves[ply, 1];
    }

    private void UpdateKillerMoves(Move move, int ply)
    {
        if (move.IsCapture || move.IsPromotion || ply < 0 || ply >= MAX_KILLER_PLY) return;
        if (move != killerMoves[ply, 0])
        {
            killerMoves[ply, 1] = killerMoves[ply, 0];
            killerMoves[ply, 0] = move;
        }
    }

    private const int HISTORY_SCORE_CAP = 1_000_000;
    private void UpdateHistoryMove(Move move, int bonus)
    {
        if (move.IsCapture || move.IsPromotion) return;
        int startIdx = move.StartSquare.Index;
        int targetIdx = move.TargetSquare.Index;
        historyMoves[startIdx, targetIdx] = Math.Min(historyMoves[startIdx, targetIdx] + bonus, HISTORY_SCORE_CAP);
        if (((negamaxPositions + qsearchPositions) & TIME_CHECK_MASK) == 0) DecayHistory();
    }

    private void DecayHistory()
    {
        for (int i = 0; i < 64; i++) for (int j = 0; j < 64; j++) historyMoves[i, j] /= 2;
    }

    private Move HandleForcedMove(Move move, Board board, int completedDepthForLog, bool isForcedMove)
    {
        this.bestScoreRoot = Evaluate(board);
        this.completedSearchDepth = completedDepthForLog;
        return LogEval(board, completedDepthForLog, isForcedMove, move);
    }

    private struct TTEntry { public ulong Key; public short Depth; public short Score; public byte Flag; public Move BestMove; }

    private const byte EXACT = 0, ALPHA = 1, BETA = 2;
    private int GetTTIndex(ulong key) => (int)(key & ttMask);

    private void AddTT(ulong key, int depth, short scoreForTT, byte flag, Move bestMove)
    {
        int index = GetTTIndex(key);
        ref TTEntry entry = ref tt[index];
        bool replace = entry.Key == 0 || depth >= entry.Depth;
        if (replace)
        {
            entry.Key = key;
            entry.Depth = (short)depth;
            entry.Score = scoreForTT;
            entry.Flag = flag;
            entry.BestMove = bestMove;
        }
    }

    private short AdjustMateScoreForTTStorage(int scoreFromNode, int currentRealPly)
    {
        if (Math.Abs(scoreFromNode) >= MATE_FOUND_SCORE)
        {
            int sign = Math.Sign(scoreFromNode);
            return (short)(scoreFromNode + (sign * currentRealPly));
        }
        return (short)scoreFromNode;
    }

    private short AdjustMateScoreFromTT(short ttScore, int currentRealPly)
    {
        if (Math.Abs(ttScore) >= MATE_FOUND_SCORE)
        {
            int sign = Math.Sign(ttScore);
            return (short)(ttScore - (sign * currentRealPly));
        }
        return ttScore;
    }

    private void DebugLog(string message)
    {
        Console.WriteLine($"{GetType().Name} {message}");
    }

    // Helper masks for Pawn Evaluation logic
    private static readonly ulong[] FileMasks = {
    0x0101010101010101, 0x0202020202020202, 0x0404040404040404, 0x0808080808080808,
    0x1010101010101010, 0x2020202020202020, 0x4040404040404040, 0x8080808080808080
    };
    private static readonly ulong[] RankMasks = {
    0x00000000000000FF, 0x000000000000FF00, 0x0000000000FF0000, 0x00000000FF000000,
    0x000000FF00000000, 0x0000FF0000000000, 0x00FF000000000000, 0xFF00000000000000
    };
    private static readonly ulong[] AdjacentFilesMasks = {
    0x0202020202020202, 0x0505050505050505, 0x0a0a0a0a0a0a0a0a, 0x1414141414141414,
    0x2828282828282828, 0x5050505050505050, 0xa0a0a0a0a0a0a0a0, 0x4040404040404040
    };
    private static readonly ulong[] WhiteForwardRankMasks = {
    0xFFFFFFFFFFFFFF00, 0xFFFFFFFFFFFF0000, 0xFFFFFFFFFF000000, 0xFFFFFFFF00000000,
    0xFFFFFF0000000000, 0xFFFF000000000000, 0xFF00000000000000, 0x0
    };
    private static readonly ulong[] BlackForwardRankMasks = {
    0x0, 0x00000000000000FF, 0x000000000000FFFF, 0x0000000000FFFFFF,
    0x00000000FFFFFFFF, 0x000000FFFFFFFFFF, 0x0000FFFFFFFFFFFF, 0x00FFFFFFFFFFFFFF
    };
}