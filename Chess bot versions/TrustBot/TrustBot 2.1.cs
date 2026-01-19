using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Buffers;

// Trustbot 2.1 - Dynamic SEE Reduction + tune
// Change: SEE Reduction is now dynamic based on depth.
// Depth > 5: Reduce by 3 (Speed optimization for deep searches).
// Depth <= 5: Reduce by 2 (Safety optimization for shallow tactical searches).

public class MyBot : IChessBot
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

    // HCE Constants
    private const int KING_ATTACK_BASE_BONUS = 20;  // +0.2
    private const int KING_ATTACK_EXTRA_BONUS = 10; // +0.1
    private const int BISHOP_MOBILITY_BONUS = 3;    // Bot actually cares about bishop mobility on diagonals now haha

    // King Safety (MG Only)
    private const int KING_CASTLE_BONUS = 20;           // +0.2 for being on files A-C or G-H
    private const int KING_SAFETY_EXPOSURE_PENALTY = 2; // -0.02 per open pseudo-queen square

    // Rook HCE
    private const int ROOK_MOBILITY_EG = 2;
    private const int ROOK_OPEN_FILE_MG = 10;
    private const int ROOK_OPEN_FILE_EG = 25;
    private const int ROOK_SEMI_OPEN_FILE_MG = 5;
    private const int ROOK_SEMI_OPEN_FILE_EG = 15;

    // Positional Bonuses
    private static readonly int[] KnightCenterBonus = { -10, 5, 15, 20 };
    private static readonly int[] KingCenterBonus = { 0, 10, 20, 25 };

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
    // Dynamic SEE Reduction Constants
    private const int SEE_REDUCTION_DEEP = 3;    // Used when depth > 5
    private const int SEE_REDUCTION_SHALLOW = 2; // Used when depth <= 5


    // Static Fields
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = TT_SIZE - 1;
    private int lastGamePlyCount = -1;

    // Instance Fields
    private long negamaxPositions, qsearchPositions;
    private int bestScoreRoot;
    private Move[,] killerMoves = new Move[MAX_KILLER_PLY, 2];
    private int[,] historyMoves = new int[64, 64];
    private int cachedPieceCount = -1;
    private ulong lastBoardHash;
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
        lastBoardHash = 0; cachedPieceCount = -1; bestScoreRoot = 0;

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
        int[] scores = ArrayPool<int>.Shared.Rent(moves.Length);
        try
        {
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
                    if (seeScoreVal >= 0) moveScore += GOOD_CAPTURE_BONUS + seeScoreVal;
                    else moveScore += LOSING_CAPTURE_BONUS + seeScoreVal;
                }
                else
                {
                    if (IsKillerMove(move, ply)) moveScore += KILLER_MOVE_BONUS;
                    moveScore += Math.Min(historyMoves[move.StartSquare.Index, move.TargetSquare.Index], HISTORY_MAX_BONUS);
                }
                if (move.IsPromotion) moveScore += PROMOTION_BASE_BONUS + GetSeeValue(move.PromotionPieceType);
                scores[i] = moveScore;
            }
            Array.Sort(scores, moves, 0, moves.Length, _descendingIntComparer);
            return moves;
        }
        finally
        {
            ArrayPool<int>.Shared.Return(scores);
        }
    }

    private int Evaluate(Board board)
    {
        if (board.IsDraw()) return 0;

        int mgScore = 0;
        int egScore = 0;
        int gamePhase = 0;

        int whiteBishopCount = 0;
        int blackBishopCount = 0;

        int whiteMaterial = 0;
        int blackMaterial = 0;

        // --- KING RING & MOBILITY ---
        Square whiteKingSq = board.GetKingSquare(true);
        Square blackKingSq = board.GetKingSquare(false);
        ulong whiteKingRing = BitboardHelper.GetKingAttacks(whiteKingSq);
        ulong blackKingRing = BitboardHelper.GetKingAttacks(blackKingSq);
        ulong allPieces = board.AllPiecesBitboard;
        ulong whitePieces = board.WhitePiecesBitboard;
        ulong blackPieces = board.BlackPiecesBitboard;
        ulong whitePawns = board.GetPieceBitboard(PieceType.Pawn, true);
        ulong blackPawns = board.GetPieceBitboard(PieceType.Pawn, false);

        for (int i = 0; i < 6; i++)
        {
            PieceType pt = (PieceType)(i + 1);
            ulong whiteBB = board.GetPieceBitboard(pt, true);
            ulong blackBB = board.GetPieceBitboard(pt, false);

            int count = BitOperations.PopCount(whiteBB | blackBB);
            if (i == 1) gamePhase += count * KnightPhase;
            else if (i == 2) gamePhase += count * BishopPhase;
            else if (i == 3) gamePhase += count * RookPhase;
            else if (i == 4) gamePhase += count * QueenPhase;

            // --- WHITE PIECES ---
            ulong tempWhite = whiteBB;
            while (tempWhite != 0)
            {
                int sqIndex = BitOperations.TrailingZeroCount(tempWhite);

                // Material Score
                if (i == 2) whiteBishopCount++;
                mgScore += MG_PieceValues[i];
                egScore += EG_PieceValues[i];

                if (i != 5) whiteMaterial += MG_PieceValues[i];

                // Bishop Mobility
                if (i == 2)
                {
                    ulong attacks = BitboardHelper.GetSliderAttacks(PieceType.Bishop, new Square(sqIndex), allPieces);
                    ulong validMoves = attacks & ~whitePieces; // Exclude friendly captures
                    int mobility = BitOperations.PopCount(validMoves) * BISHOP_MOBILITY_BONUS;
                    mgScore += mobility;
                    egScore += mobility;
                }

                // Rook Activity (Files & Mobility)
                if (i == 3)
                {
                    // 1. Files
                    int file = sqIndex & 7;
                    ulong fileMask = FileMasks[file];
                    bool myPawnsBlocked = (whitePawns & fileMask) != 0;
                    bool enemyPawnsBlocked = (blackPawns & fileMask) != 0;

                    if (!myPawnsBlocked && !enemyPawnsBlocked)
                    {
                        // Open File
                        mgScore += ROOK_OPEN_FILE_MG;
                        egScore += ROOK_OPEN_FILE_EG;
                    }
                    else if (!myPawnsBlocked && enemyPawnsBlocked)
                    {
                        // Semi-Open File
                        mgScore += ROOK_SEMI_OPEN_FILE_MG;
                        egScore += ROOK_SEMI_OPEN_FILE_EG;
                    }

                    // 2. Mobility
                    ulong attacks = BitboardHelper.GetSliderAttacks(PieceType.Rook, new Square(sqIndex), allPieces);
                    ulong validMoves = attacks & ~whitePieces;
                    int moveCount = BitOperations.PopCount(validMoves);
                    egScore += moveCount * ROOK_MOBILITY_EG;
                }

                // Knight Centrality Bonus
                if (i == 1)
                {
                    int file = sqIndex & 7; int rank = sqIndex >> 3;
                    int dist = Math.Min(Math.Min(file, 7 - file), Math.Min(rank, 7 - rank));
                    int bonus = KnightCenterBonus[dist];
                    mgScore += bonus;
                    egScore += bonus;
                }

                // King Attack Bonus (Exclude our King)
                if (i != 5)
                {
                    ulong attacks = 0;
                    Square sq = new Square(sqIndex);
                    if (pt == PieceType.Pawn) attacks = BitboardHelper.GetPawnAttacks(sq, true);
                    else if (pt == PieceType.Knight) attacks = BitboardHelper.GetKnightAttacks(sq);
                    else attacks = BitboardHelper.GetSliderAttacks(pt, sq, allPieces);

                    int hits = BitOperations.PopCount(attacks & blackKingRing);
                    if (hits > 0)
                    {
                        int bonus = KING_ATTACK_BASE_BONUS;
                        if (hits > 1) bonus += KING_ATTACK_EXTRA_BONUS;
                        mgScore += bonus;
                        egScore += bonus;
                    }
                }

                tempWhite &= tempWhite - 1;
            }

            // --- BLACK PIECES ---
            ulong tempBlack = blackBB;
            while (tempBlack != 0)
            {
                int sqIndex = BitOperations.TrailingZeroCount(tempBlack);

                // Material Score
                if (i == 2) blackBishopCount++;
                mgScore -= MG_PieceValues[i];
                egScore -= EG_PieceValues[i];

                if (i != 5) blackMaterial += MG_PieceValues[i];

                // Bishop Mobility
                if (i == 2)
                {
                    ulong attacks = BitboardHelper.GetSliderAttacks(PieceType.Bishop, new Square(sqIndex), allPieces);
                    ulong validMoves = attacks & ~blackPieces;
                    int mobility = BitOperations.PopCount(validMoves) * BISHOP_MOBILITY_BONUS;
                    mgScore -= mobility;
                    egScore -= mobility;
                }

                // Rook Activity (Files & Mobility)
                if (i == 3)
                {
                    // 1. Files
                    int file = sqIndex & 7;
                    ulong fileMask = FileMasks[file];
                    bool myPawnsBlocked = (blackPawns & fileMask) != 0;
                    bool enemyPawnsBlocked = (whitePawns & fileMask) != 0;

                    if (!myPawnsBlocked && !enemyPawnsBlocked)
                    {
                        mgScore -= ROOK_OPEN_FILE_MG;
                        egScore -= ROOK_OPEN_FILE_EG;
                    }
                    else if (!myPawnsBlocked && enemyPawnsBlocked)
                    {
                        mgScore -= ROOK_SEMI_OPEN_FILE_MG;
                        egScore -= ROOK_SEMI_OPEN_FILE_EG;
                    }

                    // 2. Mobility
                    ulong attacks = BitboardHelper.GetSliderAttacks(PieceType.Rook, new Square(sqIndex), allPieces);
                    ulong validMoves = attacks & ~blackPieces;
                    int moveCount = BitOperations.PopCount(validMoves);
                    egScore -= moveCount * ROOK_MOBILITY_EG;
                }

                // Knight Centrality Bonus
                if (i == 1)
                {
                    int file = sqIndex & 7; int rank = sqIndex >> 3;
                    int dist = Math.Min(Math.Min(file, 7 - file), Math.Min(rank, 7 - rank));
                    int bonus = KnightCenterBonus[dist];
                    mgScore -= bonus;
                    egScore -= bonus;
                }

                // King Attack Bonus (Exclude our King)
                if (i != 5)
                {
                    ulong attacks = 0;
                    Square sq = new Square(sqIndex);
                    if (pt == PieceType.Pawn) attacks = BitboardHelper.GetPawnAttacks(sq, false);
                    else if (pt == PieceType.Knight) attacks = BitboardHelper.GetKnightAttacks(sq);
                    else attacks = BitboardHelper.GetSliderAttacks(pt, sq, allPieces);

                    int hits = BitOperations.PopCount(attacks & whiteKingRing);
                    if (hits > 0)
                    {
                        int bonus = KING_ATTACK_BASE_BONUS;
                        if (hits > 1) bonus += KING_ATTACK_EXTRA_BONUS;
                        mgScore -= bonus;
                        egScore -= bonus;
                    }
                }

                tempBlack &= tempBlack - 1;
            }
        }

        // --- MG KING SAFETY ---
        // White King Castled Zones (Files A,B,C or G,H)
        int wFile = whiteKingSq.File;
        if (wFile <= 2 || wFile >= 6) mgScore += KING_CASTLE_BONUS;

        ulong wKingAttacks = BitboardHelper.GetSliderAttacks(PieceType.Queen, whiteKingSq, allPieces);
        wKingAttacks &= ~RankMasks[whiteKingSq.Rank]; // Ignore rank (pseudo-queen)
        wKingAttacks &= ~whitePieces; // Moves blocked by friends are excluded
        mgScore -= BitOperations.PopCount(wKingAttacks) * KING_SAFETY_EXPOSURE_PENALTY;

        // Black King Castled Zones
        int bFile = blackKingSq.File;
        if (bFile <= 2 || bFile >= 6) mgScore -= KING_CASTLE_BONUS;

        ulong bKingAttacks = BitboardHelper.GetSliderAttacks(PieceType.Queen, blackKingSq, allPieces);
        bKingAttacks &= ~RankMasks[blackKingSq.Rank];
        bKingAttacks &= ~blackPieces;
        mgScore += BitOperations.PopCount(bKingAttacks) * KING_SAFETY_EXPOSURE_PENALTY;


        // --- ENDGAME KING EVALUATION ---
        // 1. Proximity: Closer is better (if we are winning)
        int distW = whiteKingSq.File - blackKingSq.File;
        int distH = whiteKingSq.Rank - blackKingSq.Rank;
        int manhattanDist = Math.Abs(distW) + Math.Abs(distH);
        int distancePenalty = Math.Max(0, (manhattanDist - 2) * KING_PROXIMITY_PENALTY);

        if (distancePenalty > 0)
        {
            if (blackMaterial < ENDGAME_MAT_THRESHOLD && whiteMaterial > blackMaterial)
            {
                mgScore -= distancePenalty;
                egScore -= distancePenalty;
            }
            if (whiteMaterial < ENDGAME_MAT_THRESHOLD && blackMaterial > whiteMaterial)
            {
                mgScore += distancePenalty;
                egScore += distancePenalty;
            }
        }

        // 2. Centrality
        int wDist = Math.Min(Math.Min(wFile, 7 - wFile), Math.Min(whiteKingSq.Rank, 7 - whiteKingSq.Rank));
        egScore += KingCenterBonus[wDist];

        int bDist = Math.Min(Math.Min(bFile, 7 - bFile), Math.Min(blackKingSq.Rank, 7 - blackKingSq.Rank));
        egScore -= KingCenterBonus[bDist];


        if (whiteBishopCount >= 2) { mgScore += 25; egScore += 35; }
        if (blackBishopCount >= 2) { mgScore -= 25; egScore -= 35; }

        int pawnMg, pawnEg;
        CalculatePawnScore(board, out pawnMg, out pawnEg);
        mgScore += pawnMg;
        egScore += pawnEg;

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
        if (board.ZobristKey != lastBoardHash)
        {
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = board.ZobristKey;
        }
        const int endgameTotalPieceThreshold = 11;
        return cachedPieceCount <= endgameTotalPieceThreshold;
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