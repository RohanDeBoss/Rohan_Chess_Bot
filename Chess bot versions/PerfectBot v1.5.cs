using ChessChallenge.API;
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Buffers;

// PerfectBot v1.5: Increased MaxSafetyDepth to 999, fixed reporting and removed SEE for move ordering. (Must be named MyBot)
public class MyBot : IChessBot
{
    // --- Configuration ---
    private static readonly bool PerMoveDebugging = true;
    private static readonly bool PerDepthDebugging = false;

    private static readonly bool ConstantDepth = false;
    private static readonly short MaxDepth = 12;

    private static readonly bool UseFixedTimePerMove = false;
    private static readonly int FixedTimePerMoveMs = 500;

    // Search & Eval Constants
    private const short MaxSafetyDepth = 999; // Increased as requested.
    private const int InfiniteScore = 30000;
    private const int TT_SIZE = 1 << 22;
    private const int MAX_KILLER_PLY = 256;
    private const int MATE_FOUND_SCORE = 29000;

    // Move Ordering Bonuses
    private const int TT_MOVE_BONUS = 10_000_000;
    private const int PREVIOUS_BEST_MOVE_BONUS = 5_000_000;
    private const int CAPTURE_BONUS = 2_000_000;
    private const int PROMOTION_BASE_BONUS = 1_100_000;
    private const int KILLER_MOVE_BONUS = 900_000;
    private const int HISTORY_MAX_BONUS = 800_000;

    // Time Management & Aspiration Window Constants
    private const int INITIAL_ASPIRATION_WINDOW = 150;
    private const int MAX_ASPIRATION_DEPTH = 4;
    private const int SAFETY_MARGIN = 10;

    private const int TIME_CHECK_NODES = 1024;
    private const int TIME_CHECK_MASK = TIME_CHECK_NODES - 1;

    // Static Fields
    private TTEntry[] tt = new TTEntry[TT_SIZE];
    private readonly ulong ttMask = TT_SIZE - 1;
    private static readonly int[] PieceValues = { 100, 300, 310, 500, 900, 10000 }; // P, N, B, R, Q, K

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
        negamaxPositions = 0;
        qsearchPositions = 0;
        completedSearchDepth = 0;
        lastBoardHash = 0;
        cachedPieceCount = -1;
        this.bestScoreRoot = 0;

        short currentIterativeDepth = 1;
        int scoreFromPrevIteration = 0;
        Move bestMoveFromPrevIteration = Move.NullMove;

        var legalMoves = board.GetLegalMoves();
        if (legalMoves.Length == 0)
        {
            this.bestScoreRoot = board.IsInCheck() ? -InfiniteScore : 0;
            this.completedSearchDepth = MaxSafetyDepth; // Mate in 0
            return LogEval(board, this.completedSearchDepth, false, Move.NullMove);
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
                    this.bestScoreRoot = scoreThisAspirationLoop;
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

                if (Math.Abs(bestScoreRoot) >= MATE_FOUND_SCORE)
                {
                    int pliesToMate = (InfiniteScore - Math.Abs(bestScoreRoot) + 49) / 50;
                    this.completedSearchDepth = MaxSafetyDepth - pliesToMate;
                }
                else
                {
                    this.completedSearchDepth = currentIterativeDepth;
                }

                if (PerDepthDebugging)
                {
                    long totalNodes = negamaxPositions + qsearchPositions;
                    string timeDisplay = currentTimer.MillisecondsElapsedThisTurn <= 9999 ? $"{currentTimer.MillisecondsElapsedThisTurn}ms" : $"{(currentTimer.MillisecondsElapsedThisTurn / 1000.0):F1}s";
                    string nodesDisplay = totalNodes < 10000 ? $"{totalNodes}" : totalNodes < 10000000 ? $"{(totalNodes / 1000.0):F1}k" : $"{(totalNodes / 1000000.0):F1}m";
                    DebugLog($"Depth {currentIterativeDepth}, Score {this.bestScoreRoot}, BestMove {bestMoveOverall}, Nodes {nodesDisplay}, Time {timeDisplay}");
                }
            }
            else { break; }
            currentIterativeDepth++;
        }

        if (bestMoveOverall.IsNull && legalMoves.Length > 0) bestMoveOverall = legalMoves[0];
        if (this.completedSearchDepth == 0 && legalMoves.Length > 0 && !timeIsUp && this.bestScoreRoot == 0)
        {
            this.bestScoreRoot = Evaluate(board) * (board.IsWhiteToMove ? 1 : -1);
        }
        return LogEval(board, this.completedSearchDepth, false, bestMoveOverall);
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
                string mateInfo = GetMateInMoves(this.bestScoreRoot);
                int evalForDisplay = isWhitePlayer ? this.bestScoreRoot : -this.bestScoreRoot;
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

    private int Negamax(Board board, int depth, int alpha, int beta, int ply, int realPly)
    {
        CheckTime();
        if (timeIsUp) return 0;
        negamaxPositions++;
        if (board.IsDraw()) return 0;

        alpha = Math.Max(alpha, -InfiniteScore + realPly * 50);
        beta = Math.Min(beta, InfiniteScore - realPly * 50);
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
            return board.IsInCheck() ? (-InfiniteScore + realPly * 50) : 0;
        }

        moves = OrderMoves(moves, board, ply, ttMove);
        int originalAlpha = alpha;
        Move bestMoveCurrentNode = Move.NullMove;
        int localBestScore = -InfiniteScore;

        for (int i = 0; i < moves.Length; i++)
        {
            Move move = moves[i];
            board.MakeMove(move);
            bool givesCheck = board.IsInCheck();
            int newDepth = depth - 1;
            if (givesCheck && newDepth < MaxSafetyDepth - 1) newDepth++;

            int score = -Negamax(board, newDepth, -beta, -alpha, ply + 1, realPly + 1);

            board.UndoMove(move);
            if (timeIsUp) return 0;
            if (score > localBestScore)
            {
                localBestScore = score;
                bestMoveCurrentNode = move;
                alpha = Math.Max(alpha, score);
                if (alpha >= beta)
                {
                    if (!move.IsCapture && !move.IsPromotion)
                    {
                        UpdateKillerMoves(move, ply);
                        UpdateHistoryMove(move, depth * depth);
                    }
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
        int standPat = Evaluate(board);
        if (standPat >= beta) return beta;
        if (standPat > alpha) alpha = standPat;

        Move[] captures = board.GetLegalMoves(true);
        Move[] orderedMoves = OrderMoves(captures, board, ply);

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

                if (!ttMove.IsNull && move == ttMove)
                {
                    moveScore += TT_MOVE_BONUS;
                }
                else if (ply == 0 && pvMoveHint.HasValue && move == pvMoveHint.Value)
                {
                    moveScore += PREVIOUS_BEST_MOVE_BONUS;
                }

                if (move.IsCapture)
                {
                    int victimValue = PieceValues[(int)move.CapturePieceType - 1];
                    int attackerValue = PieceValues[(int)move.MovePieceType - 1];
                    moveScore += CAPTURE_BONUS + (victimValue * 10) - attackerValue;
                }
                else
                {
                    if (IsKillerMove(move, ply))
                    {
                        moveScore += KILLER_MOVE_BONUS;
                    }
                    moveScore += Math.Min(historyMoves[move.StartSquare.Index, move.TargetSquare.Index], HISTORY_MAX_BONUS);
                }

                if (move.IsPromotion)
                {
                    moveScore += PROMOTION_BASE_BONUS + PieceValues[(int)move.PromotionPieceType - 1];
                }

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
        int score = 0;
        bool isEndgame = IsEndgame(board);
        int whiteBishopCount = 0;
        int blackBishopCount = 0;

        for (int pieceTypeIndex = 0; pieceTypeIndex < 6; pieceTypeIndex++)
        {
            PieceType pt = (PieceType)(pieceTypeIndex + 1);
            int baseVal = PieceValues[pieceTypeIndex];
            int[] pstForPieceType = pt == PieceType.King ? (isEndgame ? KingEndGamePST : KingMiddleGamePST) : PiecePSTs[pieceTypeIndex];

            ulong whiteBitboard = board.GetPieceBitboard(pt, true);
            if (pt == PieceType.Bishop) whiteBishopCount = BitOperations.PopCount(whiteBitboard);
            while (whiteBitboard != 0)
            {
                int squareIndex = BitOperations.TrailingZeroCount(whiteBitboard);
                score += baseVal + pstForPieceType[squareIndex];
                if (isEndgame && pt == PieceType.Pawn)
                {
                    score += new Square(squareIndex).Rank * 5;
                }
                whiteBitboard &= whiteBitboard - 1;
            }

            ulong blackBitboard = board.GetPieceBitboard(pt, false);
            if (pt == PieceType.Bishop) blackBishopCount = BitOperations.PopCount(blackBitboard);
            while (blackBitboard != 0)
            {
                int squareIndex = BitOperations.TrailingZeroCount(blackBitboard);
                score -= baseVal + pstForPieceType[squareIndex ^ 56];
                if (isEndgame && pt == PieceType.Pawn)
                {
                    score -= (7 - new Square(squareIndex).Rank) * 5;
                }
                blackBitboard &= blackBitboard - 1;
            }
        }

        const int BISHOP_PAIR_BONUS = 30;
        if (whiteBishopCount >= 2) score += BISHOP_PAIR_BONUS;
        if (blackBishopCount >= 2) score -= BISHOP_PAIR_BONUS;

        if (isEndgame && Math.Abs(EvaluateMaterialOnly(board)) > 150)
        {
            Square whiteKingSquare = board.GetKingSquare(true);
            Square blackKingSquare = board.GetKingSquare(false);
            int kingDist = Math.Abs(whiteKingSquare.File - blackKingSquare.File) + Math.Abs(whiteKingSquare.Rank - blackKingSquare.Rank);
            int proximityBonus = (14 - kingDist) * 5;
            if (score > 0) score += proximityBonus;
            else if (score < 0) score -= proximityBonus;
        }

        const int TEMPO_BONUS = 10;
        score += board.IsWhiteToMove ? TEMPO_BONUS : -TEMPO_BONUS;
        return board.IsWhiteToMove ? score : -score;
    }

    private int EvaluateMaterialOnly(Board board)
    {
        int materialScore = 0;
        for (int i = 0; i < 5; i++)
        {
            materialScore += PieceValues[i] * (board.GetPieceList((PieceType)(i + 1), true).Count - board.GetPieceList((PieceType)(i + 1), false).Count);
        }
        return materialScore;
    }

    private bool IsEndgame(Board board)
    {
        if (board.ZobristKey != lastBoardHash)
        {
            cachedPieceCount = BitOperations.PopCount(board.AllPiecesBitboard);
            lastBoardHash = board.ZobristKey;
        }
        return cachedPieceCount <= 11;
    }

    private string GetMateInMoves(int score)
    {
        if (Math.Abs(score) < MATE_FOUND_SCORE) return null;
        int sign = Math.Sign(score);
        int pliesToMate = (InfiniteScore - Math.Abs(score) + 49) / 50;
        return $"{(sign > 0 ? "Winning" : "Losing")} Mate in {pliesToMate} ply";
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
        this.bestScoreRoot = Evaluate(board) * (board.IsWhiteToMove ? 1 : -1);
        this.completedSearchDepth = completedDepthForLog;
        return LogEval(board, completedDepthForLog, isForcedMove, move);
    }

    private struct TTEntry
    {
        public ulong Key;
        public short Depth;
        public short Score;
        public byte Flag;
        public Move BestMove;
    }

    private const byte EXACT = 0, ALPHA = 1, BETA = 2;
    private int GetTTIndex(ulong key) => (int)(key & ttMask);

    private void AddTT(ulong key, int depth, short scoreForTT, byte flag, Move bestMove)
    {
        int index = GetTTIndex(key);
        ref TTEntry entry = ref tt[index];
        bool replace = entry.Key == 0 || depth > entry.Depth || (depth == entry.Depth && (flag == EXACT || (flag == BETA && entry.Flag == ALPHA)));
        if (replace)
        {
            entry.Key = key;
            entry.Depth = (short)depth;
            entry.Score = scoreForTT;
            entry.Flag = flag;
            if (flag == EXACT || flag == BETA || !bestMove.IsNull)
            {
                entry.BestMove = bestMove;
            }
            else if (flag == ALPHA && bestMove.IsNull && entry.BestMove.IsNull)
            {
                entry.BestMove = Move.NullMove;
            }
        }
    }

    private short AdjustMateScoreForTTStorage(int scoreFromNode, int currentRealPly)
    {
        if (Math.Abs(scoreFromNode) >= MATE_FOUND_SCORE) return (short)Math.Clamp(scoreFromNode, -(InfiniteScore - MAX_KILLER_PLY * 50), InfiniteScore - MAX_KILLER_PLY * 50);
        return (short)scoreFromNode;
    }

    private short AdjustMateScoreFromTT(short ttScore, int currentRealPly) => ttScore;

    private void DebugLog(string message)
    {
        Console.WriteLine($"{GetType().Name} {message}");
    }

    // --- Piece Square Tables ---
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

    private static readonly int[][] PiecePSTs = {
        PawnPST, KnightPST, BishopPST, RookPST, QueenPST, KingMiddleGamePST
    };
}