module Implementation where
    import DomsMatch
    import Data.List
    import Debug.Trace
    import System.Random

    -- types for module
    type Tactic = Hand -> DominoBoard -> Player -> Scores -> Play
    type Play = (Domino, End, Float)
    type Move = (Domino, End, Float, DominoBoard) -- where Float is the numeric scoring metric for said move


    -- PLAYERS
         
    {- score dominoes player - uses tactics first drop and playing highest domino -}
    scorePlayer :: DomsPlayer
    scorePlayer hand@(domino:rest) board player scores 
        | board == InitBoard && findDom hand (4, 5) = ((4, 5), L) -- check if first drop tactic is playable
        | otherwise =  (domino, end)
            where
                (domino, end, _) = playHighest hand board player scores 

    {- defensive dominoes player - plays dominoes that will prevent opponent from getting more points -}
    defensivePlayer :: DomsPlayer
    defensivePlayer hand board p s  = (domino, end)
        where 
            (domino, end, _) = playDefensive hand board p s
    
    {- play highest domino, unless no high scoring domino then play defensive -}
    tacticalPlayer :: DomsPlayer
    tacticalPlayer hand board p s = (domino, end)
        where
            (domino, end, _)
                | score > 0 = (d, e, score)
                | otherwise = playDefensive hand board p s
                    where 
                        (d, e, score) = playHighest hand board p s

    {- optimal dominoes player - plays domino based on highest score and lowest average opponent score -}
    optimalPlayer :: DomsPlayer
    optimalPlayer hand board p s  = (domino, end)
        where 
            (domino, end, _) = playOptimal hand board p s

    {- prolong dominoes player - plays the highest scoring domino, unless no score then play domino with majority favouring -}
    prolongPlayer :: DomsPlayer
    prolongPlayer hand board player score = (domino, end) 
        where 
            (domino, end, _)
                | s > 0 = scoreMove
                | otherwise = playMajority hand board player score
                    where 
                        scoreMove@(_, _, s) = playHighest hand board player score

    {- plays highest scoring domino, unless near win -}
    nearWinPlayer :: DomsPlayer
    nearWinPlayer hand board player score@(l, r) = (domino, end)
        where 
            playerScore 
                | player == P1 = l
                | otherwise = r
            (domino, end, _)
                | playerScore > 54 && s > 0 = winMove
                | otherwise = playHighest hand board player score 
                    where 
                        winMove@(_, _, s) = nearWin hand board player score
    
    {- plays hardest to score off domino, unless opponent about to win then try block -}
    blockPlayer :: DomsPlayer
    blockPlayer hand board player score@(l, r) = (domino, end)
        where 
            opponentScore 
                | player == P1 = r
                | otherwise = l
            (domino, end, _)
                | opponentScore > 54 && s > 0 = blockMove -- block win if possible
                | otherwise = playDefensive hand board player score -- otherwise play highest
                    where 
                        blockMove@(_, _, s) = blockWin hand board player score
    
    {- improve optimal player making use of the near win tactic -}
    improvedOptimalPlayer1 :: DomsPlayer
    improvedOptimalPlayer1 hand board player score@(l, r) = (domino, end)
        where 
            playerScore 
                | player == P1 = l
                | otherwise = r
            (domino, end, _)
                | playerScore > 54 && s > 0 = winMove
                | otherwise = playOptimal hand board player score 
                    where 
                        winMove@(_, _, s) = nearWin hand board player score


    {- improve optimal player making use of the near win tactic -}
    improvedOptimalPlayer2 :: DomsPlayer
    improvedOptimalPlayer2 hand board player score@(l, r) = (domino, end)
        where 
            playerScore 
                | player == P1 = l
                | otherwise = r
            opponentScore 
                | player == P1 = r
                | otherwise = l
            (domino, end, _)
                | playerScore > 54 && s1 > 0 = winMove
                | opponentScore > 54 && s2 > 0 = blockMove
                | otherwise = playOptimal hand board player score 
                    where 
                        winMove@(_, _, s1) = nearWin hand board player score
                        blockMove@(_, _, s2) = blockWin hand board player score


    -- TACTICS

    {- return the highest scoring domino -}
    playHighest :: Tactic
    playHighest hand board _ _ = (domino, end, score) 
        where
            ((domino, end, score, _) : _) = findScores hand board 
    
    {- returns the domino with on average lowest possible score for opponents next turn-}
    playDefensive :: Tactic 
    playDefensive hand board _ _ = (domino, end, score)
        where 
            (domino, end, score, _) = last moves -- return move with least score
                where
                    moves = checkNextTurn hand board
    
    {- return the optimal domino based on gained score and potential opponent score -}
    playOptimal :: Tactic 
    playOptimal hand board _ _ = (domino, end, score)
        where 
            ((domino, end, score, _) : _) = findAvgScores (findScores hand board) (findRemainingDoms hand board)
    
    {- play dominoes with corresponding to highest majority of spot value in hand -}
    playMajority :: Tactic
    playMajority hand board _ _ = (domino, end, score)
        where 
            ((domino, end, score, _) : _) = sortBy sortMoves (findMajorityScores (findMoves hand board) (findMajority hand))
    
    {- tactic to achieve score 61 or 59 when near a win -}
    nearWin :: Tactic
    nearWin hand@(d:_) board p (s1, s2)
        | not (null (moves 61)) = head (moves 61)
        | not (null (moves 59)) = head (moves 59)
        | otherwise = (d, L, 0) -- return score of 0 if no win play
        where
            moves req = [(domino, end, 1) | (domino, end) <- scoreN board (needed req), findDom hand domino]
                where
                    needed n
                        | p == P1 = n - s1
                        | otherwise = n - s2
    
    {- try to prevent opponent from winning -}
    blockWin :: Tactic
    blockWin hand@(d:_) board p score@(s1, s2) = blockWin' needed (findMoves hand board)
        where 
            needed 
                | p == P1 = 61 - s2 -- reverse score for opponents
                | otherwise = 61 - s1
            blockWin' n moves
                | not (null blocks) = head blocks
                | otherwise = (d, L, 0) -- return score of 0 if no way to block win
                    where 
                        blocks = blockMoves moves (findRemainingDoms hand board) n
                              

    -- ADDITIONAL FUNCTIONS 

    {- return whether or not hand has domino -}
    findDom :: Hand -> Domino -> Bool
    findDom [] _ = False
    findDom (domino : rest) d@(l,r)
        | domino == (l,r) = True 
        | otherwise = findDom rest d  
    
    {- finds all playable dominoes putting them into a list of moves -}
    findMoves :: Hand -> DominoBoard -> [Move]
    findMoves hand board = 
        let
            (l, r) = possPlays hand board
            left = [(d, L, 0, newBoard) | d <- l,
                let Just newBoard = playDom P1 d board L]
            right = [(d, R, 0, newBoard) | d <- r,
                let Just newBoard = playDom P1 d board R]
        in 
            left ++ right

    {- calculates the score each playable domino will give -}
    findScores :: Hand -> DominoBoard -> [Move]
    findScores hand board = sortBy sortMoves (findScores' (findMoves hand board))
        where 
            findScores' [] = []
            findScores' ((d, e, _, b):rest) = (d, e, float (scoreBoard b), b) : findScores' rest 
    
    {- find what dominoes the opponent may have -}
    findRemainingDoms :: Hand -> DominoBoard -> [Domino]
    findRemainingDoms hand InitBoard = domSet\\hand 
    findRemainingDoms hand (Board _ _ history) = domSet\\(hand ++ played)
        where
            played = [d | (d,_,_) <- history]
    
    {- find the average score a player can make from board and remaining dominoes -} 
    checkNextTurn :: Hand -> DominoBoard -> [Move]
    checkNextTurn hand board = sortBy sortMoves (checkNextTurn' (findMoves hand board) (findRemainingDoms hand board))
        where
            checkNextTurn' [] _ = []
            checkNextTurn' ((d, e, _, b) : rest) dominoes = (d, e, defensiveScore dominoes b, b) : checkNextTurn' rest dominoes

    {- find the average score a player can make from board and remaining dominoes -} 
    findAvgScores :: [Move] -> [Domino] -> [Move]
    findAvgScores [] _ = []
    findAvgScores (move@(d, e, s, b) : rest) dominoes = sortBy sortMoves ((d, e, s - (defensiveScore dominoes b * 4), b) : findAvgScores rest dominoes)
    
    {- find the average score opponent can gain from remaining dominoes -}
    defensiveScore :: [Domino] -> DominoBoard -> Float
    defensiveScore dominoes board = sumScores (findScores dominoes board) / float (length dominoes)
            
    {- compute number of face value dominoes for majority scoring play -}
    findMajority :: Hand -> [(Int, Int)]
    findMajority hand = [(a, b) |
                            a <- [0..6],
                            let b = findVal a hand 
                                findVal a [] = 0
                                findVal a ((l, r) : rest)
                                    | l == r && l == a = 2 + findVal a rest
                                    | l == a || r == a = 1 + findVal a rest
                                    | otherwise = 0 + findVal a rest]

    {- compute a score based on how many dominoes you can play off new board -}
    findMajorityScores :: [Move] -> [(Int, Int)] -> [Move]
    findMajorityScores [] _ = []
    findMajorityScores ((d, e, _, board@(Board (l, _) (_, r) _)) : rest) occurs = (d, e, score, board) : findMajorityScores rest occurs
        where
            score = float (sum [a | (i, a) <- occurs, i == l || i == r])

    {- function to find any moves that will block opponent win -}
    blockMoves :: [Move] -> [Domino] -> Int -> [Play]
    blockMoves [] _ _= []
    blockMoves (move@(dom, end, _, board) : rest) remainingDoms score 
        | blockMoves' board remainingDoms score = (dom, end, 1) : blockMoves rest remainingDoms score
        | otherwise = blockMoves rest remainingDoms score
        where 
            blockMoves' b d s = not (null winDom)
                where 
                    winDom = [w | (w, e) <- scoreN b s, w `notElem` d] 
    
    {- sum scores from list of moves -}
    sumScores :: [Move] -> Float
    sumScores [] = 0
    sumScores (move@(_,_,score,_):rest) = score + sumScores rest 

    {- function to sort moves by score -}
    sortMoves :: Move -> Move -> Ordering
    sortMoves (_, _, a, _) (_, _, b, _)
        | a > b = LT
        | a < b = GT
        | otherwise = EQ

    {- convert int to float -}
    float :: Int -> Float
    float i = fromIntegral i :: Float                 