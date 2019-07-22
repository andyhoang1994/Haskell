import System.Environment
import System.IO (stdout,stderr,hPutStr,hPutStrLn)
import Data.Char
import Data.List
import Data.Bits
--
--

-- 1. An algebraic data type for regular expressions

data RE = Epsilon | Any | CC Bool [Char] | Ch Char | Seq RE RE | Alt RE RE | Star RE | Group RE | Plus RE deriving Show

-- 2. Setup for Glushkov algorithm and matching

-- Assignment 2 functions
countCh :: RE -> Int
matchesEmpty :: RE -> Bool
firstWithIndex :: Int -> RE -> [Int]
lastWithIndex :: Int -> RE -> [Int]
linearize :: Int -> [Int] -> [Int]
makePairs :: Int -> RE -> [[Int]]
assignBbits :: Char -> RE -> [Int]
assignInitialD :: Int -> Int -> [Int] -> [Int]
assignOtherD :: Int -> Int -> [[Int]] -> [Int]
findDVector :: Int -> [Int] -> RE -> [[Int]]
orEntries :: Int -> Int -> [[Int]] -> Int 
calculateDVector :: Int -> [[Int]] -> [Int]
assignFBits :: Int -> RE -> [Int] -> [Int]
andEntries :: Int -> [Int] -> [Int] -> [Int]
calculateMatch :: Int -> [Int] -> [Int] -> Bool
determineIfFinal :: [Int] -> RE -> Bool
substring :: Int -> Int -> [Char] -> [Char]
calculateLastState :: Int -> [Char] -> [Int] -> RE -> [Int]
makeSubstrings :: Int -> Int -> [Char] -> [[Char]]


-- Essential functions
firstSym :: RE -> [Int]
lastSym :: RE -> [Int]
symPairs :: RE -> [[Int]]
bVector :: Char -> RE -> [Int]
dVector :: [Int] -> RE -> [Int]
fVector :: RE -> [Int]
sZero :: RE -> [Int]
nextState :: [Int] -> Char -> RE -> [Int]
checkMatches :: Int -> [Char] -> RE -> Bool
printMatches :: Int -> [[Char]] -> RE -> [[Char]]

-- Linearization
-- Function used to add on the number of characters before a regex

linearize length list = map (length+) list

-- Glushkov States

countCh Epsilon = 0
countCh (Ch c) = 1
countCh (CC _ _) = 1
countCh Any = 1
countCh (Seq r1 r2) = (countCh r1) + (countCh r2)
countCh (Alt r1 r2) = (countCh r1) + (countCh r2)
countCh (Star r) = countCh r
countCh (Plus r) = countCh r
countCh (Group r) = countCh r

matchesEmpty Epsilon = True
matchesEmpty (Ch c) = False
matchesEmpty (CC _ _) = False
matchesEmpty Any = False
matchesEmpty (Seq r1 r2) = (matchesEmpty r1) && (matchesEmpty r2)
matchesEmpty (Alt r1 r2) = (matchesEmpty r1) || (matchesEmpty r2)
matchesEmpty (Star r) = True
matchesEmpty (Plus r) = False
matchesEmpty (Group r) = matchesEmpty r

-- Start Symbols
-- Finding the first symbols of a regex

firstWithIndex i Epsilon = []
firstWithIndex i (Ch c) = [i]
firstWithIndex i (CC _ _) = [i]
firstWithIndex i Any = [i]
firstWithIndex i (Seq r1 r2)
   | matchesEmpty r1 = (firstWithIndex i r1) ++ (firstWithIndex (i + countCh r1) r2)
   | otherwise       = (firstWithIndex i r1)
firstWithIndex i (Alt r1 r2) = (firstWithIndex i r1) ++ (firstWithIndex (i + countCh r1) r2)
firstWithIndex i (Star r) = firstWithIndex i r
firstWithIndex i (Plus r) = firstWithIndex i r
firstWithIndex i (Group r) = firstWithIndex i r

firstSym r = firstWithIndex 1 r

-- Final Symbols
-- Finding the last symbols of a regex

lastWithIndex i Epsilon = []
lastWithIndex i (Ch c) = [i]
lastWithIndex i (CC _ _) = [i]
lastWithIndex i Any = [i]
lastWithIndex i (Seq r1 r2)
   | matchesEmpty r2 = (lastWithIndex (i - countCh r2) r1) ++ (lastWithIndex i r2)
   | otherwise       = (lastWithIndex i r2)
lastWithIndex i (Alt r1 r2) = (lastWithIndex (i - countCh r2) r1) ++ (lastWithIndex i r2)
lastWithIndex i (Star r) = lastWithIndex i r
lastWithIndex i (Plus r) = lastWithIndex i r
lastWithIndex i (Group r) = lastWithIndex i r

lastSym r = lastWithIndex (countCh r) r

-- Symbol Pairs
-- Finding the symbol pairs of a regex

makePairs i Epsilon = []
makePairs i (Ch c) = []
makePairs i (CC _ _) = []
makePairs i Any = []
makePairs i (Seq r1 r2) = makePairs i r1 ++ (sequence([(linearize (i - 1) (lastSym r1)), (linearize (i + countCh r1 - 1) (firstSym r2))])) ++ (makePairs (i + countCh r1) r2)
makePairs i (Alt r1 r2) = makePairs i r1 ++ (makePairs (i + countCh r1) r2)
makePairs i (Star r) = makePairs i r ++ (sequence([(linearize (i - 1) (lastSym r)), (linearize (i - 1) (firstSym r))]))
makePairs i (Plus r) = makePairs i r ++ (sequence([(linearize (i - 1) (lastSym r)), (linearize (i - 1) (firstSym r))]))
makePairs i (Group r) = makePairs i r

symPairs r = sort(makePairs 1 r)

-- Bit-Parallel NFA Simulation



-- Constructing the B vectors

assignBbits char Epsilon = []
assignBbits char (Ch c)
   | char == c = [1]
   | otherwise = [0]
assignBbits char (CC True chars)
   | elem char chars = [1]
   | otherwise       = [0]
assignBbits char (CC False chars)
   | elem char chars == False = [1]
   | otherwise                = [0]
assignBbits char Any = [1]
assignBbits char (Seq r1 r2) = assignBbits char r2 ++ assignBbits char r1
assignBbits char (Alt r1 r2) = assignBbits char r2 ++ assignBbits char r1
assignBbits char (Star r) = assignBbits char r
assignBbits char (Plus r) = assignBbits char r
assignBbits char (Group r) = assignBbits char r

bVector c r = assignBbits c r ++ [1]

-- Constructing the D vectors

-- Assign vector for state 0 (first symbols)
assignInitialD i j first
   | i == j                                     = []
   | length first /= 0 && first !! 0 == (i + 1) = [1] ++ assignInitialD (i + 1) j (tail first)
   | otherwise                                  = [0] ++ assignInitialD (i + 1) j first

-- Assign vector for other states (symbol pairs)
assignOtherD i j pairs
   | i == j                                          = []
   | length pairs /= 0 && pairs !! 0 !! 1 == (i + 1) = [1] ++ assignOtherD (i + 1) j (tail pairs)
   | otherwise                                       = [0] ++ assignOtherD (i + 1) j pairs

-- Makes a list of all D vectors to be ORed
findDVector i s r 
   | i == length s = []
   | s !! i == 0 = [[1] ++ ([0] >>= replicate (length s - 1))] ++ findDVector (i + 1) s r
   | i == 0        = ([[1] ++ assignInitialD 0 (length s - 1) (firstSym r)]) ++ findDVector (i + 1) s r
   | otherwise     = ([[1] ++ assignOtherD 0 (length s - 1) (filter(\x->x !! 0 == i) (symPairs r))]) ++ findDVector (i + 1) s r

-- Or the bits of every vector
orEntries i j list
   | j == (length list) = 0
   | otherwise       = (.|.) (list!!j!!i) (orEntries i (j + 1) list)

-- Calculate the vector from the bits
calculateDVector i list
   | i == (length list) = []
   | otherwise          = [(orEntries i 0 list)] ++ (calculateDVector (i + 1) list)

dVector s r = reverse(calculateDVector 0 (findDVector 0 (reverse s) r))

-- Constructing the F vectors

assignFBits i r list
   | i == (countCh r + 1)                = []
   | i == 0 && (matchesEmpty r)          = assignFBits (i + 1) r list ++ [1]
   | i == 0 && (matchesEmpty r) == False = assignFBits (i + 1) r list ++ [0]
   | i == (list !! 0)                    = assignFBits (i + 1) r (tail list) ++ [1]
   | otherwise                           = assignFBits (i + 1) r list ++ [0]

fVector r = assignFBits 0 r (lastSym r)

-- Regular Expression Matching

-- Calculates the initial state
sZero r = ([0] >>= replicate (countCh r)) ++ [1]

andEntries i j k
   | i == (length j)              = []
   | (.&.) (j !! i) (k !! i) == 1 = [1] ++ andEntries (i + 1) j k
   | otherwise                    = [0] ++ andEntries (i + 1) j k

-- Calculates the next state
nextState s c r = andEntries 0 (dVector s r) (bVector c r)

-- Calculates value of Sn AND F vector
calculateMatch i j k
   | i == (length j)                 = False
   | ((.&.) (j !! i) (k !! i )) == 1 = True
   | otherwise                       = calculateMatch (i + 1) j k

-- Determines if last state (Sn) AND F vector is nonzero
determineIfFinal s r = calculateMatch 0 s (fVector r)

-- Function for calculating substring
substring start end text = take (end - start) (drop start text)

-- Calculates Sn of an input string
calculateLastState i s state r
   | i == length s = state
   | length s == 0 = state
   | otherwise     = calculateLastState (i + 1) s (nextState state (s !! i) r) r

-- Produces a list of all substrings of an input string
makeSubstrings i j s
   | i == length s = []
   | j == length s + 1 = makeSubstrings (i + 1) (i + 2) s
   | otherwise = [(substring i j s)] ++ makeSubstrings i (j + 1) s

-- Checks if an input string matches the regex
checkMatches i s r
   | i == (length (makeSubstrings 0 0 s))                                                = False
   | determineIfFinal (calculateLastState 0 ((makeSubstrings 0 0 s) !! i) (sZero r) r) r = True
   | otherwise                                                                           = checkMatches (i + 1) s r

-- Prints all the matches
printMatches i lines r
   | i == (length lines)           = []
   | checkMatches 0 (lines !! i) r = [(lines !! i)] ++ printMatches (i + 1) lines r
   | otherwise                     = printMatches (i + 1) lines r

-- Caseless Search
caseless [] = []
caseless (c:cs)
    | isUpper c  = '(':c:'|':(toLower c):')' : caseless cs
    | isLower c = '(':c:'|':(toUpper c):')' : caseless cs
    | otherwise  = c : caseless cs
-- 3.  A parser to convert text into regular expressions

parseRE :: [Char] -> Maybe (RE, [Char])
parseSeq :: [Char] -> Maybe (RE, [Char])
parseItem :: [Char] -> Maybe (RE, [Char])
parseElement :: [Char] -> Maybe (RE, [Char])
parseChar :: [Char] -> Maybe (RE, [Char])
parseCCitem :: [Char] -> Maybe (Char, [Char])
parseClassItems :: [Char] -> Maybe ([Char], [Char])

parseChar [] = Nothing
parseChar ('[':'^':more) =
    case parseClassItems(more) of
        Just (items, ']':yet_more) -> Just (CC False items, yet_more)
        _ -> Nothing
parseChar ('[':more) =
    case parseClassItems(more) of
        Just (items, ']':yet_more) -> Just (CC True items, yet_more)
        _ -> Nothing
parseChar ('\\':c:s)
  | isMetachar c   = Just (CC True [c], s)
  | otherwise      = Nothing
parseChar (c:s)
  | isMetachar c   = Nothing
  | otherwise      = Just (CC True [c], s)

isMetachar c = elem c "|*()\\.?+["
parseElement ('.':more) = Just (Any, more)
parseElement ('(':more) =
    case parseRE(more) of
        Just (re, ')':yet_more) -> Just(Group re, yet_more)
        _ -> Nothing
parseElement s = parseChar s

parseItem s =
   case parseElement(s) of
        Just (re, '*':more) -> Just (Star re, more)
        Just (re, '?':more) -> Just (Alt re Epsilon, more)
        Just (re, '+':more) -> Just (Plus re, more)
        Just (re, more) -> Just (re, more)
        _ -> Nothing

parseCCitem "" = Nothing
parseCCitem ('-':more) = Nothing
parseCCitem (']':more) = Nothing
parseCCitem "\\" = Nothing
parseCCitem ('\\':c:more) = Just (c, more)
parseCCitem (c: more) = Just (c, more)

parseClassItems [] = Nothing
parseClassItems (']':more) = Just([], ']':more)
parseClassItems s =
    case parseCCitem s of 
        Just (item, '-':more) -> 
            case parseCCitem more of
                Just (item2, yet_more) ->
                    case parseClassItems yet_more of
                        Just (items, furthermore) -> Just ([item .. item2] ++ items, furthermore)
                        _ -> Nothing
                _ -> Nothing
        Just (item, more) ->
            case parseClassItems more of
                Just (items, furthermore) -> Just (item:items, furthermore)
                _ -> Nothing
        _ -> Nothing

extendSeq :: (RE, [Char]) -> Maybe (RE, [Char])

parseSeq s =
    case parseItem(s) of
        Just (r, more_chars) -> extendSeq(r, more_chars)
        _ -> Nothing

extendSeq (e1, after1) =
    case parseItem(after1) of 
        Just(e2, more) -> extendSeq(Seq e1 e2, more)
        _ -> Just(e1, after1)

extendRE :: (RE, [Char]) -> Maybe (RE, [Char])
parseRE s =
    case parseSeq(s) of
        Just (r, more_chars) -> extendRE(r, more_chars)
        _ -> Nothing

extendRE (e1, []) = Just (e1, [])
extendRE (e1, '|' : after_bar) =
    case parseSeq(after_bar) of 
        Just(e2, more) -> extendRE(Alt e1 e2, more)
        _ -> Nothing
extendRE(e1, c:more) = Just (e1, c:more)

parseMain :: [Char] -> Maybe RE

parseMain s = case parseRE s of 
    Just (e, []) -> Just e
    _ -> Nothing

-- 4.  Searching for matching lines in a file

--matches :: RE -> [[Char]] -> [[Char]]
--matches re lines = printMatches 0 lines re
checking :: [Char] -> [[Char]] -> [[Char]]
checking regexp lines = case (take 2 regexp) of
                                "?i" -> matching (caseless (drop 2 regexp)) lines
                                _ -> matching regexp lines
matching :: [Char] -> [[Char]] -> [[Char]]
matching regexp lines = case parseMain regexp of
                            Just r -> printMatches 0 lines r
                            _ -> []

-- 5.  Command line interface

main = do
  [regExp, fileName] <- getArgs
  srcText <- readFile fileName
  hPutStr stdout (unlines (checking regExp (lines srcText)))
