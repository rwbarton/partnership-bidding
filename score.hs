#!/usr/bin/runhaskell

import Control.Applicative
import Control.Arrow
import Control.Monad.State
import Data.Array
import Data.Char
import Data.List
import Data.Maybe
import Data.Ratio
import System.Environment
import System.IO
import System.Process
import System.Random
import Text.Printf
import qualified Data.Map as M


-- Cards and hands 
data Suit = C | D | H | S deriving (Eq, Ord, Show, Enum)
data Rank = Spot Integer | T | J | Q | K | A deriving (Eq, Ord)
data Card = Card Suit Rank deriving Eq
newtype Hand = Hand [Card]

suits = [C, D, H, S]
ranks = map Spot [2..9] ++ [T,J,Q,K,A]
deck = Card <$> suits <*> ranks

instance Show Rank where
  show (Spot n) = show n
  show T = "T"
  show J = "J"
  show Q = "Q"
  show K = "K"
  show A = "A"

instance Show Card where
  show (Card s r) = show s ++ show r

instance Show Hand where
  show (Hand cs) = intercalate "." [ concat [ show r | r <- reverse ranks, Card s r `elem` cs ]
                                   | s <- reverse suits ]

readHand :: String -> Hand
readHand str = Hand $ concat $ zipWith (map . Card) (reverse suits) (map readSuit pieces)
  where readSuit = map readCard
        readCard 'T' = T
        readCard 'J' = J
        readCard 'Q' = Q
        readCard 'K' = K
        readCard 'A' = A
        readCard n = Spot $ read [n]
        pieces = words $ map (\x -> if x == '.' then ' ' else x) str

-- A lazy pseudorandom (but with fixed seed) stream of possible
-- distributions of the opposing cards
dealOpponents :: (Hand, Hand) -> [(Hand, Hand)]
dealOpponents (Hand n, Hand s) = evalState (sequence $ repeat dealOne) (mkStdGen 17)
  where remaining = deck \\ (n++s)
        assign [] 0 0 = return ([], [])
        assign (c:cs) remE remW = do
          g <- get
          let (x, g') = randomR (1 :: Integer, remE + remW) g
          put g'
          if x <= remE
            then first (c:) <$> assign cs (remE-1) remW
            else second (c:) <$> assign cs remE (remW-1)
        dealOne = do
          (e, w) <- assign remaining 13 13
          return (Hand e, Hand w)


-- Contracts
data Strain = Suit Suit | NT deriving (Eq, Ord)
data Level = One | Two | Three | Four | Five | Six | Seven deriving (Eq, Ord, Enum)
data Declarer = North | South deriving (Eq, Ord) -- We only let NS play the hand
data Contract = Pass | Contract Level Strain Declarer deriving (Eq, Ord)
-- We don't care about doubled or redoubled contracts.  We assume the
-- opponents never double.
type DoubleDummyData = M.Map (Strain, Declarer) Integer

strains = (Suit <$> suits) ++ [NT]
levels = [One .. Seven]
declarers = [North, South]
contracts = Pass : (Contract <$> levels <*> strains <*> declarers)

tricks :: Level -> Integer
tricks l = 7 + fromIntegral (fromEnum l)

fromNumber :: Integer -> Level
fromNumber n = toEnum (fromInteger n - 1)

instance Show Strain where
  show (Suit s) = show s
  show NT = "N"

instance Show Level where
  show l = show $ 1 + fromEnum l

instance Show Declarer where
  show North = "N"
  show South = "S"

instance Show Contract where
  show Pass = "PASS"
  show (Contract l s d) = show l ++ show s ++ " " ++ show d

-- Run the double-dummy solver on a deal to find how many tricks can
-- be taken with each strain and declarer
doubleDummy :: (Hand, Hand) -> (Hand, Hand) -> IO DoubleDummyData
doubleDummy (n, s) (e, w) =
  do let cmd = "dds /dev/stdin -giblib=1-1"
     (input, output, err, proc) <- runInteractiveCommand cmd
     hPutStr input hand
     hClose input
     let getResultLine = do
           line <- hGetLine output
           case stripPrefix resultLinePrefix line of
             Just line' -> return line'
             Nothing -> getResultLine
     resultLine <- getResultLine
     hClose output
     hClose err
     return $ M.fromList . zip [(strain, declarer) | strain <- reverse strains, declarer <- declarers] .
       map (read . ("0x"++) . return) . filter (/= '-') . takeWhile (/= ' ') $ resultLine
    where hand = (unwords . map show) [w, n, e, s] ++ ":" ++ take 20 (cycle "-0")
          resultLinePrefix = "       tricks="


-- Scoring
data Vulnerability = Nonvulnerable | Vulnerable
newtype Score = Score Integer deriving (Eq, Ord)

score :: Contract -> Integer -> Vulnerability -> Score
score Pass _ _ = Score $ 0
score (Contract l s _) n v | n < t = Score $ trickPenalty * (t-n)
  where t = tricks l
        trickPenalty = case v of
          Nonvulnerable -> -50
          Vulnerable -> -100
score (Contract l s _) n v = Score $ (n - 6) * trickScore + ntBonus + partScoreOrGameBonus + slamBonus
  where trickScore = case s of
          Suit C -> 20
          Suit D -> 20
          Suit H -> 30
          Suit S -> 30
          NT -> 30
        ntBonus = if s == NT then 10 else 0
        partScoreOrGameBonus = if (tricks l - 6) * trickScore + ntBonus >= 100
                               then case v of
                                 Nonvulnerable -> 300
                                 Vulnerable -> 500
                               else 50
        slamBonus = case (l, v) of
          (Six, Nonvulnerable) -> 500
          (Six, Vulnerable) -> 750
          (Seven, Nonvulnerable) -> 1000
          (Seven, Vulnerable) -> 1500
          _ -> 0

type Scoring = Score -> Score -> Rational -- like (-)
matchpoints :: Scoring
matchpoints s1 s2 = case compare s1 s2 of
  GT -> 100
  EQ -> 50
  LT -> 0

imps :: Scoring
imps s1 s2 | s1 < s2 = - imps s2 s1
imps (Score s1) (Score s2) = fromIntegral . fromMaybe 24 $ findIndex (> s1-s2)
                             [20,50,90,130,170,220,270,320,370,430,500,600,750,900,
                              1100,1300,1500,1750,2000,2250,2500,3000,3500,4000]

average :: Scoring -> Rational
average scoring = scoring (Score 0) (Score 0)

-- Given a set of possible double-dummy results, the vulnerability,
-- the form of scoring, and two contracts, compare the score
-- expectation of the first relative to the second.
relativeScore :: [DoubleDummyData] -> Vulnerability -> Scoring -> Contract -> Contract -> Rational
relativeScore ddd v scoring c1@(~(Contract _ s1 d1)) c2@(~(Contract _ s2 d2)) =
  sum [ score c1 (r M.! (s1, d1)) v `scoring` score c2 (r M.! (s2, d2)) v | r <- ddd ] / fromIntegral (length ddd)

-- Find the contract that beats all other contracts, if there is one.
topSpot :: [DoubleDummyData] -> Vulnerability -> Scoring -> Maybe Contract
topSpot ddd v scoring = if and [ c `cmp` c' /= LT | c' <- contracts ] then Just c else Nothing
  where c = maximumBy cmp contracts
        cmp c1 c2 = compare (relativeScore ddd v scoring c1 c2, c2) (average scoring, c1)
                    -- With equal scores, prefer the lower contract:
                    -- the usual situation is, say, 2H was making on
                    -- all of the sample deals, but there might be
                    -- some rare layout where only 1H can be made.

makingProbability :: [DoubleDummyData] -> Contract -> Maybe Rational
makingProbability _ Pass = Nothing
makingProbability ddd (Contract l s d) = Just $
  fromIntegral (length [ r | r <- ddd, r M.! (s, d) >= tricks l ]) % fromIntegral (length ddd)

appraise :: Vulnerability -> Scoring -> (Hand, Hand) -> Contract -> Int -> IO [(Rational, Contract)]
appraise v scoring ns c samples = do
  ddd <- mapM (doubleDummy ns) (take samples $ dealOpponents ns)
  return $ sort [ (relativeScore ddd v scoring c c', c') | c' <- contracts ]

averageScore :: Vulnerability -> Scoring -> (Hand, Hand) -> Contract -> Int -> IO (Rational, Contract) 
averageScore v scoring ns c samples = do
  (ddd, ddd') <- splitAt samples <$> mapM (doubleDummy ns) (take (2 * samples) $ dealOpponents ns)
  let Just c' = topSpot ddd' v scoring -- if this pattern match fails, your hand may be quite interesting!
  return $ (relativeScore ddd v scoring c c', c')
  -- We use two independent sets of double-dummy results for choosing
  -- the top spot and evaluating it relative to the chosen contract.
  -- This eliminates a (small?) bias towards the computer-determined
  -- spot, at the cost of doubling the computation time.


-- A command-line front end; contains some code duplication with the
-- above IO actions so as to reuse double dummy data
realToDouble :: Real a => a -> Double
realToDouble = realToFrac

main :: IO ()
main = do
  [nStr, sStr, vStr, scoringStr, cStr] <- map (map toUpper) <$> getArgs
  let ns = (readHand nStr, readHand sStr)
      v = case vStr of
        "NV" -> Nonvulnerable
        "V" -> Vulnerable
      scoring = case scoringStr of
        "IMPS" -> imps
        "MPS" -> matchpoints
      c = case cStr of
        "PASS" -> Pass
        [levelChar, strainChar, declarerChar] -> Contract (fromNumber $ read [levelChar]) strain declarer
          where strain = case strainChar of
                  'C' -> Suit C
                  'D' -> Suit D
                  'H' -> Suit H
                  'S' -> Suit S
                  'N' -> NT
                declarer = case declarerChar of
                  'N' -> North
                  'S' -> South
      samples = 50
  (ddd, ddd') <- splitAt samples <$> mapM (doubleDummy ns) (take (2 * samples) $ dealOpponents ns)
  let Just c' = topSpot ddd' v scoring
  putStrLn $ "Best contract: " ++ show c'
  putStrLn $ "Your score: " ++ (printf " %6.2f" $ (realToDouble $ relativeScore ddd v scoring c c'))
  putStrLn "Relative to other contracts:"
  let relativeOther = sort [ (relativeScore ddd v scoring c c', c') | c' <- contracts ]
      trimmed = better ++ [you] ++ take 10 worse
        where (better, you : worse) = span ((/= c) . snd) relativeOther
  forM_ trimmed $ \(score, c') -> do
    let p = makingProbability ddd c'
    printf " %6.2f %s (%s) %s\n" (realToDouble score) (show c') (maybe "----" (printf "%3.0f%%" . realToDouble . (100 *)) p) (if c == c' then " <--" else "")
