module AP where
import qualified Data.Set as S
main :: IO ()
main = putStrLn "AP from Lin Großmann and Shalize Oktar"

--- pretty-printers:
chop = putStrLn ("x1 ⍺Cβ x3" ++ "\n" ++ "x1"  ++ "---------" ++ "x2"  ++ "---------" ++ "x3" ++ "\n" ++ "x1" ++ "----" ++ "⍺" ++ "----" ++ "x2" ++ "----" ++ "β" ++ "----" ++ "x3")
done = putStrLn ("x2 ⍺Dβ x3" ++ "\n" ++ "x1" ++ "       " ++ "x2"  ++ "---------" ++ "x3" ++ "\n" ++ "x1" ++ "---" ++ "⍺" ++ "---" ++ "x2" ++ "\n" ++ "x1" ++ "---------" ++ "β" ++ "--------" ++ "x3")
tocome = putStrLn ("x1 ⍺Tβ x2" ++ "\n" ++ "x1" ++ "---" ++ "x2"  ++ "       " ++ "x3" ++ "\n" ++ "x1" ++ "------" ++ "β" ++ "-----" ++ "x3" ++ "\n" ++ "     " ++ "x2" ++ "---" ++ "⍺" ++ "---" ++ "x3")

type Name = String
newtype Var = Var Name deriving (Eq,Show,Ord)
    
data Formula = Atomic String [Var] | Neg Formula | Formula `Impl` Formula | Formula `Conj` Formula | Formula `Disj` Formula | Formula `Chop` Formula | Formula `Done` Formula | Formula `ToCome` Formula | PointInterval deriving Eq

data XalphaY = XAY Interval Formula deriving Eq

data Deduction = Cplus XalphaY XalphaY | Cminus XalphaY | Dplus XalphaY XalphaY | Dminus XalphaY | Tplus XalphaY XalphaY deriving Eq

instance Show Formula where
  show (Atomic p vs) = p ++ printVars vs
  show (Neg p) = "¬" ++ "(" ++ show p ++ ")"
  show (Impl p q) = "(" ++ show p ++ " → " ++ show q ++ ")"
  show (Conj p q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
  show (Disj p q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
  show (Chop p q) = "(" ++ show p ++ " C " ++ show q ++ ")" 
  show (Done p q) = "(" ++ show p ++ " D " ++ show q ++ ")" 
  show (ToCome p q) = "(" ++ show p ++ " T " ++ show q ++ ")" 
  show (PointInterval) = "𝜋"
  
instance Show XalphaY where
    show (XAY (s,t) f) = show s ++ "(" ++ show f ++ ")" ++ show t
    
instance Show Deduction where
    show (Cplus p q) = "(C+) " ++ show p ++ " " ++ show q
    show (Dplus p q) = "(D+) " ++ show p ++ " " ++ show q
    show (Tplus p q) = "(T+) " ++ show p ++ " " ++ show q
    
type Time = Int
type Interval = (Time, Time)

data Frame = Frame {points :: [Time], linearOrder :: Time -> Time -> Bool}

type Val = String -> S.Set Interval

data Model = Model {frame :: Frame, val :: Val}

--- helper-functions:
commaSep :: [String] -> String
commaSep [] = ""
commaSep [x] = x
commaSep (x:xs) = x ++ "," ++ commaSep xs

varToString :: Var -> String
varToString (Var v) = v

printVars :: [Var] -> String
printVars vs = "(" ++ commaSep (map varToString vs) ++ ")"
  
at :: String -> String -> Formula
at p v = Atomic p [Var v]

fIntervals :: Frame -> [Interval]
fIntervals fINT = [(s,t) | s <- points fINT, t <- points fINT, s <= t]

iFrame :: Interval -> Interval -> Interval -> Bool
iFrame (s,t) (u,v) (w,x) = s == w && t == u && v == x

isPoint :: Interval -> Bool
isPoint (s,t) = s == t

intervals :: Model -> [Interval]
intervals m = fIntervals (frame m)

--- evaluation:
eval :: Model -> Interval -> Formula -> Bool
eval m i@(s,t) f = case f of

  Atomic p vs ->
    i `S.member` val m p

  PointInterval ->
    isPoint i

  Neg p ->
    not (eval m i p)

  Conj p q ->
    eval m i p && eval m i q

  Disj p q ->
    eval m i p || eval m i q

  Impl p q ->
    not (eval m i p) || eval m i q

  Chop p q ->
    or [ eval m j p && eval m k q
       | j <- intervals m
       , k <- intervals m
       , iFrame j k i ]

  ToCome p q ->
    or [ eval m j p && eval m k q
       | j <- intervals m
       , k <- intervals m
       , iFrame i j k ]

  Done p q ->
    or [ eval m j p && eval m k q
       | j <- intervals m
       , k <- intervals m
       , iFrame j i k ]
       
--- deduction:    
deduct :: Model -> Deduction -> [XalphaY]
deduct m (Cplus (XAY i@(s,t) p) (XAY j@(u,v) q)) =
    if t == u && eval m i p && eval m j q
    then [(XAY (s,v) (Chop p q))]
    else error "Deduction failed."

deduct m (Dplus (XAY i@(s,t) p) (XAY j@(u,v) q)) =
    if s == u && eval m i p && eval m j q && t <= v
    then [(XAY (t,v) (Done p q))]
    else error "Deduction failed."

deduct m (Tplus (XAY i@(s,t) p) (XAY j@(u,v) q)) =
    if t == v && eval m i p && eval m j q && s <= u
    then [(XAY (s,u) (ToCome q p))]
    else error "Deduction failed."
    
--- example (for testing):
exampleFrame :: Frame
exampleFrame = Frame {points = [0..10],linearOrder = (<)}
  
exampleVal :: Val
exampleVal "asleep" = S.fromList [(0,2)]
exampleVal "awake" = S.fromList [(2,3)]
exampleVal "eating" = S.fromList [(4,5),(8,9)]
exampleVal "working" = S.fromList [(5,6)]
exampleVal "jogging" = S.fromList [(6,7)]
exampleVal "worktime" = S.fromList [(s,t) | s <- [3..7], t <- [s..8]]
exampleVal "freetime" = S.fromList [(s,t) | s <- [6,7], t <- [7,8]]
exampleVal "alarm"  = S.fromList [(2,2)]
exampleVal "night"  = S.fromList [(s,t) | s <- [0..3], t <- [s..3]]
exampleVal "day"    = S.fromList [(s,t) | s <- [3..8], t <- [s..8]]
exampleVal _ = S.empty

exampleModel :: Model
exampleModel = Model {frame = exampleFrame,val = exampleVal}