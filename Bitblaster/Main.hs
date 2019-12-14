{-# OPTIONS_GHC -Wall -Werror #-}
{-# LANGUAGE DeriveFunctor #-}

module Main where

import System.Environment
import Data.Maybe
import Data.List
import Foreign.Marshal.Utils
import Text.Read


-------------- Data Type for CNF Formulas --------------

-- A Clause is a disjunction of literals (denoted by integers)
data Clause = Disj [Int] deriving (Eq)

instance Show Clause where
    show (Disj []) = "0"
    show (Disj (x:xs)) = show x ++ " " ++ show (Disj xs)

-- Get the variable with the highest number in a clause
maxVarOfClause :: Clause -> Int
maxVarOfClause (Disj c) = maximum $ map abs c        -- literals can be negative -> take the absolute value


-- A (CNF) Formula is a conjunction of clauses
data CNFFormula = Conj [Clause]

-- Printing a SAT formula
instance Show CNFFormula where
    show (Conj c) = unlines $ ["p cnf " ++ numVars ++ " " ++ numClauses] ++ (map show c)
        where numVars = show $ maxVarOfFormula (Conj c)   -- Highest variable number as variable count
              numClauses = show $ length c

-- Conjoin (and) a list of SAT formulas
conjoin :: [CNFFormula] -> CNFFormula
conjoin fs = Conj $ concat (map (\(Conj d) -> d) fs)

-- Get the variable with the highest number in a formula
maxVarOfFormula :: CNFFormula -> Int
maxVarOfFormula (Conj c) = maximum (map maxVarOfClause c)

-- Drop duplicate clauses
shorten :: CNFFormula -> CNFFormula
shorten (Conj ds) = Conj (nub ds)


-------------- Data Type for more general Boolean Logic/SAT --------------

data BooleanLogic = BConst Bool | Variable Int deriving (Eq)
type SATFormula = LogicExpression BooleanLogic

instance Show BooleanLogic where
    show (BConst True) = "⊤"
    show (BConst False) = "⊥"
    show (Variable i) = "x" ++ show i

-- Find the highest variable number in a boolean logic expression
maxVarOfExpression :: SATFormula -> Int
maxVarOfExpression e = maximum variablesOfExpression
    where variablesOfExpression = map varNum (subExpressions e)
          varNum :: SATFormula -> Int
          varNum (Atom (Variable i)) = i
          varNum _ = 0

-------------- General Logic Expressions --------------

-- Arbitrary logical expression (tree)
data LogicExpression l = Atom l
                        | Not (LogicExpression l)
                        | And (LogicExpression l) (LogicExpression l)
                        | BigAnd [LogicExpression l]
                        | Or (LogicExpression l) (LogicExpression l)
                        | BigOr [LogicExpression l]
                        | Xor (LogicExpression l) (LogicExpression l)
                        | Implies (LogicExpression l) (LogicExpression l)
                        | Equivalent (LogicExpression l) (LogicExpression l)
                        deriving (Eq, Functor)

instance Show l => Show (LogicExpression l) where
    show (Atom a) = show a
    show (Not x) = "¬" ++ show x
    show (And x y) = "(" ++ show x ++ " ∧ " ++ show y ++ ")"
    show (BigAnd []) = "⊤"
    show (BigAnd (x:xs)) = "(" ++ show x ++ concat (map (\y -> " ∧ " ++ show y) xs) ++ ")"
    show (Or x y) = "(" ++ show x ++ " ∨ " ++ show y ++ ")"
    show (BigOr []) = "⊥"
    show (BigOr (x:xs)) = "(" ++ show x ++ concat (map (\y -> " ∨ " ++ show y) xs) ++ ")"
    show (Xor x y) = "(" ++ show x ++ " ⊕ " ++ show y ++ ")"
    show (Implies x y) = "(" ++ show x ++ " → " ++ show y ++ ")"
    show (Equivalent x y) = "(" ++ show x ++ " ↔ " ++ show y ++ ")"


-- The direct subexpressions (children) of a logical expression (node)
directSubExpressions :: (LogicExpression l) -> [LogicExpression l]
directSubExpressions (Equivalent e f) = [e, f]
directSubExpressions (Implies e f) = [e, f]
directSubExpressions (Xor e f) = [e, f]
directSubExpressions (BigOr es) = es
directSubExpressions (Or e f) = [e, f]
directSubExpressions (BigAnd es) = es
directSubExpressions (And e f) = [e, f]
directSubExpressions (Not e) = [e]
directSubExpressions (Atom _) = []

-- All (recursive) subexpressions of a logical expression (including itself)
subExpressions :: (LogicExpression l) -> [LogicExpression l]
subExpressions e = e : (concat $ map subExpressions (directSubExpressions e))

-- Find index of subexpression in list of an expression's subexpressions
subExpressionIndex :: Eq l => (LogicExpression l) -> (LogicExpression l) -> Int
subExpressionIndex expr subExp = (fromJust $ findIndex (==subExp) (subExpressions expr))

-- Whether a given logic expression is an atom
isAtom :: (LogicExpression l) -> Bool
isAtom (Atom _) = True
isAtom _ = False

-- All atoms contained in a logic expression
atoms :: (LogicExpression l) -> [LogicExpression l]
atoms e = filter isAtom $ subExpressions e

-- All atoms contained in a logic expression, given in the respective logic
logicAtoms :: (LogicExpression l) -> [l]
logicAtoms e = map (\(Atom a) -> a) (atoms e)

-- Atom number of an atom in a logic expression
atomIndex :: Eq l => (LogicExpression l) -> l -> Int
atomIndex f a = fromJust $ findIndex (==a) (logicAtoms f)

-- The boolean skeleton / propositional abstraction of a logic expression
booleanSkeleton :: Eq l => (LogicExpression l) -> SATFormula
booleanSkeleton f = fmap (\a -> (Variable $ (atomIndex f a) + 1)) f


-- Make a list of two logical expressions each equivalent
allEquivalences :: [LogicExpression a] -> [LogicExpression a] -> LogicExpression a
allEquivalences as bs = BigAnd $ map (\(a,b) -> Equivalent a b) (zip as bs)

-- Negate all the expressions
negateAll :: [LogicExpression a] -> [LogicExpression a]
negateAll = map Not

-- Return the conjunctions of two terms each
andAll :: [LogicExpression a] -> [LogicExpression a] -> [LogicExpression a]
andAll as bs = map (\(a,b) -> a `And` b) $ zip as bs

-- Return the disjunctions of two terms each
orAll :: [LogicExpression a] -> [LogicExpression a] -> [LogicExpression a]
orAll as bs = map (\(a,b) -> a `Or` b) $ zip as bs


-------------- Bit Vector Logic --------------

data BitVector = BVVar String Int                   -- Variable Bit Vector with name and certain length
                | BVConst [Bool]                    -- Constant Bit Vector
                | BVnk Int Int                      -- bv_n,k
                | BVConcat BitVector BitVector      -- concat x y
                | BVExtract Int Int BitVector       -- extract_i,j x
                | BVZeroExtend Int BitVector        -- zero extend_n x
                | BVSignExtend Int BitVector        -- sign extend_n x
                | BVNot BitVector                   -- logical not
                | BVAnd BitVector BitVector         -- logical and
                | BVOr BitVector BitVector          -- logical or
                | BVShl BitVector BitVector         -- logical left shift
                | BVLShr BitVector BitVector        -- logical right shift
                | BVAShr BitVector BitVector        -- arithmetic right shift
                | BVAdd BitVector BitVector         -- addition
                | BVSub BitVector BitVector         -- subtraction
                -- | BVMul BitVector BitVector         -- multiplication
                deriving (Eq)

instance Show BitVector where
    show (BVVar name _) = name
    show (BVConst values) = concat $ map (show . (fromBool::Bool -> Int)) values
    show (BVnk n k) = "bv_" ++ (show n) ++ "," ++ (show k)
    show (BVConcat x y) = show x ++ " · " ++ show y
    show (BVExtract i j x) = "extract_" ++ (show i) ++ "," ++ (show j)  ++ "(" ++ (show x) ++ ")"
    show (BVZeroExtend n x) = "zeroextend_" ++ (show n) ++ "(" ++ (show x) ++ ")"
    show (BVSignExtend n x) = "signextend_" ++ (show n) ++ "(" ++ (show x) ++ ")"
    show (BVNot x) = "~" ++ show x
    show (BVAnd x y) = "(" ++ show x ++ " & " ++ show y ++ ")"
    show (BVOr x y) = "(" ++ show x ++ " | " ++ show y ++ ")"
    show (BVShl x y) = "(" ++ show x ++ " << " ++ show y ++ ")"
    show (BVLShr x y) = "(" ++ show x ++ " >>> " ++ show y ++ ")"
    show (BVAShr x y) = "(" ++ show x ++ " >> " ++ show y ++ ")"
    show (BVAdd x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
    show (BVSub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
    -- show (BVMul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"

-- Size of a bit vector
bvLength :: BitVector -> Int
bvLength (BVVar _ l) = l
bvLength (BVConst x) = length x
bvLength (BVnk n _) = n
bvLength (BVConcat x y) = bvLength x + bvLength y
bvLength (BVExtract i j _) = i - j + 1
bvLength (BVZeroExtend n x) = bvLength x + n
bvLength (BVSignExtend n x) = bvLength x + n
bvLength (BVNot x) = bvLength x
bvLength (BVAnd x _) = bvLength x
bvLength (BVOr x _) = bvLength x
bvLength (BVShl x _) = bvLength x
bvLength (BVLShr x _) = bvLength x
bvLength (BVAShr x _) = bvLength x
bvLength (BVAdd x _) = bvLength x
bvLength (BVSub x _) = bvLength x
-- bvLength (BVMul x _) = bvLength x

-- Children of a bit vector (imagine a tree) (it is a tree)
bvTermChildren :: BitVector -> [BitVector]
bvTermChildren (BVVar _ _) = []
bvTermChildren (BVConst _) = []
bvTermChildren (BVnk _ _) = []
bvTermChildren (BVConcat x y) = [x, y]
bvTermChildren (BVExtract _ _ x) = [x]
bvTermChildren (BVZeroExtend _ x) = [x]
bvTermChildren (BVSignExtend _ x) = [x]
bvTermChildren (BVNot x) = [x]
bvTermChildren (BVAnd x y) = [x, y]
bvTermChildren (BVOr x y) = [x, y]
bvTermChildren (BVShl x y) = [x, y] ++ (map (\i -> BVnk (bvLength x) i) [0..bvLength x])
bvTermChildren (BVLShr x y) = [x, y]
bvTermChildren (BVAShr x y) = [x, y]
bvTermChildren z@(BVAdd x y) = [x, y] ++ [BVVar ("_carry"++(show z)) (bvLength x)]
bvTermChildren (BVSub x y) = [x, y]
-- bvTermChildren (BVMul x y) = [x, y]

-- All sub-terms of a bit vector (root of a tree), including itself
bvSubTerms :: BitVector -> [BitVector]
bvSubTerms t = t:(concat $ map bvSubTerms (bvTermChildren t))

-- "Smart" constructor for multiplications -> Already transform multiplication at creation time
bvMul :: BitVector -> BitVector -> BitVector
bvMul x y | (bvLength x) /= (bvLength y) = error "Multiplication of vectors with different lengths!"
          | otherwise = sumOfVectors rows
              where sumOfVectors :: [BitVector] -> BitVector
                    sumOfVectors [] = error "Empty sum"
                    sumOfVectors [a] = a
                    sumOfVectors [a,b] = BVAdd a b
                    sumOfVectors (a:as) = BVAdd a (sumOfVectors as)
                    rows = map rowTerm [0..(bvLength x)-1]
                    rowTerm :: Int -> BitVector
                    rowTerm i = ((bVec i) `BVAnd` (shiftedA i))
                    bVec :: Int -> BitVector
                    bVec i = (BVSignExtend ((bvLength x)-1) (BVExtract i i y))
                    shiftedA :: Int -> BitVector
                    shiftedA i = (BVShl x (BVnk (bvLength x) i))


-- Atom in a Bit-vector formula
data BVAtom_ v = BVEq v v           -- equality
                | BVUlt v v         -- unsigned less than
                | BVUle v v         -- unsigned less than or equal
                | BVSlt v v         -- signed less than
                | BVSle v v         -- signed less than or equal
                deriving (Eq, Functor)
type BVAtom = BVAtom_ BitVector

instance Show v => Show (BVAtom_ v) where
    show (BVEq a b) = show a ++ " = " ++ show b
    show (BVUlt a b) = show a ++ " < " ++ show b
    show (BVUle a b) = show a ++ " ≤ " ++ show b
    show (BVSlt a b) = show a ++ " ≺ " ++ show b
    show (BVSle a b) = show a ++ " ≼ " ++ show b

-- Direct children of a bit vector logic atom
bvAtomTerms :: BVAtom -> [BitVector]
bvAtomTerms (BVEq x y) = [x, y]
bvAtomTerms (BVUlt x y) = [x, y]
bvAtomTerms (BVUle x y) = [x, y]
bvAtomTerms (BVSlt x y) = [x, y]
bvAtomTerms (BVSle x y) = [x, y]

-- All sub-terms (bit vectors) contained within a bit vector logic atom
bvAtomAllTerms :: BVAtom -> [BitVector]
bvAtomAllTerms a = concat $ map bvSubTerms (bvAtomTerms a)


-- Bit vector logic formula
type BVFormula = LogicExpression BVAtom

-- All terms in a bit vector formula (no duplicates)
terms :: BVFormula -> [BitVector]
terms f = nub $ concat $ map bvAtomAllTerms (logicAtoms f)

-- Index of a sub-term (bit vector) in a bit vector formula
subTermIndex :: BVFormula -> BitVector -> Int
subTermIndex f t = fromJust $ findIndex (==t) (terms f)


-- Number of the Boolean variable describing the i-th bit of a vector t in a formula f
bvVariableAt :: BVFormula -> BitVector -> Int -> Int
bvVariableAt f t i = length (atoms f) + (sum $ take j bvLengths) + i + 1    -- sat variables start at 1
    where bvLengths = map bvLength (terms f)
          j = subTermIndex f t

bvIndexAtom :: BVFormula -> BitVector -> Int -> SATFormula
bvIndexAtom f x i = Atom $ Variable $ bvVariableAt f x i

-- All boolean variable atoms for a list of indices in a bit-vector
bvIndexAtoms :: BVFormula -> BitVector -> [Int] -> [SATFormula]
bvIndexAtoms f x = map $ bvIndexAtom f x

-- All boolean variable atoms in a bit-vector
bvAtoms :: BVFormula -> BitVector -> [SATFormula]
bvAtoms f x = bvIndexAtoms f x ([0..(bvLength x)-1])

-- Logic expression for a specific element of a bit-vector to be true or false
bvTruthAtomAt :: BVFormula -> BitVector -> Int -> Bool -> SATFormula
bvTruthAtomAt f x i True = Atom $ Variable $ bvVariableAt f x i
bvTruthAtomAt f x i False = Not $ bvTruthAtomAt f x i True

-- Logic expression for a range of elements in a bit-vector to hold certain values
bvTruthAtomsRange :: BVFormula -> BitVector -> [Int] -> [Bool] -> SATFormula
bvTruthAtomsRange f x is ts = BigAnd $ map (\(i, t) -> bvTruthAtomAt f x i t) indexedValues
    where indexedValues = zip is ts

-- Conjunction of logic expressions for a bit-vector to equal a certain boolean array
bvTruthAtoms :: BVFormula -> BitVector -> [Bool] -> SATFormula
bvTruthAtoms f x = bvTruthAtomsRange f x [0..(bvLength x)-1]

-- Comments that show which terms are represented by which boolean variables
bvTermComments :: BVFormula -> [String]
bvTermComments f = ["c " ++ show f] ++ map termComment (varTerms)
    where varTerms = filter isVariable (terms f)
          isVariable (BVVar ('_':_) _) = False
          isVariable (BVVar _ _) = True
          isVariable _ = False
          termComment t = "c Variables for vector " ++ (show t) ++ ": " ++ (show vars)
              where vars = [start..end]
                    start = bvVariableAt f t 0
                    end = start + (bvLength t) - 1


-------------- Bit Blasting --------------

bitBlast :: BVFormula -> SATFormula
bitBlast f = BigAnd ([booleanSkeleton f] ++ (map (fullAtomConstraint f) at) ++ (map (termConstraint f) t))
    where at = logicAtoms f
          t = terms f

-- The full atom constraint as in: the atom is satisfied = the constraint has to hold
fullAtomConstraint :: BVFormula -> BVAtom -> SATFormula
fullAtomConstraint f a = (Atom $ Variable $ (atomIndex f a) + 1) `Equivalent` (atomConstraint f a)

-- Just the actual constraint of an atom in a bit vector formula
atomConstraint :: BVFormula -> BVAtom -> SATFormula
atomConstraint f (BVEq x y) = allEquivalences (bvAtoms f x) (bvAtoms f y)
atomConstraint f (BVUlt x y) = termsLessThanRange f x y [0..(bvLength x)-1]
atomConstraint f (BVUle x y) = (atomConstraint f (BVEq x y)) `Or` (atomConstraint f (BVUlt x y))
atomConstraint f (BVSlt x y) = sltBySign `Or` (sameSign `And` (termsLessThanRange f x y [0..(bvLength x)-2]))
    where signOf t = bvIndexAtom f t 0
          sltBySign = signOf x `And` (Not $ signOf y)   -- x < y if x < 0 and y > 0
          sameSign = signOf x `Equivalent` signOf y
atomConstraint f (BVSle x y) = (atomConstraint f (BVEq x y)) `Or` (atomConstraint f (BVSlt x y))

-- Less-than constraint for two vectors, more specifically a certain range of their bits (e.g. so you can drop the sign)
termsLessThanRange :: BVFormula -> BitVector -> BitVector -> [Int] -> SATFormula
termsLessThanRange f x y range = BigOr $ map ltForIndex range
    where differenceAtIndex i = (bvTruthAtomAt f x i False) `And` (bvTruthAtomAt f y i True)
          ltForIndex 0 = differenceAtIndex 0
          ltForIndex i = (differenceAtIndex i) `And` allPreviousEquivalent
             where allPreviousEquivalent = allEquivalences (bvIndexAtoms f x [0..i-1]) (bvIndexAtoms f y [0..i-1])


-- Term constraint of a term in a bit vector formula
termConstraint :: BVFormula -> BitVector -> SATFormula
-- A variable bit vector has no constraints
termConstraint _ (BVVar _ _) = Atom (BConst True)
-- A constant bit vector has its assigned values (this can probably be optimized away)
termConstraint f z@(BVConst b) = bvTruthAtoms f z b
-- A bit vector of length n representing the number k
termConstraint f z@(BVnk n k) = bvTruthAtoms f z (toBinaryPadded n k)
-- Concatenation of two bit vectors
termConstraint f z@(BVConcat x y) = allEquivalences (bvAtoms f z) ((bvAtoms f x) ++ (bvAtoms f y))
-- Bits extracted from a bit-vector, from j to i where j's significance is lower than i's
termConstraint f z@(BVExtract i j x) = allEquivalences (bvAtoms f z) (bvIndexAtoms f x [i'..j'])
    where i' = (bvLength x) - 1 - i   -- because MSB is index 0 in our representation
          j' = (bvLength x) - 1 - j
-- Extend a vector with n zeroes
termConstraint f z@(BVZeroExtend n x) = zeroPad `And` rest
    where zeroPad = bvTruthAtomsRange f z [0..n-1] (repeat False)
          rest = allEquivalences (bvIndexAtoms f z [n..(bvLength z)-1]) (bvAtoms f x)
-- Extend a vector with n times its sign (so it keeps its value)
termConstraint f z@(BVSignExtend n x) = signedPad `And` rest
    where signedPad = allEquivalences (bvIndexAtoms f z [0..n-1]) (repeat $ bvIndexAtom f x 0)
          rest = allEquivalences (bvIndexAtoms f z [n..(bvLength z)-1]) (bvAtoms f x)
-- Bitwise NOT
termConstraint f z@(BVNot x) = allEquivalences (bvAtoms f z) (negateAll $ bvAtoms f x)
-- Bitwise AND
termConstraint f z@(BVAnd x y) = allEquivalences (bvAtoms f z) (andAll (bvAtoms f x) (bvAtoms f y))
-- Bitwise OR
termConstraint f z@(BVOr x y) = allEquivalences (bvAtoms f z) (orAll (bvAtoms f x) (bvAtoms f y))
-- Shift a bit-vector x to the left by y bits
termConstraint f z@(BVShl x y) = (shiftTooFar `And` zAllZero) `Or` (notShiftTooFar `And` leftShiftTerm)
    where shiftTooFar = atomConstraint f (BVUle (BVnk (bvLength x) (bvLength x)) y)
          zAllZero = bvTruthAtoms f z (repeat False)
          notShiftTooFar = atomConstraint f (BVUlt y (BVnk (bvLength x) (bvLength x)))
          leftShiftTerm = BigOr $ map ls [0..(bvLength x)-1]
          -- actual non-trivial left-shift
          ls :: Int -> SATFormula
          ls 0 = (yEqualsI 0) `And` (shiftedRest 0)   -- shift by 0 -> z is exactly x
          ls i = (yEqualsI i) `And` (trailingZeroes i) `And` (shiftedRest i)
          yEqualsI i = (atomConstraint f (y `BVEq` (BVnk (bvLength x) i)))
          trailingZeroes i = bvTruthAtomsRange f z (take i $ reverse [0..(bvLength z)-1]) (repeat False)
          shiftedRest i = allEquivalences (drop i $ reverse $ bvAtoms f z) (reverse $ bvAtoms f x)
-- Addition of two vectors x and y
termConstraint f z@(BVAdd x y) = addConstraints `And` carryConstraints
    where addConstraints = allEquivalences (bvAtoms f z) (add (bvAtoms f x) (bvAtoms f y) (bvAtoms f carryVector))
          add :: [SATFormula] -> [SATFormula] -> [SATFormula] -> [SATFormula]
          add _x _y _c = map (\(u,v,w) -> u `Xor` v `Xor` w) (zip3 _x _y _c)

          carryVector = (last (bvTermChildren z))
          carryConstraints = firstCarry `And` restCarry
              where firstCarry = bvTruthAtomAt f carryVector ((bvLength x)-1) False
                    restCarry = allEquivalences (bvIndexAtoms f carryVector [0..(bvLength x)-2]) (tail carryFormulas)
          carryFormulas = map (\(u,v,w) -> BigOr [u `And` v, u `And` w, v `And` w]) zippedBits
          zippedBits = zip3 (bvAtoms f x) (bvAtoms f y) (bvAtoms f carryVector)

termConstraint _ _ = error "Unsupported term in bit blasting"


-------------- Util --------------

-- Convert an integer into binary (list of booleans)
toBinary :: Int -> [Bool]
toBinary 0 = []
toBinary n = toBinary (n `quot` 2) ++ [n `rem` 2 == 1]

-- Left-pad a list to length n with constant p
leftPad :: a -> Int -> [a] -> [a]
leftPad p n l = replicate (n - length l) p ++ l

-- Binary of an integer, padded to a certain length
toBinaryPadded :: Int -> Int -> [Bool]
toBinaryPadded len num = leftPad False len $ toBinary num


-------------- Logic expressions to CNF --------------

logicExpressionToCNF :: SATFormula -> CNFFormula
logicExpressionToCNF f = plaistedGreenbaum . simplifyLogic $ f


-- Recursively simplify a logic expression to only contain NOT, AND, OR subexpressions
simplifyLogic :: (LogicExpression l) -> (LogicExpression l)
simplifyLogic f@(Atom _) = f
simplifyLogic (Not (Not g)) = simplifyLogic g       -- get rid of double negations
simplifyLogic (Not g) = (Not (simplifyLogic g))
simplifyLogic (And g h) = (And (simplifyLogic g) (simplifyLogic h))
simplifyLogic (BigAnd [a]) = simplifyLogic a
simplifyLogic (BigAnd gs) = BigAnd $ map simplifyLogic gs
simplifyLogic (Or g h) = (Or (simplifyLogic g) (simplifyLogic h))
simplifyLogic (BigOr [a@(Atom _)]) = a
simplifyLogic (BigOr gs) = BigOr $ map simplifyLogic gs
simplifyLogic (Xor g h) = simplifyLogic (Or (And g (Not h)) (And (Not g) h))
simplifyLogic (Implies g h) = simplifyLogic (Or (Not g) h)
simplifyLogic (Equivalent g h) = simplifyLogic (And (Implies g h) (Implies h g))


-- Variable number for a subexpression in the Tseitin Encoding
subexpressionVarNumber :: SATFormula -> SATFormula -> Int
subexpressionVarNumber _ (Atom (Variable i)) = i
subexpressionVarNumber expr subExp = (maxVarOfExpression expr) + (subExpressionIndex expr subExp) + 1
-- Just for brevity...
svn :: SATFormula -> SATFormula -> Int
svn = subexpressionVarNumber


-- Plaisted-Greenbaum Optimization variation on the Tseitin-Encoding
plaistedGreenbaum :: SATFormula -> CNFFormula
plaistedGreenbaum e = conjoin [Conj [Disj [subexpressionVarNumber e e]], pgTerm True e e]

pgTerm :: Bool -> SATFormula -> SATFormula -> CNFFormula
pgTerm p e f@(And g h) = conjoin [pgDef p e f, pgTerm p e g, pgTerm p e h]
pgTerm p e f@(BigAnd gs) = conjoin $ [pgDef p e f] ++ (map (pgTerm p e) gs)
pgTerm p e f@(Or g h) = conjoin [pgDef p e f, pgTerm p e g, pgTerm p e h]
pgTerm p e f@(BigOr gs) = conjoin $ [pgDef p e f] ++ (map (pgTerm p e) gs)
pgTerm p e f@(Not g) = conjoin [pgDef p e f, pgTerm (not p) e g]
pgTerm _ _ (Atom _) = Conj []
pgTerm _ _ _ = error "Illegal subexpression in Tseitin Encoding (Plaisted-Greenbaum Optimization)"

pgDef :: Bool -> SATFormula -> SATFormula -> CNFFormula
pgDef True e f@(And g h) = Conj [Disj [-(svn e f), svn e g], Disj [-(svn e f), svn e h]]
pgDef True e f@(BigAnd gs) = Conj $ map (\g -> Disj [-(svn e f), svn e g]) gs
pgDef True e f@(Or g h) = Conj [Disj [-(svn e f), svn e g, svn e h]]
pgDef True e f@(BigOr gs) = Conj [Disj (-(svn e f):(map (svn e) gs))]
pgDef True e f@(Not g) = Conj [Disj [-(svn e f), -(svn e g)]]
pgDef False e f@(And g h) = Conj [Disj [svn e f, -(svn e g), -(svn e h)]]
pgDef False e f@(BigAnd gs) = Conj [Disj ((svn e f):(map (\g -> -(svn e g)) gs))]
pgDef False e f@(Or g h) = Conj [Disj [svn e f, -(svn e g)], Disj [svn e f, -(svn e h)]]
pgDef False e f@(BigOr gs) = Conj $ map (\g -> Disj [svn e f, -(svn e g)]) gs
pgDef False e f@(Not g) = Conj [Disj [svn e f, svn e g]]
pgDef _ _ _ = error "Illegal subexpression in Tseitin Encoding (Plaisted-Greenbaum Optimization)"


-------------- Convenience functions --------------

-- Bit blasting the multiplication of two integers
multiplicationFormula :: Int -> Int -> BVFormula
multiplicationFormula a b = Atom $ (BVVar "result" n) `BVEq` ((BVnk n a) `bvMul` (BVnk n b))
    where n = 2 * maximum [length (toBinary a), length (toBinary b)]

-- Bit blasting the integer factorization of an integer a
primeCheckFormula :: Int -> BVFormula
primeCheckFormula a = factorization `And` xGreaterOne `And` yGreaterOne
    where factorization = Atom $ (BVnk (2*n) a) `BVEq` ((BVZeroExtend n x) `bvMul` (BVZeroExtend n y))
          xGreaterOne = Atom $ (BVnk n 1) `BVUlt` x
          yGreaterOne = Atom $ (BVnk n 1) `BVUlt` y
          x = BVVar "x" n
          y = BVVar "y" n
          n = length (toBinary a)


-------------- Really simple command parser --------------

data Command = Multiply Int Int
              | CheckPrime Int
              deriving (Read, Show)

formulaFromCommand :: Command -> BVFormula
formulaFromCommand (Multiply x y) = multiplicationFormula x y
formulaFromCommand (CheckPrime x) = primeCheckFormula x

execute :: Maybe Command -> String
execute (Just c) = do
    let formula = formulaFromCommand c
    unlines $ ["c Command: " ++ show c] ++ (bvTermComments formula) ++ [show $ logicExpressionToCNF (bitBlast formula)]
execute _ = unlines ["Commands:", "\tMultiply x y", "\tCheckPrime x"]   -- help message


-------------- IO stuff --------------

main :: IO ()
main = do
    args <- getArgs
    putStr $ execute $ readMaybe $ concatMap (" "++) args
