module Hsat where

import qualified Data.Set as Set
import qualified Data.List as List

{-
    Checks if a given variable is already assigned
    Takes:
        Partial assignment
        Variable number
    How it works:
        Maps the partial assignment tuples to a list of only the first element (i.e. variable number)
        Checks if the given variable number is in that list
-}
varAssigned :: [(Int, Bool)] -> Int -> Bool
varAssigned pa var = var `elem` (map fst pa)

{-
    Gets the number of the first unassigned variable
    Takes:
        Partial Assignment
        Total number of variables
    How it works:
        Generates a list [1..numVar]
        Filters that list for the variables that are unassigned in the partial assignment
    
-}
getUnassigned :: [(Int, Bool)] -> Int -> Int
getUnassigned pa numVar = head $ filter (not . (varAssigned pa)) [1..numVar]

{-
    Looks for a contradiction in a partial assignment,
    i.e. if a variable is assigned both true and false.
    Takes:
        Partial Assignment
    How it works:
        Map the partial assignment tuples to a list of only the first element (i.e. variable number)
        Convert that to a set (eliminates doubles)
        Check if the length of that set is the same as the original assignment list
-}
contradiction :: [(Int, Bool)] -> Bool
contradiction pa = length pa /= length (Set.fromList $ map fst pa)

{-
    Repeatedly does unit propagation on a given clause set and keeps track of the partial assignment
    Takes:
        Clause Set
        Partial Assignment
    How it works:
        Does a step of unit propagation
        If there's no new assignments, return immediately
        Otherwise do unit propagation with the updated clause set
-}
unitProp :: [[Int]] -> [(Int, Bool)] -> ([[Int]], [(Int, Bool)])
unitProp cs pa
    | length newAssignments == 0 = (cs, pa)
    | otherwise = unitProp cs2 (pa ++ newAssignments)
        where (cs2, newAssignments) = unitPropStep cs

{-
    Does one step of unit propagation
    Takes:
        Clause Set
    How it works:
        Looks for unit clauses by filtering clauses of length 1 and putting them in a list
        Generate new assignments
            Map the literals of the unit clauses to their absolute value (variable number)
            Map the literals to their truth value (True if >0, false if <0)
            Zip the two mappings into one list of assignments
        Filter subsumed clauses
            Calculate intersection of clause with list of units
            If the intersection is the empty set, the clause is not subsumed, thus we keep it
        Delete literals that are the negative of a unit
            Calculate the negatives of the units by mapping them with *-1
            Filter all remaining clauses for literals that are not the negative of a unit
-}
unitPropStep :: [[Int]] -> ([[Int]], [(Int, Bool)])
unitPropStep cs = (clauses, assignments)
    where units = List.nub $ concat $ filter (\x -> length x == 1) cs
          assignments = zip (map abs units) (map (>0) units)
          subsumed = filter (\x -> null (List.intersect x units)) cs
          negUnits = map (*(-1)) units
          clauses = map (filter (not . (`elem` negUnits))) subsumed

{-
    Takes:
        Two results of the solve algorithm
    If one of them is SAT output that one, otherwise output UNSAT
    Used for deciding the output after branching
-}
choose :: (Maybe Bool, [(Int, Bool)]) -> (Maybe Bool, [(Int, Bool)]) -> (Maybe Bool, [(Int, Bool)])
choose (Just True, a) _ = (Just True, a)
choose _ (Just True, a) = (Just True, a)
choose _ _ = (Just False, [])

{-
    The SAT Solving algorithm; decides whether a set of clauses is satisfiable.
    Takes:
        Clause Set
        Number of variables
        Partial assignment
    Gives:
        Tuple:
        The first element is Just True if the formula is SAT, and Just False if it's UNSAT
        Assignment of variables (A list of tuples)

    How it works:
        Do unit propagation
        Check for contradictions in the partial assignment
        Check if all variables are assigned, if so => SAT
        Otherwise choose a variable to branch on and branch
-}
solve :: [[Int]] -> Int -> [(Int, Bool)] -> (Maybe Bool, [(Int, Bool)])
solve clauses numVars partAssignment 
    | contradiction pa = (Just False, [])
    | length pa == numVars = (Just True, pa)
    | otherwise = choose (solve ([nextVar]:cs) numVars pa) (solve ([-nextVar]:cs) numVars pa) 
        where (cs, pa) = unitProp clauses partAssignment
              nextVar = getUnassigned pa numVars

