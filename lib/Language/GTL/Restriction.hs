{-| Provides a data type to represent restrictions on a single variable and
    functions to work on it. -}
module Language.GTL.Restriction
       (Restriction(..),
        emptyRestriction,
        plusRestriction) where

import Language.GTL.Expression
import Language.GTL.Types

import Data.Set as Set

{-| Represents a value space for a single variable. -}
data Restriction v = Restriction
                     { restrictionType :: GTLType -- ^ The type of the value space
                     , lowerLimits :: [(Bool,TypedExpr v)] -- ^ Expressions that form a lower limit on the allowed values
                     , upperLimits :: [(Bool,TypedExpr v)] -- ^ Upper limits for the value space
                     , allowedValues :: Maybe (Set (GTLValue ())) -- ^ Can be a set of values that are allowed (everything else is then forbidden)
                     , forbiddenValues :: Set (GTLValue ()) -- ^ A set of forbidden values
                     , equals :: [TypedExpr v] -- ^ A list of expressions that must be equal to the allowed values
                     , unequals :: [TypedExpr v] -- ^ A list of expressions which must be unequal to the allowed values
                     } deriving (Show,Eq,Ord)

-- | Construct an empty restriction for a given type
emptyRestriction :: GTLType -> Restriction v
emptyRestriction tp = Restriction tp [] [] Nothing Set.empty [] []

insertLimit :: Ord v => Bool -> (Bool,TypedExpr v) -> [(Bool,TypedExpr v)] -> [(Bool,TypedExpr v)]
insertLimit upper l [] = [l]
insertLimit upper (inc,l) rest@((inc',l'):ls)
  = if inc /= inc'
    then (inc',l'):insertLimit upper (inc,l) ls
    else (case compareExpr l l' of
             EEQ -> rest
             EGT -> if upper
                    then rest
                    else insertLimit upper (inc,l) ls
             ELT -> if upper
                    then insertLimit upper (inc,l) ls
                    else rest
             _ -> (inc',l'):insertLimit upper (inc,l) ls)

insertRestriction :: Ord v => Bool -> TypedExpr v -> [TypedExpr v] -> Maybe [TypedExpr v]
insertRestriction _ e [] = return [e]
insertRestriction eq e (x:xs) = case compareExpr e x of
  EUNK -> do
    r <- insertRestriction eq e xs
    return (x:r)
  EEQ -> return (x:xs)
  _ -> if eq then Nothing else (do
                                   r <- insertRestriction eq e xs
                                   return (x:r))  

mergeLimits :: Ord v => Bool -> [(Bool,TypedExpr v)] -> [(Bool,TypedExpr v)] -> [(Bool,TypedExpr v)]
mergeLimits upper xs ys = foldl (\ys' x -> insertLimit upper x ys') ys xs

mergeRestrictions :: Ord v => Bool -> [TypedExpr v] -> [TypedExpr v] -> Maybe [TypedExpr v]
mergeRestrictions eq xs ys = foldl (\ys' x -> case ys' of
                                       Nothing -> Nothing
                                       Just ys'' -> insertRestriction eq x ys'') (Just ys) xs

-- | Merge two restrictions. If they conflict, 'Nothing' is returned.
plusRestriction :: Ord v => Restriction v -> Restriction v -> Maybe (Restriction v)
plusRestriction r1 r2
  | restrictionType r1 == restrictionType r2
    = do
      let nupper = mergeLimits True (upperLimits r1) (upperLimits r2)
          nlower = mergeLimits False (lowerLimits r1) (lowerLimits r2)
      nallowed <- case allowedValues r1 of
        Nothing -> return $ allowedValues r2
        Just a1 -> case allowedValues r2 of
          Nothing -> return $ Just a1
          Just a2 -> let s = Set.intersection a1 a2
                     in if Set.null s
                        then Nothing
                        else return $ Just s
      nequals <- mergeRestrictions True (equals r1) (equals r2)
      nunequals <- mergeRestrictions False (unequals r1) (unequals r2)
      return $ Restriction { restrictionType = restrictionType r1
                           , upperLimits = nupper
                           , lowerLimits = nlower
                           , allowedValues = nallowed
                           , forbiddenValues = Set.union (forbiddenValues r1) (forbiddenValues r2)
                           , equals = nequals
                           , unequals = nunequals
                           }
  | otherwise = error $ "Merging restrictions of type "++show (restrictionType r1)++" and "++show (restrictionType r2)
