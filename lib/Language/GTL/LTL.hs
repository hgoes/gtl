{-| Implements Linear Time Logic and its translation into Buchi-Automaton.
 -}
module Language.GTL.LTL(
  -- * Formulas
  LTL(..),
  BinOp(..),
  UnOp(..),
  -- * Buchi translation
  GBuchi,
  Buchi(..),
  BuchiState(..),
  ltlToBuchi,
  ltlToBuchiM,
  translateGBA,
  buchiProduct
  ) where

import Data.Set as Set
import Data.Map as Map
import Data.Foldable
import Prelude hiding (foldl)
import Control.Monad.Identity
import Language.GTL.Buchi

-- | A LTL formula with atoms of type /a/.
data LTL a = Atom a
           | Bin BinOp (LTL a) (LTL a)
           | Un UnOp (LTL a)
           | Ground Bool
           | LTLAutomaton (Buchi (Map a Bool)) Integer Integer
           deriving (Eq,Ord)

-- | Minimal set of binary operators for LTL.
data BinOp = And
           | Or
           | Until
           | UntilOp
           deriving (Eq,Ord)

-- | Unary operators for LTL.
data UnOp = Not
          | Next
          deriving (Eq,Ord)

binPrec :: BinOp -> Int
binPrec And = 7
binPrec Or = 6
binPrec Until = 5
binPrec UntilOp = 5

unPrec :: UnOp -> Int
unPrec Not = 9
unPrec Next = 4

instance Show BinOp where
  {-
  show And = "\x2227"
  show Or = "\x2228" -}
  show Until = "U"
  show UntilOp = "V"
  show And = "and"
  show Or = "or"

instance Show UnOp where
  --show Not = "\xac"
  show Not = "not "
  show Next = "X "

instance Show a => Show (LTL a) where
  showsPrec p (Atom x) = showsPrec p x
  showsPrec p (Bin op l r) = let str = showsPrec (binPrec op) l . 
                                       showChar ' ' .
                                       shows op . 
                                       showChar ' ' .
                                       showsPrec (binPrec op) r
                             in if p >= binPrec op
                                then showChar '(' . str . showChar ')'
                                else str
  showsPrec p (Un op x) = let str = shows op .
                                    showsPrec (unPrec op) x
                          in if p >= unPrec op
                             then showChar '(' . str . showChar ')'
                             else str
  showsPrec _ (Ground x) = if x then showString "T" --showChar '\x22a4'
                           else showString "F" --showChar '\x22a5'

distributeNegation :: LTL a -> LTL a
distributeNegation (Atom x) = Atom x
distributeNegation (Ground p) = Ground p
distributeNegation (Bin op l r) = Bin op (distributeNegation l) (distributeNegation r)
distributeNegation (Un Not x) = pushNegation x
distributeNegation (Un op x) = Un op (distributeNegation x)

pushNegation :: LTL a -> LTL a
pushNegation (Atom x) = Un Not (Atom x)
pushNegation (Ground p) = Ground $ not p
pushNegation (Bin op l r) = Bin (case op of 
                                    And -> Or
                                    Or -> And
                                    Until -> UntilOp
                                    UntilOp -> Until)
                            (pushNegation l)
                            (pushNegation r)
pushNegation (Un Not x) = distributeNegation x
pushNegation (Un Next x) = Un Next (pushNegation x)
pushNegation aut@(LTLAutomaton _ _ _) = Un Not aut

-- | Extracts all until constructs from a LTL formula.
--   Each until gets a unique `Integer' identifier.
untils :: Ord a => LTL a -> (Map (LTL a,LTL a) Integer,Integer)
untils = untils' 0
  where
    untils' :: Ord a => Integer -> LTL a -> (Map (LTL a,LTL a) Integer,Integer)
    untils' n (Atom _) = (Map.empty,n)
    untils' n (Ground _) = (Map.empty,n)
    untils' n (Bin Until l r) = let (mpl,nl) = untils' n l
                                    (mpr,nr) = untils' nl r
                                in (Map.insert (l,r) nr (Map.union mpl mpr),nr+1)
    untils' n (Bin op l r) = let (mpl,nl) = untils' n l
                                 (mpr,nr) = untils' nl r
                             in (Map.union mpl mpr,nr+1)
    untils' n (Un op x) = untils' n x
    untils' n (LTLAutomaton _ _ _) = (Map.empty,n)

ltlAtoms :: Ord b => (a -> [b]) -> LTL a -> Set b
ltlAtoms f (Atom x) = Set.fromList (f x)
ltlAtoms _ (Ground _) = Set.empty
ltlAtoms f (Bin _ l r) = Set.union (ltlAtoms f l) (ltlAtoms f r)
ltlAtoms f (Un _ x) = ltlAtoms f x

type NodeSet a = Map (Set (LTL a),Set (LTL a)) (Integer,Set Integer,Set Integer,Set Integer)

data Node a = Node
              { name :: Integer
              , new :: [LTL a]
              , old :: Set (LTL a)
              , next :: Set (LTL a)
              , incoming :: Set Integer
              , outgoing :: Set Integer
              , finals :: Set Integer
              } deriving Show


type Untils a = Map (LTL a,LTL a) Integer
type UntilsRHS a = Set (LTL a)

untilsToUntilsRHS :: Ord a => Untils a -> UntilsRHS a
untilsToUntilsRHS mp = Set.map snd $ Map.keysSet mp

-- | Same as `ltlToBuchi' but also allows the user to construct the variable type and runs in a monad.
ltlToBuchiM :: (Ord a,Monad m,Show a) => ([(a,Bool)] -> m b) -> LTL a -> m (Buchi b)
ltlToBuchiM p f = let f' = distributeNegation f
                      (unt,max_unt) = untils f'
                      untr = untilsToUntilsRHS unt
                  in buildGraph p unt (buildNodeSet untr max_unt f')

-- | Converts a LTL formula to a generalized buchi automaton.
ltlToBuchi :: (Ord a,Show a) => LTL a -> Buchi (Map a Bool)
ltlToBuchi f = runIdentity $ ltlToBuchiM (return.Map.fromList) f

finalSet :: Ord a => Set (LTL a) -> Untils a -> Set Integer
finalSet cur acc = Set.fromList $ Map.elems $ Map.difference acc $ 
                   Map.fromList [ ((l,r),undefined) | Bin Until l r <- Set.toList cur,not $ Set.member r cur ]

buildGraph :: (Ord a,Monad m) => ([(a,Bool)] -> m b) -> Untils a -> NodeSet a -> m (Buchi b)
buildGraph f untils nset 
  = foldlM (\mp ((old,next),(name,inc,out,fin)) -> do
               v <- f $ [ (p,True) | Atom p <- Set.toList old ] ++
                    [ (p,False) | Un Not (Atom p) <- Set.toList old ]
               return $ Map.alter (\cur -> Just $ BuchiState { isStart = Set.member 0 inc
                                                             , vars = v
                                                             , finalSets = Set.union (finalSet old untils) fin
                                                             , successors = case cur of
                                                               Nothing -> out
                                                               Just buchi -> Set.union out (successors buchi)
                                                             }
                                  ) name $ 
                 foldl (\cmp i -> if i == 0
                                  then cmp
                                  else Map.alter (\cur -> case cur of
                                                     Nothing -> Just $ BuchiState { isStart = undefined
                                                                                  , vars = undefined
                                                                                  , finalSets = undefined
                                                                                  , successors = Set.singleton name
                                                                                  }
                                                     Just buchi -> Just $ buchi { successors = Set.insert name $ successors buchi }
                                                 ) i cmp
                       ) mp inc
           ) Map.empty (Map.toList nset)

buildNodeSet :: Ord a => UntilsRHS a -> Integer -> LTL a -> NodeSet a
buildNodeSet untils curf ltl
  = let (ns,_,_) = expand untils 2 curf (Node { name = 1
                                              , new = [ltl]
                                              , old = Set.empty
                                              , next = Set.empty
                                              , incoming = Set.singleton 0
                                              , outgoing = Set.empty
                                              , finals = Set.empty
                                              }) Map.empty
    in ns

expand :: Ord a => UntilsRHS a -> Integer -> Integer -> Node a -> NodeSet a -> (NodeSet a,Integer,Integer)
expand untils n f node nset = case new node of
  [] -> let (res,nset') = Map.insertLookupWithKey
                         (\_ (k2,inc2,out2,fin2) (k1,inc1,out1,fin1) -> (k1,Set.union inc1 inc2,Set.union out1 out2,Set.union fin1 fin2))
                         (old node,next node)
                         (name node,incoming node,outgoing node,finals node)
                         nset
       in case res of
         Nothing -> expand untils (n+1) f (Node { name = n
                                                , new = Set.toList (next node)
                                                , old = Set.empty
                                                , next = Set.empty
                                                , incoming = Set.singleton (name node)
                                                , outgoing = Set.empty
                                                , finals = Set.empty
                                                }) nset'
         Just prev -> (nset',n,f)
  (x:xs) -> if Set.member x (old node)
           then expand untils n f (node { new = xs }) nset
           else case x of
             Atom p -> if Set.member (Un Not (Atom p)) (old node)
                      then (nset,n,f)
                      else expand untils n f (node { old = Set.insert x (old node)
                                                   , new = xs
                                                   }) nset
             Ground p -> if p
                        then expand untils n f (node { new = xs }) nset
                        else (nset,n,f)
             Un Not (Atom p) -> if Set.member (Atom p) (old node)
                               then (nset,n,f)
                               else expand untils n f (node { old = Set.insert x (old node)
                                                            , new = xs
                                                            }) nset
             Un Next ff -> expand untils n f (node { new = xs
                                                   , old = Set.insert x (old node)
                                                   , next = Set.insert ff (next node)
                                                   }) nset
             Bin And l r -> expand untils n f (node { new = l:r:xs
                                                    , old = if Set.member x untils
                                                            then Set.insert x (old node)
                                                            else old node
                                                    }) nset
             Bin Or l r -> let storeOld = Set.member x untils
                               node1 = Node { name = n
                                            , incoming = incoming node
                                            , new = l:xs
                                            , old = if storeOld
                                                    then Set.insert x (old node)
                                                    else old node
                                            , next = next node
                                            , outgoing = outgoing node
                                            , finals = finals node
                                            }
                               node2 = Node { name = n+1
                                            , incoming = incoming node
                                            , new = r:xs
                                            , old = if storeOld
                                                    then Set.insert x (old node)
                                                    else old node
                                            , next = next node
                                            , outgoing = outgoing node
                                            , finals = finals node
                                            }
                               (nset',n',f') = expand untils (n+2) f node1 nset
                          in expand untils n' f' node2 nset'
             Bin Until l r -> let node1 = Node { name = n
                                              , incoming = incoming node
                                              , outgoing = outgoing node
                                              , new = l:xs
                                              , old = Set.insert x (old node)
                                              , next = Set.insert x (next node)
                                              , finals = finals node
                                              }
                                  node2 = Node { name = n+1
                                               , incoming = incoming node
                                               , outgoing = outgoing node
                                               , new = r:xs
                                               , old = Set.insert x (old node)
                                               , next = next node
                                               , finals = finals node
                                               }
                                  (nset',n',f') = expand untils (n+2) f node1 nset
                             in expand untils n' f' node2 nset'
             Bin UntilOp l r -> let node1 = Node { name = n
                                                , incoming = incoming node
                                                , outgoing = outgoing node
                                                , new = r:xs
                                                , old = Set.insert x (old node)
                                                , next = Set.insert x (next node)
                                                , finals = finals node
                                                }
                                    node2 = Node { name = n+1
                                                 , incoming = incoming node
                                                 , outgoing = outgoing node
                                                 , new = l:r:xs
                                                 , old = Set.insert x (old node)
                                                 , next = next node
                                                 , finals = finals node
                                                 }
                                    (nset',n',f') = expand untils (n+2) f node1 nset
                               in expand untils n' f' node2 nset'
             LTLAutomaton buchi maxst maxf -> foldl (\(ns,cn,cf) nd -> expand untils cn cf nd ns) (nset,n+maxst,f+maxf)
                                              [ Node { name = n + st
                                                     , incoming = if isStart co
                                                                  then incoming node
                                                                  else Set.empty
                                                     , outgoing = Set.map (+n) (successors co)
                                                     , new = xs
                                                     , old = Set.union (Set.insert x (old node)) (Set.fromList [ if p
                                                                                                                 then Atom var
                                                                                                                 else Un Not (Atom var)
                                                                                                               | (var,p) <- Map.toList (vars co) ])
                                                     , next = next node
                                                     , finals = Set.map (+f) (finalSets co)
                                                     }
                                              | (st,co) <- Map.toList buchi ]