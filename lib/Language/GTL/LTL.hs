module Language.GTL.LTL where

import Data.Set as Set
import Data.Map as Map
import Data.Foldable
import Prelude hiding (foldl)
import Control.Monad.Identity

data LTL a = Atom a
           | Bin BinOp (LTL a) (LTL a)
           | Un UnOp (LTL a)
           | Ground Bool
           deriving (Eq,Ord)

data BinOp = And
           | Or
           | Until
           | UntilOp
           deriving (Eq,Ord)

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

untils :: Ord a => LTL a -> Map (LTL a,LTL a) Integer
untils = fst . untils' 0

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

type NodeSet a = Map (Set (LTL a),Set (LTL a)) (Integer,Set Integer)

data Node a = Node
              { name :: Integer
              , new :: [LTL a]
              , old :: Set (LTL a)
              , next :: Set (LTL a)
              , incoming :: Set Integer
              } deriving Show

type Buchi a = Map Integer (BuchiState a) --(Bool,Set a,Set a,Set Integer,Set Integer)

data BuchiState a = BuchiState
                    { isStart :: Bool
                    , vars :: a
                    , finalSets :: Set Integer
                    , successors :: Set Integer
                    } deriving Show

type Untils a = Map (LTL a,LTL a) Integer

ltlToBuchiM :: (Ord a,Monad m,Show a) => ([(a,Bool)] -> m b) -> LTL a -> m (Buchi b)
ltlToBuchiM p f = let f' = distributeNegation f
                      unt = untils f'
                  in buildGraph p unt (buildNodeSet f')

ltlToBuchi :: (Ord a,Show a) => LTL a -> Buchi (Map a Bool)
ltlToBuchi f = runIdentity $ ltlToBuchiM (return.Map.fromList) f

finalSet :: Ord a => Set (LTL a) -> Untils a -> Set Integer
finalSet cur acc = Set.fromList $ Map.elems $ Map.difference acc $ 
                   Map.fromList [ ((l,r),undefined) | Bin Until l r <- Set.toList cur,not $ Set.member r cur ]

buildGraph :: (Ord a,Monad m) => ([(a,Bool)] -> m b) -> Untils a -> NodeSet a -> m (Buchi b)
buildGraph f untils nset 
  = foldlM (\mp ((old,next),(name,inc)) -> do
               v <- f $ [ (p,True) | Atom p <- Set.toList old ] ++
                    [ (p,False) | Un Not (Atom p) <- Set.toList old ]
               return $ Map.alter (\cur -> Just $ BuchiState { isStart = Set.member 0 inc
                                                             , vars = v
                                                             , finalSets = finalSet old untils
                                                             , successors = case cur of
                                                               Nothing -> Set.empty
                                                               Just buchi -> successors buchi
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

buildNodeSet :: Ord a => LTL a -> NodeSet a
buildNodeSet ltl = fst $ expand 2 (Node { name = 1
                                        , new = [ltl]
                                        , old = Set.empty
                                        , next = Set.empty
                                        , incoming = Set.singleton 0
                                        }) Map.empty

expand :: Ord a => Integer -> Node a -> NodeSet a -> (NodeSet a,Integer)
expand n node nset = case new node of
  [] -> let (res,nset') = Map.insertLookupWithKey
                         (\_ (k2,inc2) (k1,inc1) -> (k1,Set.union inc1 inc2))
                         (old node,next node)
                         (name node,incoming node)
                         nset
       in case res of
         Nothing -> expand (n+1) (Node
                                 { name = n
                                 , new = Set.toList (next node)
                                 , old = Set.empty
                                 , next = Set.empty
                                 , incoming = Set.singleton (name node)
                                 }) nset'
         Just prev -> (nset',n)
  (x:xs) -> if Set.member x (old node)
           then expand n (node { new = xs }) nset
           else case x of
             Atom p -> if Set.member (Un Not (Atom p)) (old node)
                      then (nset,n)
                      else expand n (node { old = Set.insert x (old node)
                                          , new = xs
                                          }) nset
             Ground p -> if p
                        then expand n (node { new = xs }) nset
                        else (nset,n)
             Un Not (Atom p) -> if Set.member (Atom p) (old node)
                               then (nset,n)
                               else expand n (node { old = Set.insert x (old node)
                                                   , new = xs
                                                   }) nset
             Un Next f -> expand n (node { new = xs
                                        , old = Set.insert x (old node)
                                        , next = Set.insert f (next node)
                                        }) nset
             Bin And l r -> expand n (node { new = l:r:xs
                                          , old = Set.insert x (old node)
                                          }) nset
             Bin Or l r -> let node1 = Node { name = n
                                           , incoming = incoming node
                                           , new = l:xs
                                           , old = Set.insert x (old node)
                                           , next = next node
                                           }
                               node2 = Node { name = n+1
                                            , incoming = incoming node
                                            , new = r:xs
                                            , old = Set.insert x (old node)
                                            , next = next node
                                            }
                               (nset',n') = expand (n+2) node1 nset
                          in expand n' node2 nset'
             Bin Until l r -> let node1 = Node { name = n
                                              , incoming = incoming node
                                              , new = l:xs
                                              , old = Set.insert x (old node)
                                              , next = Set.insert x (next node)
                                              }
                                  node2 = Node { name = n+1
                                               , incoming = incoming node
                                               , new = r:xs
                                               , old = Set.insert x (old node)
                                               , next = next node
                                               }
                                  (nset',n') = expand (n+2) node1 nset
                             in expand n' node2 nset'
             Bin UntilOp l r -> let node1 = Node { name = n
                                                , incoming = incoming node
                                                , new = r:xs
                                                , old = Set.insert x (old node)
                                                , next = Set.insert x (next node)
                                                }
                                    node2 = Node { name = n+1
                                                 , incoming = incoming node
                                                 , new = l:r:xs
                                                 , old = Set.insert x (old node)
                                                 , next = next node
                                                 }
                                    (nset',n') = expand (n+2) node1 nset
                               in expand n' node2 nset'

f1 = Bin Until (Atom "x") (Ground False)
f2 = Un Not (Bin Until (Ground True) (Atom "x"))
f3 = Bin Until (Ground True) (Atom "x")