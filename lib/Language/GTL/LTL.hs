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
  translateGBA,
  buchiProduct
  ) where

import Data.Set as Set
import Data.Map as Map
import Data.Foldable
import Prelude hiding (foldl,mapM,foldl1)
import Language.GTL.Buchi

-- | A LTL formula with atoms of type /a/.
data LTL a = Atom a
           | Bin BinOp (LTL a) (LTL a)
           | Un UnOp (LTL a)
           | Ground Bool
           | LTLAutomaton (GBuchi String (LTL a) Bool)
           | LTLSimpleAutomaton (GBuchi Integer (Set a) Bool)
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
distributeNegation aut@(LTLSimpleAutomaton _) = aut
distributeNegation aut@(LTLAutomaton _) = aut

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
pushNegation (LTLSimpleAutomaton _) = error "Complementing automata is not yet implemented"
pushNegation (LTLAutomaton _) = error "Complementing automata is not yet implemented"

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
    untils' n (LTLSimpleAutomaton _) = (Map.empty,n)
    untils' n (LTLAutomaton buchi) = foldl (\(mp,n) co -> let (nmp,n') = untils' n (vars co)
                                                          in (Map.union mp nmp,n')
                                           ) (Map.empty,0)
                                     (Map.elems buchi)

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

extractAutomata :: LTL a -> (Maybe (LTL a),[GBuchi Integer (Set a) Bool])
extractAutomata (LTLSimpleAutomaton buchi) = (Nothing,[buchi])
extractAutomata (Bin And l r) = let (ml,al) = extractAutomata l
                                    (mr,ar) = extractAutomata r
                                in (case ml of
                                       Nothing -> mr
                                       Just rl -> case mr of
                                         Nothing -> Just rl
                                         Just rr -> Just (Bin And rl rr),al++ar)
extractAutomata x = (Just x,[])

-- | Same as `ltlToBuchi' but also allows the user to construct the variable type and runs in a monad.
ltlToBuchi :: (Ord a,Show a) => (a -> a) -> LTL a -> Buchi (Set (a,Bool))
ltlToBuchi lneg f
  = let (f',buchis) = extractAutomata f
        mbuchi_prod b1 b2 = buchiProduct'
                            (\s1 s2 -> s1 + s2*(fromIntegral $ Map.size b1)) 
                            Set.union
                            (either (*2) ((+1).(*2)))
                            b1 b2
        rbuchi = case buchis of
          [] -> Nothing
          _ -> Just $ foldl1 mbuchi_prod $ fmap
               (fmap (\co -> co { vars = Set.map (\x -> (x,True)) (vars co)
                                , finalSets = if finalSets co
                                              then Set.singleton 0
                                              else Set.empty
                                }
                     )
               ) buchis
        res = case f' of
          Nothing -> case rbuchi of
            Nothing -> Map.singleton 0 (BuchiState { isStart = True
                                                   , vars = Set.empty
                                                   , finalSets = Set.empty
                                                   , successors = Set.singleton 0
                                                   })
            Just b -> b
          Just formula -> let negf = distributeNegation formula
                              (unt,max_unt) = untils negf                      
                              untr = untilsToUntilsRHS unt
                              buchi = buildGraph unt (buildNodeSet lneg untr max_unt negf)
                          in case rbuchi of
                            Nothing -> buchi
                            Just b -> mbuchi_prod buchi b
    in res

--- | Converts a LTL formula to a generalized buchi automaton.
--ltlToBuchi :: (Ord a,Show a) => LTL a -> Buchi (Map a Bool)
--ltlToBuchi f = runIdentity $ ltlToBuchiM (return.Map.fromList) f

finalSet :: Ord a => Set (LTL a) -> Untils a -> Set Integer
finalSet cur acc = Set.fromList $ Map.elems $ Map.difference acc $ 
                   Map.fromList [ ((l,r),undefined) | Bin Until l r <- Set.toList cur,not $ Set.member r cur ]

buildGraph :: Ord a => Untils a -> NodeSet a -> Buchi (Set (a,Bool))
buildGraph untils nset 
  = foldl (\mp ((old,next),(name,inc,out,fin))
           -> let v = Set.fromList $
                      [ (p,True) | Atom p <- Set.toList old ] ++
                      [ (p,False) | Un Not (Atom p) <- Set.toList old ]
              in Map.alter (\cur -> Just $ BuchiState { isStart = Set.member 0 inc
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

buildNodeSet :: Ord a => (a -> a) -> UntilsRHS a -> Integer -> LTL a -> NodeSet a
buildNodeSet lneg untils curf ltl
  = let (ns,_,_) = expand lneg untils 2 curf (Node { name = 1
                                                   , new = [ltl]
                                                   , old = Set.empty
                                                   , next = Set.empty
                                                   , incoming = Set.singleton 0
                                                   , outgoing = Set.empty
                                                   , finals = Set.empty
                                                   }) Map.empty
    in ns

expand :: Ord a => (a -> a) -> UntilsRHS a -> Integer -> Integer -> Node a -> NodeSet a -> (NodeSet a,Integer,Integer)
expand lneg untils n f node nset = case new node of
  [] -> let (res,nset') = Map.insertLookupWithKey
                         (\_ (k2,inc2,out2,fin2) (k1,inc1,out1,fin1) -> (k1,Set.union inc1 inc2,Set.union out1 out2,Set.union fin1 fin2))
                         (old node,next node)
                         (name node,incoming node,outgoing node,finals node)
                         nset
       in case res of
         Nothing -> expand lneg untils (n+1) f
                    (Node { name = n
                          , new = Set.toList (next node)
                          , old = Set.empty
                          , next = Set.empty
                          , incoming = Set.singleton (name node)
                          , outgoing = Set.empty
                          , finals = Set.empty
                          }) nset'
         Just prev -> (nset',n,f)
  (x:xs)
    | Set.member x (old node) -> expand lneg untils n f (node { new = xs }) nset
    | otherwise -> case x of
             Atom p -> if Set.member (Atom (lneg p)) (old node) || Set.member (Un Not (Atom p)) (old node)
                       then (nset,n,f)
                       else expand lneg untils n f (node { old = Set.insert x (old node)
                                                         , new = xs
                                                         }) nset
             Ground p -> if p
                         then expand lneg untils n f (node { new = xs }) nset
                         else (nset,n,f)
             Un Not (Atom p) -> if Set.member (Atom p) (old node) || Set.member (Un Not (Atom (lneg p))) (old node)
                                then (nset,n,f)
                                else expand lneg untils n f (node { old = Set.insert x (old node)
                                                                  , new = xs
                                                                  }) nset
             Un Next ff -> expand lneg untils n f (node { new = xs
                                                        , old = Set.insert x (old node)
                                                        , next = Set.insert ff (next node)
                                                        }) nset
             Bin And l r -> expand lneg untils n f (node { new = l:r:xs
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
                               (nset',n',f') = expand lneg untils (n+2) f node1 nset
                          in expand lneg untils n' f' node2 nset'
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
                                  (nset',n',f') = expand lneg untils (n+2) f node1 nset
                             in expand lneg untils n' f' node2 nset'
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
                                    (nset',n',f') = expand lneg untils (n+2) f node1 nset
                               in expand lneg untils n' f' node2 nset'
             LTLAutomaton buchi -> let stmp = Map.fromList $ zip (Map.keys buchi) [n..]
                                       n' = n+(fromIntegral $ Map.size buchi)
                                       nodes = [ Node { name = stmp!st
                                                      , new = (vars co):xs
                                                      , old = Set.insert x (old node)
                                                      , next = next node
                                                      , incoming = if isStart co
                                                                   then incoming node
                                                                   else Set.empty
                                                      , outgoing = Set.map (stmp!) (successors co)
                                                      , finals = if finalSets co
                                                                 then Set.singleton f
                                                                 else Set.empty
                                                      } | (st,co) <- Map.toList buchi ]
                                   in foldl (\(ns,cn,cf) node -> expand lneg untils cn cf node ns) (nset,n',f+1) nodes
