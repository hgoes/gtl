{-| Implements Linear Time Logic and its translation into Buchi-Automaton.
 -}
{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies #-}
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
  buchiProduct,
  ltl2vwaa,
  vwaa2gba,
  minimizeGBA,
  gba2ba,
  minimizeBA,
  optimizeTransitionsBA,
  VWAA,
  GBA,
  BA(..),
  ltl2ba,
  AtomContainer(..),
  mapLTL,
  baProduct,
  baMapAlphabet
  ) where

import Data.Set as Set
import Data.Map as Map
import qualified Data.List as List
import Data.Foldable
import Prelude hiding (foldl,mapM,foldl1,concat,foldr)
import Language.GTL.Buchi
import Language.GTL.Expression (ExprOrdering(..))

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

mapLTL :: (Ord a,Ord b) => (a -> b) -> LTL a -> LTL b
mapLTL f (Atom x) = Atom (f x)
mapLTL f (Bin op l r) = Bin op (mapLTL f l) (mapLTL f r)
mapLTL f (Un op x) = Un op (mapLTL f x)
mapLTL f (Ground p) = Ground p
mapLTL f (LTLAutomaton b) = LTLAutomaton $ fmap (\st -> st { vars = mapLTL f (vars st) }) b
mapLTL f (LTLSimpleAutomaton b) = LTLSimpleAutomaton $ fmap (\st -> st { vars = Set.map f (vars st) }) b

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
  showsPrec p (Bin Until (Ground True) phi) = let str = showString "F " . showsPrec (binPrec Until) phi
                                              in if p >= binPrec Until
                                                 then showChar '(' . str . showChar ')'
                                                 else str
  showsPrec p (Bin UntilOp (Ground False) phi) = let str = showString "G " . showsPrec (binPrec UntilOp) phi
                                                 in if p >= binPrec UntilOp
                                                    then showChar '(' . str . showChar ')'
                                                    else str
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
  showsPrec _ (Ground x) = if x then showString "tt" --showChar '\x22a4'
                           else showString "ff" --showChar '\x22a5'

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

class Ord b => AtomContainer a b | a -> b where
  atomsTrue :: a
  atomSingleton :: Bool -> b -> a
  compareAtoms :: a -> a -> ExprOrdering
  mergeAtoms :: a -> a -> Maybe a

instance Ord a => AtomContainer (Map a Bool) a where
  atomsTrue = Map.empty
  atomSingleton t p = Map.singleton p t
  compareAtoms x y
    | x == y = EEQ
    | Map.isSubmapOf x y = EGT
    | Map.isSubmapOf y x = ELT
    | otherwise = ENEQ
  mergeAtoms = mergeAlphabet

optimizeTransitionsBA :: (Ord st,AtomContainer b a,Ord b) => BA b st -> BA b st
optimizeTransitionsBA ba = BA { baTransitions = ntrans
                              , baInits = baInits ba
                              , baFinals = baFinals ba
                              }
  where
    ntrans = fmap (\set -> Set.fromList $ minimizeTrans [] (Set.toList set)) (baTransitions ba)
    
    minimizeTrans d [] = d
    minimizeTrans d ((c,st):ts) = minimizeTrans' d c st [] ts
    
    minimizeTrans' d c st d' [] = minimizeTrans ((c,st):d) d'
    minimizeTrans' d c st d' ((c',st'):ts) = if st==st' && (case compareAtoms c' c of
                                                               EEQ -> True
                                                               ELT -> True
                                                               _ -> False)
                                             then minimizeTrans' d c st d' ts
                                             else minimizeTrans' d c st ((c',st'):d') ts

minimizeBA :: (AtomContainer b a,Ord st,Ord b) => BA b st -> BA b st
minimizeBA ba = BA { baTransitions = ntrans
                   , baInits = Set.intersection (baInits ba) (Map.keysSet ntrans)
                   , baFinals = Set.intersection (baFinals ba) (Map.keysSet ntrans)
                   }
  where
    ntrans = Map.fromList $ minimizeBA' False (Map.toList (baTransitions ba)) []
    
    minimizeBA' False d [] = d
    minimizeBA' True d [] = minimizeBA' False [] d
    minimizeBA' ch d ((st,trans):xs) = minimizeBA'' ch d st trans [] xs
    
    minimizeBA'' ch d st trans d' [] = minimizeBA' ch ((st,trans):d) d'
    minimizeBA'' ch d st trans d' ((st',trans'):xs) = if (trans==trans') && (Set.member st (baFinals ba) == Set.member st' (baFinals ba))
                                                      then minimizeBA'' True (updateTranss st st' d) st
                                                           (updateTrans st st' trans) (updateTranss st st' d') (updateTranss st st' xs)
                                                      else minimizeBA'' ch d st trans ((st',trans'):d') xs
    
    updateTrans st st' trans = Set.map (\(cond,trg) -> if trg==st'
                                                       then (cond,st)
                                                       else (cond,trg)) trans
    
    updateTranss st st' = fmap (\(cst,trans) -> (cst,updateTrans st st' trans))

gba2ba :: (Ord st,AtomContainer b a,Ord b) => GBA b st -> BA b (Set st,Int)
gba2ba gba = BA { baInits = inits
                , baFinals = Set.map (\x -> (x,final_size)) (Map.keysSet (gbaTransitions gba))
                , baTransitions = buildTrans (Set.toList inits) Map.empty
                }
  where
    inits = Set.map (\x -> (x,0)) (gbaInits gba)
    
    finals = foldl (\f ts -> foldl (\f' (_,_,fins) -> Set.union f' fins) f ts) Set.empty (gbaTransitions gba)
    finalList = Set.toList finals
    final_size = Set.size finals
    
    buildTrans [] mp = mp
    buildTrans ((st,i):sts) mp
      | Map.member (st,i) mp = buildTrans sts mp
      | otherwise = let ntrans = Set.map (\(cond,trg,fins) -> (cond,(trg,next i fins))) ((gbaTransitions gba)!st)
                    in buildTrans ([ trg | (_,trg) <- Set.toList ntrans ]++sts) (Map.insert (st,i) ntrans mp)
    
    next j fin = let j' = if j==final_size
                          then 0
                          else j
                            
                     findNext k [] = k
                     findNext k (f:fs) = if Set.member f fin
                                         then findNext (k+1) fs
                                         else k
                 in findNext j' (drop j' finalList)

showCond :: Show a => Map a Bool -> String
showCond cond = concat $ List.intersperse "," [ (if pos then "" else "!")++show var | (var,pos) <- Map.toList cond ]

minimizeGBA :: (Ord st,Ord b,AtomContainer b a) => GBA b st -> GBA b st
minimizeGBA gba = case minimizeGBA' gba of
  Nothing -> gba
  Just ngba -> minimizeGBA ngba

minimizeGBA' :: (Ord st,Ord b,AtomContainer b a) => GBA b st -> Maybe (GBA b st)
minimizeGBA' gba = if changed
                   then Just (GBA { gbaTransitions = Map.fromList ntrans
                                  , gbaInits = ninit
                                  })
                   else Nothing
  where
    (changed,ntrans,ninit) = minimizeTrans False [] (Map.toList (gbaTransitions gba)) (gbaInits gba)
    
    updateTrans old new = fmap (\(st,t) -> (st,Set.map (\(cond,trg,fin) -> (cond,if trg==old
                                                                                 then new
                                                                                 else trg,fin)) t))
    
    minimizeTrans ch res [] i = (ch,res,i)
    minimizeTrans ch res ((st,t):xs) i
      = let (ch',res',ni,nxs) = minimizeTrans' st t ch ((st,t):res) i [] xs
        in minimizeTrans ch' res' nxs ni
    
    minimizeTrans' st t cch cres ci cxs [] = (cch,cres,ci,cxs)
    minimizeTrans' st t cch cres ci cxs ((st',t'):ys)
      = if t==t'
        then minimizeTrans' st t True 
             (updateTrans st' st cres)
             (if Set.member st' ci
              then Set.insert st (Set.delete st' ci)
              else ci)
             (updateTrans st' st cxs)
             (updateTrans st' st ys)
        else minimizeTrans' st t cch cres ci ((st',t'):cxs) ys

optimizeVWAATransitions :: (AtomContainer b a,Ord st) => [(b,Set st)] -> [(b,Set st)]
optimizeVWAATransitions mp = List.filter
                             (\(cond,trg)
                              -> case List.find (\(cond',trg') -> (compareAtoms cond cond' == ELT)
                                                                  && (Set.isSubsetOf trg' trg)) mp of
                                   Nothing -> True
                                   Just _ -> False) mp

insertGBATransition :: (AtomContainer b a,Ord st) => (b,Set st,Set st) -> [(b,Set st,Set st)] -> [(b,Set st,Set st)]
insertGBATransition x [] = [x]
insertGBATransition t@(cond,trg,fin) all@(t'@(cond',trg',fin'):ys)
  | trg==trg' = case compareAtoms cond cond' of
    EEQ
      | Set.isSubsetOf fin' fin -> all
      | Set.isSubsetOf fin fin' -> t:ys
      | otherwise -> t':(insertGBATransition t ys)
    ELT
      | Set.isSubsetOf fin' fin -> all
      | otherwise -> t':(insertGBATransition t ys)
    EGT
      | Set.isSubsetOf fin fin' -> t:ys
      | otherwise -> t':(insertGBATransition t ys)
    _ -> t':(insertGBATransition t ys)
  | otherwise = t':(insertGBATransition t ys)

optimizeGBATransitions :: (AtomContainer b a,Ord st) => [(b,Set st,Set st)] -> [(b,Set st,Set st)]
optimizeGBATransitions = foldl (\ts t -> insertGBATransition t ts) []

vwaa2gba :: (AtomContainer b a,Ord b) => VWAA b (LTL a) -> GBA b (LTL a)
vwaa2gba aut = GBA { gbaTransitions = buildTrans (Set.toList (vwaaInits aut)) Map.empty
                   , gbaInits = vwaaInits aut
                   }
  where
    buildTrans [] mp = mp
    buildTrans (x:xs) mp 
      | Map.member x mp = buildTrans xs mp
      | otherwise = let trans = optimizeGBATransitions $ finalSet $ convertTrans x
                    in buildTrans ([ trg | (_,trg,_) <- trans ]++xs) (Map.insert x (Set.fromList trans) mp)
    
    convertTrans sts 
      | Set.null sts = []
      | otherwise = foldl1 transProd [ Set.toList $ (vwaaTransitions aut)!st | st <- Set.toList sts ]
    
    finalSet trans = [(cond,trg,Set.filter (\f -> not (Set.member f trg) ||
                                                  not (List.null [ (cond,trg')
                                                                 | (cond',trg') <- delta f, 
                                                                   (case compareAtoms cond cond' of
                                                                       EEQ -> True
                                                                       ELT -> True
                                                                       _ -> False) && 
                                                                   Set.isSubsetOf trg trg' &&
                                                                   not (Set.member f trg')
                                                                 ])
                                           ) (vwaaCoFinals aut)) 
                     | (cond,trg) <- trans ]

delta, delta' :: AtomContainer b a => LTL a -> [(b,Set (LTL a))]
delta (Ground True) = [(atomsTrue,Set.singleton (Ground True))]
delta (Ground False) = []
delta (Atom p) = [(atomSingleton True p,Set.singleton (Ground True))]
delta (Un Not (Atom p)) = [(atomSingleton False p,Set.singleton (Ground True))]
delta (Un Next f) = [ (atomsTrue,xs) | xs <- Set.toList (cform f) ]
delta (Bin Until l r) = transUnion (delta' r) (transProd (delta' l) [(atomsTrue,Set.singleton (Bin Until l r))])
delta (Bin UntilOp l r) = transProd (delta' r) (transUnion (delta' l) [(atomsTrue,Set.singleton (Bin UntilOp l r))])

delta' (Bin Or l r) = transUnion (delta' l) (delta' r)
delta' (Bin And l r) = transProd (delta' l) (delta' r)
delta' f = delta f

cform :: Ord  a => LTL a -> Set (Set (LTL a))
cform (Bin And lhs rhs) = Set.fromList [ Set.union e1 e2
                                       | e1 <- Set.toList (cform lhs)
                                       , e2 <- Set.toList (cform rhs) ]
cform (Bin Or lhs rhs) = Set.union (cform lhs) (cform rhs)
cform f = Set.singleton (Set.singleton f)

ltl2vwaa :: (Ord b,AtomContainer b a) => LTL a -> VWAA b (LTL a)
ltl2vwaa ltl = VWAA { vwaaTransitions = trans'
                    , vwaaInits = inits'
                    , vwaaCoFinals = getFinals trans'
                    }
  where
    inits' = cform ltl
    trans' = buildTrans (concat [ Set.toList xs | xs <- Set.toList inits']) Map.empty
    
    buildTrans [] mp = mp
    buildTrans (x:xs) mp
      | Map.member x mp = buildTrans xs mp
      | otherwise = let ts = optimizeVWAATransitions $ delta x
                    in buildTrans (concat [ Set.toList c | (_,c) <- ts ]++xs) (Map.insert x (Set.fromList ts) mp)
    
    isFinal (Bin Until _ _) = True
    isFinal _ = False
    
    getFinals mp = Set.filter isFinal $ Map.keysSet mp
    
mergeAlphabet :: Ord a => Map a Bool -> Map a Bool -> Maybe (Map a Bool)
mergeAlphabet a1 a2
  = if confl
    then Nothing
    else Just nmp
      where (confl,nmp) = Map.mapAccum (\hasC (x,y) -> (hasC || x/=y,x)) False $ Map.unionWith (\(x1,_) (y1,_) -> (x1,y1))
                          (fmap (\x -> (x,x)) a1)
                          (fmap (\x -> (x,x)) a2)

transProd :: AtomContainer b a => [(b,Set (LTL a))] -> [(b,Set (LTL a))] -> [(b,Set (LTL a))]
transProd m1 m2 = [ (na,transAnd e1 e2)
                  | (a1,e1) <- m1
                  , (a2,e2) <- m2
                  , na <- case mergeAtoms a1 a2 of
                    Nothing -> []
                    Just p -> [p]
                  ]

transAnd :: Ord a => Set (LTL a) -> Set (LTL a) -> Set (LTL a)
transAnd s1 s2
  | Set.toList s1 == [Ground True] = s2
  | Set.toList s2 == [Ground True] = s1
  | otherwise = Set.union s1 s2

transUnion :: AtomContainer b a => [(b,Set (LTL a))] -> [(b,Set (LTL a))] -> [(b,Set (LTL a))]
transUnion = (++)

ltl2ba :: (AtomContainer b a,Ord b) => LTL a -> BA b Integer
ltl2ba = renameStates . optimizeTransitionsBA . minimizeBA . gba2ba . minimizeGBA . vwaa2gba . ltl2vwaa . distributeNegation

renameStates :: Ord st => BA a st -> BA a Integer
renameStates ba = let (_,stmp) = Map.mapAccum (\i _ -> (i+1,i)) 0 (baTransitions ba)
                      trans' = fmap (\trg -> Set.mapMonotonic (\(c,t) -> (c,stmp!t)) trg) $ Map.mapKeysMonotonic (\k -> stmp!k) (baTransitions ba)
                      inits' = Set.mapMonotonic (stmp!) (baInits ba)
                      fins' = Set.mapMonotonic (stmp!) (baFinals ba)
                  in BA { baTransitions = trans'
                        , baInits = inits'
                        , baFinals = fins'
                        }

baProduct :: (Ord a,Ord st,Ord st') => AtomContainer a b => BA a st -> BA a st' -> BA a (st,st',Bool)
baProduct b1 b2 = BA { baTransitions = trans'
                     , baInits = Set.fromList inits'
                     , baFinals = fins'
                     }
  where
    inits' = [ (i1,i2,False) 
             | i1 <- Set.toList (baInits b1),
               i2 <- Set.toList (baInits b2)
             ]
             
    trans' = traceStates inits' Map.empty
    
    fins' = Set.filter (\(st1,st2,i) -> i && Set.member st2 (baFinals b2)) $ Map.keysSet trans'
    
    traceStates [] mp = mp
    traceStates (x@(s1,s2,i):xs) mp
      | Map.member x mp = traceStates xs mp
      | otherwise = let t1 = (baTransitions b1)!s1
                        t2 = (baTransitions b2)!s2
                        trgs = [ (c,(nst1,nst2,if ((not i) && (Set.member nst1 (baFinals b1)))
                                                  || (i && (Set.member nst2 (baFinals b2)))
                                               then not i
                                               else i))
                               | (c1,nst1) <- Set.toList t1
                               , (c2,nst2) <- Set.toList t2 
                               , c <- case mergeAtoms c1 c2 of
                                 Nothing -> []
                                 Just x -> [x]
                               ]
                    in traceStates ((fmap snd trgs)++xs) (Map.insert (s1,s2,i) (Set.fromList trgs) mp)

ltlToBuchi :: (Ord a,Show a) => (a -> a) -> LTL a -> Buchi (Set (a,Bool))
ltlToBuchi = undefined

{-
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
-}