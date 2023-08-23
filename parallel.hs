module Parallel where

import Framework 
import Algebraic (KAlg(..))
import Exceptions
import Writer hiding (iso1,iso2)

import Control.Monad (ap, liftM)
import Control.Monad.Writer.Lazy (WriterT(..))
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Maybe (catMaybes)

-- parallel effects

data FreePar rho a where
   Pure  :: a                                                -> FreePar rho a
   For   :: rho (FreePar rho b) -> (rho b -> FreePar rho a)  -> FreePar rho a

-- algebraic and parallel effects

data Comp sig rho a where
   Pure'     :: a -> Comp sig rho a
   Perform'  :: sig (Comp sig rho a) -> Comp sig rho a
   For'      :: rho (Comp sig rho b) -> (rho b -> Comp sig rho a) -> Comp sig rho a

instance (Functor sig, Functor rho) => Functor (Comp sig rho) where
   fmap = liftM

instance (Functor sig, Functor rho) => Applicative (Comp sig rho) where
    pure  = Pure'
    (<*>) = ap

instance (Functor sig, Functor rho) => Monad (Comp sig rho) where
   return = pure
   (Pure'  x)      >>= f = f x
   (Perform'  op)  >>= f = Perform' (fmap (>>= f) op)
   (For' iters k)  >>= f = For' iters ((>>= f) . k)

-- framework
-- step 1

data KPar rho f a where
   For_     :: rho (f b) -> (rho b -> a) -> KPar rho f a

instance Functor (KPar rho f) where
   fmap f (For_ iters k) = For_ iters (f . k)

-- step 2

instance Functor rho => HOFunctor (KPar rho) where
   kmap k (For_ iters c) = For_ (fmap k iters) c

-- step 3 

iso1 :: Functor rho => FreePar rho a -> T (KPar rho) a
iso1 (Pure x)       = VarT x
iso1 (For iters k)  = OpT (For_ (fmap iso1 iters) (fmap iso1 k))

iso2 :: Functor rho => T (KPar rho) a -> FreePar rho a
iso2 (VarT x)              = Pure x
iso2 (OpT (For_ iters k))  = For (fmap iso2 iters) (fmap iso2 k)

-- step 4

hPar   :: (Functor rho, Pointed g)
       => (a -> g b) -> (forall x . KPar rho g (g x) -> g x) -> T (KPar rho) a -> g b
hPar   = fold

hComp  :: (Functor sig, Functor rho, Pointed g)
       => (a -> g b) -> (forall x . (KAlg sig !+! KPar rho) g (g x) -> g x)
       -> T (KAlg sig !+! KPar rho) a -> g b
hComp  = fold

-- example: weak exceptions

hTell  :: (Monoid w, Fwd k (WriterT w (T k))) 
       => T (KAlg (Tell w) !+! k) a -> T k (a, w)
hTell  = runWriterT . fold eta (algTell' !#! fwd)

hFor   :: (Monoid w, Fwd k (MaybeT (WriterT w (T k)))) 
       => T (KPar [] !+! k) (Maybe a, w) -> T k (Maybe a, w)
hFor   = runWriterT . runMaybeT . fold (MaybeT . WriterT . return) (algFor !#! fwd) 

algFor :: (HOFunctor k, Monoid w) 
       => KPar [] (MaybeT (WriterT w (T k))) (MaybeT (WriterT w (T k)) a) -> MaybeT (WriterT w (T k)) a
algFor (For_ iters k) = sequence iters >>= k 

-- constructors

for     :: [T (Exc !+! (KAlg (Tell String) !+! (KPar [] !+! HEmpty))) a]
        ->  T (Exc !+! (KAlg (Tell String) !+! (KPar [] !+! HEmpty))) [a]
for xs  = OpT (Out (Out (In ((For_ xs) return))))

tells   :: HOFunctor k => w -> T (Exc !+! (KAlg (Tell w) !+! k)) ()
tells w = OpT $ Out $ In $ Op_ $ Tell w (return ())

-- example

weak = do  tells "start "
           for (fmap (\i -> if i == 2
              then  do  tells "!"; throwGlob; 
                        tells "unreachable"
              else  tells (show i)) [0..4]) 
           tells " end"; return 0

exExc :: T HEmpty (Maybe Int, [Char])
exExc = hFor $ hTell $ hExc' weak
-- (Nothing,"start 01!34")

-- forwarding

bimap :: Monoid w => [(b, w)] -> ([b], w)
bimap [] = ([], mempty)
bimap ((b, w):xs) = let (bs, w') = bimap xs in (b:bs, w <> w')

containsNothing :: [Maybe a] -> Bool
containsNothing [] = False 
containsNothing (Nothing:xs) = True
containsNothing (Just _:xs) = containsNothing xs

instance Monoid w => Fwd (KPar [] !+! HEmpty) (WriterT w (T (KPar [] !+! HEmpty))) where 
   fwd (In (For_ iters k)) = WriterT (OpT (In (For_ (fmap runWriterT iters) ((\ (bs, w) -> (fmap (fmap ((<>) w)) . runWriterT) (k bs)) . bimap))))
   fwd (Out HEmpty)        = WriterT (OpT (Out HEmpty))

instance Fwd (KAlg (Tell [Char]) !+! (KPar [] !+! HEmpty)) (MaybeT (T (KAlg (Tell [Char]) !+! (KPar [] !+! HEmpty)))) where 
   fwd (In  (Op_ (Tell w k)))      = MaybeT (OpT (In (Op_ (Tell w (runMaybeT k)))))
   fwd (Out (In (For_ iters k)))   = MaybeT (OpT (Out (In (For_ (fmap runMaybeT iters) (\mbs -> if containsNothing mbs then return Nothing else runMaybeT (k (catMaybes mbs))))))) 
   fwd (Out (Out HEmpty))          = MaybeT (OpT (Out (Out HEmpty)))

instance Fwd HEmpty (MaybeT (WriterT w (T HEmpty))) where 
  fwd HEmpty = MaybeT (WriterT (OpT HEmpty))

-- example: amb

data Amb r = Amb [r] deriving (Functor)

-- handler

hAmb :: T (KAlg Amb !+! KPar []) a -> [a]
hAmb = fold return (algAmb !#! algForAmb)

algAmb :: KAlg Amb [] [a] -> [a]
algAmb (Op_ (Amb r)) = concat r

algForAmb :: KPar [] [] [a] -> [a]
algForAmb (For_ iters k) = concat (fmap k (foldr catProd [[]] iters))

catProd :: [a] -> [[a]] -> [[a]]
catProd xs yss = [x:ys | x <- xs, ys <- yss]

-- constructors

amb :: [T (KAlg Amb !+! k) a ] -> T (KAlg Amb !+! k) a 
amb r = OpT (In (Op_ (Amb r)))

-- coin example

exCoin :: [String]
exCoin = hAmb $ do 
    chars <- OpT (Out (For_ (replicate 3 (amb [return "H", return "T"])) return))
    return (concat chars)
-- ["HHH","HHT","HTH","HTT","THH","THT","TTH","TTT"]

-- parallel into sequential code

newtype AC w a = AC { unAmb :: [(a, w)] } deriving (Functor)

instance Monoid w => Pointed (AC w) where 
  eta x = AC (return (x, mempty))

hAmb'  :: Monoid w 
       => T (KAlg Amb !+! (KAlg (Tell w) !+! KPar [])) a -> [(a, w)]
hAmb'  = unAmb . fold eta (algAmb' !#! (algTellAmb !#! algForAmb'))

algAmb' :: KAlg Amb (AC w) (AC w a) -> AC w a
algAmb' (Op_ (Amb r)) = AC (concat (fmap unAmb r))

algTellAmb :: Monoid w => KAlg (Tell w) (AC w) (AC w a) -> AC w a
algTellAmb (Op_ (Tell w k)) = AC (do (x, w') <- unAmb k; return (x, w <> w'))

algForAmb' :: Monoid w => KPar [] (AC w) (AC w a) -> AC w a
algForAmb' (For_ iters k) = AC (aggr (unAmb . k) (foldr catProd [[]] (fmap unAmb iters))) 

aggr :: Monoid w => ([b] -> [(a,w)]) -> [[(b, w)]] -> [(a,w)]
aggr k = concat . fmap ((\ (bs, w) -> fmap (fmap ((<>) w)) (k bs)) . bimap)

exDigit :: [(Int, Int)]
exDigit = concat $ fmap snd $ hAmb' $ do 
  d1 <- amb (fmap return [0..9])
  d2 <- amb (fmap return [0..9])
  if d1 + d2 == 13 
  then OpT (Out (In (Op_ (Tell [(d1, d2)] (return ())))))
  else return ()
-- [(4,9),(5,8),(6,7),(7,6),(8,5),(9,4)]
