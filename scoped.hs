module Scoped where

import Control.Monad                    (ap, join)
import Prelude                   hiding (or, fail)

import Framework
import Algebraic (KAlg(..), NondetF(..), algND, ND(..), algND')

-- free monad for algebraic and scoped effects

data Prog sig gam a where
   Return'  :: a                                    -> Prog sig gam a
   Call'    :: sig (Prog sig gam a)                 -> Prog sig gam a
   Enter'   :: gam (Prog sig gam (Prog sig gam a))  -> Prog sig gam a
        deriving (Functor)

instance (Functor f , Functor g) => Applicative (Prog f g) where
     pure  = Return'
     (<*>) = ap

instance (Functor f, Functor g) => Monad (Prog f g) where
     return             = pure
     Return' x   >>= f  = f x
     Call' op    >>= f  = Call'   (fmap (>>= f) op)
     Enter' scs  >>= f  = Enter'  (fmap (fmap (>>= f)) scs)

-- free monad for scoped effects only

data FreeSc gam a where
   Return  :: a                                -> FreeSc gam a
   Enter   :: gam (FreeSc gam (FreeSc gam a))  -> FreeSc gam a
        deriving (Functor)

-- interpreting free monad for scoped effects

data EndoAlg gam f = EndoAlg {
   returnE  :: forall x .  x -> f x,
   enterE   :: forall x .  gam (f (f x)) -> f x }

data BaseAlg gam f a = BaseAlg {
   enterB   :: gam (f a) -> a }

hcata :: Functor gam => EndoAlg gam f -> FreeSc gam a -> f a
hcata ealg (Return x)    = returnE ealg x
hcata ealg (Enter scs)   = (enterE ealg . fmap (hcata ealg . fmap (hcata ealg))) scs

foldSc  :: Functor gam => (a -> b) -> EndoAlg gam f -> BaseAlg gam f b -> FreeSc gam a -> b
foldSc gen ealg balg (Return x)    = gen x
foldSc gen ealg balg (Enter scs)   = enterB balg (fmap endo scs)
     where endo = hcata ealg . fmap (foldSc gen ealg balg)

-- framework
-- step 1

data KSc gam f a where
   Enter_  :: gam (f a) -> KSc gam f a

instance (Functor f, Functor gam) => Functor (KSc gam f) where
   fmap f (Enter_ scs) = Enter_ (fmap (fmap f) scs)

-- step 2

instance Functor gam => HOFunctor (KSc gam) where
   kmap k (Enter_  scs)  = Enter_ (fmap k scs)

-- step 3

iso1 :: Functor gam => FreeSc gam a -> T (KSc gam) a
iso1 (Return x)  = VarT x
iso1 (Enter scs)  = OpT (Enter_ (fmap (iso1 . fmap iso1) scs))

iso2 :: Functor gam => T (KSc gam) a -> FreeSc gam a
iso2 (VarT x)           = Return x
iso2 (OpT (Enter_ scs))  = Enter (fmap (iso2 . fmap iso2) scs)

-- step 4

hSc  :: (Functor gam, Pointed g)
     => (a -> g b) -> (forall x . KSc gam g (g x) -> g x) -> T (KSc gam) a -> g b
hSc  = fold

-- example: nondeterminism with once

data Once a    = Once a deriving (Functor)

hOnce :: T (KAlg NondetF !+! KSc Once) a -> [a]
hOnce = fold eta (algND !#! algOnce) where
     algOnce :: KSc Once [] [a] -> [a]
     algOnce (Enter_ (Once x)) = head x

-- modular form

hOnce' :: (HOFunctor k, Fwd k (ND k)) => T (KAlg NondetF !+! (KSc Once !+! k)) a -> T k [a]
hOnce' = unND . fold eta (algND' !#! (algOnce' !#! fwd))

algOnce' :: HOFunctor k => KSc Once (ND k) (ND k a) -> ND k a
algOnce' (Enter_ (Once x)) = ND (join (fmap (unND . head) (unND x)))

-- constructors

fail :: T (KAlg NondetF !+! k) a
fail = OpT (In (Op_ Fail))

or :: T (KAlg NondetF !+! k) a -> T (KAlg NondetF !+! k) a -> T (KAlg NondetF !+! k) a
or x y = OpT (In (Op_ (Or x y)))

once :: HOFunctor k => T (KAlg NondetF !+! (KSc Once !+! k)) a -> T (KAlg NondetF !+! (KSc Once !+! k)) a
once x = OpT (Out (In (Enter_ (Once (fmap return x)))))

-- examples

exOnce :: T HEmpty [Int]
exOnce = hOnce' (once (or (return 1) (return 5)) >>= \x -> or (return x) (return (x + 1)))

exOr :: T HEmpty [Int]
exOr = hOnce' (or (return 1) (return 5) >>= \x -> or (return x) (return (x + 1)))

-- example: catch as a scoped effect

data Raise  e a  =  Raise  e deriving (Functor)
data Catch  a    =  Catch  a a deriving (Functor)

-- handler

hCatch :: T (KAlg (Raise e) !+! KSc Catch) a -> Either e a 
hCatch = fold eta (algRaise !#! algCatch)

algRaise :: KAlg (Raise e) (Either e) (Either e a) -> Either e a
algRaise (Op_ (Raise e)) = Left e

algCatch :: KSc Catch (Either e) (Either e a) -> Either e a
algCatch (Enter_ (Catch p k)) = case p of { Left e' -> join k; _ -> join p }

instance Pointed (Either e) where 
   eta = return

-- constructors

raise :: e -> T (KAlg (Raise e) !+! KSc Catch) a
raise e = OpT (In (Op_ (Raise e)))

catch :: T (KAlg (Raise e) !+! KSc Catch) a -> T (KAlg (Raise e) !+! KSc Catch) a -> T (KAlg (Raise e) !+! KSc Catch) a
catch p k = OpT (Out (Enter_ (Catch (return p) (fmap return k))))

cCatch :: Int -> T (KAlg (Raise String) !+! KSc Catch) Int
cCatch x = catch (if x > 5 then raise "Error!" else return (x + 1)) (return x)

exCatch1 :: Either String Int
exCatch1 = hCatch (cCatch 5)
-- Right 6

exCatch2 :: Either String Int
exCatch2 = hCatch (cCatch 10)
-- Left "Error!"

-- example: reader

data Ask    r a  = Ask    (r -> a)   deriving (Functor)
data Local  r a  = Local  (r -> r) a deriving (Functor)

-- handler

hRead :: T (KAlg (Ask r) !+! KSc (Local r)) a -> r -> a
hRead = fold eta (algAsk !#! algLocal)

algAsk :: KAlg (Ask r) ((->) r) (r -> a) -> r -> a
algAsk (Op_ (Ask k)) = \r -> k r r

algLocal :: KSc (Local r) ((->) r) (r -> a) -> r -> a
algLocal (Enter_ (Local f k)) = \r -> k (f r) r

-- constructors

ask :: T (KAlg (Ask r) !+! KSc (Local r)) r
ask = OpT (In (Op_ (Ask return)))

local :: (r -> r) -> T (KAlg (Ask r) !+! KSc (Local r)) a -> T (KAlg (Ask r) !+! KSc (Local r)) a 
local f k = OpT (Out (Enter_ (Local f (fmap return k))))

exRead :: (Int, Int, Int)
exRead = hRead (do r1 <- ask; r2 <- local (*2) ask; r3 <- ask; return (r1, r2, r3)) 1
-- (1,2,1)

-- example: nondeterminism with cut

data CutList a = Ret [a] | Flag [a] deriving (Functor, Show)

instance Pointed CutList where 
   eta x = Ret [x]

instance Applicative CutList where 
    pure = Ret . pure
    (<*>) = ap

instance Monad CutList where 
   return = pure
   Ret  []     >>= f = Ret  []
   Flag []     >>= f = Flag []
   Ret  (x:xs) >>= f = append (f x) (Ret xs >>= f)
   Flag (x:xs) >>= f = append (f x) (Flag xs >>= f)

-- helper functions

append :: CutList a -> CutList a -> CutList a 
append (Ret  xs)   (Ret  ys)  = Ret   (xs ++ ys)
append (Ret  xs)   (Flag ys)  = Flag  (xs ++ ys)
append (Flag xs)   _          = Flag  xs

open :: CutList a -> CutList a 
open (Flag xs) = Ret xs 
open (Ret  xs) = Ret xs

close :: CutList a -> CutList a 
close (Flag xs) = Flag xs 
close (Ret  xs) = Flag xs

-- signatures

data Cut a = Cut a deriving (Functor)

data Calls k = Calls k deriving (Functor)

-- handler

hCut :: T (KAlg NondetF !+! (KAlg Cut !+! KSc Calls)) a -> CutList a 
hCut = fold eta (algNDCut !#! (algCut !#! algCalls))

algNDCut :: KAlg NondetF CutList (CutList a) -> CutList a
algNDCut (Op_ Fail)      = Ret []
algNDCut (Op_ (Or p q))  = append p q

algCut :: KAlg Cut CutList (CutList a) -> CutList a
algCut (Op_ (Cut k)) = close k

algCalls :: KSc Calls CutList (CutList a) -> CutList a
algCalls (Enter_ (Calls k)) = join (open k)

-- constructors

cut :: T (KAlg NondetF !+! (KAlg Cut !+! KSc Calls)) ()
cut = OpT (Out (In (Op_ (Cut (return ())))))

call :: T (KAlg NondetF !+! (KAlg Cut !+! KSc Calls)) a -> T (KAlg NondetF !+! (KAlg Cut !+! KSc Calls)) a
call k = OpT (Out (Out (Enter_ (Calls (fmap return k)))))

exCut = hCut (or (call (or (cut >> return 1) (return 2))) (return 3))
-- Ret [1,3]

-- example: depth-bounded search

data Depth a = Depth Int a  deriving (Functor)

newtype DepthCarrier a = DC { unDC :: Int -> [(a, Int)] } deriving (Functor)

instance Pointed DepthCarrier where 
    eta x = DC (\i -> [(x, i)])

hDepth :: T (KAlg NondetF !+! KSc Depth) a -> Int -> [(a, Int)]
hDepth = unDC . fold eta (algOr !#! algDepth) 

algOr :: KAlg NondetF DepthCarrier (DepthCarrier a) -> DepthCarrier a
algOr (Op_ Fail)      = DC (const [])
algOr (Op_ (Or p q))  = DC (\i -> if i == 0 then [] else unDC p (i-1) ++ unDC q (i-1))

algDepth :: KSc Depth DepthCarrier (DepthCarrier a) -> DepthCarrier a
algDepth (Enter_ (Depth i k)) = DC (\i' -> concatMap fst (unDC (fmap (($ i') . unDC) k) i))

-- constructors

depth :: Int -> T (KAlg NondetF !+! KSc Depth) a -> T (KAlg NondetF !+! KSc Depth) a 
depth i p = OpT (Out (Enter_ (Depth i (fmap return p))))

cDepth = depth 1 (or (return 1) (or (return 2) (return 3))) 
            >>= \x -> (or (return x) (or (return 4) (or (return 5) (return 6))))

exDepth = hDepth cDepth 2
-- [(1,1),(4,0)]

-- example: concurrency

data Act m a = Act (m a) | Kill deriving (Functor)
data Con a = Spawn a a | Atomic a deriving (Functor)

-- helper functions

data Res m a = More (m (Res m a)) | Done a deriving (Functor)

instance Monad m => Pointed (Res m) where 
   eta = Done

instance Monad m => Applicative (Res m) where 
   pure = Done 
   (<*>) = ap

instance Monad m => Monad (Res m) where 
   return = pure 
   Done x >>= f = f x 
   More r >>= f = More (fmap (>>= f) r)

retraction :: Monad m => Res m a -> m a
retraction (More m)  = m >>= retraction
retraction (Done x)  = return x

interleave  :: Monad m => Res m a -> Res m b -> Res m a
interleave (Done x)    r          = fmap (const x) r
interleave r           (Done _)   = r
interleave (More m1)   (More m2)  = More (do  r1 <- m1; r2 <- m2; return (interleave r1 r2))

-- handler  

hConc  :: Monad m  => T (KAlg (Act m) !+! KSc Con) a -> Res m a
hConc  = fold Done (algAct !#! algCon)

algAct :: KAlg (Act m) (Res m) (Res m a) -> Res m a
algAct (Op_ (Act m))  = More m
algAct (Op_ Kill)     = Done (error "main process killed")

algCon :: Monad m => KSc Con (Res m) (Res m a) -> Res m a
algCon (Enter_ (Atomic r))     = More (retraction r)
algCon (Enter_ (Spawn r1 r2))  = join (interleave r1 r2)

-- constructors

spawn :: Monad m => T (KAlg (Act m) !+! KSc Con) a -> T (KAlg (Act m) !+! KSc Con) b -> T (KAlg (Act m) !+! KSc Con) a
spawn p q = OpT (Out (Enter_ (Spawn (fmap return p) (fmap return (q >> kill)))))

atomic :: Monad m => T (KAlg (Act m) !+! KSc Con) a -> T (KAlg (Act m) !+! KSc Con) a
atomic p = OpT (Out (Enter_ (Atomic (fmap return p))))

kill :: T (KAlg (Act m) !+! KSc Con) a 
kill = OpT (In (Op_ Kill))

act :: Monad m => m a -> T (KAlg (Act m) !+! KSc Con) a 
act m = OpT (In (Op_ (Act (fmap return m))))

say = act . putStr
conTest1 =  spawn  (say "hello " >> say "world ") 
                   (say "goodbye " >> say "cruel " >> say "world ")
conTest2 =  spawn  (atomic (spawn  (mapM say ["a", "b", "c"])  
                                   (mapM say ["A", "B", "C"]))) 
                   (atomic (spawn  (mapM say ["1", "2", "3"])  
                                   (mapM say ["-", "-", "-"])))

exCon1 :: IO ()
exCon1 = retraction (hConc conTest1)
-- hello goodbye world cruel world 

exCon2 :: IO [()]
exCon2 = retraction (hConc conTest2)
-- aAbBcC1-2-3-[(),(),()]
