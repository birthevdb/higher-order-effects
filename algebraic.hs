
module Algebraic where

import Framework

import Control.Monad.Trans.State.Lazy (StateT(..))
import Prelude hiding (fail, or)
import Control.Monad (ap)
import Control.Monad.Trans (MonadTrans(..))

-- free monad for algebraic effects

data Free (sig :: * -> *) a where
   Var  :: a                 -> Free sig a
   Op   :: sig (Free sig a)  -> Free sig a

instance  Functor sig => Monad (Free sig) where
   return         = pure 
   Var x  >>= k   = k x
   Op t   >>= k   = Op (fmap (>>= k) t)

instance Functor sig => Functor (Free sig) where
   fmap f (Var x) = Var (f x)
   fmap f (Op ops) = Op (fmap (fmap f) ops)

instance Functor sig => Applicative (Free sig) where
   pure = Var
   (<*>) = ap

-- folding over the free monad

foldAlg :: Functor sig => (a -> b) -> (sig b -> b) -> Free sig a -> b
foldAlg gen alg (Var x)   = gen x
foldAlg gen alg (Op ops)  = alg (fmap (foldAlg gen alg) ops)

-- framework
-- step 1

data KAlg sig (f :: * -> *) a where
   Op_ :: sig a -> KAlg sig f a

instance Functor sig => Functor (KAlg sig f) where
   fmap f (Op_ ops) = Op_ (fmap f ops)

-- step 2

instance Functor sig => HOFunctor (KAlg sig) where
   kmap k (Op_ x) = Op_ x

-- step 3 

iso1 :: Functor sig => Free sig a -> T (KAlg sig) a
iso1 (Var x)   = VarT x
iso1 (Op ops)  = OpT (Op_ (fmap iso1 ops))

iso2 :: Functor sig => T (KAlg sig) a -> Free sig a
iso2 (VarT x)         = Var x
iso2 (OpT (Op_ ops))  = Op (fmap iso2 ops)

-- step 4

hAlg  :: (Functor sig, Pointed g)
       => (a -> g b) -> (forall x . KAlg sig g (g x) -> g x) -> T (KAlg sig) a -> g b
hAlg  = fold

-- State

data StateF s a = Get (s -> a) | Put s a deriving (Functor)

instance HOFunctor k => Pointed (StateT s (T k)) where
   eta = return

hSt :: T (KAlg (StateF s)) a -> (s -> (a, s))
hSt = fold (,) algSt where

algSt :: KAlg (StateF s) ((->) s) (s -> a) -> s -> a
algSt (Op_ (Get k))     = \ s -> k s s
algSt (Op_ (Put s' k))  = \ _ -> k s'

instance Pointed ((->) s) where 
   eta = const

get :: T (KAlg (StateF s)) s
get = OpT (Op_ (Get return))

put :: s -> T (KAlg (StateF s)) ()
put s = OpT (Op_ (Put s (return ())))

incr :: Num s => T (KAlg (StateF s)) ()
incr = get >>= \s -> put (s + 1)

exState :: (String, Int)
exState = hSt (incr >> return "done") 5
-- ("done",6)

-- nondeterminism

data NondetF a = Fail | Or a a deriving (Functor)

hND :: T (KAlg NondetF) a -> [a]
hND = fold eta algND where 

algND :: KAlg NondetF [] [x] -> [x]
algND (Op_ Fail)     = []
algND (Op_ (Or p q)) = p ++ q

instance Pointed [] where 
   eta = return

fail :: T (KAlg NondetF) a
fail = OpT (Op_ Fail)

or :: T (KAlg NondetF) a -> T (KAlg NondetF) a -> T (KAlg NondetF) a
or p q = OpT (Op_ (Or p q))

exND :: [Int]
exND = hND (or (return 1) (or (or (return 2) (return 3)) fail))
-- [1,2,3]

-- example: state + nondeterminism

-- state, modular

hSt'    :: (HOFunctor k, Fwd k (StateT s (T k)))
        => T (KAlg (StateF s) !+! k) a -> (s -> T k (a, s))
hSt'    = runStateT . fold return (algSt' !#! fwd)

algSt'  :: KAlg (StateF s) (StateT s m) (StateT s m a) -> StateT s m a 
algSt'  (Op_ (Get k))     = StateT (\ s -> runStateT (k s) s)
algSt'  (Op_ (Put s' k))  = StateT (\ _ -> runStateT k s')

instance MonadTrans t => Fwd HEmpty (t (T HEmpty)) where 
    fwd HEmpty = lift (OpT HEmpty)

instance Functor sig => Fwd (KAlg sig) (StateT s (T (KAlg sig))) where 
 	fwd (Op_ ops) = StateT (\s -> (OpT (Op_ (fmap (($ s) . runStateT) ops))))

instance Functor sig => Fwd (KAlg sig !+! HEmpty) (StateT s (T (KAlg sig !+! HEmpty))) where 
 	fwd (In (Op_ ops)) = StateT $ \s -> (OpT (In (Op_ (fmap (($ s) . runStateT) ops))))
 	fwd (Out HEmpty)  = StateT $ \_ -> (OpT (Out HEmpty))

-- nondeterminism, modular

data ND k a = ND { unND :: T k [a] } deriving (Functor)

instance HOFunctor k => Pointed (ND k) where
   eta = ND . return . return

hND' :: (HOFunctor k, Fwd k (ND k)) => T (KAlg NondetF !+! k) a -> T k [a]
hND' = unND . fold eta (algND' !#! fwd)

algND' :: HOFunctor k => KAlg NondetF (ND k) (ND k a) -> ND k a
algND' (Op_ Fail)      = ND $ return []
algND' (Op_ (Or p q))  = ND $ (++) <$> (unND p) <*> (unND q)

instance Fwd HEmpty (ND HEmpty) where 
 	fwd HEmpty = ND (OpT HEmpty)

instance Functor sig => Fwd (KAlg sig !+! HEmpty) (ND (KAlg sig !+! HEmpty)) where 
 	fwd (In (Op_ ops)) = ND (OpT (In (Op_ (fmap unND ops))))
 	fwd (Out HEmpty)  = ND (OpT (Out HEmpty))

-- global state

orGlob :: T (KAlg NondetF !+! k) a -> T (KAlg NondetF !+! k) a -> T (KAlg NondetF !+! k) a
orGlob p q = OpT (In (Op_ (Or p q)))

incrGlob :: HOFunctor k => T (KAlg NondetF !+! (KAlg (StateF s) !+! k)) ()
incrGlob = OpT (Out (In (Op_ (Get (\s -> OpT (Out (In (Op_ (Put s (return ()))))))))))

testGlob :: HOFunctor k => T (KAlg NondetF !+! (KAlg (StateF Int) !+! k)) String
testGlob = orGlob (incrGlob >> return "a") (return "b")

exGlob :: T HEmpty ([String], Int)
exGlob = hSt' (hND' testGlob) 5 
-- (["a","b"],5)

-- local state

orLoc :: T (KAlg (StateF s) !+! (KAlg NondetF !+! k)) a -> T (KAlg (StateF s) !+! (KAlg NondetF !+! k)) a -> T (KAlg (StateF s) !+! (KAlg NondetF !+! k)) a
orLoc p q = OpT (Out (In (Op_ (Or p q))))

incrLoc :: (Num s, HOFunctor k) => T (KAlg (StateF s) !+! k) ()
incrLoc = OpT (In (Op_ (Get (\s -> OpT (In (Op_ (Put (s+1) (return ()))))))))

testLoc :: HOFunctor k => T (KAlg (StateF Int) !+! (KAlg NondetF !+! k)) String
testLoc = orLoc (incrLoc >> return "a") (return "b")

exLoc :: T HEmpty [(String, Int)]
exLoc = hND' (hSt' testLoc 5) 
-- [("a",6),("b",5)]