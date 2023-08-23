module Exceptions where 

import Framework
import Algebraic (KAlg(..),StateF(..),hSt')

import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Trans.State.Lazy (StateT(..))

-- exception signature

data Exc f r = Throw | forall x . Catch (f x) (Maybe x -> r)

instance Functor (Exc f) where
   fmap f Throw = Throw
   fmap f (Catch c k) = Catch c (f . k)

instance HOFunctor Exc where
   kmap f Throw = Throw
   kmap f (Catch c k) = Catch (f c) k

progExc :: Int -> T Exc String
progExc x = OpT (Catch (if x >= 0 then return x else OpT Throw) k)
       where  k Nothing  = return "Too small"
              k (Just x) = return (show x)

instance Pointed Maybe where
   eta = Just

-- handler

hExc :: T Exc a -> Maybe a
hExc = fold Just algExc

algExc :: Exc Maybe (Maybe a) -> Maybe a
algExc Throw        = Nothing
algExc (Catch c k)  = k c

testExc1 :: Maybe String
testExc1 = hExc (progExc 5)
-- Just "5"

testExc2 :: Maybe String
testExc2 = hExc (progExc (-5))
-- Just "Too small"

-- state + exceptions

hExc'   :: (HOFunctor k, Fwd k (MaybeT (T k))) 
        => T (Exc !+! k) a -> T k (Maybe a)
hExc'   = runMaybeT . fold return (algExc' !#! fwd)  

algExc'  :: HOFunctor k => Exc (MaybeT (T k)) (MaybeT (T k) a)
        -> MaybeT (T k) a
algExc'  Throw        = MaybeT (return Nothing)
algExc'  (Catch c k)  = MaybeT (runMaybeT c >>= runMaybeT . k)

instance Functor sig => Fwd (KAlg sig) (MaybeT (T (KAlg sig))) where 
	fwd (Op_ ops) = MaybeT (OpT (Op_ (fmap runMaybeT ops )))

instance Monad m => Pointed (MaybeT m) where
   eta = MaybeT . return . return

-- example global state

getGlob :: HOFunctor k => T (Exc !+! (KAlg (StateF s) !+! k)) s
getGlob = OpT (Out (In (Op_ (Get return))))

putGlob :: HOFunctor k => s -> T (Exc !+! (KAlg (StateF s) !+! k)) ()
putGlob s = OpT (Out (In (Op_ (Put s (return ())))))

throwGlob :: T (Exc !+! k) ()
throwGlob = OpT (In Throw)

catchGlob :: HOFunctor k => T (Exc !+! k) a -> T (Exc !+! k) a -> T (Exc !+! k) a
catchGlob op k = OpT (In (Catch op (maybe k return)))

decrGlob :: (Num s, Ord s, HOFunctor k) => T (Exc !+! (KAlg (StateF s) !+! k)) ()
decrGlob = getGlob >>= \s -> if s > 0 then putGlob (s - 1) else throwGlob

instance Functor sig => Fwd (KAlg sig !+! HEmpty) (MaybeT (T (KAlg sig !+! HEmpty))) where 
 	fwd (In (Op_ ops)) = MaybeT (OpT (In (Op_ (fmap runMaybeT ops))))
 	fwd (Out HEmpty)  = MaybeT (OpT (Out HEmpty))

testExcGlob :: HOFunctor k => T (Exc !+! (KAlg (StateF Int) !+! k)) ()
testExcGlob = decrGlob >> catchGlob (decrGlob >> decrGlob) (return ())

exExcGlob :: T HEmpty (Maybe (), Int)
exExcGlob = hSt' (hExc' testExcGlob) 2 
-- (Just (), 0)

-- example local state

getLoc :: HOFunctor k => T (KAlg (StateF s) !+! (Exc !+! k)) s
getLoc = OpT (In (Op_ (Get return)))

putLoc :: HOFunctor k => s -> T (KAlg (StateF s) !+! (Exc !+! k)) ()
putLoc s = OpT (In (Op_ (Put s (return ()))))

throwLoc :: T (KAlg (StateF s) !+! (Exc !+! k)) ()
throwLoc = OpT (Out (In Throw))

catchLoc :: HOFunctor k => T (KAlg (StateF s) !+! (Exc !+! k)) a -> T (KAlg (StateF s) !+! (Exc !+! k)) a -> T (KAlg (StateF s) !+! (Exc !+! k)) a
catchLoc op k = OpT (Out (In (Catch op (maybe k return))))

decrLoc :: (Num s, Ord s, HOFunctor k) => T (KAlg (StateF s) !+! (Exc !+! k)) ()
decrLoc = getLoc >>= \s -> if s > 0 then putLoc (s - 1) else throwLoc

instance Fwd (Exc !+! HEmpty) (StateT s (T (Exc !+! HEmpty))) where 
 	fwd (In Throw)        = StateT $ \_ -> OpT (In Throw)
 	fwd (In (Catch op k)) = StateT $ \s -> OpT (In (Catch (runStateT op s) (\m -> runStateT (k (fmap fst m)) s))) where 
 	fwd (Out HEmpty)      = StateT $ \_ -> (OpT (Out HEmpty))

testExcLoc :: HOFunctor k => T (KAlg (StateF Int) !+! (Exc !+! k)) ()
testExcLoc = decrLoc >> catchLoc (decrLoc >> decrLoc) (return ())

exExcLoc :: T HEmpty (Maybe ((), Int))
exExcLoc = hExc' (hSt' testExcLoc 2) 
-- Just ((), 1)