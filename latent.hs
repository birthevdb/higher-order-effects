{-# LANGUAGE GADTs #-}

module Latent where

import Framework

import Control.Monad (ap,liftM,join)
import Control.Monad.Trans.State.Lazy (StateT(..))

import Algebraic (KAlg(..),StateF(..),algSt')
import Scoped (KSc(..),Ask(..),Local(..))

-- monad for latent effects

data FreeLat zet lat a where
  Leaf  :: a -> FreeLat zet lat a
  Node  :: zet p c -> lat () -> (forall x . c x -> lat () -> FreeLat zet lat (lat x))
        -> (lat p -> FreeLat zet lat a)  -> FreeLat zet lat a

instance Functor (FreeLat zet l) where
  fmap = liftM

instance Applicative (FreeLat zet l) where
  pure   = Leaf
  (<*>)  = ap

instance Monad (FreeLat zet l) where
  return                 = pure
  Leaf x         >>=  f  = f x
  Node c l st k  >>=  f  = Node c l st (\x -> k x >>= f)

-- framework
-- step 1

data KLat zet lat f a where
   Node_ :: zet p c -> lat () -> (forall x. c x -> lat () -> f (lat x)) -> (lat p -> a) -> KLat zet lat f a

instance Functor (KLat zet lat f) where
   fmap f (Node_ sub lat st c) = Node_ sub lat st (f . c)

-- step 2

instance HOFunctor (KLat zet lat) where
   kmap k (Node_ sub lat st c) = Node_ sub lat (fmap k . st) c

-- step 3

iso1 :: FreeLat zet lat a -> T (KLat zet lat) a
iso1 (Leaf x)           = VarT x
iso1 (Node ops l sub k) = OpT (Node_ ops l (fmap (fmap iso1) sub) (fmap iso1 k))
iso2 :: T (KLat zet lat) a -> FreeLat zet lat a
iso2 (VarT x)                  = Leaf x
iso2 (OpT (Node_ ops l sub k)) = Node ops l (fmap (fmap iso2) sub) (fmap iso2 k)

-- step 4

hLat  :: Pointed g
      => (a -> g b) -> (forall x . KLat zet lat g (g x) -> g x) 
      -> T (KLat zet lat) a -> g b
hLat  = fold

-- example: lazy evaluation with memoization

type Ptr                = Int

data Thunking v :: * -> (* -> *) -> * where
  Force  :: Ptr ->  Thunking v v    NoSub
  Thunk  ::         Thunking v Ptr  (OneSub v)

data NoSub :: * -> * where
data OneSub v  :: * -> *
  where One :: OneSub v v

data Id a = Id { unId :: a } deriving (Functor)

instance Applicative Id where 
  pure = Id
  (<*>) = ap

instance Monad Id where 
  return = pure 
  m >>= f = f (unId m)

type Expr v a = T   (     KAlg  (StateF v)   !+!   KAlg (Ask [v])
                    !+!   KSc   (Local [v])  !+!   KLat  (Thunking v) Id) a

newtype StateL s l a  = StateL { unStateL :: (s, l a) }
data Value = Val Int | Func (Expr Value Value)

-- lazy handler

hLazy  :: Expr v a -> v -> [v] -> [Thunk v] -> (StateL (v, [Thunk v]) Id a)
hLazy  = unH . fold gen (algSt !#! (algAsk !#! (algLocal' !#! algLatLazy))) where

gen :: a -> H v a
gen x = H $ \s _ th -> StateL ((s, th), Id x) 

algSt :: KAlg (StateF v) (H v) (H v a) -> H v a
algSt (Op_ (Get k)) = H $ \s -> unH (k s) s
algSt (Op_ (Put s' k)) = H $ \_ -> unH k s'

algAsk :: KAlg (Ask [v]) (H v) (H v a) -> H v a
algAsk (Op_ (Ask k)) = H $ \s nv -> unH (k nv) s nv

algLocal' :: KSc (Local [v]) (H v) (H v a) -> H v a
algLocal' (Enter_ (Local f k)) = H $ \s nv th -> unH (join k) s (f nv) th

algLatLazy :: KLat (Thunking v) Id (H v) (H v a) -> H v a
algLatLazy (Node_ Thunk     l st k) = H $ \s nv th -> unH (k (fmap (const (length th)) l)) s nv (th ++ [Left (st One)])
algLatLazy (Node_ (Force p) l st k) = H $ \s nv th -> case (th !! p) of
        Left t -> do
           let StateL ((s', th'), Id lv) = unH (t l) s nv th
           unId $ fmap (\v -> unH (k lv) s' nv (replace p (Right v) th')) lv
        Right v -> unH (k (fmap (const v) l)) s nv th

-- eager handler

hEager  :: Expr v a -> v -> [v] -> [Thunk v] -> (StateL (v, [Thunk v]) Id a)
hEager  = unH . fold gen (algSt !#! (algAsk !#! (algLocal' !#! algLatEager)))

algLatEager :: KLat (Thunking v) Id (H v) (H v a) -> H v a
algLatEager (Node_ Thunk l st k) = H $ \s nv th -> 
        let StateL ((s', th'), lv) = unH (st One l) s nv th in
        unId $ fmap (\v -> unH (k (fmap (const (length th')) l)) s' nv (th' ++ [Right v])) (unId lv)
algLatEager (Node_ (Force p) l st k) = H $ \s nv th -> case (th !! p) of
        Right v -> unH (k (fmap (const v) l)) s nv th

-- helper functions

instance Functor l => Functor (StateL s l) where
  fmap f (StateL (s, la)) = StateL (s, fmap f la)

replace :: Int -> a -> [a] -> [a]
replace 0 x (_ : xs)          = x : xs
replace i x (y : xs) | i > 0  = y : replace (i - 1) x xs
replace _ _ _                 = error "bad index"

type Thunk v = Either (Id () -> H v (Id v)) v

data H v a = H { unH :: v -> [v] -> [Thunk v] -> StateL (v, [Thunk v]) Id a }
     deriving (Functor)

instance Pointed (H v) where
  eta = return

instance Applicative (H v) where
  pure x = H $ \s nv th -> StateL ((s, th), Id x)
  (<*>) = ap

instance Monad (H v) where
  return = pure
  m >>= f = H $ \s nv th -> (\(StateL ((s', th'), Id x)) -> unH (f x) s' nv th') $ unH m s nv th

-- constructors

get    :: Expr v v
get    = OpT $ In $ Op_ ((Get return))

put    :: v -> Expr v ()
put s  = OpT $ In $ Op_ ((Put s (return ())))

local       :: [v] -> Expr v a -> Expr v a
local r' t  = OpT $ Out $ Out $ In $ Enter_ ((Local (const r') (return t)))

ask         :: Expr v [v]
ask         = OpT $ Out $ In $ Op_ ((Ask return))

thunk    :: Expr v v -> Expr v Ptr
thunk t  = OpT $ Out $ Out $ Out $ Node_ (Thunk) (Id ()) (\One _-> fmap Id t) (VarT . unId)

force    :: Ptr -> Expr v v
force p  = OpT $ Out $ Out $ Out $ Node_ ((Force p)) (Id ()) (\x -> case x of) (VarT . unId)

var_mem  :: Ptr -> Expr Value Value
var_mem  x = do nv <- ask; local ([nv !! x]) (force 0)

abs_mem  :: Expr Value Value -> Expr Value Value
abs_mem body = return (Func body)

app_mem  :: Expr Value Value -> Expr Value Value -> Expr Value Value
app_mem e1 e2 = do
  vf <- e1; nv <- ask; p <- thunk e2
  case vf of Func body -> local ([nv !! p]) body

-- example

prog :: Expr Value Value
prog = do
  let e1 = abs_mem (return (Val 3)) -- (var_mem 0)
  let e2 = (do put (Val 42); return (Val 5))
  app_mem e1 e2

exLazy :: StateL (Value, [Thunk Value]) Id Value
exLazy = hLazy prog (Val 0) [] []
-- ("0","[Left thunk]","3")

exEager :: StateL (Value, [Thunk Value]) Id Value
exEager = hEager prog (Val 0) [] []
-- ("42","[Right 5]","3")

instance Show (Id () -> H Value (Id Value)) where
  show t = "thunk"

instance Show Value where
  show (Val x) = show x
  show (Func _) = "Func"

instance Show (StateL (Value, [Thunk Value]) Id Value) where
  show (StateL ((s, th), Id x)) = show (show s, show th, show x)

-- example: lambda by CBPV


data Lambda th fun f a where
  Lambda  ::  (th b -> f c)    ->  (fun (th b) c  -> a)  -> Lambda th fun f a
  Vari    ::  (th b)           ->  (b             -> a)  -> Lambda th fun f a
  Apply   ::  (fun (th b) c)   ->  (f b) -> (c    -> a)  -> Lambda th fun f a

deriving instance forall th fun f. Functor (Lambda th fun f)

instance HOFunctor (Lambda th fun) where
  kmap f (Lambda body   k) = Lambda (f . body) k
  kmap _ (Vari x        k) = Vari x k
  kmap f (Apply fun arg k) = Apply fun (f arg) k

newtype Fun m b a = Fun { fun :: b -> m a }

instance Pointed (StateT s Id) where 
  eta x = StateT (\s -> Id (x,s))

-- handler call-by-name

hCBN  :: T (Lambda Id (Fun (StateT s Id)) !+! KAlg (StateF s)) a 
      -> s -> (a,s)
hCBN  = fmap unId . runStateT . fold eta (algCBN !#! algSt')

algCBN :: Monad m => Lambda Id (Fun m) m (m a) -> m a
algCBN (Lambda body k)  = k (Fun body)
algCBN (Vari x k)       = k (unId x)
algCBN (Apply f x k)    = do v <- x; fun f (Id v) >>= k 

-- handler call-by-value

hCBV  :: T (Lambda (StateT s Id) (Fun (StateT s Id)) !+! KAlg (StateF s)) a 
      -> s -> (a,s)
hCBV  = fmap unId . runStateT . fold eta (algCBV !#! algSt')

algCBV :: Monad m => Lambda m (Fun m) m (m a) -> m a 
algCBV (Lambda body k)  = k (Fun body)
algCBV (Vari x k)       = x >>= k
algCBV (Apply f x k)    = fun f x >>= k

-- example

lambda :: HOFunctor k => (c t1 -> T (Lambda c fun !+! k) t2) -> T (Lambda c fun !+! k) (fun (c t1) t2)
lambda body = OpT (In (Lambda body return))

apply :: HOFunctor k => (fun (c t1) t2) -> T (Lambda c fun !+! k) t1 -> T (Lambda c fun !+! k) t2
apply fun arg = OpT (In (Apply fun arg return))

put' :: s -> T (Lambda c fun !+! KAlg (StateF s)) ()
put' s = OpT (Out (Op_ (Put s (return ()))))

exCBN :: ((), Int)
exCBN = hCBN (do put' 1; f <- lambda (\_ -> return ()); apply f (put' 3)) 0
-- ((),3)

exCBV :: ((), Int)
exCBV = hCBV (do put' 1; f <- lambda (\_ -> return ()); apply f (put' 3)) 0
-- ((),1)
