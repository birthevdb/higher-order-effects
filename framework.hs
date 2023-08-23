{-# LANGUAGE QuantifiedConstraints #-}

module Framework where

import Control.Monad (ap)

-- natural transformations

type f ~> g = forall a . f a -> g a

-- higher-order functors

class (forall f. Functor f => Functor (k f)) => HOFunctor (k :: (* -> *) -> (* -> *)) where
     kmap :: (Functor f, Functor f') => f ~> f' -> k f ~> k f'

-- generic free monad for higher-order effects

data T k a =  VarT a |  OpT (k (T k) (T k a))

instance HOFunctor k => Functor (T k) where
   fmap f (VarT x) = VarT (f x)
   fmap f (OpT op) = OpT (fmap (fmap f) op)

instance HOFunctor k => Applicative (T k) where
   pure = VarT
   (<*>) = ap

instance HOFunctor k => Monad (T k) where
   return          = pure
   VarT x   >>= f  = f x
   OpT ops  >>= f  = OpT (fmap (>>= f) ops)

-- pointed functors

class Functor g => Pointed g where
   eta :: a -> g a

instance HOFunctor k => Pointed (T k) where
   eta = return

-- folding over free monad

fold  :: (HOFunctor k, Pointed g)
       => (a -> g b) -> (forall x. k g (g x) -> g x) -> (T k a -> g b)
fold gen alg (VarT  x)   = gen x
fold gen alg (OpT   op)  = alg (kmap (fold2 alg) (fmap (fold gen alg) op))
 
fold2 :: (HOFunctor k, Pointed g) => (forall x . k g (g x) -> (g x)) -> T k ~> g
fold2 alg (VarT x)  = eta x
fold2 alg (OpT t)   = alg (kmap (fold2 alg) (fmap (fold2 alg) t))

-- modular composition
-- empty higher-order functor

data HEmpty (f :: * -> *) a = HEmpty

instance Functor (HEmpty f) where 
   fmap f x = HEmpty

instance HOFunctor HEmpty where 
   kmap k x = HEmpty

-- composing higher-order functors

data (k1 !+! k2) (f :: * -> *) a = In (k1 f a) | Out (k2 f a)

infixr !+!

instance (HOFunctor k1, HOFunctor k2, Functor f) => Functor ((k1 !+! k2) f) where
   fmap f (In x)  = In  (fmap f x)
   fmap f (Out y) = Out (fmap f y)

instance (HOFunctor k1, HOFunctor k2) => HOFunctor (k1 !+! k2) where
   kmap k (In x)  = In  (kmap k x)
   kmap k (Out y) = Out (kmap k y)

(!#!) :: (k1 f a -> g b) -> (k2 f a -> g b) -> (k1 !+! k2) f a -> g b
(lft !#! rht)  (In   op)  =  lft op
(lft !#! rht)  (Out  op)  =  rht op

instance Show a => Show (T HEmpty a) where
   show (VarT x) = show x

-- forwarding 

class HOFunctor k => Fwd k f where 
   fwd :: forall a . k f (f a) -> f a