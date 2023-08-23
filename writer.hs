module Writer where

import Control.Monad.Writer.Lazy (WriterT(..))
import Data.Set as Set hiding (fold)

import Framework
import Algebraic (KAlg(..))
import Scoped (KSc(..))

-- free monad for writer

data FreeWrite phi a where
   Ret    :: a                                      -> FreeWrite phi a
   Exec   :: FreeWrite phi (phi (FreeWrite phi a))  -> FreeWrite phi a
    deriving (Functor)

-- framework
-- step 1

data KWrite phi f a where
   Exec_   :: f (phi a) -> KWrite phi f a

instance (Functor f, Functor phi) => Functor (KWrite phi f) where
   fmap f (Exec_ x) = Exec_ (fmap (fmap f) x)

-- step 2

instance Functor phi => HOFunctor (KWrite phi) where
   kmap k (Exec_ x) = Exec_ (k x)

-- step 3

iso1 :: Functor phi => FreeWrite phi a -> T (KWrite phi) a
iso1 (Ret x)    = VarT x
iso1 (Exec ops)  = OpT (Exec_ ((iso1 . fmap (fmap iso1)) ops))

iso2 :: Functor phi => T (KWrite phi) a -> FreeWrite phi a
iso2 (VarT x)          = Ret x
iso2 (OpT (Exec_ ops))  = Exec ((iso2 . fmap (fmap iso2)) ops)

-- step 4

hProd  :: (Functor phi, Pointed g)
        => (a -> g b) -> (forall x . KWrite phi g (g x) -> g x) 
        -> T (KWrite phi) a -> g b
hProd  = fold

-- example: resetting the log

data Tell w a = Tell w a deriving (Functor)

type Listen w = ((->) w)
type Pass w = ((,) (w -> w))

instance Monoid w => Pointed ((,) w) where 
   eta = (,) mempty

hWrite  :: Monoid w
        => T (KAlg (Tell w) !+! KWrite (Listen w) !+! KWrite (Pass w)) a -> (w, a)
hWrite  = fold ((,) mempty) (algTell !#! (algListen !#! algPass))

algTell :: Monoid w => KAlg (Tell w) ((,) w) (w, a) -> (w, a)
algTell     (Op_ (Tell w k))     = (fst k <> w, snd k)

algListen :: KWrite (Listen w) ((,) w) (w, a) -> (w, a)
algListen  (Exec_ (w, f))       = f w

algPass :: KWrite (Pass w) ((,) w) (w, a) -> (w, a)
algPass    (Exec_ (w, (f, x)))  = (f w, snd x)

-- constructors

tell   :: HOFunctor k => w -> T (KAlg (Tell w) !+! k) ()
tell w = OpT $ In $ Op_ $ Tell w (return ())

reset  :: Monoid w
        => T (KAlg (Tell w) !+! (KWrite (Listen w) !+! (KWrite (Pass w)))) ()
reset  = OpT (Out (Out (Exec_ (fmap (\(x, f) -> (f, return x)) ((return ((), const mempty)))))))

exReset   :: (String, ())
exReset    = hWrite (tell "post" >> reset >> tell "pre")
-- ("post",())

-- same example, modularly

instance (Monoid w, Monad m) => Pointed (WriterT w m) where
  eta  = WriterT . return . (, mempty)

hWrite'  :: (HOFunctor k, Monoid w, Fwd k (WriterT w (T k)))
        => T (KAlg (Tell w) !+! (KWrite (Listen w) !+! (KWrite (Pass w) !+! k))) a -> T k (a, w)
hWrite' = runWriterT . fold eta (algTell' !#! (algListen' !#! (algPass' !#! fwd)))

algTell' :: (HOFunctor k, Monoid w) => KAlg (Tell w) (WriterT w (T k)) (WriterT w (T k) a) -> WriterT w (T k) a
algTell' (Op_ (Tell w k)) = WriterT $ do (x, w') <- runWriterT k; return (x, w <> w')

algListen' :: HOFunctor k => KWrite (Listen w) (WriterT w (T k)) (WriterT w (T k) a) -> WriterT w (T k) a
algListen' (Exec_ op) = WriterT (runWriterT op >>= \(f, w) -> runWriterT (f w))

algPass' :: HOFunctor k => KWrite (Pass w) (WriterT w (T k)) (WriterT w (T k) a) -> WriterT w (T k) a
algPass' (Exec_ op) = WriterT (runWriterT op >>= \((f, mx), _) -> do (x, w) <- runWriterT mx; return (x, f w))

listen'   :: HOFunctor k => T (KAlg (Tell w) !+! (KWrite (Listen w) !+! k)) a
         -> T (KAlg (Tell w) !+! (KWrite (Listen w) !+! k)) (a, w)
listen' k = OpT $ Out $ In $ Exec_ $ fmap (\x -> (\w -> return (x, w))) k

pass'   :: HOFunctor k => T (KAlg (Tell w) !+! (KWrite (Listen w) !+! (KWrite (Pass w) !+! k))) (a, w -> w)
       -> T (KAlg (Tell w) !+! (KWrite (Listen w) !+! (KWrite (Pass w) !+! k))) a
pass' k = OpT $ Out $ Out $ In $ Exec_ $ fmap (\(x, f) -> (f, return x)) k

reset'  :: (HOFunctor k, Monoid w)
       => T (KAlg (Tell w) !+! (KWrite (Listen w) !+! (KWrite (Pass w) !+! k))) ()
reset'  = pass' (return ((), const mempty))

exReset'   :: T HEmpty ((), String)
exReset'    = hWrite' (tell "post" >> reset' >> tell "pre")
-- ((),"post")

-- two ways of modifying the log with censor

-- in terms of pass

pass :: T (KAlg (Tell w) !+! (KWrite (Listen w) !+! KWrite (Pass w))) (a, w -> w)
        -> T (KAlg (Tell w) !+! (KWrite (Listen w) !+! KWrite (Pass w))) a
pass k = OpT $ Out $ Out $ Exec_ $ fmap (\(x, f) -> (f, return x)) k

censor :: (w -> w) -> T (KAlg (Tell w) !+! KWrite (Listen w) !+! KWrite (Pass w)) a
       -> T (KAlg (Tell w) !+! KWrite (Listen w) !+! KWrite (Pass w)) a
censor f k = pass $ do x <- k; return (x, f)

exCensor1 :: (String, ())
exCensor1 = hWrite (tell "post" >> censor (const mempty) (return ()) >> tell "pre")
-- ("post",())

-- as a scoped effect

data Censor w a = Censor (w -> w) a deriving (Functor)

hCensor  :: (Monoid w)
         => T (KAlg (Tell w) !+! (KSc (Censor w) !+! (KWrite (Listen w) !+! KWrite (Pass w)))) a -> (w, a)
hCensor  = fold eta (algTell !#! (algCensor !#! (algListen !#! algPass))) where

algCensor :: KSc (Censor w) ((,) w) (w, a) -> (w, a)
algCensor (Enter_ (Censor f (_, (w, x)))) = (f w, x)

-- helper functions

data Term = Var' String | Lam String Term | App Term Term
type FV = Set String

freeVars1 :: Term -> T (KAlg (Tell FV) !+! KSc (Censor FV) !+! KWrite (Listen FV) !+! KWrite (Pass FV)) ()
freeVars1 (Var' x)  = tell $ Set.singleton x
freeVars1 (App f e) = freeVars1 f >> freeVars1 e
freeVars1 (Lam x e) = censors (Set.delete x) (freeVars1 e)

freeVars2 :: Term -> T (KAlg (Tell FV) !+! KWrite (Listen FV) !+! KWrite (Pass FV)) ()
freeVars2 (Var' x)  = tell $ Set.singleton x
freeVars2 (App f e) = freeVars2 f >> freeVars2 e
freeVars2 (Lam x e) = censor (Set.delete x) (freeVars2 e)

censors :: (w -> w)
        -> T (KAlg (Tell w) !+! KSc (Censor w) !+! KWrite (Listen w) !+! KWrite (Pass w)) a
        -> T (KAlg (Tell w) !+! KSc (Censor w) !+! KWrite (Listen w) !+! KWrite (Pass w)) a
censors f k = OpT $ Out $ In $ Enter_ $ Censor f (return k)

term = Lam "x" (App (Var' "y") (Var' "x"))

exCensor2 :: (FV, ())
exCensor2 = hCensor (freeVars1 term)
-- (fromList ["y"],())

exCensor3 :: (FV, ())
exCensor3 = hWrite (freeVars2 term)
-- (fromList ["y"],())


