module Bracket where

import Framework
import Algebraic (KAlg(..))

import System.IO
import Control.Monad (join)
import Control.Exception (bracket)

-- monad for releasing resources

data FreeRes a where
   Open     :: a                                -> FreeRes a
   Bracket  :: FreeRes (FreeRes (), FreeRes a)  -> FreeRes a
    deriving (Functor)

-- framework
-- step 1

data KRes f a where
   Bracket_   :: f (f (), f a) -> KRes f a

instance (Functor f) => Functor (KRes f) where
   fmap f (Bracket_ res) = Bracket_ (fmap (fmap (fmap f)) res)

-- step 2

instance HOFunctor KRes where
   kmap k (Bracket_ res) = Bracket_ (k (fmap (\(r, u) -> (k r, k u)) res))

-- step 3

iso1 :: FreeRes a -> T KRes a
iso1 (Open x)       = VarT x
iso1 (Bracket res)  = OpT (Bracket_ (iso1 (fmap (\(x, y) -> (iso1 x, return (iso1 y))) res)))

iso2 :: T KRes a -> FreeRes a
iso2 (VarT x)              = Open x
iso2 (OpT (Bracket_ res))  = Bracket (iso2 (fmap (\(x, y) -> (iso2 x, iso2 (join y))) res))

-- step 4

hRes  :: (Pointed g)
      => (a -> g b) -> (forall x . KRes g (g x) -> g x) -> T KRes a -> g b
hRes  = fold

-- example: Print First Two Characters of a file

data Teletype    a  =  HGetChar   Handle    (Char -> a)
                    |  Print      String    a
                    |  ReadFile   FilePath  (String -> a)
                    |  OpenFile   FilePath  IOMode (Handle -> a)
                    |  HClose     Handle    a
    deriving (Functor)

hBracket :: T (KAlg Teletype !+! KRes) a -> IO a
hBracket = fold return (algTele !#! algRes)

algTele :: KAlg Teletype IO (IO a) -> IO a
algTele (Op_  (HGetChar h f))        = hGetChar h         >>= f 
algTele (Op_  (Print s io))          = print s            >> io 
algTele (Op_  (ReadFile fp f))       = readFile fp        >>= f 
algTele (Op_  (OpenFile fp mode f))  = openFile fp mode   >>= f 
algTele (Op_  (HClose h k))          = hClose h           >> k

algRes :: KRes IO (IO a) -> IO a
algRes (Bracket_ res) = do  (r, u) <- res; bracket (return ()) (const r) (const (join u))

instance Pointed IO where
   eta = return

-- constructors

readF :: FilePath -> T (KAlg Teletype !+! KRes) String
readF fp = OpT (In (Op_ (ReadFile fp return)))

openF :: FilePath -> IOMode -> T (KAlg Teletype !+! KRes) Handle
openF fp mode = OpT (In (Op_ (OpenFile fp mode return)))

hGetC :: Handle -> T (KAlg Teletype !+! KRes) Char
hGetC h = OpT (In (Op_ (HGetChar h return)))

prnt :: String -> T (KAlg Teletype !+! KRes) ()
prnt s = OpT (In (Op_ (Print s (return ()))))

hClos :: Handle -> T (KAlg Teletype !+! KRes) ()
hClos h = OpT (In (Op_ (HClose h (return ()))))

brckt :: T (KAlg Teletype !+! KRes) b
      -> (b -> T (KAlg Teletype !+! KRes) ())
      -> (b -> T (KAlg Teletype !+! KRes) a)
      -> T (KAlg Teletype !+! KRes) a
brckt res rel use = OpT (Out (Bracket_ $ do rs <- res; return (rel rs, return $ use rs)))


firstTwo file = brckt  (openF file ReadMode) 
                       (\h -> do hClos h; prnt "released")
                       (\h -> do x <- hGetC h; y <- hGetC h; prnt (show (x,y)))

-- < repl hBracket (readF "foo.txt" >>= prnt >> firstTwo')
-- < "H"
-- < "released"
-- < "***Exception: foo.txt hGetChar end of file"

exShort :: IO ()
exShort = hBracket $ readF "short.txt" >>= prnt >> firstTwo "short.txt"
-- "H"
-- "released"
-- *** Exception: short.txt: hGetChar: end of file

exLong :: IO ()
exLong = hBracket $ readF "long.txt" >>= prnt >> firstTwo "long.txt"
-- "HELLO, WORLD!"
-- "('H','E')"
-- "released"