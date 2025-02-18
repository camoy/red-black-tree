{-# LANGUAGE PatternSynonyms #-}

module RedBlackTree where
import Control.Monad (liftM, ap)

--
-- trees
--

data Color = Red | Black
data Tree a = E | N Color (Tree a) a (Tree a)

pattern R :: (Tree a) -> a -> (Tree a) -> Tree a
pattern R a x b = N Red a x b

pattern B :: (Tree a) -> a -> (Tree a) -> Tree a
pattern B a x b = N Black a x b

--
-- results
--

type Result a = Result' a a
data Result' a b = D a | T b

instance Functor (Result' a) where
  fmap = liftM

instance Applicative (Result' a) where
  pure  = T
  (<*>) = ap

instance Monad (Result' a) where
  (D x) >>= f = D x
  (T x) >>= f = f x

fromResult :: Result a -> a
fromResult (D x) = x
fromResult (T x) = x

(<$$>) :: (a -> b) -> Result a -> Result b
f <$$> (D x) = D (f x)
f <$$> (T x) = T (f x)

--
-- insert
--

insert :: Ord a => a -> Tree a -> Tree a
insert x s = (blacken . fromResult . ins) s
  where ins E = T (R E x E)
        ins (N k a y b)
          | x < y = balance =<< (\a -> N k a y b) <$$> ins a
          | x == y = D (N k a y b)
          | x > y = balance =<< (\b -> N k a y b) <$$> ins b

balance :: Tree a -> Result (Tree a)
balance (B (R (R a x b) y c) z d) = T (R (B a x b) y (B c z d))
balance (B (R a x (R b y c)) z d) = T (R (B a x b) y (B c z d))
balance (B a x (R (R b y c) z d)) = T (R (B a x b) y (B c z d))
balance (B a x (R b y (R c z d))) = T (R (B a x b) y (B c z d))
balance (B a x b) = D (B a x b)
balance (R a x b) = T (R a x b)

blacken :: Tree a -> Tree a
blacken (N _ a y b) = B a y b
blacken s = s

--
-- delete
--

delete :: Ord a => a -> Tree a -> Tree a
delete x s = (fromResult . del) s
  where del E = D E
        del (N k a y b)
          | x < y = eqL =<< (\a -> N k a y b) <$$> del a
          | x == y = delCur (N k a y b)
          | x > y = eqR =<< (\b -> N k a y b) <$$> del b

delCur :: Tree a -> Result (Tree a)
delCur (R a y E) = D a
delCur (B a y E) = blacken' a
delCur (N k a y b) = eqR =<< (\b -> N k a min b) <$$> b'
  where (b', min) = delMin b

delMin :: Tree a -> (Result (Tree a), a)
delMin (R E y b) = (D b, y)
delMin (B E y b) = (blacken' b, y)
delMin (N k a y b) = (eqL =<< (\a -> N k a y b) <$$> a', min)
  where (a', min) = delMin a

balance' :: Tree a -> Result (Tree a)
balance' (N k (R (R a x b) y c) z d) = D (N k (B a x b) y (B c z d))
balance' (N k (R a x (R b y c)) z d) = D (N k (B a x b) y (B c z d))
balance' (N k a x (R (R b y c) z d)) = D (N k (B a x b) y (B c z d))
balance' (N k a x (R b y (R c z d))) = D (N k (B a x b) y (B c z d))
balance' s = blacken' s

blacken' :: Tree a -> Result (Tree a)
blacken' (R a y b) = D (B a y b)
blacken' s = T s

eqL :: Tree a -> Result (Tree a)
eqL (N k a x (B b y c)) = balance' (N k a x (R b y c))
eqL (N k a x (R b y c)) = (\a -> B a y c) <$$> eqL (R a x b)

eqR :: Tree a -> Result (Tree a)
eqR (N k (B a x b) y c) = balance' (N k (R a x b) y c)
eqR (N k (R a x b) y c) = (\b -> B a x b) <$$> eqR (R b y c)
