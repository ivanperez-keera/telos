{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstrainedClassMethods   #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}

module Logic where

-- External imports
import Control.Monad.State       hiding (fail)
import Data.List                 (intercalate)
import Data.Maybe                (catMaybes)
import Data.String
import Data.Type.Equality
import GHC.Exts                  (IsList (..))
import GHC.Generics
import Prelude                   hiding (fail)
import System.IO
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Text.Pretty.Simple
import Type.Reflection

-- * Introduce variables in any extensible type.

data Term f = Var      Var
            | Compound f
 deriving (Eq, Generic)

instance Show f => Show (Term f) where
  show (Var x)      = x
  show (Compound f) = show f

instance Num a => Num (Term a) where
  fromInteger = Compound . fromInteger

instance IsList a => IsList (Term a) where
  type Item (Term a) = Item a
  fromList = C . fromList

-- We have to manually define this.
--
-- Unification does not work by default based on the structure because it's a
-- sum type.
instance Logic a => UnifyLocal (Term a) where
  unifyLocal t1 t2 = e
     where
       e = Branch (\s -> (s, HEQ (t1, t2), [Leaf]))

instance Occurs x => Occurs (Term x) where
  occurs v (Var y)      = v == y
  occurs v (Compound x) = occurs v x

instance (Typeable u, Substitute u) => Substitute (Term u) where
  substitute x t t2@(Var y) =
    case testEquality (typeOf t) (typeOf t2) of
      Just Refl -> if x == y then t else t2
      Nothing   -> t2
  substitute x t (Compound y) = Compound $ substitute x t y

-- These patterns just make it a bit easier to write values
pattern V x = Var x
pattern C x = Compound x

-- | Allow strings to represent variables.
instance IsString (Term f) where
  fromString = Var

-- | Variable name.
type Var = String

-- * Unification

-- ** Constraints

-- | Pair of terms that must unify.
--
-- This is existentially quantified so that we can put pairs of terms of
-- different types in the same list.
data Constraint = forall t . Logic t => HEQ (Term t, Term t) -- Herbrand Equality

instance Substitute Constraint where
  substitute x t (HEQ (l, r)) = HEQ (substitute x t l, substitute x t r)

-- | Show constraints.
instance Show Constraint where
  show (HEQ (t1, t2)) = show t1 ++ " = " ++ show t2

-- | A constraint is trivial if one that is obviously satisfied (e.g., the two
-- terms are equal).
isTrivial :: Constraint -> Bool
isTrivial (HEQ (x, y)) = x == y

-- | Remove trivial constraints from a list.
removeTrivial :: [Constraint] -> [Constraint]
removeTrivial = filter (not . isTrivial)

-- | A constraint that always unifies.
true :: Constraint
true = HEQ (Compound (), Compound ())

-- | A constraint that never unifies.
false :: Constraint
false = HEQ (Compound True, Compound False)


-- ** Tree of solutions or constraints

data Tree s a = Stub | Leaf | Scope (Tree s a) | Cut (Tree s a) | Branch (s -> (s, a, [Tree s a]))
  deriving (Generic)

-- unify :: Tree Int Constraint -> UTree Constraint
--
-- data UTree a = Stub | Leaf | Branch (a, [UTree a])
--   deriving (Generic)

instance (Typeable u, Substitute u) => Substitute (Tree s u) where
  substitute x t Stub       = Stub
  substitute x t Leaf       = Leaf
  substitute x t (Cut f)    = Cut (substitute x t f)
  substitute x t (Scope f)  = Scope (substitute x t f)
  substitute x t (Branch f) = Branch $ \i ->
    let (s', a, as) = f i
    in (s', substitute x t a, map (substitute x t) as)

-- | Append a Tree at the end of another.
--
-- It won't append the trie to any stubs.
appendTree :: Tree i a -> Tree i a -> Tree i a
appendTree _ Stub       = Stub
appendTree x Leaf       = x
appendTree x (Cut f)    = Cut (appendTree x f)
appendTree x (Scope f)  = Scope (appendTree x f)
appendTree x (Branch f) = Branch $ \i -> let (v, a, ts) = f i
                                         in (v, a, map (appendTree x) ts)

fail :: Tree Int Constraint
fail = Branch (\s -> (s, false, [Leaf]))

succeed :: Tree Int Constraint
succeed = Branch (\s -> (s, true, [Leaf]))

-- | Flatten a Tree into lists of elements.
--
-- Any traversal that ends in a Stub is discarded.
--
-- The function returns Nothing at the top level if every path down the Tree
-- ends in a Stub.
pathsToLeaves :: forall i a . i -> Tree i a -> [[a]]
pathsToLeaves i t = (pathsToLeaves' 500 i t)
  where
    -- | Flatten trie with an accumulator
    pathsToLeaves' :: forall i a . Int ->  i -> Tree i a -> [[a]]
    pathsToLeaves' 0 _ _ = [[]]
    pathsToLeaves' n i Stub      = []
    pathsToLeaves' n i Leaf      = [[]]
    -- pathsToLeaves' i xs (Scope f) = (fst (pathsToLeaves' i xs f), False)
    -- pathsToLeaves' i xs (Cut f)   = (fst (pathsToLeaves' i xs f), True)
    pathsToLeaves' n i (Branch f) =
      case f i of
        (_, v, []) ->
          [[v]]

        -- TODO: Make this lazier.
        (i', v, ts) ->
          let g :: Tree i a -> [[a]]
              g x = pathsToLeaves' (n - 1) i' x

              -- -- This works but we want to clean this and use better names.
              -- myfoldr xs []             = xs
              -- myfoldr xs ((Nothing):ys) = myfoldr xs ys
              -- myfoldr xs ((Just y):ys)  = concat [ xs, y, myfoldr [] ys]

              -- u' :: [[a]] -> Maybe [[a]]
              -- u' = Just -- (\x -> if null x then Nothing else Just x)

          in -- u'
             --  $ id -- myfoldr []
             map (v:) $ concat $ map g ts

exists :: (Term a -> Tree Int Constraint) -> Tree Int Constraint
exists f = Branch $ \i -> (i+1, true, [ f (var i) ])

exist :: Int -> ([Term a] -> Tree Int Constraint) -> Tree Int Constraint
exist n f = Branch $ \i ->
  let i' = i + n
  in (i', true, [ f (map var [i..(i' - 1)])])

var :: Int -> Term a
var n = V $ "_" ++ show n

-- ** Constraint resolution

-- | Resolution algorithm
solve :: Tree Int Constraint -> Tree Int Constraint
solve = solve' 0

solve' :: Int -> Tree Int Constraint -> Tree Int Constraint
solve' c Stub = Stub
solve' c Leaf = Leaf
solve' c (Cut f) = Cut (solve' c f)
solve' c (Scope f) = Scope (solve' c f)
solve' c (Branch f) = g f c
  where
    g f c
      | (c', HEQ (t1, t2), as) <- f c
      , t1 == t2
      = let diff = c' - c
        in Branch $ \i -> (i + diff, true, map (solve' c') as) -- delete + decompose

      | (c', HEQ (Compound x, Compound y), as) <- f c
      = solve' c' $ appendTree (Branch (\i -> (i, true, as)))
                               (unifyLocal x y)

      | (c', HEQ (Compound p,  Var x), as) <- f c
      = let diff = c' - c
        in solve' c' $ Branch $ \c2 ->
             let c2' = c2 + diff
             in (c2', HEQ (Var x, Compound p), as)

      | (c', HEQ (Var x, t), as) <- f c
      , occurs x t
      = Stub

      | (c', HEQ (Var x, t), as) <- f c
      = let diff = c' - c
        in Branch (\i -> (i + diff, HEQ (Var x, t), map (solve' (i + diff)) $ map (substitute x t) as))

-- ** Local unification or value unification

-- | Class that captures individual values that can be unified.
--
-- It should be the case that, if x == y, then unifyLocal x y = Just [].
class UnifyLocal x where
  unifyLocal :: x -> x -> Tree Int Constraint

  default unifyLocal :: (Show x, UnifyLocal' (Rep x), Generic x)
                     => x -> x -> Tree Int Constraint
  unifyLocal a1 a2 = unifyLocal' (from a1) (from a2)

-- | Auxiliary class used to generate UnifyLocal instances automatically.
class UnifyLocal' f where
  unifyLocal' :: f p -> f p -> Tree Int Constraint

instance UnifyLocal' V1 where
  unifyLocal' _ _ = Leaf

instance UnifyLocal' U1 where
  unifyLocal' _ _ = Leaf

instance (Show a, UnifyLocal a) => UnifyLocal' (K1 p a) where
  unifyLocal' (K1 c1) (K1 c2) = unifyLocal c1 c2

instance UnifyLocal' a => UnifyLocal' (M1 i c a) where
  unifyLocal' (M1 v1) (M1 v2) = unifyLocal' v1 v2

instance (UnifyLocal' c1, UnifyLocal' c2) => UnifyLocal' (c1 :*: c2) where
  unifyLocal' (c1 :*: c2) (d1 :*: d2) =
    appendTree (unifyLocal' c2 d2) (unifyLocal' c1 d1)

instance (UnifyLocal' c1, UnifyLocal' c2) => UnifyLocal' (c1 :+: c2) where
  unifyLocal' (L1 x) (L1 y) = unifyLocal' x y
  unifyLocal' (R1 x) (R1 y) = unifyLocal' x y
  unifyLocal' _      _      = Stub

-- ** Occurrence of variables

-- | Capture that notion that a variable occurs in an expression.
class Occurs x where
  occurs :: Var -> x -> Bool

  default occurs :: (Occurs' (Rep x), Generic x) => Var -> x -> Bool
  occurs v a = occurs' v (from a)

-- | Auxiliary class used to generate UnifyLocal instances automatically.
class Occurs' f where
  occurs' :: Var -> f w -> Bool

instance Occurs' V1 where
  occurs' _ _ = False

instance Occurs' U1 where
  occurs' _ _ = False

instance Occurs a => Occurs' (K1 p a) where
  occurs' v (K1 c1) = occurs v c1

instance Occurs' a => Occurs' (M1 i c a) where
  occurs' v (M1 c1) = occurs' v c1

instance (Occurs' c1, Occurs' c2) => Occurs' (c1 :*: c2) where
  occurs' v (c1 :*: c2) = occurs' v c1 || occurs' v c2

instance (Occurs' c1, Occurs' c2) => Occurs' (c1 :+: c2) where
  occurs' v (L1 c) = occurs' v c
  occurs' v (R1 c) = occurs' v c

-- ** Variable substitution

class Substitute u where
  substitute :: (Show x, Typeable x) => Var -> Term x -> u -> u

  default substitute :: (Show x, Typeable x, Substitute' (Rep u), Generic u)
                     => Var -> Term x -> u -> u
  substitute v t x = to $ substitute' v t (from x)

-- | Auxiliary class used to generate UnifyLocal instances automatically.
class Substitute' f where
  substitute' :: (Show x, Typeable x) => Var -> Term x -> f u -> f u

instance Substitute' V1 where
  substitute' _ _ x = x

instance Substitute' U1 where
  substitute' _ _ x = x

instance (Substitute a) => Substitute' (K1 p a) where
  substitute' v t (K1 c1) = K1 (substitute v t c1)

instance (Substitute' a) => Substitute' (M1 i c a) where
  substitute' v t x@(M1 c1) = x { unM1 = u }
    where
      u = substitute' v t c1

instance (Substitute' c1, Substitute' c2) => Substitute' (c1 :*: c2) where
  substitute' v t (c1 :*: c2) = v1 :*: v2
    where
      v1 = substitute' v t c1
      v2 = substitute' v t c2

instance (Substitute' c1, Substitute' c2) => Substitute' (c1 :+: c2) where
  substitute' v t (L1 c) = L1 (substitute' v t c)
  substitute' v t (R1 c) = R1 (substitute' v t c)

-- ** Compatible types

-- | This class captures all constraints needed to work with types using our
-- logic programming DSL.
class (Arbitrary a, Eq a, UnifyLocal a, Substitute a, Occurs a, Show a, Typeable a) => Logic a

-- * Goal evaluation

type Goal = Tree Int Constraint

eval :: Goal -> IO ()
eval p =
  pPrint $ (fmap (resolveAll . removeTrivial)) $ pathsToLeaves 0 $ solve p

eval' p = pPrint $ pathsToLeaves 0 $ solve p

isSolvable :: Goal -> Bool
isSolvable p = not $ null $ (fmap (resolveAll . removeTrivial)) $ pathsToLeaves 0 $ solve p

valueOf :: Logic a => Term a -> Goal -> Maybe (Term a)
valueOf v p =
  case findAll v p of
    []    -> Nothing
    (x:_) -> Just x

allSolutions :: Logic a => Term a -> Goal -> [[Constraint]]
allSolutions v p =
      fmap (resolveAll . removeTrivial) $ pathsToLeaves 0 $ solve $ exists $ \v' -> v' =:= v @@ p

findAll :: Logic a => Term a -> Goal -> [Term a]
findAll v p = allVals' v solutions
  where
    solutions :: [[Constraint]]
    solutions = allSolutions v p

    -- -- | Compute all possible ground values of a variable term in a list of solutions.
    -- allVals :: Logic a => Term a -> Maybe [[Constraint]] -> [Term a]
    -- allVals v Nothing = []
    -- allVals v (Just xs) = allVals' v xs

    -- | Compute all possible ground values of a variable term in a list of solutions.
    allVals' :: Logic a => Term a -> [[Constraint]] -> [Term a]
    allVals' v = catMaybes . map (firstVal v)

    -- | Compute a possible ground value of a variable term in a list of solutions.
    firstVal :: Logic a => Term a -> [Constraint] -> Maybe (Term a)
    firstVal (C _) _                  = Nothing
    firstVal _     []                 = Nothing
    firstVal v     ((HEQ (x1, x2)):xs) =
      case testEquality (typeOf v) (typeOf x1) of
        Just Refl -> if v == x1 then Just x2 else Nothing
        Nothing   -> firstVal v xs

-- | Aid to evaluate goals and show the results.
repl :: Goal -> IO ()
repl p = do
    hSetBuffering stdin NoBuffering
    hSetEcho stdin False
    go p
  where
    go t = go' $ pathsToLeaves 0 $ solve t

    go' []     = putStrLn "false."
    go' ([x])  = putStr (printSolution x) >> putStrLn "."
    go' (x:xs) = do
      putStr $ printSolution x ++ " "
      hFlush stdout
      let key = do r <- getChar
                   case r of
                     ' '  -> putStrLn ";" >> go' (xs)
                     '\n' -> putStrLn "."
                     _    -> key
      key

    printSolution xs = printSolution' $ resolveAll $ removeTrivial xs
    printSolution' [] = "true"
    printSolution' xs = intercalate ", " $ map show xs

-- | Remove internal variables (those whose names were not picked by the user).
removeInternal :: [Constraint] -> [Constraint]
removeInternal [] = []
removeInternal (e@(HEQ (Var ('_':_), t)) : xs) = removeInternal xs
removeInternal (e : xs) = e : removeInternal xs

-- Apply any constraints to all other constraints in a list. For example, if
-- the list contains in (HEQ v t), then v is substituted with t in every
-- appearance in the rest of the list (ahead or behind).
resolveAll :: [Constraint] -> [Constraint]
-- resolveAll xs = removeInternal $ reverse $ resolve $ reverse $ resolve xs
resolveAll xs = reverse $ resolve $ reverse $ resolve xs

-- | Substitute variables with their values in all subsequent constraints.
-- That is, any constraint at a point in the list will be applied to the
-- remainder of the list.
resolve :: [Constraint] -> [Constraint]
resolve [] = []
resolve (e@(HEQ (Var x, t)) : xs) = e : resolve (map (substitute x t) xs)
resolve (e : xs) = e : resolve xs

-- *** Auxiliary notation to make writing goals a bit easier.

infixr 2 @@
(@@) x xs = appendTree xs x

infixr 1 @|
(@|) x y = Branch (\i -> (i, true, [x, y]))

(=:=) :: Logic t => Term t -> Term t -> Tree Int Constraint
(=:=) x y
  | x == y    = Leaf
  | otherwise = Branch (\i -> (i, HEQ (x, y), [Leaf]))

(=/=) :: Logic t => Term t -> Term t -> Tree Int Constraint
(=/=) x y = scope $ (x =:= y @! fail) @| succeed

infixr 2 @!
(@!) x y = x @@ (Cut y)

scope :: Tree i a -> Tree i a
scope = Scope

-- * Examples

-- ** Non-extensible types

-- *** String

instance Occurs String where
  occurs _ _ = False

instance Substitute String where
  substitute x t t2 = t2

instance UnifyLocal String where
  unifyLocal x y = if x == y then Leaf else Stub

instance Logic String where

instance Occurs () where
  occurs _ _ = False

instance Substitute () where
  substitute x t t2 = t2

instance UnifyLocal () where
  unifyLocal x y = Leaf

instance Logic ()

-- *** Bool

instance Occurs Bool where
  occurs _ _ = False

instance Substitute Bool where
  substitute x t t2 = t2

instance UnifyLocal Bool where
  unifyLocal x y = if x == y then Leaf else Stub

instance Logic Bool where

-- *** Int

instance Occurs Int where
  occurs _ _ = False

instance Substitute Int where
  substitute x t t2 = t2

instance UnifyLocal Int where
  unifyLocal x y = if x == y then Leaf else Stub

instance Logic Int where

class IsGround g where
  isGround :: g -> Goal

  isAlreadyGround :: g -> Goal

  ground :: [ g ]

  type Base g

  promote :: g -> Maybe (Base g)

  demote :: Base g -> g

instance (Logic a, IsGround a) => IsGround (Term a) where

  isGround :: (Logic a, IsGround a) => Term a -> Goal
  isGround v@(Var _)      = anyP $ map (v =:=) (ground :: [ Term a ])
    where
      anyP :: [Goal] -> Goal
      anyP ps = -- Branch true foldr (\p1 p2 -> p1 @| p2) fail
        Branch (\s -> (s, true, ps))

  isGround c@(Compound x) = isGround x

  isAlreadyGround (Var _) = fail
  isAlreadyGround (Compound x) = isAlreadyGround x

  ground = map Compound ground

  type Base (Term a) = Base a

  promote (Var _) = Nothing
  promote (Compound x) = promote x

  demote x = Compound (demote x)

isVar :: Term a -> Goal
isVar (V _) = succeed
isVar _ = fail

nonVar :: Term a -> Goal
nonVar (C _) = succeed
nonVar _ = fail

-- * Arbitrary value generation

instance Arbitrary a => Arbitrary (Term a) where
  arbitrary = Compound <$> arbitrary

-- | PRE: Goal p ya ha unificado
arbitraryP :: (MyArbitrary x, Logic x) => Term x -> Goal -> Gen (Term x)
arbitraryP t p = do
  -- We need a guarantee that the variable x doesn't have any variable inside
  -- with constraints applied to itself.

  -- We need to be careful because predicates in our language have specific
  -- order. Changing the order of branches could change the meaning.
  -- Seems important to have done unify first.
  x <- findAll' t <$> randomize p
  let xs = map myArbitrary x
  oneof xs

class MyArbitrary x where
  myArbitrary :: x -> Gen x

instance (MyArbitrary x, Arbitrary x) => MyArbitrary (Term x) where
  myArbitrary (Var _)      = Compound <$> arbitrary
  myArbitrary (Compound x) = Compound <$> myArbitrary x

-- randomize = id
-- | PRE: Goal p already unified
enumerateP :: Logic x => Term x -> Goal -> Gen (Term x)
enumerateP t p = elements $ findAll' t p

randomize :: Tree Int Constraint -> Gen (Tree Int Constraint)
randomize = randomize' 0

randomize' :: Int -> Tree Int Constraint -> Gen (Tree Int Constraint)
randomize' c Stub       = return $ Stub
randomize' c Leaf       = return $ Leaf
randomize' c (Scope t)  = Scope <$> randomize' c t
randomize' c (Cut t)    = Cut <$> randomize' c t
randomize' c (Branch f) = do
  let (c', u, as) = f c
      diff = c' - c
  as' <- shuffle as
  gs  <- mapM (randomize' c') as'
  return $ Branch (\i -> (i + diff, u, gs))

-- findAll' is a findAll sin unificacion
findAll' :: Logic a => Term a -> Goal -> [Term a]
findAll' v p = allVals' v solutions
  where
    solutions :: [[Constraint]]
    solutions =
      -- fmap (fmap (resolveAll . removeTrivial)) $ pathsToLeaves 0 $ p
      (fmap (resolveAll)) $ pathsToLeaves 0 $ p

    -- -- | Compute all possible ground values of a variable term in a list of solutions.
    -- allVals :: Logic a => Term a -> Maybe [[Constraint]] -> [Term a]
    -- allVals v Nothing = []
    -- allVals v (Just xs) = allVals' v xs

    -- | Compute all possible ground values of a variable term in a list of solutions.
    allVals' :: Logic a => Term a -> [[Constraint]] -> [Term a]
    allVals' v = catMaybes . map (firstVal v)

    -- | Compute a possible ground value of a variable term in a list of solutions.
    firstVal :: Logic a => Term a -> [Constraint] -> Maybe (Term a)
    firstVal (C _) _                  = Nothing
    firstVal _     []                 = Nothing
    firstVal v     ((HEQ (x1, x2)):xs) =
      case testEquality (typeOf v) (typeOf x1) of
        Just Refl -> if v == x1 then Just x2 else Nothing
        Nothing   -> firstVal v xs
