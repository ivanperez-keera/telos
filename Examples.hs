{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- module Examples where

-- External imports
import Data.List       (isSubsequenceOf)
import qualified Data.List as List
import GHC.Exts            (IsList(..))
import GHC.Generics
import Type.Reflection
import Prelude hiding (fail)

import Text.Pretty.Simple

import qualified Test.QuickCheck as QC
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen (Gen, generate, sample')
import Test.QuickCheck.Modifiers (getNonNegative)

-- Internal imports
import Logic

-- ** Natural numbers

-- ** Natural numbers as an extensible type
data NatF f = Zero | Suc (f (NatF f))
  deriving Generic

instance Num (NatF Term) where
  fromInteger 0 = Zero
  fromInteger n
    | n < 0 = error "Cannot convert below zero"
    | otherwise = Suc (C (fromInteger (n - 1)))

-- ** Logic programming extension of natural numbers

type NatTerm = Term (NatF Term)

instance Show (NatF Term) where
  show x = show' 0 x
    where
      show' :: Int -> NatF Term -> String
      show' x Zero                 = show x
      show' x (Suc c@(Var y))      = show (x + 1) ++ " + " ++ show c
      show' x (Suc c@(Compound y)) = show' (x + 1) y

deriving instance Eq (NatF Term)
instance UnifyLocal  (NatF Term)
instance Occurs      (NatF Term)
instance Substitute  (NatF Term)
instance Logic       (NatF Term)

instance IsGround (NatF Term) where
  isGround Zero    = succeed
  isGround (Suc v) = isGround v

  isAlreadyGround Zero    = succeed
  isAlreadyGround (Suc v) = isAlreadyGround v

  ground = go
    where
      go = Zero : map (Suc . C) go

  type Base (NatF Term) = Int

  promote Zero = Just 0
  promote (Suc v) = do
    v' <- promote v
    return $ 1 + v'

  demote 0 = Zero
  demote n = Suc (Compound (demote (n-1)))

isZero :: NatTerm -> Goal
isZero p = p =:= C Zero

isNotZero :: NatTerm -> Goal
isNotZero p = exists $ \v ->
  p =:= C (Suc v)


-- | True if the first variable is lower than the second.
--
-- This code is the same as:
--
-- @
-- lowerThan :: NatTerm -> NatTerm -> Goal
-- lowerThan p q = exists $ \v1 ->
--                 exists $ \v2 ->
--                 exists $ \v3 ->
--     (  p =:= C Zero     @@ q =:= C (Suc v3)
--     @| p =:= C (Suc v1) @@ q =:= C (Suc v2) @@ lowerThan v1 v2
--     )
-- @
--
-- but in can be shorter because the three variables have the same type.
-- lowerThan :: NatTerm -> NatTerm -> Goal
-- lowerThan p q = exist 3 $ \[v1, v2, v3] ->
--     (  p =:= C Zero     @@ q =:= C (Suc v3)
--     @| p =:= C (Suc v1) @@ q =:= C (Suc v2) @@ lowerThan v1 v2
--     )
--
lowerThan :: NatTerm -> NatTerm -> Goal
lowerThan p q = lowerThan' 500 p q

lowerThan' :: Int -> NatTerm -> NatTerm -> Goal
lowerThan' 0 p q = succeed
lowerThan' n p q =
    ( (
          p =:= C Zero @@ (exists $ \v1 -> q =:= C (Suc v1))
      )
    @|
      ( exists $ \v1 ->
        exists $ \v2 ->
          p =:= C (Suc v1) @@ q =:= C (Suc v2) @@ lowerThan' (n - 1) v1 v2
      )
    )
-- lowerThan :: NatTerm -> NatTerm -> Goal
-- lowerThan p q =
--     ( (
--           p =:= C Zero @@ (exists $ \v1 -> q =:= C (Suc v1))
--       )
--     @|
--       ( exists $ \v1 ->
--         exists $ \v2 ->
--           p =:= C (Suc v1) @@ q =:= C (Suc v2) @@ lowerThan v1 v2
--       )
--     )

between :: NatTerm -> NatTerm -> NatTerm -> Goal
between p q r = exists $ \v1 ->
                exists $ \v2 ->
                exists $ \v3 ->
     p =:= C Zero @@ isNotZero q @@ lowerThan q r
  @| p =:= C (Suc v1) @@ q =:= C (Suc v2) @@ r =:= C (Suc v3) @@ between v1 v2 v3

leq :: NatTerm -> NatTerm -> Goal
leq p q = exists $ \v1 ->
          exists $ \v2 ->

       p =:= C Zero
    @| p =:= C (Suc v1) @@ q =:= C (Suc v2) @@ leq v1 v2

-- ** People

data PersonF f = PersonF
    { name :: f String
    , age  :: f (NatF f)
    }
  deriving Generic

type VarPerson = Term (PersonF Term)

deriving instance Show (PersonF Term)
deriving instance Eq   (PersonF Term)
instance UnifyLocal    (PersonF Term)
instance Occurs        (PersonF Term)
instance Substitute    (PersonF Term)
instance Arbitrary     (PersonF Term)
instance Logic         (PersonF Term)

pattern Person x y = Compound (PersonF x y)

-- ** Lists

data ListF f a = Nil | Cons (f a) (f (ListF f a))
  deriving Generic

type ListTerm a = Term (ListF Term a)

instance Show a => Show (ListF Term a) where
  show Nil        = "[]"
  show (Cons h t) = show h ++ " : " ++ show t

deriving instance Eq a              => Eq         (ListF Term a)
instance Logic a                    => UnifyLocal (ListF Term a)
instance Occurs a                   => Occurs     (ListF Term a)
instance (Substitute a, Typeable a) => Substitute (ListF Term a)
instance (Arbitrary a) => Arbitrary (ListF Term a)
instance Logic a                    => Logic    (ListF Term a)

-- The following instances enable list overloading.
instance IsList (ListF Term a) where
  type Item (ListF Term a) = Term a
  fromList [] = Nil
  fromList (x:xs) = Cons x (fromList xs)

-- instance Foldable (ListF Term) where
--   foldr f k Nil          = k
--   foldr f k (Cons v1 v2) = f v1 (foldr f k v2)

-- We also provide the notation x :< xs to put an element to the head
-- of a list. This is useful for cases where the list has variables.

infixr 6 :<
pattern x :< xs = C (Cons x xs)

-- *** Goals

isNil :: Logic a => ListTerm a -> Goal
isNil p = p =:= C Nil

isCons :: Logic a => ListTerm a -> Goal
isCons p = exists $ \v1 -> exists $ \v2 ->
  p =:= C (Cons v1 v2)

isHead :: Logic a
       => ListTerm a -> Term a -> Goal
isHead x y = exists $ \v ->
  x =:= (y :< v)

-- | Append
append :: Logic a => ListTerm a -> ListTerm a -> ListTerm a -> Goal
append x y z = exists $ \hx ->
               exists $ \tx ->
               exists $ \tz ->

       x =:= C Nil      @@ y =:= z
    @| x =:= (hx :< tx) @@ z =:= (hx :< tz) @@ append tx y tz

type NatList = Term (ListF Term (NatF Term))

sorted :: NatList -> Goal
sorted v =  v =:= []

         @| ( exists $ \e1 ->
                v =:= [e1]
            )

         @| ( exists $ \e1 ->
              exists $ \e2 ->
              exists $ \ts ->

                 v =:= (e1 :< e2 :< ts)
              @@ lowerThan e1 e2
              @@ sorted (e2 :< ts)
            )

member :: Logic a => Term a -> ListTerm a -> Goal
member x xs =
     ( exists $ \tl ->
         xs =:= (x :< tl)
     )
  @| ( exists $ \hd ->
       exists $ \tl ->

         xs =:= (hd :< tl) @@ member x tl
     )

notMember :: Logic a => Term a -> ListTerm a -> Goal
notMember x xs =
     xs =:= []
  @| ( exists $ \hd ->
       exists $ \tl ->

         xs =:= (hd :< tl) @@ x =/= hd @@ notMember x tl
     )

isLast :: Logic a => Term a -> ListTerm a -> Goal
isLast x xs =
      xs =:= C (Cons x (C Nil))
   @|
      ( exists $ \hd ->
        exists $ \tl ->
             xs =:= (hd :< tl)
          @@ isLast x tl
      )

-- | Remove exactly one occurrence of x from the list.
--
-- Requires that the member be in the list at least once.
delete :: Logic a => Term a -> ListTerm a -> ListTerm a -> Goal
delete x ys zs =
     ( ys =:= C (Cons x zs) )
  @| ( exists $ \y ->
       exists $ \tl ->
       exists $ \tl1 ->
          ys =:= C (Cons y tl)
       @@ zs =:= C (Cons y tl1)
       @@ delete x tl tl1
     )

sublist :: Logic a => ListTerm a -> ListTerm a -> Goal
sublist s l =
  exists $ \l1 ->
  exists $ \l2 ->
  exists $ \l3 ->

     append l1 l2 l
  @@ append s  l3 l2

insert :: Logic a => Term a -> ListTerm a -> ListTerm a -> Goal
insert x ys zs = delete x zs ys

-- | This is not very efficient and ends up in an infinite loop very easily.
permutation :: Logic a => ListTerm a -> ListTerm a -> Goal
permutation xs ys =
     ( xs =:= C Nil @@ ys =:= C Nil )
  @| ( exists $ \x ->
       exists $ \l ->

       xs =:= C (Cons x l)

       @@ (exists $ \l1 ->
           exists $ \p  ->

                insert x l1 p
             @@ permutation l l1
          )
     )


sort :: NatList -> NatList -> Goal
sort xs ys =
  permutation xs ys @@ sorted ys

evenLength :: Logic a => ListTerm a -> Goal
evenLength x =
     x =:= C Nil

  @| ( exists $ \x1 ->
       exists $ \x2 ->
       exists $ \tl ->

          x =:= (x1 :< x2 :< tl)
       @@ evenLength tl
     )

oddLength :: Logic a => ListTerm a -> Goal
oddLength x =
  exists $ \x1 ->
  exists $ \tl ->
      x =:= (x1 :< tl)
   @@ evenLength tl

isLength :: Logic a => NatTerm -> ListTerm a -> Goal
isLength x ys =
     x =:= C Zero @@ ys =:= C Nil
  @| (  exists $ \y ->
        exists $ \ys' ->
        exists $ \x' ->

           x =:= C (Suc x')
        @@ ys =:= (y :< ys')
        @@ isLength x' ys'
      )

forAll :: Logic a => (Term a -> Goal) -> ListTerm a -> Goal
forAll p xs =
     xs =:= C Nil
  @| ( exists $ \hd ->
       exists $ \tl ->
          xs =:= (hd :< tl)
       @@ p hd
       @@ forAll p tl
     )

reverseL :: Logic a => ListTerm a -> ListTerm a -> Goal
reverseL list reversed = scope $
     isNil list @@ isNil reversed @! succeed
  @| (exists $ \head ->
      exists $ \tail ->
      exists $ \revTail ->

      list =:= (head :< tail) @@ reverseL tail revTail @@ append revTail [head] reversed
     )

-- ** Sample queries

-- *** Natural numbers

isThree :: NatTerm -> Goal
isThree g = g =:= three

three = Compound (Suc (Compound (Suc (Compound (Suc (Compound Zero))))))
four = Compound (Suc three)

evenP :: NatTerm -> Goal
evenP x =
     x =:= C Zero

  @| ( exists $ \x1 ->
          (x =:= C (Suc (C (Suc x1))) @@ evenP x1)
     )

-- | Any number X such that Z is 3.
--
-- Prolog: isThree(X).
exampleAnyIs3 :: IO ()
exampleAnyIs3 = repl $ isThree "z"

-- | Any number Z such that Z + 2 is 3.
--
-- Prolog: X is Z + 2, isThree(X).
exampleAnyPlus2Is3 :: IO ()
exampleAnyPlus2Is3 = repl $ isThree $ plus2 "z"

plus2 :: NatTerm -> NatTerm
plus2 x = C (Suc (C (Suc x)))

plus :: NatTerm -> NatTerm -> NatTerm -> Goal
plus x y z = exists $ \v1 ->
             exists $ \v2 ->

       x =:= C Zero     @@ y =:= z
    @| x =:= C (Suc v1) @@ z =:= C (Suc v2) @@ plus v1 y v2

exampleAnyPlus123 :: IO ()
exampleAnyPlus123 = repl $
  plus 1 2 3

-- *** People

father :: VarPerson -> VarPerson -> Goal
father p h =
    p =:= miguel  @@ h =:= antonio
 @| p =:= miguel  @@ h =:= oscar
 @| p =:= antonio @@ h =:= roberto

antonio :: VarPerson
antonio = Compound (PersonF (Compound "Antonio") (Compound (Suc (Compound Zero))))

oscar :: VarPerson
oscar = Compound (PersonF (Compound "Oscar")   (Compound (Suc (Compound Zero))))

miguel :: VarPerson
miguel = Compound (PersonF (Compound "Miguel")  (Compound (Suc (Compound (Suc (Compound Zero))))))

roberto :: VarPerson
roberto = Compound (PersonF (Compound "Roberto") (Compound (Suc (Compound (Suc (Compound Zero))))))

directlyRelated :: VarPerson -> VarPerson -> Goal
directlyRelated person1 person2 =
  father person1 person2 @| father person2 person1

grandfather :: VarPerson -> VarPerson -> Goal
grandfather grandpa grandson = exists $ \dad ->
  father grandpa dad @@ father dad grandson

pair =
        ( HEQ
            ( Compound PersonF
                { name = Compound "Miguel"
                , age = Var "age_father"
                }
            , Compound PersonF
                { name = Compound "Miguel"
                , age = Compound 2
                }
            )
        )

-- Should give two results:
--
-- father(PersonF miguel Age_Father, Son).
exampleAnySonMiguel :: IO ()
exampleAnySonMiguel = repl $
  father (Person (C "Miguel") "age_father") "son"

-- Should be two:
--
-- father(PersonF miguel (Suc Y), PersonF Name Y).
exampleAnySonMiguel1 :: IO ()
exampleAnySonMiguel1 = repl $
  father
    (Compound (PersonF (Compound "Miguel") (Compound (Suc (Var "y")))))
    (Compound (PersonF (Var "name")        (Var "y")))

-- Should be empty:
--
-- father(PersonF miguel Y, PersonF Name Y).
exampleAnySonMiguel2 :: IO ()
exampleAnySonMiguel2 = eval $
  father
    (Compound (PersonF (Compound "Miguel") (Var "y")))
    (Compound (PersonF (Var "name")        (Var "y")))

-- Should be empty:
--
-- father(PersonF miguel Age, PersonF Name Age).
exampleAnySonMiguel3 :: IO ()
exampleAnySonMiguel3 = repl $
  father (Person (C "Miguel") "age") (Person "name" "age")

exampleAnyGrandsonMiguel3 :: IO ()
exampleAnyGrandsonMiguel3 = repl $
  grandfather (Person (C "Miguel") "age") (Person "name" "age2")

exampleAnyRelated :: IO ()
exampleAnyRelated = repl $
  directlyRelated antonio "person"

-- *** Lists

-- **** Head

exampleHead1 :: IO ()
exampleHead1 = eval $
  isHead sampleList (C (1 :: Int))

exampleHead2 :: IO ()
exampleHead2 = eval $
  isHead (C (Cons (V "x") (C (Cons (C 2) (C Nil))))) (C (1 :: Int))

exampleHead3 :: IO ()
exampleHead3 = eval $
  isHead sampleList (V "y")

sampleList = C (Cons (C (1 :: Int)) (C (Cons (C 2) (C Nil))))

-- **** Append

exampleAppend1 :: IO ()
exampleAppend1 = repl $
  append (C Nil) l2 (V "y")

exampleAppend2 :: IO ()
exampleAppend2 = repl $
  append (C (Cons (C 2) (C Nil))) l2 l2

exampleAppend3 :: IO ()
exampleAppend3 = eval $
  append (C (Cons (C 2) (C Nil))) l2 l3

exampleAppend4 :: IO ()
exampleAppend4 = repl $
  append l1 l2 l3

l1 = V "x"
l2 = C (Cons (C (75 :: Int)) (C (Cons (C 2) (C Nil))))
l3 = C (Cons (C 2) (C (Cons (C (75 :: Int)) (C (Cons (C 2) (C Nil))))))

-- This list demonstrates that it is possible to do list overloading.
list1 :: NatList
list1 = [75, 2]

-- This list demonstrates convenient notation to concatenate head and tail.
list2 :: NatList
list2 = 1 :< 2 :< []

-- This one spells out the list constructors
list3 :: NatList
list3 = C (Cons (C 2) (C (Cons (C 1) (C Nil))))

-- This one spells out all constructors
list4 :: NatList
list4 = Compound (Cons (Var "x") (Compound (Cons (Compound 1) (Compound Nil))))

list5 :: NatList
list5 = C (Cons (C 2) (C (Cons (C 0) (C Nil))))

-- This one shows how to combine concrete numerical values with variables
list6 :: NatList
list6 = [75, 2, "x"]

same3NotZero :: NatTerm -> NatTerm -> NatTerm -> Goal
same3NotZero x y z =
     x =:= 0 @! fail
  @| y =:= 0 @! fail
  @| x =:= y @@ y =:= z

testCut1 :: IO ()
testCut1 = repl $ goal
  where
    goal :: Goal
    goal = same3NotZero x y z @| x =:= 0

    x = 0
    y = "y"
    z = "z"

testCut2 :: IO ()
testCut2 = repl $ goal
  where
    goal :: Goal
    goal = (scope (same3NotZero x y z)) @| x =:= 0

    x = 0
    y = "y"
    z = "z"

testResults1 :: String
testResults1
  | isSolvable (append (C (Cons (C 2) (C Nil))) l2 l3)
  = "Admits solutions"
  | otherwise
  = "Does not admit solutions"

testResults2 :: IO ()
testResults2 = print $ valueOf variable goal
  where
    variable :: NatTerm
    variable = "x"

    goal :: Goal
    goal = isThree $ plus2 "x"

testResults3 :: IO ()
testResults3 = print $ findAll variable goal
  where
    variable :: NatTerm
    variable = "x"

    goal :: Goal
    goal = lowerThan "x" 5

data VertexF (f :: * -> *) = VertexAF | VertexBF | VertexCF | VertexDF | VertexEF
  deriving (Generic)

instance Show (VertexF f) where
  show VertexAF = "a"
  show VertexBF = "b"
  show VertexCF = "c"
  show VertexDF = "d"
  show VertexEF = "e"

type VertexTerm = Term (VertexF Term)

pattern VertexA = C VertexAF
pattern VertexB = C VertexBF
pattern VertexC = C VertexCF
pattern VertexD = C VertexDF
pattern VertexE = C VertexEF

deriving instance Eq (VertexF Term)
instance UnifyLocal  (VertexF Term)
instance Occurs      (VertexF Term)
instance Substitute  (VertexF Term)
instance Arbitrary (VertexF Term)
instance Logic       (VertexF Term)

type PathTerm vf = Term (ListF Term (vf Term))

path :: Logic (vf Term) => (Term (vf Term)) -> (Term (vf Term)) -> (PathTerm vf) -> Goal
path start end path =
  exists $ \revPath ->
    traverseP start end [start] revPath @@
      reverseL revPath path

traverseP :: Logic (vf Term) => (Term (vf Term)) ->  (Term (vf Term)) -> PathTerm vf -> PathTerm vf -> Goal
traverseP start end visited path =
     path =:= (end :< visited) @@ edge start end
  @| ( exists $ \next ->
         edge start next
         @@ next =/= end
         @@ notMember next visited
         @@ traverseP next end (next :< visited) path
     )

-- edge :: vf Term -> vf Term -> Goal
edge = undefined

-- VertexTerm -> VertexTerm -> Goal
-- edge :: VertexTerm -> VertexTerm -> Goal
-- edge v1 v2 =
--      v1 =:= VertexA @@ v2 =:= VertexB
--   @| v1 =:= VertexA @@ v2 =:= VertexC
--   @| v1 =:= VertexB @@ v2 =:= VertexD
--   @| v1 =:= VertexC @@ v2 =:= VertexD
--   @| v1 =:= VertexD @@ v2 =:= VertexE

data PF (f :: * -> *) = P1F | P2F | P3F | P4F | P5F | P6F
  deriving (Generic, Enum, Bounded)

instance Show (PF f) where
  show P1F = "1"
  show P2F = "2"
  show P3F = "3"
  show P4F = "4"
  show P5F = "5"
  show P6F = "6"

type PTerm = Term (PF Term)

pattern P1 = C P1F
pattern P2 = C P2F
pattern P3 = C P3F
pattern P4 = C P4F
pattern P5 = C P5F
pattern P6 = C P6F

deriving instance Eq (PF Term)
instance UnifyLocal  (PF Term)
instance Occurs      (PF Term)
instance Substitute  (PF Term)
instance Arbitrary   (PF Term)
instance Logic       (PF Term)

sudoku ex = repl $ solved ex

example :: Term (ListF Term (PF Term))
example = [ "r1c1", "r1c2", "r1c3", "r1c4"
          , "r2c1", "r2c2", "r2c3", "r2c4"
          , "r3c1", "r3c2", "r3c3", "r3c4"
          , "r4c1", "r4c2", "r4c3", "r4c4"
          ]

example2 :: [ PTerm ]
example2 = [ "r1c1", "r1c2", "r1c3", "r1c4"
          , "r2c1", "r2c2", "r2c3", "r2c4"
          , "r3c1", "r3c2", "r3c3", "r3c4"
          , "r4c1", "r4c2", "r4c3", "r4c4"
          ]

example3 :: Term (ListF Term (PF Term))
example3 = [ P1, P2, P3, P4
           , P3, P4, P1, P2
           , P4, P3, P2, P1
           , P2, P1, P4, P3
           ]

example4 :: Term (ListF Term (PF Term))
example4 = [ P1,     P2,     "r1c3", P4
           , P3,     "r2c2", P1,     "r2c4"
           , "r3c1", "r3c2", P2,     P1
           , P2,     P1,     P4,     "r4c4"
           ]

solved :: Term (ListF Term (PF Term)) -> Goal
solved ls = exist 36 $ \rs ->
  ls =:= listOf rs
  @@ allP (map isGround rs)
  @@ ( allP $ map different $
             [ row    rs n     | n  <- [0..5] ]
          ++ [ column rs n     | n  <- [0..5] ]
          ++ [ block  rs n1 n2 | n1 <- [0..1], n2 <- [0..2] ]
     )

instance IsGround (PF Term) where
  isGround _ = succeed

  ground = [minBound..maxBound]

  isAlreadyGround _ = succeed

  type Base (PF Term) = Int

  promote = Just . fromEnum

  demote = toEnum


-- allP :: [Goal] -> Goal
allP = foldr (\p1 p2 -> p1 @@ p2) succeed

allP' p = foldr (\p1 p2 -> p p1 @@ p2) succeed

anyP :: [Goal] -> Goal
anyP ps = -- Branch true foldr (\p1 p2 -> p1 @| p2) fail
  Branch (\s -> (s, true, ps))

row :: [a] -> Int -> [a]
row ls 0 = take 6 ls
row ls n = row (drop 6 ls) (n - 1)

column :: [a] -> Int -> [a]
column [] n = []
column ls n = head cs : column rs n
  where
    (r,rs) = splitAt 6 ls
    (_,cs) = splitAt n r

block :: [a] -> Int -> Int -> [a]
block xs bx by = [ xs !! p | x <- [bx*3..bx*3+1]
                           , y <- [by*2..by*2+2]
                           , let p = posOf (x, y)
                 ]

posOf :: (Int, Int) -> Int
posOf (x, y) = y * 6 + x

listOf :: [Term a] -> Term (ListF Term a)
listOf = foldr (:<) []

different :: Logic a => [Term a] -> Goal
different []     = succeed
different (x:xs) = notIn x xs @@ different xs
  where
    notIn x ys = allP $ map (x =/=) ys

test1 = v =:= C Zero @@ isAlreadyGround v
  where
    v :: NatTerm
    v = "x"

-- type NatListTerm = Term (ListF Term (NatF Term))
-- type NatListTerm = Term (ListF NatTerm)
-- type BoolListTerm = ListTerm Bool
--                   = Term (ListF Term Bool)
--
--                   | Var String
--
--                   | Compound Nil
--
--                   | Compound (Cons (Term Bool) (Term (ListF Term Bool)))

(!!!) :: Goal
(!!!) = succeed @! succeed

pred :: Goal
pred = succeed @@ (!!!) @@ succeed

-- data ListF f a = Nil | Cons (f a) (f (ListF f a))
--   deriving Generic

sudoku6 :: Term (ListF Term (PF Term))
sudoku6 =
  ["r1c1",  P5,     P6,     "r1c4", "r1c5", "r1c6"
  , "r2c1", "r2c2", "r2c3", "r2c4", "r2c5", P5
  , P6,      P4,    "r3c3", P2,     P3,     P1
  , "r4c1", "r4c2", "r4c3", "r4c4", P5,     P4
  , P5,      P6,    P2,     "r5c4", "r5c5", "r5c6"
  , "r6c1", "r6c2", P1,     P5,     "r6c5", "r6c6"
  ]

-- main = repl $ solved sudoku6

-- type NatTerm =
--
-- type ListTerm a = Term (ListF (Term (NatF Term)))
--
-- data ListF a = Nil | Cons (Term a) (Term (ListF a))

-- Compound (Variable "x")
-- Variable "x"
--
-- Term (Term a) == Term a
-- Compound x == x
--
-- lista = C Cons (C (V "x")) (C Nil)

-- Nos quedamos aquí:
--
-- Si vamos a querer dar a los usuarios una forma de generar instancias
-- automaticas como hace Barbies. Y podemos hablar con el autor para que nos
-- ayude.
--
-- Tenemos que crear un fichero prolog ejecutable para comparar.
--
-- - [X] Generador de variables libres
-- - [X] Recursion
-- - [X] Unificacion para tipos especificos con variables dentro.
-- - [X] Unificacion para cualquier tipo con variables dentro.
-- - [X] Unificacion cuando las variables pueden ser de varios tipos. Considerar
--       la opcion de que las variables en si mismas tengan el tipo (o bien
--       en su propio tipo, o en tiempo de ejecucion).
-- - [X] Unificacion para tipos parametricos con variables dentro.
-- - [X] Listas.
-- - [X] Generador de instancias automatico.
--
-- - [X] Paper?
-- - [X] Negacion.

-- - Hay un error cuando evaluamos evenP que nos da mala espina.

-- - [ ] Mejor interfaz tanto de las respuestas como de los inputs.
-- - [ ] Mas ejemplos
-- - [X] Aritmetica.
-- - [X] Grafos.
-- - [ ] Maquinas de estado.
-- - [ ] Conjuntos.

-- data Expr f = Const (f Int)
--             | Add (f (Expr f)) (f (Expr f))
--             | Neg (f (Expr f))
--
-- data Lambda f = LVar (f String)
--               | Lambda (f String) (f (Lambda f))
--               | LApp (f (Lambda f)) (f (Lambda f))
--
-- type family ExprF f x where
--   ExprF _ String = String
--   ExprF f x = f x
--
-- type Embed = Lambda (ExprF Expr)

-- genEven :: Gen Int
-- genEven = do
--   x <- arbitrary
--   guard (even x)

genSingleton' :: Gen NatList
genSingleton' =
    arbitraryP x (solve p) :: Gen NatList
  where
    x :: NatList
    x = Var "x"

    p = exists $ \x1 ->

        x =:= C (Cons x1 (C Nil))

instance MyArbitrary (Term NatTerm) => MyArbitrary (NatF Term) where
  myArbitrary Zero    = return Zero
  myArbitrary (Suc x) = Suc <$> myArbitrary x

instance Arbitrary (NatF Term) where
  arbitrary = do
    x <- arbitrary
    return $ fromInteger $ getNonNegative x

instance (Arbitrary x, MyArbitrary (Term x)) => MyArbitrary (ListF Term x) where
  myArbitrary Nil     = return Nil
  myArbitrary (Cons x1 x2) = Cons <$> myArbitrary x1 <*> myArbitrary x2

test :: IO ()
test = do
  x <- sample' (genSingleton')
  pPrint x

main =
  repl $ lowerThan 500 550

testQC v = sample' v >>= pPrint

-- Queremos demostrar que se generan menos ejemplos que se tiren, porque es más
-- eficiente.
--
-- Por ejemplo, si hay un predicado que sólo se pueda aplicar a listas
-- ordenadas, un generador aleatorio tiraría muchas listas porque no estarían
-- ordenadas.
--
-- Por ejemplo, insertSort.

-- PRE: first argument is sorted list
insertSort :: Ord a => [a] -> a -> [a]
insertSort []     y = [y]
insertSort (x:xs) y
  | y < x     = y : x : xs
  | otherwise = x : insertSort xs y

testInsertSort =
    QC.forAll arbitraryL $ \ls' ->
    QC.forAll arbitrary $ \(e :: Int) ->
      let ls :: [Int]
          ls = toListN ls'
      in    length (insertSort ls e) == length ls + 1
         && isSorted (insertSort ls e)
         && elem e ls
         && subsetOf ls (insertSort ls e)

arbitraryL :: Gen NatList
arbitraryL = arbitraryP lsV propertySorted -- (solve propertySorted)
  where
    propertySorted = sorted lsV

    lsV :: NatList
    lsV = Var "lsV"

toListN :: NatList -> [Int]
toListN (Var _) = error "Variable"
toListN (Compound Nil) = []
toListN (Compound (Cons v tl)) = toInt v : toListN tl
  where
    toInt :: NatTerm -> Int
    toInt (Var _)            = error "Variable Int"
    toInt (Compound Zero)    = 0
    toInt (Compound (Suc x)) = 1 + toInt x

isSorted :: Ord a => [a] -> Bool
isSorted ls = ls == List.sort ls

subsetOf :: Eq a => [a] -> [a] -> Bool
subsetOf = isSubsequenceOf

-- testInsertSort' =
--   forAll arbitrary $ \ls ->
--   forAll arbitrary $ \e ->
--   sorted ls ==>    length (insertSort ls e) == length ls + 1
--                 && sorted (insertSort ls e)
--                 && elem ls e
--                 && subsetOf ls (insertSort ls e)
--
-- -- Por que no hacer esto?
-- testInsertSort' =
--   forAll arbitrary $ \ls' ->
--   forAll arbitrary $ \e ->
--   let ls = sort ls'
--   in length (insertSort ls e) == length ls + 1
--        && sorted (insertSort ls e)
--        && elem ls e
--        && subsetOf ls (insertSort ls e)

-- Tienes que tener la funcion sort. A lo mejor solo tienes sorted.
-- Sort puede ser mas ineficiente.
--   Hay que compararlo con generar y filtrar?
--   Hay que compararlo con la complejidad de resolver el predicado.
-- Calidad de los datos? Van a ser buenos datos? Son lo suficientemente
--   aleatorios?
-- Este es un ejemplo didactico. Quiza podamos encontrar un ejemplo mejor.
--
-- Siguiente paso (2024-11-13): Probar testInsertSort y comprobar cuantos
-- valores se generan comparando con la forma "tradicional".
--
-- Por que teniamos que darle el solve a arbitraryP
--
-- Siguiente paso (2024-11-20)
-- Seguir el codigo es demasiado complicado y tenemos que hacer refactoring.
-- Cambiar goal a goal ya.
--
-- Cuidado con los tipos de las variables en las queries. GHCi asume ciertos
-- tipos para variables y argumentos a predicados que no siempre son correctos.
-- Hay que hacerlos explicitos.
