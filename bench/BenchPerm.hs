{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedLists    #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}

-- module BenchPerm where

-- External imports
import GHC.Exts            (IsList(..))
import GHC.Generics
import Type.Reflection
import Prelude hiding (fail)
import Test.QuickCheck (Arbitrary)

-- Internal imports
import Logic

main  =
  repl $ permutation l1 l2
  -- repl $     (permutation l1 l2 @@ fail)
  --         @| succeed

  where
    l1 :: ListTerm Int
    l1 = [1,2,3,4,5,6,7,8,9,10,11]
    -- l1 = [1,2,3,4,5,6,7]
    -- l1 = [1,2,3]

    l2 :: ListTerm Int
    l2 = "l"

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
instance Logic a                    => Logic    (ListF Term a)
instance Arbitrary (ListF Term a)

-- The following instances enable list overloading.
instance IsList (ListF Term a) where
  type Item (ListF Term a) = Term a
  fromList [] = Nil
  fromList (x:xs) = Cons x (fromList xs)

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

-- type NatList = Term (ListF Term (NatF Term))
--
-- sorted :: NatList -> Goal
-- sorted v =  v =:= []
--
--          @| ( exists $ \e1 ->
--                 v =:= [e1]
--             )
--
--          @| ( exists $ \e1 ->
--               exists $ \e2 ->
--               exists $ \ts ->
--
--                  v =:= (e1 :< e2 :< ts)
--               @@ lowerThan e1 e2
--               @@ sorted (e2 :< ts)
--             )

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
insert x ys zs =
      zs =:= C (Cons x ys)

   @| ( exists $ \h ->
        exists $ \t ->
        exists $ \l ->

           ys =:= C (Cons h t)
        @@ zs =:= C (Cons h l)
        @@ insert x t l
      )

-- | This is not very efficient and ends up in an infinite loop very easily.
permutation :: Logic a => ListTerm a -> ListTerm a -> Goal
permutation xs ys =
     ( xs =:= C Nil @@ ys =:= C Nil )
  @| ( exists $ \x ->
       exists $ \t ->
       exists $ \l1 ->

          xs =:= C (Cons x t)
       @@ permutation t l1
       @@ insert x l1 ys
     )

-- main :-
--   permutation([1,2,3,4,5,6,7,8,9,10,11],_),
--   fail.
-- main :-
--   writeln('end').
--
-- permutation([],[]).
-- permutation([H|T],P) :-
--   permutation(T,TP),
--   insert(H,TP,P).
--
-- insert(X,L,[X|L]).
-- insert(X,[H|T],[H|L]) :-
--   insert(X,T,L).


-- sort :: NatList -> NatList -> Goal
-- sort xs ys =
--   permutation xs ys @@ sorted ys

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

-- isLength :: Logic a => NatTerm -> ListTerm a -> Goal
-- isLength x ys =
--      x =:= C Zero @@ ys =:= C Nil
--   @| (  exists $ \y ->
--         exists $ \ys' ->
--         exists $ \x' ->
--
--            x =:= C (Suc x')
--         @@ ys =:= (y :< ys')
--         @@ isLength x' ys'
--       )

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
list1 :: ListTerm Int
list1 = [75, 2]

-- This list demonstrates convenient notation to concatenate head and tail.
list2 :: ListTerm Int
list2 = 1 :< 2 :< []

-- This one spells out the list constructors
list3 :: ListTerm Int
list3 = C (Cons (C 2) (C (Cons (C 1) (C Nil))))

-- This one spells out all constructors
list4 :: ListTerm Int
list4 = Compound (Cons (Var "x") (Compound (Cons (Compound 1) (Compound Nil))))

list5 :: ListTerm Int
list5 = C (Cons (C 2) (C (Cons (C 0) (C Nil))))

-- This one shows how to combine concrete numerical values with variables
list6 :: ListTerm Int
list6 = [75, 2, "x"]

