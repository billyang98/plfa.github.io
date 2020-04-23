---
title     : "Lists: Lists and higher-order functions"
layout    : page
prev      : /Decidable/
permalink : /Lists/
next      : /Lambda/
---

```
module plfa.part1.Lists_solutions where
```

This chapter discusses the list data type.  It gives further examples
of many of the techniques we have developed so far, and provides
examples of polymorphic types and higher-order functions.

## Imports

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)
```


## Lists

Lists are defined in Agda as follows:
```
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
```
Let's unpack this definition. If `A` is a set, then `List A` is a set.
The next two lines tell us that `[]` (pronounced _nil_) is a list of
type `A` (often called the _empty_ list), and that `_∷_` (pronounced
_cons_, short for _constructor_) takes a value of type `A` and a value
of type `List A` and returns a value of type `List A`.  Operator `_∷_`
has precedence level 5 and associates to the right.

For example,
```
_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []
```
denotes the list of the first three natural numbers.  Since `_∷_`
associates to the right, the term parses as `0 ∷ (1 ∷ (2 ∷ []))`.
Here `0` is the first element of the list, called the _head_,
and `1 ∷ (2 ∷ [])` is a list of the remaining elements, called the
_tail_. A list is a strange beast: it has a head and a tail,
nothing in between, and the tail is itself another list!

As we've seen, parameterised types can be translated to
indexed types. The definition above is equivalent to the following:
```
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A
```
Each constructor takes the parameter as an implicit argument.
Thus, our example list could also be written:
```
_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))
```
where here we have provided the implicit parameters explicitly.

Including the pragma:

    {-# BUILTIN LIST List #-}

tells Agda that the type `List` corresponds to the Haskell type
list, and the constructors `[]` and `_∷_` correspond to nil and
cons respectively, allowing a more efficient representation of lists.


## List syntax

We can write lists more conveniently by introducing the following definitions:
```
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
```
This is our first use of pattern declarations.  For instance,
the third line tells us that `[ x , y , z ]` is equivalent to
`x ∷ y ∷ z ∷ []`, and permits the former to appear either in
a pattern on the left-hand side of an equation, or a term
on the right-hand side of an equation.


## Append

Our first function on lists is written `_++_` and pronounced
_append_:

```
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
```
The type `A` is an implicit argument to append, making it a _polymorphic_
function (one that can be used at many types). A list appended to the empty list
yields the list itself. A list appended to a non-empty list yields a list with
the head the same as the head of the non-empty list, and a tail the same as the
other list appended to tail of the non-empty list.

Here is an example, showing how to compute the result
of appending two lists:
```
_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎
```
Appending two lists requires time linear in the
number of elements in the first list.


## Reasoning about append

We can reason about lists in much the same way that we reason
about numbers.  Here is the proof that append is associative:
```
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
```
The proof is by induction on the first argument. The base case instantiates
to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs`,
and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated by a recursive
invocation of the proof, in this case `++-assoc xs ys zs`.

Recall that Agda supports [sections]({{ site.baseurl }}/Induction/#sections).
Applying `cong (x ∷_)` promotes the inductive hypothesis:

    (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

to the equality:

    x ∷ ((xs ++ ys) ++ zs) ≡ x ∷ (xs ++ (ys ++ zs))

which is needed in the proof.

It is also easy to show that `[]` is a left and right identity for `_++_`.
That it is a left identity is immediate from the definition:
```
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
```
That it is a right identity follows by simple induction:
```
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
```
As we will see later,
these three properties establish that `_++_` and `[]` form
a _monoid_ over lists.

## Length

Our next function finds the length of a list:
```
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)
```
Again, it takes an implicit parameter `A`.
The length of the empty list is zero.
The length of a non-empty list
is one greater than the length of the tail of the list.

Here is an example showing how to compute the length of a list:
```
_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎
```
Computing the length of a list requires time
linear in the number of elements in the list.

In the second-to-last line, we cannot write simply `length []` but
must instead write `length {ℕ} []`.  Since `[]` has no elements, Agda
has insufficient information to infer the implicit parameter.


## Reasoning about length

The length of one list appended to another is the
sum of the lengths of the lists:
```
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
```
The proof is by induction on the first argument. The base case
instantiates to `[]`, and follows by straightforward computation.  As
before, Agda cannot infer the implicit type parameter to `length`, and
it must be given explicitly.  The inductive case instantiates to
`x ∷ xs`, and follows by straightforward computation combined with the
inductive hypothesis.  As usual, the inductive hypothesis is indicated
by a recursive invocation of the proof, in this case `length-++ xs ys`,
and it is promoted by the congruence `cong suc`.


## Reverse

Using append, it is easy to formulate a function to reverse a list:
```
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]
```
The reverse of the empty list is the empty list.
The reverse of a non-empty list
is the reverse of its tail appended to a unit list
containing its head.

Here is an example showing how to reverse a list:
```
_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎
```
Reversing a list in this way takes time _quadratic_ in the length of
the list. This is because reverse ends up appending lists of lengths
`1`, `2`, up to `n - 1`, where `n` is the length of the list being
reversed, append takes time linear in the length of the first
list, and the sum of the numbers up to `n - 1` is `n * (n - 1) / 2`.
(We will validate that last fact in an exercise later in this chapter.)

#### Exercise `reverse-++-distrib` (recommended) ****HOMEWORK****

Show that the reverse of one list appended to another is the
reverse of the second appended to the reverse of the first:

    reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
```    
reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
  
reverse-++-distrib {A} [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    (reverse ys) ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong ( _++ [ x ] ) (reverse-++-distrib  xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) ( [ x ] ) ⟩
    reverse ys ++ ( reverse xs ++ [ x ] )
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎
```

#### Exercise `reverse-involutive` (recommended) ****HOMEWORK****

A function is an _involution_ if when applied twice it acts
as the identity function.  Show that reverse is an involution:

    reverse (reverse xs) ≡ xs
```
reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs

reverse-involutive {A} [] =
  begin
    reverse (reverse [])
  ≡⟨⟩
    reverse []
  ≡⟨⟩
    []
  ∎

reverse-involutive {A} (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ (reverse-++-distrib (reverse xs) ([ x ])) ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    [ x ]  ++ reverse (reverse xs)
  ≡⟨ cong ([ x ] ++_) (reverse-involutive xs)⟩
    [ x ] ++ xs
  ≡⟨⟩
    (x ∷ xs)
  ∎

```


## Faster reverse

The definition above, while easy to reason about, is less efficient than
one might expect since it takes time quadratic in the length of the list.
The idea is that we generalise reverse to take an additional argument:
```
shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)
```
The definition is by recursion on the first argument. The second argument
actually becomes _larger_, but this is not a problem because the argument
on which we recurse becomes _smaller_.

Shunt is related to reverse as follows:
```
shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎
```
The proof is by induction on the first argument.
The base case instantiates to `[]`, and follows by straightforward computation.
The inductive case instantiates to `x ∷ xs` and follows by the inductive
hypothesis and associativity of append.  When we invoke the inductive hypothesis,
the second argument actually becomes *larger*, but this is not a problem because
the argument on which we induct becomes *smaller*.

Generalising on an auxiliary argument, which becomes larger as the argument on
which we recurse or induct becomes smaller, is a common trick. It belongs in
your quiver of arrows, ready to slay the right problem.

Having defined shunt be generalisation, it is now easy to respecialise to
give a more efficient definition of reverse:
```
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []
```

Given our previous lemma, it is straightforward to show
the two definitions equivalent:
```
reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎
```

Here is an example showing fast reverse of the list `[ 0 , 1 , 2 ]`:
```
_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎
```
Now the time to reverse a list is linear in the length of the list.

## Map {#Map}

Map applies a function to every element of a list to generate a corresponding list.
Map is an example of a _higher-order function_, one which takes a function as an
argument or returns a function as a result:
```
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs
```
Map of the empty list is the empty list.
Map of a non-empty list yields a list
with head the same as the function applied to the head of the given list,
and tail the same as map of the function applied to the tail of the given list.

Here is an example showing how to use map to increment every element of a list:
```
_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎
```
Map requires time linear in the length of the list.

It is often convenient to exploit currying by applying
map to a function to yield a new function, and at a later
point applying the resulting function:
```
sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎
```

Any type that is parameterised on another type, such as lists, has a
corresponding map, which accepts a function and returns a function
from the type parameterised on the domain of the function to the type
parameterised on the range of the function. Further, a type that is
parameterised on _n_ types will have a map that is parameterised on
_n_ functions.


#### Exercise `map-compose` (practice) ****HOMEWORK****

Prove that the map of a composition is equal to the composition of two maps:

    map (g ∘ f) ≡ map g ∘ map f

The last step of the proof requires extensionality.

```
-- Your code goes here
map-compose' : ∀ { A B C : Set }  (f : (A → B) ) ( g : (B → C) ) ( xs : List A )
  → map ( g ∘ f ) xs ≡ (map g ∘ map f) xs
map-compose' f g [] =
  begin
    map ( g ∘ f ) []
  ≡⟨⟩
   (map g ∘ map f) []
  ∎

map-compose' f g (x ∷ xs) =
  begin
    map ( g ∘ f ) (x ∷ xs)
  ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong ((g ∘ f) x ∷_) (map-compose' f g xs) ⟩
    (g ∘ f) x ∷ (map g ∘ map f) xs
  ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
  ∎

map-compose : ∀ { A B C : Set }  (f : (A → B) ) ( g : (B → C) )
   → map ( g ∘ f ) ≡ (map g ∘ map f)
map-compose f g = extensionality λ{ xs → map-compose' f g xs }

```

#### Exercise `map-++-distribute` (practice) ****HOMEWORK****

Prove the following relationship between map and append:

    map f (xs ++ ys) ≡ map f xs ++ map f ys

```
-- Your code goes here
map-++-distribute : ∀ { A B : Set }  (f : (A → B) ) ( xs ys : List A )
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys =
  begin
    map f ([] ++ ys)
  ≡⟨⟩
    map f [] ++ map f ys
  ∎
map-++-distribute f (x ∷ xs) ys =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨⟩
    map f (x ∷ (xs ++ ys))
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (λ y → f x ∷ y) (map-++-distribute f xs ys)⟩
    f x ∷ map f xs ++ map f ys
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎

```

#### Exercise `map-Tree` (practice) ****HOMEWORK****

Define a type of trees with leaves of type `A` and internal
nodes of type `B`:
```
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B
```
Define a suitable map operator over trees:

    map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D

```
-- Your code goes here
map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf A) = leaf (f A)
map-Tree f g (node treel B treer) = node (map-Tree f g treel) (g B) (map-Tree f g treer)
```

## Fold {#Fold}

Fold takes an operator and a value, and uses the operator to combine
each of the elements of the list, taking the given value as the result
for the empty list:
```
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs
```
Fold of the empty list is the given value.
Fold of a non-empty list uses the operator to combine
the head of the list and the fold of the tail of the list.

Here is an example showing how to use fold to find the sum of a list:
```
_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎
```
Here we have an instance of `foldr` where `A` and `B` are both `ℕ`.
Fold requires time linear in the length of the list.

It is often convenient to exploit currying by applying
fold to an operator and a value to yield a new function,
and at a later point applying the resulting function:
```
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎
```

Just as the list type has two constructors, `[]` and `_∷_`,
so the fold function takes two arguments, `e` and `_⊗_`
(in addition to the list argument).
In general, a data type with _n_ constructors will have
a corresponding fold function that takes _n_ arguments.

As another example, observe that

    foldr _∷_ [] xs ≡ xs

Here, if `xs` is of type `List A`, then we see we have an instance of
`foldr` where `A` is `A` and `B` is `List A`.  It follows that

    xs ++ ys ≡ foldr _∷_ ys xs

Demonstrating both these equations is left as an exercise.


#### Exercise `product` (recommended) ****HOMEWORK****

Use fold to define a function to find the product of a list of numbers.
For example:

    product [ 1 , 2 , 3 , 4 ] ≡ 24

```
-- Your code goes here
product : List ℕ → ℕ
product = foldr _*_ 1

_ :  product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl
```

#### Exercise `foldr-++` (recommended) ****HOMEWORK****

Show that fold and append are related as follows:

    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

```
-- Your code goes here
foldr-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin 
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    foldr _⊗_ e (x ∷ (xs ++ ys))
  ≡⟨⟩
    x ⊗ foldr _⊗_ e (xs ++ ys)
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys)⟩
    x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
  ∎

```

#### Exercise `foldr-∷` (practice) ****HOMEWORK****

Show

    foldr _∷_ [] xs ≡ xs

Show as a consequence of `foldr-++` above that

    xs ++ ys ≡ foldr _∷_ ys xs


```
-- Your code goes here
foldr-[]∷ :  ∀ { A : Set } (xs : List A)
  → foldr _∷_ [] xs ≡ xs
foldr-[]∷ [] = refl
foldr-[]∷ (x ∷ xs) =
  begin
    foldr _∷_ [] (x ∷ xs)
  ≡⟨⟩
    x ∷ foldr _∷_ [] xs
  ≡⟨ cong (x ∷_) (foldr-[]∷ xs) ⟩
    (x ∷ xs)
  ∎

foldr-∷ : ∀ { A : Set } (xs ys : List A)
  → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷ [] ys = refl
foldr-∷ (x ∷ xs) ys =
  begin
    (x ∷ xs) ++ ys
  ≡⟨⟩
    x ∷ (xs ++ ys)
  ≡⟨ cong (x ∷_) (foldr-∷ xs ys)⟩
    x ∷ foldr _∷_ ys xs
  ≡⟨⟩
    foldr _∷_ ys (x ∷ xs)
  ∎

```

#### Exercise `map-is-foldr` (practice) ****HOMEWORK****

Show that map can be defined using fold:

    map f ≡ foldr (λ x xs → f x ∷ xs) []

The proof requires extensionality.

```
-- Your code goes here
map-is-foldr' : ∀ { A B : Set } (f : (A → B)) (ys : List A)
  → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
map-is-foldr' f [] = refl
map-is-foldr' f (y ∷ ys) =
  begin
    map f (y ∷ ys)
  ≡⟨⟩
    f y ∷ map f ys
  ≡⟨ cong (f y ∷_) (map-is-foldr' f ys) ⟩
    f y ∷ foldr (λ x xs → f x ∷ xs) [] ys
  ≡⟨⟩
    foldr (λ x xs → f x ∷ xs) [] (y ∷ ys)
  ∎

map-is-foldr : ∀ { A B : Set } (f : (A → B))
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (λ ys → map-is-foldr' f ys )
```

#### Exercise `fold-Tree` (practice) ****HOMEWORK****

Define a suitable fold function for the type of trees given earlier:

    fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C


```
-- Your code goes here
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf a) = f a
fold-Tree f g (node l b r) = g (fold-Tree f g l) (b) (fold-Tree f g r) 
```

#### Exercise `map-is-fold-Tree` (practice) ****HOMEWORK****

Demonstrate an analogue of `map-is-foldr` for the type of trees.

```
-- Your code goes here
map-is-fold-Tree' : ∀ { A B C D : Set} (f : (A → C)) (g : (B → D))
  (t : Tree A B)
  → map-Tree f g t ≡ fold-Tree (λ l → leaf (f l))
    (λ l p r → node (l) (g p) (r)) t
map-is-fold-Tree' f g (leaf a) = refl
map-is-fold-Tree' f g (node L B R) =
  begin
    map-Tree f g (node L B R)
  ≡⟨⟩
    node (map-Tree f g L) (g B) (map-Tree f g R)
  ≡⟨ cong (λ x → node x _ _) (map-is-fold-Tree' f g L)⟩
    node (fold-Tree (λ l → leaf (f l)) (λ l p r → node (l) (g p) (r)) L)
      (g B) (map-Tree f g R)
  ≡⟨ cong (λ x → node _ _ x) (map-is-fold-Tree' f g R)⟩
    node (fold-Tree (λ l → leaf (f l)) (λ l p r → node (l) (g p) (r)) L)
      (g B)
      (fold-Tree (λ l → leaf (f l)) (λ l p r → node (l) (g p) (r)) R)
  ≡⟨⟩
    fold-Tree (λ l → leaf (f l)) (λ l p r → node (l) (g p) (r)) (node L B R)
  ∎

map-is-fold-Tree : ∀ { A B C D : Set} (f : (A → C)) (g : (B → D))
  → map-Tree f g ≡ fold-Tree (λ l → leaf (f l)) (λ l p r → node (l) (g p) (r))
map-is-fold-Tree f g = extensionality (λ t → map-is-fold-Tree' f g t )
```

#### Exercise `sum-downFrom` (stretch) ****HOMEWORK****

Define a function that counts down as follows:
```
downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n
```
For example:
```
_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl
```
Prove that the sum of the numbers `(n - 1) + ⋯ + 0` is
equal to `n * (n ∸ 1) / 2`:

    sum (downFrom n) * 2 ≡ n * (n ∸ 1)
```
---- my *-distrib-+ from my Induction HW
*-distrib-+ : ∀ (m n p : ℕ) →  (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
   n * p
  ≡⟨⟩
   zero + n * p
  ≡⟨⟩
   zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
   (suc (m + n)) * p
  ≡⟨⟩
   p + ((m + n) * p)
  ≡⟨ cong (λ x -> p + x) (*-distrib-+ m n p) ⟩
   p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p))⟩
   (p + m * p) + n * p
  ≡⟨⟩
   suc m * p + n * p
  ∎

ssn-1*n : ∀ (n : ℕ)
  →  suc (suc (n ∸ 1)) * n ≡ suc n * (suc n ∸ 1)
ssn-1*n zero = refl
ssn-1*n (suc n) = refl
  
sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (foldr _+_ 0 (n ∷ downFrom n)) * 2
  ≡⟨⟩
    (n + foldr _+_ 0 (downFrom n)) * 2
  ≡⟨⟩
    (n + (sum (downFrom n))) * 2
  ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩
    n * 2 + sum (downFrom n) * 2
  ≡⟨ cong (λ x → n * 2 + x) (sum-downFrom n)⟩
    n * 2 + n * (n ∸ 1)
  ≡⟨ cong (_+ n * (n ∸ 1)) (*-comm n 2) ⟩
    2 * n + n * (n ∸ 1)
  ≡⟨ cong (2 * n +_) (*-comm n (n ∸ 1))⟩
    2 * n + (n ∸ 1) * n
  ≡⟨ sym (*-distrib-+ 2 (n ∸ 1) n) ⟩
    (2 + (n ∸ 1)) * n
  ≡⟨⟩
    suc (suc (n ∸ 1)) * n
  ≡⟨ ssn-1*n n ⟩ 
    suc n * (suc n ∸ 1)
  ∎

```


## Monoids

Typically when we use a fold the operator is associative and the
value is a left and right identity for the operator, meaning that the
operator and the value form a _monoid_.

We can define a monoid as a suitable record type:
```
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
```

As examples, sum and zero, multiplication and one, and append and the empty
list, are all examples of monoids:
```
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }
```

If `_⊗_` and `e` form a monoid, then we can re-express fold on the
same operator and an arbitrary value:
```
foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎
```

In a previous exercise we showed the following.

postulate
  foldr-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) (xs ys : List A) →
    foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs


As a consequence, using a previous exercise, we have the following:
```
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎
```

#### Exercise `foldl` (practice) ****HOMEWORK****

Define a function `foldl` which is analogous to `foldr`, but where
operations associate to the left rather than the right.  For example:

    foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
    foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

    

```
-- Your code goes here
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e []        =  e
foldl _⊗_ e (x ∷ xs)  = foldl _⊗_ (e ⊗ x) xs

ex-foldr : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (x y z : A)
  → foldr _⊗_ e [ x , y , z ]  ≡  x ⊗ (y ⊗ (z ⊗ e))
ex-foldr  _⊗_ e  x  y  z = refl

ex-foldl : ∀ {A B : Set} (_⊗_ : B → A → B) (e : B) (x y z : A)
  → foldl _⊗_ e [ x , y , z ]  ≡  ((e ⊗ x) ⊗ y) ⊗ z
ex-foldl  _⊗_ e  x  y  z = refl

```


#### Exercise `foldr-monoid-foldl` (practice)

Show that if `_⊗_` and `e` form a monoid, then `foldr _⊗_ e` and
`foldl _⊗_ e` always compute the same result.

```
-- Your code goes here
```


## All {#All}

We can also define predicates over lists. Two of the most important
are `All` and `Any`.

Predicate `All P` holds if predicate `P` is satisfied by every element of a list:
```
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
```
The type has two constructors, reusing the names of the same constructors for lists.
The first asserts that `P` holds for every element of the empty list.
The second asserts that if `P` holds of the head of a list and for every
element of the tail of a list, then `P` holds for every element of the list.
Agda uses types to disambiguate whether the constructor is building
a list or evidence that `All P` holds.

For example, `All (_≤ 2)` holds of a list where every element is less
than or equal to two.  Recall that `z≤n` proves `zero ≤ n` for any
`n`, and that if `m≤n` proves `m ≤ n` then `s≤s m≤n` proves `suc m ≤
suc n`, for any `m` and `n`:
```
_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []
```
Here `_∷_` and `[]` are the constructors of `All P` rather than of `List A`.
The three items are proofs of `0 ≤ 2`, `1 ≤ 2`, and `2 ≤ 2`, respectively.

(One might wonder whether a pattern such as `[_,_,_]` can be used to
construct values of type `All` as well as type `List`, since both use
the same constructors. Indeed it can, so long as both types are in
scope when the pattern is declared.  That's not the case here, since
`List` is defined before `[_,_,_]`, but `All` is defined later.)


## Any

Predicate `Any P` holds if predicate `P` is satisfied by some element of a list:
```
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
```
The first constructor provides evidence that the head of the list
satisfies `P`, while the second provides evidence that some element of
the tail of the list satisfies `P`.  For example, we can define list
membership as follows:
```
infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)
```
For example, zero is an element of the list `[ 0 , 1 , 0 , 2 ]`.  Indeed, we can demonstrate
this fact in two different ways, corresponding to the two different
occurrences of zero in the list, as the first element and as the third element:
```
_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))
```
Further, we can demonstrate that three is not in the list, because
any possible proof that it is in the list leads to contradiction:
```
not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))
```
The five occurrences of `()` attest to the fact that there is no
possible evidence for `3 ≡ 0`, `3 ≡ 1`, `3 ≡ 0`, `3 ≡ 2`, and
`3 ∈ []`, respectively.

## All and append

A predicate holds for every element of one list appended to another if and
only if it holds for every element of both lists:
```
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩
```

#### Exercise `Any-++-⇔` (recommended) ****HOMEWORK****

Prove a result similar to `All-++-⇔`, but with `Any` in place of `All`, and a suitable
replacement for `_×_`.  As a consequence, demonstrate an equivalence relating
`_∈_` and `_++_`.

```
-- Your code goes here
Any⊎++ : ∀ {A : Set} {P : A → Set} (xs ys : List A) (x : A) →
  (Any P xs ⊎ Any P ys) → (Any P (x ∷ xs) ⊎ Any P ys)
Any⊎++ xs ys x AnyP with AnyP
... | inj₁ px = inj₁ (there px)
... | inj₂ py = inj₂ py

Any-++-⇔-to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
Any-++-⇔-to [] ys Pys = inj₂ Pys
Any-++-⇔-to (x ∷ xs) ys AnyP with AnyP
... | here P = inj₁ (here P)
... | there P = Any⊎++ xs ys x (Any-++-⇔-to xs ys P)

Anyx→x+y : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P xs → Any P (xs ++ ys)
Anyx→x+y [] ys ()
Anyx→x+y (x ∷ xs) ys AnyP with AnyP
... | here P = here P
... | there P = there (Anyx→x+y xs ys P)

Anyy→x+y : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P ys → Any P (xs ++ ys)
Anyy→x+y [] ys AnyP = AnyP
Anyy→x+y (x₁ ∷ xs) ys AnyP = there (Anyy→x+y xs ys AnyP)


Any-++-⇔-from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  (Any P xs ⊎ Any P ys) → Any P (xs ++ ys) 
Any-++-⇔-from xs ys (inj₁ px) = Anyx→x+y xs ys px
Any-++-⇔-from xs ys (inj₂ py) = Anyy→x+y xs ys py

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = Any-++-⇔-to xs ys
    ; from = Any-++-⇔-from xs ys
    }

∈-++-⇔ : ∀ { A : Set} (x : A) (xs ys : List A)
  → (x ∈ (xs ++ ys)) ⇔ (x ∈ xs ⊎ x ∈ ys)
∈-++-⇔ x xs ys = Any-++-⇔ xs ys
```

#### Exercise `All-++-≃` (stretch)

Show that the equivalence `All-++-⇔` can be extended to an isomorphism.

```
-- Your code goes here
```

#### Exercise `¬Any⇔All¬` (recommended) ****HOMEWORK****

Show that `Any` and `All` satisfy a version of De Morgan's Law:

    (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

(Can you see why it is important that here `_∘_` is generalised
to arbitrary levels, as described in the section on
[universe polymorphism]({{ site.baseurl }}/Equality/#unipoly)?)

Do we also have the following?

    (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs

If so, prove; if not, explain why.

We cannot prove this in Agda because given that (¬_ ∘ All P) xs
we do not have any evidence for a specific x ∈ xs such that
¬P x is true, so we cannot prove  Any (¬_ ∘ P) xs

```
-- Your code goes here
¬Any⇔All¬-to : ∀ {A : Set} (P : A → Set) (xs : List A )
  → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
¬Any⇔All¬-to P [] = λ x → []
¬Any⇔All¬-to P (x ∷ xs) AnyPxs = (λ x₂ → AnyPxs ( here x₂)) ∷ (¬Any⇔All¬-to P xs (λ z → AnyPxs (there z)))

¬Any⇔All¬-from : ∀ {A : Set} (P : A → Set) (xs : List A )
  → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
¬Any⇔All¬-from P (x ∷ xs) (px ∷ AllP) AnyP with AnyP
... | here p = px p
... | there p = ¬Any⇔All¬-from P xs AllP p

¬Any⇔All¬ : ∀ {A : Set} (P : A → Set) (xs : List A )
  → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs

¬Any⇔All¬ P xs  = record
  { to = ¬Any⇔All¬-to P xs
  ; from = ¬Any⇔All¬-from P xs 
  }
```

#### Exercise `¬Any≃All¬` (stretch)

Show that the equivalence `¬Any⇔All¬` can be extended to an isomorphism.
You will need to use extensionality.

```
-- Your code goes here
```

#### Exercise `All-∀` (practice) ****HOMEWORK EC****

Show that `All P xs` is isomorphic to `∀ {x} → x ∈ xs → P x`.

```
-- You code goes here

All-∀-to : ∀ {A : Set} (P : A → Set) (xs : List A )
  → All P xs → (∀ {x} → x ∈ xs → P x)
All-∀-to P [] [] ()
All-∀-to P (x ∷ xs) (px ∷ pxs) x∈x∷xs with x∈x∷xs
... | here Px rewrite Px = px
... | there Px = All-∀-to P xs pxs Px

All-∀-from : ∀ {A : Set} (P : A → Set) (xs : List A )
  → (∀ {x} → x ∈ xs → P x) → All P xs
All-∀-from P [] _ = []
All-∀-from {A} P (x ∷ xs) px = (px (here refl)) ∷ All-∀-from P xs (λ x∈ → px (there x∈))

All-∀-from∘to : ∀ {A : Set} (P : A → Set) (xs : List A )
  → (x : All P xs) → All-∀-from P xs (All-∀-to P xs x) ≡ x
All-∀-from∘to P [] [] = refl
All-∀-from∘to P (x ∷ xs) (px ∷ pxs) rewrite All-∀-from∘to P xs pxs = refl

postulate
 qextensionality : ∀ {C : Set} {A : C → Set}
   {B : {y : C} → A y → Set}
   {f g : {y : C} → (x : A y) → B {y} x}
   → (∀ {y : C} (x : A y) → f {y} x ≡ g {y} x)
   -----------------------
   → (λ {y} → f {y}) ≡ g
All-∀-to∘from : ∀ {A : Set} {P : A → Set} (xs : List A)
 → (x∈→Px : {x : A} → x ∈ xs → P x)
 → (λ {x} → All-∀-to P xs (All-∀-from P xs x∈→Px) {x}) ≡ x∈→Px
All-∀-to∘from {A}{P} xs x∈→Px = qextensionality (G xs x∈→Px)
 where
  G : (xs : List A) (x∈→Px : {x : A} → x ∈ xs → P x)
      {y : A} (y∈ : y ∈ xs) →
      All-∀-to P xs (All-∀-from P xs x∈→Px) y∈ ≡ x∈→Px y∈
  G [] x∈xspx ()
  G (x ∷ xs) x∈→xspx = λ { (here refl) → refl
                         ; (there px) → G xs {!!}  px
                         }
 
All-∀ : ∀ {A : Set} (P : A → Set) (xs : List A )
  → All P xs ≃ (∀ {x} → x ∈ xs → P x)
All-∀ P xs = record
  { to = All-∀-to P xs
  ; from = All-∀-from P xs  
  ; from∘to = All-∀-from∘to P xs
  ; to∘from = All-∀-to∘from xs
  }

```


#### Exercise `Any-∃` (practice) ****HOMEWORK EC****

Show that `Any P xs` is isomorphic to `∃[ x ] (x ∈ xs × P x)`.

```
-- You code goes here
Any-∃-x∷xs : ∀ {A : Set} (P : A → Set) (xs : List A ) (y : A)
  →  (∃[ x ] (x ∈ xs × P x)) → (∃[ x ] (x ∈ y ∷ xs × P x))
Any-∃-x∷xs P xs y ⟨ x , ⟨ x∈ , px ⟩ ⟩ = ⟨ x  , ⟨ there x∈ , px ⟩ ⟩ 


Any-∃-to : ∀ {A : Set} (P : A → Set) (xs : List A )
  → Any P xs → (∃[ x ] (x ∈ xs × P x))
Any-∃-to P [] ()
Any-∃-to P (x ∷ xs) AnyP with AnyP
... | here Px =  ⟨ x , ⟨ here refl , Px ⟩  ⟩
... | there Pxs = Any-∃-x∷xs P xs x (Any-∃-to P xs Pxs)

Any-∃-from : ∀ {A : Set} (P : A → Set) (xs : List A )
  → (∃[ x ] (x ∈ xs × P x)) → Any P xs
Any-∃-from P [] ⟨ x , ⟨ () , px ⟩ ⟩
Any-∃-from P (y ∷ ys) ⟨ x , ⟨ x∈x∷xs , px ⟩ ⟩ with x∈x∷xs
... | here x∈ rewrite x∈ =  here px
... | there x∈ = there (Any-∃-from P ys ⟨ x , ⟨ x∈ , px ⟩ ⟩)

Any-∃-fromto : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (x : Any P xs)
  → Any-∃-from P xs (Any-∃-to P xs x) ≡ x
Any-∃-fromto P [] ()
Any-∃-fromto P (y ∷ ys) AnyP with AnyP
... | here Py = refl
... | there Pys rewrite Any-∃-fromto P ys Pys = refl 

Any-∃-tofrom : ∀ {A : Set} (P : A → Set) (xs : List A)
    → (∃x∈xsPx : ∃[ x ] (x ∈ xs × P x))
    → Any-∃-to P xs (Any-∃-from P xs ∃x∈xsPx) ≡ ∃x∈xsPx
Any-∃-tofrom P [] ()
Any-∃-tofrom P (y ∷ ys) ⟨ x , ⟨ here refl , Px ⟩ ⟩ = refl
Any-∃-tofrom P (y ∷ ys) ⟨ x , ⟨ there x∈ys , Px ⟩ ⟩ rewrite Any-∃-tofrom P ys ⟨ x , ⟨ x∈ys , Px ⟩ ⟩ = refl

Any-∃ : ∀ {A : Set} (P : A → Set) (xs : List A )
  → Any P xs ≃ (∃[ x ] (x ∈ xs × P x))
Any-∃ P xs = record
  { to = Any-∃-to P xs
  ; from = Any-∃-from P xs
  ; from∘to = Any-∃-fromto P xs
  ; to∘from = Any-∃-tofrom P xs
  }
```


## Decidability of All

If we consider a predicate as a function that yields a boolean,
it is easy to define an analogue of `All`, which returns true if
a given predicate returns true for every element of a list:
```
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p
```
The function can be written in a particularly compact style by
using the higher-order functions `map` and `foldr`.

As one would hope, if we replace booleans by decidables there is again
an analogue of `All`.  First, return to the notion of a predicate `P` as
a function of type `A → Set`, taking a value `x` of type `A` into evidence
`P x` that a property holds for `x`.  Say that a predicate `P` is _decidable_
if we have a function that for a given `x` can decide `P x`:
```
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)
```
Then if predicate `P` is decidable, it is also decidable whether every
element of a list satisfies the predicate:
```
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
```
If the list is empty, then trivially `P` holds for every element of
the list.  Otherwise, the structure of the proof is similar to that
showing that the conjunction of two decidable propositions is itself
decidable, using `_∷_` rather than `⟨_,_⟩` to combine the evidence for
the head and tail of the list.


#### Exercise `Any?` (stretch)

Just as `All` has analogues `all` and `All?` which determine whether a
predicate holds for every element of a list, so does `Any` have
analogues `any` and `Any?` which determine whether a predicate holds
for some element of a list.  Give their definitions.

```
-- Your code goes here
```


#### Exercise `split` (stretch) ****HOMEWORK EC****

The relation `merge` holds when two lists merge to give a third list.
```
data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)
```

For example,
```
_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

```

Given a decidable predicate and a list, we can split the list
into two lists that merge to give the original list, where all
elements of one list satisfy the predicate, and all elements of
the other do not satisfy the predicate.

Define the following variant of the traditional `filter` function on
lists, which given a decidable predicate and a list returns a list of
elements that satisfy the predicate and a list of elements that don't,
with their corresponding proofs.

    split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
      → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )

```
-- Your code goes here
```

## Standard Library

Definitions similar to those in this chapter can be found in the standard library:
```
import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
import Data.List.All using (All; []; _∷_)
import Data.List.Any using (Any; here; there)
import Data.List.Membership.Propositional using (_∈_)
import Data.List.Properties
  using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
  renaming (mapIsFold to map-is-foldr)
import Algebra.Structures using (IsMonoid)
import Relation.Unary using (Decidable)
import Relation.Binary using (Decidable)
```
The standard library version of `IsMonoid` differs from the
one given here, in that it is also parameterised on an equivalence relation.

Both `Relation.Unary` and `Relation.Binary` define a version of `Decidable`,
one for unary relations (as used in this chapter where `P` ranges over
unary predicates) and one for binary relations (as used earlier, where `_≤_`
ranges over a binary relation).

## Unicode

This chapter uses the following unicode:

    ∷  U+2237  PROPORTION  (\::)
    ⊗  U+2297  CIRCLED TIMES  (\otimes, \ox)
    ∈  U+2208  ELEMENT OF  (\in)
    ∉  U+2209  NOT AN ELEMENT OF  (\inn, \notin)
