{-# OPTIONS --without-K --exact-split #-}

module 10-26-22 where
open import foundation

--The type of natural numbers has two constructors: a number "zero", 
--and an endofunction "suc" for successor (think a + 1). 

data ℕ : UU where
    zero : ℕ
    suc : ℕ → ℕ

--We define addition of natural numbers by induction on the left argument; 
--zero + b is defined as b, and (a + 1) + b is defined as (a + b) + 1.

add : ℕ → ℕ → ℕ
add zero b = b
add (suc a) b = suc (add a b)

--We prove a couple of important heretofore undiscussed lemmas about equality. 
--Paths between points/equalities between terms are preserved by function "application",
--and "it sure would be nice if equality were symmetric and transitive!" :)
--A note on notation: curly brackets denote implicit arguments, i.e.
--arguments we can infer reasonably from other arguments (such as x, y from p).

app : {A B : UU} (f : A → B) {x y : A} (p : x ＝ y) → f x ＝ f y
app f refl = refl

symm : {A : UU} {x y : A} (p : x ＝ y) → y ＝ x
symm refl = refl

trans : {A : UU} {x y z : A} (p : x ＝ y) (q : y ＝ z) → x ＝ z
trans refl q = q

--We defined addition by induction on the left argument, and to prove commutativity of addition 
--we will need that we could have done this induction on the right argument just as well. 
--We will be able to argue this by function extensionality later, but for now:
--we prove ad-hoc that it didn't matter which order we did the induction in.

ladd-radd : (a b : ℕ) → add (suc a) b ＝ add a (suc b)
ladd-radd zero b = refl
ladd-radd (suc a) b = app suc (ladd-radd a b)

--One last lemma: that b is equal to (b + 0). 

lemma : (b : ℕ) → b ＝ add b zero
lemma zero = refl
lemma (suc b) = app suc (lemma b)

--Now let's pack the sausage with all these ingredients and prove addition is commutative.

add-comm : (a b : ℕ) → add a b ＝ add b a
add-comm zero b = lemma b
add-comm (suc a) zero = app suc (add-comm a zero)
add-comm (suc a) (suc b) = app suc (trans (symm (ladd-radd a b)) 
                                   (trans (app suc (add-comm a b)) (ladd-radd b a)))