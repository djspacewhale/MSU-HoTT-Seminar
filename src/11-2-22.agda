{-# OPTIONS --without-K --exact-split #-}

module 11-2-22 where
open import foundation 
open import 10-26-22

--Last week, we started implementing things! Defined the naturals,
--proved addition is commutative, and picked up some cool lemmas on
--the way. This week, we'll implement some more. 

--First, let's revisit addition, and prove that it's associative.
add-assoc : (x y z : ℕ) → (add x (add y z)) ＝ (add (add x y) z)
add-assoc zero y z = refl
add-assoc (suc x) y z = app suc (add-assoc x y z)

--Let's define multiplication.
mult : ℕ → ℕ → ℕ
mult zero y = zero
mult (suc x) y = add (mult x y) y

--We know when numbers are strictly less than each other now.
_le_ : ℕ → ℕ → bool
zero le zero = false
zero le suc y = true
suc x le zero = false
suc x le suc y = x le y

--Next week: We'll define strong and weak induction, and
--prove that they imply each other! What next...?