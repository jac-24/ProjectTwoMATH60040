/-
Copyright (c) 2026 Jibreel Chaudhry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jibreel Chaudhry
-/

module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index

/-!
Project Two.
-/

@[expose] public section

variable {s : Set ℕ} (G : Type*) [Group G] [Finite G]

def IsPiNumber (s : Set ℕ) (n : ℕ) : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → p ∣ n → p ∈ s

def IsPiPrimeNumber (s : Set ℕ) (n : ℕ) : Prop :=
  sorry

-- See whether we get Finite H immediately
def IsPiSubgroup (s : Set ℕ) (H : Subgroup G) : Prop :=
  IsPiNumber s (Nat.card H)

example (H : Subgroup G) : Finite H := by
  exact Subgroup.instFiniteSubtypeMem H

-- Subgroup actually has carrier set but the toSubgroup coerces it to a subgroup
structure PiSubgroup (s : Set ℕ) extends Subgroup G where
  is_pi_num : IsPiNumber s (Nat.card toSubgroup)

structure HallSubgroup extends Subgroup G where
  coprime_index : Nat.Coprime (Nat.card toSubgroup) (toSubgroup.index)

structure HallPiSubgroup (s : Set ℕ) extends PiSubgroup G s, HallSubgroup G

#check Nat.primeFactors

/-- If `m n : ℕ` are π-numbers then so is `m * n`. -/
lemma pi_num_clos_mul {m n : ℕ} (hm : IsPiNumber s m) (hn : IsPiNumber s n) :
    IsPiNumber s (m * n) := by
  intro p hp hmn
  rcases (Nat.Prime.dvd_or_dvd hp hmn) with hpm | hpn
  · exact hm hp hpm
  · exact hn hp hpn

/-- `1 : ℕ` is a π-number for any non-empty set of primes `s`. -/
lemma one_is_pi_num : IsPiNumber s 1 := by
  intro p hp hp_one
  by_contra hs
  exact Nat.Prime.not_dvd_one hp hp_one

-- In definition of π-number have ∀ {p : ℕ} so don't include p in the fun here
lemma div_pi_num_is_pi_num {m n : ℕ} (hn : IsPiNumber s n) (hmn : m ∣ n) :
    IsPiNumber s m :=
  fun hp hpm ↦ hn hp (dvd_trans hpm hmn)
