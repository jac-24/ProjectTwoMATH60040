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
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
Project Two.
-/

@[expose] public section

namespace defSection

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

end defSection


namespace theoremSection

variable {s : Set ℕ} {G : Type*} [Group G] (H : Subgroup G)

lemma inv_pow_is_one' {p : ℕ} {a b : G} (ha : a ∈ H) (hb : b ∈ H) : (a * b) ^ p = 1 := by
  sorry

lemma inv_pow_is_one {p : ℕ} {a : G} (ha : a ^ p = 1) : (a⁻¹) ^ p = 1 := by
  rw [inv_pow, ha, inv_one]

/-
Went through a few iterations before could stop using Set.mem_Pred... . Broke off
into helper lemmas. Do they exist already?
-/
-- H : Subgroup G means that Lean can infer G? Yes
-- CommGroup or IsMulCommutative?
-- This is just not nice in terms of definitional equality and ease of use of Mathlib lemmas
-- Commutativity to be able to swap product in (a * b) ^ p requires the whole group to be
-- commutative so isn't that easy to restrict it the subgroup case where subgroup commutative
-- but the whole group isn't
def PowSubgroup [CommGroup H] (p : ℕ) : Subgroup G where
  carrier := {x ∈ H | x ^ p = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    constructor
    · exact H.mul_mem' ha.1 hb.1
    · sorry
  inv_mem' := fun ha ↦ ⟨H.inv_mem ha.1, inv_pow_is_one ha.2⟩

lemma pow_subgr_in_subgr {x : G} [CommGroup H] (p : ℕ) (hx : x ∈ PowSubgroup H p) :
    x ∈ H := hx.1

lemma pow_subgr_pow_p {x : G} [CommGroup H] (p : ℕ) (hx : x ∈ PowSubgroup H p) :
    x ^ p = 1 := hx.2

def PowSubgroup' (H : Type*) [CommGroup H] (p : ℕ) : Subgroup H :=
  (zpowGroupHom p).ker

@[simp]
lemma in_pow_subgroup [CommGroup H] (x : G) (p : ℕ) :
    x ∈ PowSubgroup H p ↔ (x ∈ H ∧ x ^ p = 1) := by
  rfl

/-
Subgroup.comap f.toMonoidHom N is the pre-image of N under the map f.toMonoidHom.
Have to do .toMonoidHom as f is actually a bundled structure which contains the
original function, its inverse, the fact that they're inverses, and the fact that
f preserves multiplication.
-/
-- Make this an instance? Seems that's what happens in Mathlib
-- zpowGroupHom
-- Characteristic in H not G. Cannot really write this though, Subgroup.characteristic takes
-- G as the group as H : Subgroup G
lemma powsubgroup_is_char [CommGroup H] (p : ℕ) : Subgroup.Characteristic (PowSubgroup H p) := by
  apply Subgroup.characteristic_iff_map_le.2
  intro f x ⟨y, hy, hyx⟩
  simp only [SetLike.mem_coe, in_pow_subgroup] at hy ⊢
  rw [← hyx]
  sorry

/-- In a solvable group we have that any minimal normal subgroup is abelian. -/
theorem min_norm_in_solv_is_comm [Finite G] {N : Subgroup G} [N.Normal]
    [Group.IsSolvable G] (hNbot : N ≠ ⊥) (hNmin : ∀ K : Subgroup G, K ≤ N
    → (K = ⊥) ∨ (K = N)) : IsMulCommutative N := by
  refine Subgroup.commutator_self_eq_bot_iff.1 ?_
  refine (hNmin ⁅N, N⁆ (Subgroup.commutator_le_self N)).resolve_right ?_
  refine ne_of_lt <| Group.IsSolvable.commutator_lt_of_ne_bot hNbot
  -- check to see if can use dot notation

/-- In a finite group we have that any non-trivial subgroup has order greater than 1. -/
lemma non_triv_subgr_has_prime_div [Finite G] (h : H ≠ ⊥) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ Nat.card H := by
  apply Nat.ne_one_iff_exists_prime_dvd.1
  simp only [ne_eq, Subgroup.card_eq_one]
  exact h

lemma pow_subgroup_not_bot [Finite G] {p : ℕ} {N : Subgroup G} [CommGroup N]
    (hp : Nat.Prime p) (hpN : p ∣ Nat.card N) (hNbot : N ≠ ⊥) :
    PowSubgroup N p ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩ -- check
  have what : p ∣ Nat.card G := by
    sorry
  simp only [ne_eq, Subgroup.ne_bot_iff_exists_ne_one, Subtype.exists, Subgroup.mk_eq_one]
  rcases exists_prime_orderOf_dvd_card' p what with ⟨x, hx⟩
  use x
  rw [orderOf_eq_iff] at hx
  constructor
  · sorry
  · sorry
  sorry

-- There are different ways to say commutator of two subgroups and commutator of the
-- actual group
-- Need to see how to weaken solvability condition to just N being solvable
-- Can do this in reality but need to think how to do in Lean
open scoped IsMulCommutative in
theorem elementary_abelian [Finite G] {N : Subgroup G} [N.Normal]
    [Group.IsSolvable G] (hNbot : N ≠ ⊥) (hNmin : ∀ K : Subgroup G, K ≤ N
    → (K = ⊥) ∨ (K = N)) : ∃ p : ℕ, IsPGroup p N := by
  let : IsMulCommutative N := min_norm_in_solv_is_comm hNbot hNmin
  rcases non_triv_subgr_has_prime_div N hNbot with ⟨p, hpprime, hpdiv⟩
  use p
  have this10 : (PowSubgroup N p = ⊥) ∨ (PowSubgroup N p = N) := by
    apply hNmin
    intro x hx
    exact pow_subgr_in_subgr N p hx
  let : Fact p.Prime := ⟨hpprime⟩ -- Check
  have this : ∃ x : N, orderOf x = p := by
    exact exists_prime_orderOf_dvd_card' p hpdiv
  have this11 : (PowSubgroup N p ≠ ⊥) := by
    sorry
  have this12 : PowSubgroup N p = N := by
    exact this10.resolve_left this11
  intro a
  use 1
  simp
  sorry

  -- Problem is that want PowSubgroup N p = N but the types don't match.
  -- Also check instances IsMulCommutative N, and CommGroup N.

#check Subgroup.card_mul_eq_card_subgroup_mul_card_quotient

open Pointwise
lemma solvable_ext_splits {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (h : (Nat.card N).Coprime (N.index)) : ∃ K : Subgroup G, G = (N * K : Set G) ∧ Disjoint N K
    := by
  rcases (Subgroup.exists_right_complement'_of_coprime h) with ⟨K, hK⟩
  use K
  constructor
  · sorry
  · exact hK.disjoint -- dot notation makes this very nice

end theoremSection
