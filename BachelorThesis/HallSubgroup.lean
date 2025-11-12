--import Mathlib.Algebra.Group.Defs
--import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Index
--import Mathlib.Algebra.Quotient
--import Mathlib.GroupTheory.QuotientGroup.Defs
--import Mathlib.GroupTheory.Coset.Card
--import Mathlib.GroupTheory.Coset.Defs
import Init.Data.Nat.Lemmas
import Mathlib.Data.Fintype.Card

noncomputable section
open scoped Pointwise
/-!
Exercise 3.3.10 `Hall Subgroup`
-- A subgroup H of a finite group G is called a Hall Subgroup of G if (|G : H|, |H|) = 1.
-- Prove that if H is a Hall subgroup of G and N is the normal subgroup of G,
-- then H ⊓ N is a Hall subgroup of N and HN ⧸ N is a Hall subgroup of G ⧸ N.
-/

variable {G : Type*} [Group G] [Fintype G]

/-! The definition of Hall Group-/
abbrev IsHallSubgroup (H : Subgroup G) : Prop := Nat.Coprime H.index (Nat.card H)

/-! The definition that H ⊓ N is a subgroup of N-/
def inter_of_subHN (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup N :=
  (H ⊓ N).comap N.subtype

/-! Prove that H ⊓ N is a Hall Subgroup of N-/
theorem inter_of_hall_nor_is_Hall (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (inter_of_subHN H N).index (Nat.card (inter_of_subHN H N)) := by
  set K : Subgroup N := inter_of_subHN H N
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  have hgcd :
    Nat.gcd K.index (Nat.card K) ∣ Nat.gcd H.index (Nat.card H) := by
      sorry
  have : Nat.gcd H.index (Nat.card H) = 1 := Nat.coprime_iff_gcd_eq_one.mp hH
  have : Nat.gcd K.index (Nat.card K) = 1 := by exact Nat.dvd_one.mp (by simpa [this] using hgcd)
  exact this

/-! The definition that HN ⧸ N is a subgroup of G ⧸ N-/
def HNmodNisSubgroup (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup (G ⧸ N) :=
  (H ⊔ N).map (QuotientGroup.mk' N)

/-! Prove that HN ⧸ N is a Hall subgroup of G ⧸ N-/
theorem CosetsOfQuotientGrpIsHall (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (HNmodNisSubgroup H N).index (Nat.card ((HNmodNisSubgroup H N))) := by
  sorry
