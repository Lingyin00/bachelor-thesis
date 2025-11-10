--import Mathlib.Algebra.Group.Defs
--import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Index
--import Mathlib.Algebra.Quotient
--import Mathlib.GroupTheory.QuotientGroup.Defs
--import Mathlib.GroupTheory.Coset.Card
--import Mathlib.GroupTheory.Coset.Defs
import Init.Data.Nat.Lemmas

/-!
Exercise 3.3.10 `Hall Subgroup`
-- A subgroup H of a finite group G is called a Hall Subgroup of G if (|G : H|, |H|) = 1.
-- Prove that if H is a Hall subgroup of G and N is the normal subgroup of G,
-- then H ⊓ N is a Hall subgroup of N and HN ⧸ N is a Hall subgroup of G ⧸ N.
-/
#check Subgroup.index_eq_card
#check Subgroup.card_mul_index

variable {G : Type*} [Group G] [Fintype G]
/-! The definition of Hall Group-/
abbrev IsHallSubgroup (H : Subgroup G) : Prop := Nat.Coprime H.index (Nat.card H)
--noncomputable def n (H : Subgroup G) : ℕ := H.index

/-！Prove that H ⊓ N is a Hall subgroup of N-/
theorem HallGrpwithNormalIsHall (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] : Nat.Coprime (H ⊓ N).index (Nat.card (H ⊓ N : Subgroup G)) := by
  have hH : (Nat.card H : ℕ) ∣  Nat.card G := by exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨n, hn⟩ := hH
  have : H.index = n := by sorry
  have hpn: n.Coprime (Nat.card ↥H) := by simpa [this] using hH
  -- clue: focusing the divisibility and prime translation in equations
  sorry

/-! The definition that HN ⧸ N is a subgroup of G ⧸ N-/
def HNmodNisSubgroup (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup (G ⧸ N) :=
  (H ⊔ N).map (QuotientGroup.mk' N)

/-! Prove that HN ⧸ N is a Hall subgroup of G ⧸ N-/
theorem CosetsOfQuotientGrpIsHall (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (HNmodNisSubgroup H N).index (Nat.card ((HNmodNisSubgroup H N))) := by
  sorry
