import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Coset.Defs
/-!
Exercise 3.3.10 `Hall Subgroup`
-- A subgroup H of a finite group G is called a Hall Subgroup of G if (|G : H|, |H|) = 1.
-- Prove that if H is a Hall subgroup of G and N is the normal subgroup of G,
-- then H ⊓ N is a Hall subgroup of N and HN ⧸ N is a Hall subgroup of G ⧸ N.
-/

variable {G : Type*} [Group G] [Fintype G] (N H : Subgroup G) [N.Normal]

/-! The definition of Hall Group-/
def IsHallSubgroup (H : Subgroup G) : Prop := Nat.Coprime H.index (Nat.card H)

theorem HallGrpwithNormalIsHall (H : Subgroup G) (hH : IsHallSubgroup H)
    (N : Subgroup G) [N.Normal] : IsHallSubgroup (H ⊓ N) := by
  sorry

def HNmodNisSubgroup (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup (G ⧸ N) :=
  (H ⊔ N).map (QuotientGroup.mk' N)

theorem CosetsOfQuotientGrpIsHall (H : Subgroup G) (hH : IsHallSubgroup H)
    (N : Subgroup G) [N.Normal] : IsHallSubgroup (HNmodNisSubgroup H N) := by
  sorry
