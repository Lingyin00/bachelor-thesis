import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Coset.Defs
/-!
Exercise 3.3.10 `Hall Group`
-- A subgroup H of a finite group G is called a Hall Group of G if (|G : H|, |H|) = 1.
-- Prove that if H is a Hall subgroup of G and N is the normal subgroup of G,
-- then H ⊓ N is a Hall subgroup of N and HN ⧸ N is a Hall subgroup of G ⧸ N.
-/

variable {K : Type*} [Group K] [Fintype K] (N H : Subgroup K) [N.Normal]

/-! The definition of Hall Group-/
def IsHallGroup (H : Subgroup K): Prop :=
  Nat.Coprime H.index (Nat.card H)

theorem HallGrpwithNormalIsHall (H : Subgroup K) (hH : IsHallGroup H) (N : Subgroup K) [N.Normal] :
  IsHallGroup (H ⊓ N) := sorry

--example {N : Subgroup K} : Finite (K ⧸ N) := inferInstance
--example : Group (K ⧸ N) := inferInstance

def HNmodNisSubgroup (H : Subgroup K) (N : Subgroup K) [N.Normal] : Subgroup (K ⧸ N) :=
  (H ⊔ N).map (QuotientGroup.mk' N)

theorem CosetsOfQuotientGrpIsHall (H : Subgroup K) (hH : IsHallGroup H)
    (N : Subgroup K) [N.Normal]: IsHallGroup (HNmodNisSubgroup H N) :=
  by sorry
