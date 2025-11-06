import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Defs

noncomputable section -- on the Prop level
open scoped Classical -- using classical logic

/-!
Exercise 3.4.1 `Abelian Simple Group`
-- Prove that if G is an abelian simple group then G ≃* Zₚ for some prime p
-/
variable {G : Type*} [CommGroup G] [IsSimpleGroup G]

-- **this small lemma might be a PR to mathlib**
@[simp]
lemma finiteCyclicIffFiniteCarrier  (g : G) (hp : ¬orderOf g = 0) :
    Finite (Subgroup.zpowers g) = ((Subgroup.zpowers g) : Set G).Finite := by rfl

/-! Using g to build a finite cyclic group-/
lemma finiteOfFinOrderGenerator (g : G) (hp : ¬orderOf g = 0) : Finite (Subgroup.zpowers g) := by simp_all

/-! Finitness of an abelian simple group -/
lemma FiniteOfSimpleCyclic : (Finite G) := by
  obtain ⟨g, hg⟩ := -- G is cyclic
    (isCyclic_iff_exists_zpowers_eq_top : IsCyclic G ↔ _).mp (by infer_instance)
  by_contra hnf
  have hne : Nonempty G := ⟨(1 : G)⟩
  -- using zpowers g and Infinite G to get that orderOg g is 0
  have horder : orderOf g = 0 := by
    by_contra h0
    have hfin : Finite (Subgroup.zpowers g) := by exact finiteOfFinOrderGenerator g h0
    haveI : Finite ((⊤ : Subgroup G)) := by simpa [hg] using hfin
    -- transfer the Finiteness through surjection into G，to get contradiction
    have hfinG : Finite G :=
      Finite.of_surjective (Subtype.val : (⊤ : Subgroup G) → G)
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    exact hnf hfinG
  have H : Subgroup G := Subgroup.zpowers (g ^ 2)
  have Hnorm : H.Normal := by exact Subgroup.normal_of_comm H
  -- H ≠ ⊤
  have hneq_Top : H ≠ ⊤ := by
    intro htop
    -- show that odd elements ∈ T but not in H
    sorry
  -- H ≠ ⊥
  have hneq_bot : H ≠ ⊥ := by
    intro hbot
    have : Nat.card H = 1 := (Subgroup.eq_bot_iff_card H).mp hbot
    -- now show that Nat.card H ≠ 1, then we could have False
    -- in order to show Nat.card H ≠ 1, we show that g ^ 2 ≠ 1
    sorry
  have := IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := H) Hnorm
  rcases this <;> contradiction

/-！Main theorem : if G is an abelian simple group then G ≃* Zₚ for some prime p. -/
theorem AbelianSimpleGroupIsoOfZp : ∃ p : ℕ , (Nat.Prime p) ∧ Nonempty (Additive G ≃+ ZMod p) := by
  have hcyc : IsCyclic G := by infer_instance -- a simple abelian group is cyclic
  rcases (isCyclic_iff_exists_zpowers_eq_top.mp hcyc) with ⟨g, hg⟩ -- get the generator
  let p : ℕ := orderOf g -- get the order of g, not assuming g ≠ 0 here
  have orderG : Nat.card G = p := by exact Eq.symm (orderOf_eq_card_of_zpowers_eq_top hg)
  have FinG : Finite G := by exact FiniteOfSimpleCyclic
  -- using the mathlib theorem about prime_card
  have hp : Nat.Prime p := by rw [← orderG]; apply IsSimpleGroup.prime_card
  use p
  constructor
  · assumption
  · refine Nonempty.intro ?_
    rw [← orderG]
    have e : ZMod (Nat.card G) ≃+ Additive G := by
      simpa using zmodAddCyclicAddEquiv (G := Additive G) (by infer_instance)
    exact e.symm
