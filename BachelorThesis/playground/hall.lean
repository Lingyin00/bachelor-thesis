import Mathlib.GroupTheory.Index
/- `Summary`:
  1. this proof is done on paper by:
    firstly showing the connection of |HN| and |H|, |N|
  2. see the conncetion to the second Isomphorphic theorem
  3. transfer the co-prime property
  However in Lean it is better proved using backward reasoning. Otherwise when introducing the
  first lemma, the cardinality of HN(the union of unique left cosets) is problematic, since
  left coset is defined on set, counting on set arouses non-trival type problems for later proof.
-/
open scoped Pointwise
/-*This file contains the scratch during the proof of HallSubgroup.lean*-/
#check Subgroup.subtype
#check Subgroup.index_eq_card
#check Subgroup.card_mul_index
--#check relIndex
#check Subgroup.card_eq_card_quotient_mul_card_subgroup --Lagrange's theorem

variable {G : Type*} [Group G] [Fintype G]

/- *Counting on set might overcomplicate the Lean proof, paper must be adjusted with mathlib*-/
lemma order_union_of_left_cosets (H : Subgroup G) (N : Subgroup G) :
    Nat.card (⋃ h : H, h • N : Set G) =
    (Nat.card H * Nat.card N) / Nat.card ((H ∩ N : Set G)) := by
  sorry
/-*using the mathlib definition if my method cannot work* -/
theorem inter_of_hallSub_normal_is_Hall_one (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  sorry

-- /- **?** this trival result shoud be added in mathlib? or is it already exist -/
-- lemma index_eq_of_mul_eq_mul  {n : ℕ} (H : Subgroup G)
--     (h : Nat.card (G ⧸ H) * Nat.card H = Nat.card H * n) : H.index = n := by
--   have hn : Nat.card (G ⧸ H) = n := by
--     sorry
--   simpa [Subgroup.index, Nat.card_eq_fintype_card] using hn


/- *!attention: wrong definition!!!*-/
--   have hH : (Nat.card H : ℕ) ∣  Nat.card G := by exact Subgroup.card_subgroup_dvd_card H
--   obtain ⟨n, hn⟩ := hH
--   have : H.index = n := by
--   surprised.shouldn't it just result followed from lagrange theorem and the definition of index?
--     rw[Subgroup.card_eq_card_quotient_mul_card_subgroup H] at hn --using the Lagrange's theorem
--     exact index_eq_of_mul_eq_mul H hn
--   have hpn: n.Coprime (Nat.card ↥H) := by simpa [this] using hH
--   -- clue: focusing the divisibility and prime translation in equations
--   sorry
