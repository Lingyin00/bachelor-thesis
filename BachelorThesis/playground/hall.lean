import Mathlib.GroupTheory.Index

/-*This file contains the scratch during the proof of HallSubgroup.lean*-/
#check Subgroup.subtype
#check Subgroup.index_eq_card
#check Subgroup.card_mul_index
--#check relIndex
#check Subgroup.card_eq_card_quotient_mul_card_subgroup --Lagrange's theorem

-- /- **?** this trival result shoud be added in mathlib? or is it already exist -/
-- lemma index_eq_of_mul_eq_mul  {n : ℕ} (H : Subgroup G)
--     (h : Nat.card (G ⧸ H) * Nat.card H = Nat.card H * n) : H.index = n := by
--   have hn : Nat.card (G ⧸ H) = n := by
--     sorry
--   simpa [Subgroup.index, Nat.card_eq_fintype_card] using hn


--   have hH : (Nat.card H : ℕ) ∣  Nat.card G := by exact Subgroup.card_subgroup_dvd_card H
--   obtain ⟨n, hn⟩ := hH
--   have : H.index = n := by
-- -- surprised...shouldn't it just result followed from lagrange theorem and the definition of index?
--     rw[Subgroup.card_eq_card_quotient_mul_card_subgroup H] at hn --using the Lagrange's theorem
--     exact index_eq_of_mul_eq_mul H hn
--   have hpn: n.Coprime (Nat.card ↥H) := by simpa [this] using hH
--   -- clue: focusing the divisibility and prime translation in equations
--   sorry
