import Mathlib.GroupTheory.Index
import Init.Data.Nat.Lemmas
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

/-!
Exercise 3.3.10 `Hall Subgroup`
-- A subgroup H of a finite group G is called a Hall Subgroup of G if (|G : H|, |H|) = 1.
-- Prove that if H is a Hall subgroup of G and N is the normal subgroup of G,
-- then H ⊓ N is a Hall subgroup of N and HN ⧸ N is a Hall subgroup of G ⧸ N.
-/

variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (N : Subgroup G) [N.Normal]

/-! The definition of Hall Group-/
abbrev IsHallSubgroup (H : Subgroup G) : Prop := Nat.Coprime H.index (Nat.card H)

/-! The definition that H ⊓ N is a subgroup of N-/
abbrev inter_of_subHN (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup N :=
  (H ⊓ N).comap N.subtype -- this might be unnecessary by using relIndex from the mathlib def.
#check H.relIndex N

/-! The definition that H ⊔ N is a subgroup of G-/
abbrev HN (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup G := H ⊔ N

#check QuotientGroup.quotientInfEquivProdNormalizerQuotient
#check Subgroup.subgroupOf
lemma snd_iso_index (H N : Subgroup G) (hLE : H ≤ N.normalizer) :
    Nat.card (↥H ⧸ N.subgroupOf H) = Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by
  sorry

/-! Prove that H ⊓ N is a Hall Subgroup of N-/
theorem inter_of_hallSub_normal_is_Hall_new (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  have hgcd :
      Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ Nat.gcd H.index (Nat.card H) := by
    -- using the 2.Isomorphism theorem
    have h1 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ H.index := by
      have : H.relIndex N ∣ H.index := by
        have hIndex : H.index = (H ⊔ N).index * H.relIndex N := by
          have card_G_one : Nat.card G = H.index * Nat.card H := by
            exact Eq.symm (Subgroup.index_mul_card H)
          have card_G_two : Nat.card G = (H ⊔ N).index * Nat.card (H ⊔ N : Subgroup G):= by
            exact Eq.symm (Subgroup.index_mul_card (H ⊔ N))
          have h_index : Nat.card H =
              Nat.card (↥H ⧸ N.subgroupOf H) * Nat.card (H ⊓ N : Subgroup G) := by
            sorry
          have n_index : Nat.card N =
              H.relIndex N * Nat.card (H ⊓ N : Subgroup G) := by
            sorry
          have hn_index : Nat.card (H ⊔ N : Subgroup G) =
              Nat.card (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) * Nat.card N := by
            sorry
          rw [h_index] at card_G_one
          rw [hn_index] at card_G_two
          rw [card_G_one, snd_iso_index, n_index] at card_G_two
          simp only [mul_comm, mul_left_comm, mul_assoc] at card_G_two
          apply mul_left_cancel₀ at card_G_two
          rw [← mul_assoc] at card_G_two
          apply mul_right_cancel₀ at card_G_two
          · assumption
          · sorry
          · sorry
          · exact Subgroup.le_normalizer_of_normal
        exact Dvd.intro_left (H ⊔ N).index (id (Eq.symm hIndex))
      have h : (H.relIndex N).gcd (Nat.card ↥(H ⊓ N)) ∣ H.relIndex N :=
        Nat.gcd_dvd_left _ _
      exact Nat.dvd_trans h this
    have h2 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ Nat.card H := by
      have hLag : Nat.card (H ⊓ N : Subgroup G) ∣ Nat.card H := by
        apply Subgroup.card_dvd_of_le
        exact inf_le_left
      have hgcd :
          Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G))∣ Nat.card (H ⊓ N : Subgroup G) :=
        Nat.gcd_dvd_right _ _
      exact Nat.dvd_trans hgcd hLag
    exact Nat.dvd_gcd h1 h2
  have : Nat.gcd H.index (Nat.card H) = 1 := Nat.coprime_iff_gcd_eq_one.mp hH
  have : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) = 1 := by
    exact Nat.dvd_one.mp (by simpa [this] using hgcd)
  exact this

/-! The definition that HN ⧸ N is a subgroup of G ⧸ N-/
def HNmodNisSubgroup (H : Subgroup G) (N : Subgroup G) [N.Normal] : Subgroup (G ⧸ N) :=
  (H ⊔ N).map (QuotientGroup.mk' N)

/-! Prove that HN ⧸ N is a Hall subgroup of G ⧸ N-/
theorem CosetsOfQuotientGrpIsHall (H : Subgroup G) (hH : Nat.Coprime H.index (Nat.card H))
    (N : Subgroup G) [N.Normal] :
    Nat.Coprime (HNmodNisSubgroup H N).index (Nat.card ((HNmodNisSubgroup H N))) := by
  sorry
