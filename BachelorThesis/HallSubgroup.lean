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

/- *possilbe lemma to mathlib?*-/
-- the cardinality of HN are equal, no matter if we count it in subgroup H or in subgroup G
lemma card_comap_subtype (H K : Subgroup G) (hKH : K ≤ H) :
    Nat.card ((K.comap H.subtype : Subgroup H)) = Nat.card K := by
  simp_all only [Subgroup.comap_subtype]
  let e : (K.subgroupOf H) ≃ K := sorry
  exact Nat.card_congr e

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
          have iso : (H ⊓ N).comap H.subtype  ≃* (H ⊔ N).map (QuotientGroup.mk' N) := by
            sorry
          have index_iso : ((H ⊓ N).comap H.subtype).index =
            ((H ⊔ N).map (QuotientGroup.mk' N)).index := by
              sorry --should somehow use Subgroup.index_map_equiv
          sorry
        exact Dvd.intro_left (H ⊔ N).index (id (Eq.symm hIndex))
      have h : (H.relIndex N).gcd (Nat.card ↥(H ⊓ N)) ∣ H.relIndex N :=
        Nat.gcd_dvd_left _ _
      exact Nat.dvd_trans h this
    have h2 : Nat.gcd (H.relIndex N) (Nat.card (H ⊓ N : Subgroup G)) ∣ Nat.card H := by
      have hLag : Nat.card (H ⊓ N : Subgroup G) ∣ Nat.card H := by
        let HN_in_H : Subgroup H := (H ⊓ N : Subgroup G).comap H.subtype
        have hCardEq : Nat.card HN_in_H = Nat.card (H ⊓ N : Subgroup G) := by
          refine card_comap_subtype H (H ⊓ N) ?_
          simp_all only [Subgroup.mem_inf, inf_le_left]
        rw [← hCardEq]
        apply Subgroup.card_subgroup_dvd_card   -- using Lagrange's theorem
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
