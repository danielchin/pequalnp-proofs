import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18753_aux

open PEqualNP.BicliqueBlockCost

theorem main_proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (T : Finset (Fin n)), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
        HasBlockCost G (G.edgeSet.ncard + T.card - 1) := by
  classical
  intro n G _ T hcov
  let L : Fin n → Finset (Fin n) := fun u =>
    Finset.univ.filter fun v : Fin n => G.Adj u v ∧ (v ∉ T ∨ u < v)
  let T' : Finset (Fin n) := T.filter fun u => (L u).Nonempty
  let mkStar : Fin n → Block n := fun u => ({u}, L u)
  let F : Finset (Block n) := T'.image mkStar
  have hinj : Function.Injective mkStar := by
    intro u v h
    have h1 : ({u} : Finset (Fin n)) = {v} := congrArg Prod.fst h
    exact Finset.singleton_injective h1
  have hcover : IsBlockCover G F := by
    constructor
    · intro p hp
      rw [Finset.mem_image] at hp
      rcases hp with ⟨u, hu, rfl⟩
      rw [Finset.mem_filter] at hu
      refine ⟨?_, Finset.singleton_nonempty u, hu.2, ?_⟩
      · rw [Finset.disjoint_singleton_left]
        intro hmem
        have hmem' := (Finset.mem_filter.mp hmem).2
        exact G.ne_of_adj hmem'.1 rfl
      · intro a ha b hb
        rw [Finset.mem_singleton] at ha
        subst ha
        exact (Finset.mem_filter.mp hb).2.1
    · intro u v huv
      have hne : u ≠ v := G.ne_of_adj huv
      rcases hcov u v huv with hu | hv
      · by_cases hvT : v ∈ T
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hvL : v ∈ L u := Finset.mem_filter.mpr ⟨Finset.mem_univ v, huv, Or.inr hlt⟩
            have hu' : u ∈ T' := Finset.mem_filter.mpr ⟨hu, ⟨v, hvL⟩⟩
            exact ⟨mkStar u, Finset.mem_image_of_mem mkStar hu', Or.inl ⟨Finset.mem_singleton_self u, hvL⟩⟩
          · have huL : u ∈ L v := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huv.symm, Or.inr hgt⟩
            have hv' : v ∈ T' := Finset.mem_filter.mpr ⟨hvT, ⟨u, huL⟩⟩
            exact ⟨mkStar v, Finset.mem_image_of_mem mkStar hv', Or.inr ⟨Finset.mem_singleton_self v, huL⟩⟩
        · have hvL : v ∈ L u := Finset.mem_filter.mpr ⟨Finset.mem_univ v, huv, Or.inl hvT⟩
          have hu' : u ∈ T' := Finset.mem_filter.mpr ⟨hu, ⟨v, hvL⟩⟩
          exact ⟨mkStar u, Finset.mem_image_of_mem mkStar hu', Or.inl ⟨Finset.mem_singleton_self u, hvL⟩⟩
      · by_cases huT : u ∈ T
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hvL : v ∈ L u := Finset.mem_filter.mpr ⟨Finset.mem_univ v, huv, Or.inr hlt⟩
            have hu' : u ∈ T' := Finset.mem_filter.mpr ⟨huT, ⟨v, hvL⟩⟩
            exact ⟨mkStar u, Finset.mem_image_of_mem mkStar hu', Or.inl ⟨Finset.mem_singleton_self u, hvL⟩⟩
          · have huL : u ∈ L v := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huv.symm, Or.inr hgt⟩
            have hv' : v ∈ T' := Finset.mem_filter.mpr ⟨hv, ⟨u, huL⟩⟩
            exact ⟨mkStar v, Finset.mem_image_of_mem mkStar hv', Or.inr ⟨Finset.mem_singleton_self v, huL⟩⟩
        · have huL : u ∈ L v := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huv.symm, Or.inl huT⟩
          have hv' : v ∈ T' := Finset.mem_filter.mpr ⟨hv, ⟨u, huL⟩⟩
          exact ⟨mkStar v, Finset.mem_image_of_mem mkStar hv', Or.inr ⟨Finset.mem_singleton_self v, huL⟩⟩
  have hsum_le : ∑ u ∈ T', (L u).card ≤ G.edgeSet.ncard := by
    let Epart : Fin n → Finset (Sym2 (Fin n)) := fun u => (L u).image (fun v => s(u, v))
    have hcard_eq : ∀ u ∈ T', (Epart u).card = (L u).card := by
      intro u _
      apply Finset.card_image_of_injective
      intro x y hxy
      rcases Sym2.eq_iff.mp hxy with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    have hdisj : Set.PairwiseDisjoint (T' : Set (Fin n)) Epart := by
      intro u hu v hv huv
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e heu hev
      rw [Finset.mem_image] at heu hev
      rcases heu with ⟨x, hx, rfl⟩
      rcases hev with ⟨y, hy, heq⟩
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      rw [Finset.mem_coe, Finset.mem_filter] at hu hv
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv rfl
      · rcases hx'.2 with h1 | h1
        · exact h1 hv.1
        · rcases hy'.2 with h2 | h2
          · exact h2 hu.1
          · exact lt_asymm h1 h2
    have hsub : (T'.biUnion Epart : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_biUnion] at he
      rcases he with ⟨u, _, heu⟩
      rw [Finset.mem_image] at heu
      rcases heu with ⟨v, hv, rfl⟩
      exact G.mem_edgeSet.mpr (Finset.mem_filter.mp hv).2.1
    have hbi : (T'.biUnion Epart).card = ∑ u ∈ T', (L u).card := by
      rw [Finset.card_biUnion hdisj]
      exact Finset.sum_congr rfl hcard_eq
    have hnc : (T'.biUnion Epart : Set (Sym2 (Fin n))).ncard = (T'.biUnion Epart).card :=
      Set.ncard_coe_finset _
    have hle := Set.ncard_le_ncard hsub (Set.toFinite G.edgeSet)
    omega
  refine ⟨F, hcover, ?_⟩
  have hFcard : F.card = T'.card := Finset.card_image_of_injective T' hinj
  have hT'le : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hsumF : ∑ p ∈ F, blockCost p = ∑ u ∈ T', (L u).card := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    apply Finset.sum_congr rfl
    intro u _
    simp [mkStar, blockCost]
  change (∑ p ∈ F, blockCost p) + (F.card - 1) ≤ G.edgeSet.ncard + T.card - 1
  rw [hsumF, hFcard]
  rcases Nat.eq_zero_or_pos T'.card with h0 | hpos
  · have hT'0 : T' = ∅ := Finset.card_eq_zero.mp h0
    simp [hT'0]
  · omega

end PEqualNP.Outside.L_meta_18753_aux

theorem PEqualNP.Outside.L_meta_18753 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 (x2.edgeSet.ncard + x4.card - (1 : ℕ)))  := by
  exact PEqualNP.Outside.L_meta_18753_aux.main_proof
