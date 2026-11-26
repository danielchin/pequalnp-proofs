import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18823_aux

open PEqualNP.HeptadCover

theorem main_proof :
    ∀ p l : Fin 13, p ∈ singerLines3 l ↔ -l ∈ singerLines3 (-p) := by
  decide

end PEqualNP.Outside.L_meta_18823_aux

theorem PEqualNP.Outside.L_meta_18823 : (∀ (x1 x2 : Fin (13 : ℕ)), x1 ∈ PEqualNP.HeptadCover.singerLines3 x2 ↔ -x2 ∈ PEqualNP.HeptadCover.singerLines3 (-x1))  := by
  exact PEqualNP.Outside.L_meta_18823_aux.main_proof
