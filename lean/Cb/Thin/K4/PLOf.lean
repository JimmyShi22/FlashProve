-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K4/PLOf.lean.
BRIDGES FROM THE LIBRARY's BUNDLES TO Link.PL: PROJECTIONS. THEY NAME GoodT | GoodB | AllT | OkFrom
ON PURPOSE: none is a thin statement.

-/
import Cb.Thin.K4.PL
import Ior.KnowCollPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
open Prob IOR IOR.Chain

/-- B1 -/
theorem pl_of_goodT {K : Type} {A B : Joint K} (l : Link K A B) (g : l.GoodT) : l.PL :=
  ⟨g.point, g.isLocal⟩

/-- B2 -/
theorem pl_of_goodB {K : Type} {A B : Joint K} (l : Link K A B) (g : l.GoodB) : l.PL :=
  ⟨g.point, g.isLocal⟩

/-- B3 -/
theorem each_pl_of_allT {K : Type} {A B : Joint K} (c : Chain K A B) :
    c.AllT → c.Each (PLk K) := by
  induction c with
  | one l =>
      intro h
      exact (each_one _ l).2 (pl_of_goodT l ((Chain.allT_one l).1 h))
  | snoc c l ih =>
      intro h
      exact (each_snoc _ c l).2
        ⟨ih ((Chain.allT_snoc c l).1 h).1, pl_of_goodT l ((Chain.allT_snoc c l).1 h).2⟩

/-- B4: a chain that stands behind c₀: a link is of one of the two kinds; both have the two facts.
-/
theorem each_pl_of_okFrom {K : Type} {Z A B : Joint K} (c : Chain K A B) (c₀ : Chain K Z A) :
    c.OkFrom c₀ → c.Each (PLk K) := by
  induction c with
  | one l =>
      intro h
      exact (each_one _ l).2
        (((okFrom_one c₀ l).1 h).elim (pl_of_goodT l) fun ⟨_, hD, _⟩ => pl_of_goodB l hD.base)
  | snoc c l ih =>
      intro h
      exact (each_snoc _ c l).2
        ⟨ih ((okFrom_snoc c₀ c l).1 h).1,
          ((okFrom_snoc c₀ c l).1 h).2.elim (pl_of_goodT l) fun ⟨_, hD, _⟩ => pl_of_goodB l hD.base⟩

end Iop

