-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gl/GlOff.lean: a test on a group over p = 2^64 - 2^32 + 1, within a third of the distances:
clauses on codes in the hypotheses of its theorem follow from conditions on its Reed-Solomon codes
and radii, with no hypothesis on list sizes or on mutual correlated agreement; the other clauses
are asked as they stand.


Definitions, statements (in `Cb.Gl.Spec`) and proofs (an assembly).





Here: F the integers modulo p, E = F[x] / (x^3 - 2); every code `GlC` (Cb/Gl/GlLd.lean: built from
families of plain Reed-Solomon codes on subgroups of orders at most 2^32). The clauses on codes are
derived, but for those listed below as asked.


Main names:
  `RunGl D`: a test on a group: its whole test is a tower with `TowGGl` (Cb/GlVal/GlThird.lean), it
    needs as many long positions as that tower (`D.t = Tw.toG.q`); bound 1; each member's code at
    the group's positions is `GlC` with distance d; 3 e < d; Fits; the bridge's evader.
  `Spec.gl3_run`: `RunGl D` gives `D.In3` (`LdRunD.In3`, Cb/Obj/LdObjectThird.lean): a test on a
    group within a third of the distances.





















Limits: one kind of clause speaks of sender and code together and is asked, not derived: what the
encodings of the oracle messages sent hide (the limits of Cb/GlVal/GlThird.lean).
A member's code at the group's positions is asked `GlC` at t = 0 only.



Asked as they stand too: of a shaped tower `Sh.view.Laws` (inside `TowGGl`, Cb/GlVal/GlThird.lean);
at each switch of a tower: `Sample.PrivateSim` of the switch's sample (inside `TowGl`, `TowGGl`).
`RunGl` asks `GlC` of the code of a group's complex (a family of the members' codes): the closure
has the clause `GlC.fam` for complexes (Cb/Gl/GlLd.lean).
Until an instance is exhibited, faults in these conditions cannot be excluded.


No instance that meets `RunGl` is part of this library; as far as the library shows, `gl3_run` may
hold of nothing.



This file does not say that `RunGl` can be met by numbers of interest: whether lengths and rates of
interest meet 3 e < d together with the errors wanted is not looked at.
It says nothing on the online phase, nothing on lengths above 2^32, nothing on the compiled
argument.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlThird
import Cb.Obj.LdObjectThirdEndProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR

/-- A test on a group, all of whose codes are built from plain Reed-Solomon families, within a
third. -/
def RunGl {S : Sig E} (D : LdRunD S) : Prop :=
  ∃ (Tw : LdTowG3 D.G D.Sb D.sl D.Z) (d : ℕ), D.T = Tw.toG.toEnd ∧ D.t = Tw.toG.q ∧
    D.L = 1 ∧ (∀ a : D.G.A, GlC ((S.om a.1).C.atPos (D.G.pos a)) d 0) ∧
    3 * D.G.e < d ∧ D.G.Fits ∧ D.Z.OK ∧ TowGGl Tw

namespace Spec

def gl3_run : Prop := ∀ (S : Sig E) (D : LdRunD S), RunGl D → D.In3

end Spec

theorem gl3_run : Spec.gl3_run := by
  rintro S D ⟨Tw, d, h1, h2, h3, hG, hlt, hF, hZ, hT⟩
  exact ⟨Tw, d, h1, h2, h3, gl3_group S D.G d hG hlt hF, hZ, gl3_towerG _ S D.G D.Sb D.sl D.Z Tw hT⟩

end Cb.Gl
