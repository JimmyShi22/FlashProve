-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/AtFull.lean: CONDITIONAL. TWO NUMBERS OF THE LAYERS'
LAYOUT AT THE FULL SIZE.

What is here. The two hypotheses on numbers that `k4_live` (Law/Live/Whole.lean) takes: hll: the
point that the layers' own rounds (sub-protocol K4) draw between the two gated layers has one
coordinate (ll - 1 = 1) · hLam: at most two layers of a group have routed experts (LamM ≤ 2).
`llLam_of_layout`: both hold at every layout that the verifier's function `layout` returns for a
shape with ll = 2 (the library's `laySizes_of_layout`, Johnson/Road/K4/PlanSizes.lean: the layout
holds its shape, and LamM = 2 ^ ll / 2). `ll_full`: the layers' shape of the full-size model's
parameter file, in closed form (`Pv v`, Johnson/Road/K4/RowHead/Twins.lean), has ll = 2 (the
library's `shapeIs`, Johnson/Road/K4/RowHead/ClosedTies.lean). `llLam_of_scan`: so both hold at the
layers' data of what the verifier's public part (`Verify.publicOf`) returns (through the library's
`publicH_of_public`, Johnson/Road/HeadMade.lean), where its scan of the parameter file is `Pv v`.
Statements and proofs.

Not shown here. hP: THAT THE SCAN IS `Pv v`: a hypothesis. We have read a call of it, not its
statement: by that call (Johnson/Road/K4/RowHead/FrontOfHead.lean, in `front_of_head`) the library
has it where the public files lie in the goals' scope and are read (`Hd.scan_of_scope`); that
statement is not called here. hX: that the public part returns. That the public data at which K4's
hearing runs are those layers' data. THE FULL SIZE ALONE.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
by a program's walk from import to import, which stops unopened at every module under Johnson/Goal/,
Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its
imports reach one such module: Johnson.Goal.Meaning.ScopeScan.
Kin. `llLam_at_base` (Law/Live/AtBase.lean) has both numbers at the description's base, under the
library's head, by `llLam_of_layout`. The library has ll = 2 of the layers' shape at the full size
as a step inside two proofs (`rowLight_of_head`, Johnson/Road/K4/RowLightOfHead.lean;
`rowLight_in_scope`, Johnson/Road/K4/RowLightInScope.lean); of the parameter file's own number,
which the shape copies, it has it from its list of numbers `PublicAt`, as a step inside further
proofs (`public_of_publicOf`, Johnson/Road/HeadL5Pub.lean, is one) and as a field of `FillRef`
(`fillRef_of_at`, Johnson/Road/HeadL5All.lean); this file names no other statement that
ends in the two numbers.
No property is claimed.
-/
import Johnson.Road.K4.RowHead.ClosedTies
import Johnson.Road.K4.PlanSizes
import Johnson.Road.HeadMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (Pv laySizes_of_layout)

/-- Both numbers, at every layout of a shape with ll = 2. -/
theorem llLam_of_layout {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (hy : Layer.layout h pc = .ok y) (e : h.ll = 2) : y.h.ll - 1 = 1 ∧ y.LamM ≤ 2 := by
  have L := laySizes_of_layout hy
  rw [L.shape, L.LamM, e]
  exact ⟨rfl, Nat.le_refl 2⟩

/-- The full-size model's layers' shape has ll = 2. -/
theorem ll_full (v : VerifierAndGoals.FreeLines) : (Verify.layerShape (Pv v)).ll = 2 := by
  rw [OnBytes.Road.K4.Closed.shapeIs]
  rfl

/-- CONDITIONAL on hX and hP. **Both numbers at the layers' data of the verifier's public
part.** -/
theorem llLam_of_scan {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    {v : VerifierAndGoals.FreeLines} (hX : Verify.publicOf pol KL lay = .ok X) (hP : X.P = Pv v) :
    X.layers.y.h.ll - 1 = 1 ∧ X.layers.y.LamM ≤ 2 :=
  llLam_of_layout (OnBytes.Road.Hd.publicH_of_public hX).lay (by rw [hP]; exact ll_full v)

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.llLam_of_layout
#print axioms ProofFile.Honest.K4.Live.ll_full
#print axioms ProofFile.Honest.K4.Live.llLam_of_scan
