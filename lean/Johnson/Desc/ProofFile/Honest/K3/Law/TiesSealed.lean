-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/TiesSealed.lean: three definitions of this folder that write
out a text of the library's, each tied to it by an equation. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md.

Why. If the library's text turned, this folder's would stay, unseen. With the equations here Lean
would report it.

What is shown.
  `inE_eq_readE`: `inE` (Honest/K3/Wit.lean) is the library's `OnBytes.Slice.readE`
    (OnBytes/Slice/ProgField.lean). By `rfl`.
  `outE_eq_liftGl`: `outE` (Wit.lean) is the library's `D6.Bridge.liftGl`
    (OnBytes/Desc/First/NormBridge/HonestGl.lean). By `rfl`.
  `tlOf_eq_tlAt`: `tlOf X i` (Honest/K3/WitPlan.lean) is the library's `First.Look.tlAt X i`
    (Johnson/Desc/First/Look/Laid.lean), with the empty structure where that returns nothing.

Hypotheses that remain. None.

Imported. Honest/K3/WitPlan.lean (and through it Wit.lean); the three files of the library that are
named above. Other files lie beneath: Honest/ForKinds.lean, Honest/Frame.lean, Honest/Side.lean and
Honest/Sum.lean.


Limits. Equations of definitions: nothing is said on what the definitions are good for. No file that
bears one of the six names is changed. Honest/K3/WitFill.lean has a `tlAt` of its own, of another
type: it is not spoken of here. Ties among this folder's own texts: Honest/K3/Law/Ties.lean
[not in this library]. Two ties to the library stand elsewhere already: `inE_is_gl`
(Honest/K3/Law/KeysAreKvG.lean: `inE` is `Reading.gl.val`) and `tlAt_tlOf`
(Honest/K3/Law/OwnerKeyIs.lean: at the matrices' entries alone). The like for other definitions:
Honest/K3/Law/TiesSealedLot.lean [not in this library], Honest/K3/Law/TiesSealedFits.lean
[not in this library].

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitPlan
import OnBytes.Slice.ProgField
import OnBytes.Desc.First.NormBridge.HonestGl
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Ties

/-- The program's element in the library's field: this folder's text is the library's reading. -/
theorem inE_eq_readE (x : OnBytes.E) : inE x = OnBytes.Slice.readE x := rfl

/-- The library's element as the program's: this folder's text is the library's. -/
theorem outE_eq_liftGl (x : Cb.Gl.E) : outE x = D6.Bridge.liftGl x := rfl

/-- The structure of a link's smallness test: this folder's text is the library's, with the empty
structure where the library's returns nothing. -/
theorem tlOf_eq_tlAt (X : OnBytes.Model.Verify.Public) (i : ℕ) :
    tlOf X i = (VerifiableInference.Desc.First.Look.tlAt X i).getD {} := by
  unfold tlOf linkH stepOf VerifiableInference.Desc.First.Look.tlAt
  dsimp only
  split_ifs <;> rfl

end ProofFile.Honest.K3.Ties

#print axioms ProofFile.Honest.K3.Ties.inE_eq_readE
#print axioms ProofFile.Honest.K3.Ties.outE_eq_liftGl
#print axioms ProofFile.Honest.K3.Ties.tlOf_eq_tlAt
