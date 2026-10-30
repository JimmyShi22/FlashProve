-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4FrontOfMeans.lean: K4's ROW's STRUCTURE OF LINES `K4Front` (K4PromiseFront.lean:
what the meaning's items in front of K4's sub-protocol say to K4's law) OUT OF THE STRUCTURE OF
EQUATIONS `K4Means`. One statement with its proof: a call of `k4Front_at` (K4AtMg.lean) at the
lookups' own public parameters X and the segment's number m itself.

  **`k4Front_of_means`**: `K4Means Mg D` · D.links = links · X is a value of `Verify.publicOf` ·
    THREE LINES ON THESE PARAMETERS (m is a feed-forward segment's number: not the head's, a
    multiple of the step, with a plan hp) · the table's test pubFit at the door's filling D.moreL ⟹
    `K4Front` at the layout's own shape, lmb, first slot 0 and the item's own condition on the
    ledger.

Limits. The lines on X and the test are premises: facts on the public parameters and the plan.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4MeansFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (ModelPart Meaning pubFit)
open VerifiableInference.OnPublicFiles (LeftQ)
open VerifiableInference.Desc.Sound (MsgT)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {pol KL : ByteArray} {layout : Option ByteArray} {hp : Layer.HPlan2}

/-- **`K4Front` out of the structure of equations.** -/
theorem k4Front_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) (hlinks : D.links = links)
    (h : Verify.publicOf pol KL layout = .ok X)
    (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[m / (if X.p4 then 2 else 1)]? = some hp)
    (fit : pubFit D.moreL links ps = true) :
    K4Front Mg Z links ps m X.y.fo X.y.h.lmb 0 (LeftQ hp.ns) :=
  k4Front_at Z (hlinks ▸ E.fields) H h hn h0 hg (E.eL Z m) (E.eO Z m) (E.more ▸ fit)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Front_of_means
