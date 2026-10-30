-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/NsOfAtMgAll.lean: THE COMPOSED MEANING's OWN NUMBER OF SLOTS OF SEGMENT 2 g
(the field nsOf of MgData.pubD, Johnson/Desc/Sound/MgAll.lean: read by the public test freeAbove) IS
THE NUMBER OF WHICH K4's SUB-PROTOCOL SPEAKS, par.hp.ns. One statement: a call of built_ns
(Johnson/Road/K4/Riders/BuiltNs.lean): Lean unfolds the field.

  **`nsOf_mgAll`**: Dm.pubD.nsOf (2 * g) = some x.2.hp.ns. Premises: the goals' scope (hS, hR) · an
    opening O of the IOP as written in Lean · g < 12 · hx, hl: x is the member of K4's lot's list
    that bears the number 2 g (k04_sits_desc, Johnson/Road/K4/K04Sits.lean, gives one) · hb: the
    parameter built of Dm is the public part's own list of built segments: OWED BY WHOEVER FILLS Dm.
Limits. hb is shown at no filling. That there is an opening is shown by no theorem. K04_law, the law
of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Riders.BuiltNs
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MgData)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **The composed meaning's number of slots of segment 2 g is K4's own.** -/
theorem nsOf_mgAll {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi P Tok rows cols nR X) {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {x : Bool × Par} (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none)
    (hl : x.2.link = 2 * g) (hb : Dm.built = Z.p.built.links) :
    Dm.pubD.nsOf (2 * g) = some x.2.hp.ns :=
  built_ns hS hR O hg hx hl hb

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.nsOf_mgAll
