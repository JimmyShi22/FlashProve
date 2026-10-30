-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03HobAt.lean: the kind "lookup" (K3), at the closed constant: ACROSS AN ACCEPT OF THE
STATED LOOKUP ON THE DIGITS, WHAT THE LEDGER BEHIND STILL OWES THE LEDGER IN FRONT OWED.
  `k03_hob_dig`: at every segment l < 25, from the stated sub-protocol's own accept (`StepRel`)
    alone: no promise, no "reached", no mark is asked. One call of `k3_digits_step_hob`
    (Johnson/Desc/Sound/MgAt/K3DigitsPlanesHead.lean); the credit is that file's.
  `k03_hOb_head`: the same at the output head's link, with the four idle hands of the
    premise hOb of `ridesAtR_digits_head_hole` (Johnson/Desc/Sound/MgAt/K3RidesDigFwd3.lean): the
    binder Ob of Johnson/P5J/K03Due8.lean and K03Due9.lean, to the letter.

Limits. An implication over two states and two ledgers; that there is an accept is not said. The
head is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). Nothing on soundness; nothing on hiding.


-/
import Johnson.P5J.K03RidesDigAt
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **What the ledger behind still owes, the ledger in front owed: at every segment's digits.** -/
theorem k03_hob_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) {b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S
      VerifiableInference.Desc.Claim}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    {s s' : VerifiableInference.Desc.First.S} (hR : StepRel b' s s') :
    ∀ F G, K3Pass s s' F G → ∀ i, VerifiableInference.Desc.K3.unpaid G i = true →
      VerifiableInference.Desc.K3.unpaid F i = true := by
  intro F G Q
  obtain ⟨rs, gs, hd⟩ := id hR
  exact k3_digits_step_hob K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes
    Zp.first.shape (IM.k3Place l true) b' hb
    ((k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃).planOk l hl true b' hb) l rfl
    (k03_pieceAt_dig h.toAtMg l) s s' rs gs hd Q

/-- **The premise hOb at the output head's digits, to the letter.** -/
theorem k03_hOb_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
      ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F G, K3Pass u.1 v.1 F G → ∀ i, VerifiableInference.Desc.K3.unpaid G i = true →
        VerifiableInference.Desc.K3.unpaid F i = true :=
  fun _ hb _ _ _ _ _ _ _ hR => k03_hob_dig h 𝔏 q₁ q₂ q₃ (by omega) hb hR

end P5J

#print axioms P5J.k03_hob_dig
#print axioms P5J.k03_hOb_head
