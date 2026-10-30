-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03MergeAll.lean: THE LOOKUP ARGUMENT ON THE DIGITS AT THE OUTPUT HEAD's SEGMENT: THE
NAMED FACT hmerge, IN ITS OWN TEXT, AT THE CLOSED CONSTANT, UNDER THE HEAD `AtMgA`, A VALUE OF
`Free` AND ITS THREE EQUATIONS: the one
premise of `k03_mergeAt_digits_head` (Johnson/P5J/K03MergeHeadDigitsAt.lean) PAID by
`noMerge_345` (Johnson/K11R/NoMergeAt345.lean: at a state reached at border 345, without a mark, the
merge has laid
nothing), at "reached" := `AtMg.rch`. WITH IT hmerge STANDS AT ALL FIFTY LOOKUP ARGUMENTS:
  the 12 layers' digits: `k03_mergeAt_digits_lay` (Johnson/P5J/K03MergeAt.lean) · attention's 12
  digits: `k03_mergeAt_digits_att` (K03MergeAttAt.lean) · the 24 calls: `k03_mergeAt_calls`
  (K03MergeIdleAt.lean) · the head's calls: `k03_mergeAt_head_calls` (K03MergeIdleHeadAt.lean) · the
  head's digits: **`k03_mergeAt_digits_head_paid`**, here.

Limits. It asks something at the 12 layers' digits alone; at the other 38 the merge has no slot. The
head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side
library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03MergeHeadDigitsAt
import Johnson.P5J.K03MergeIdleHeadAt
import Johnson.K11R.NoMergeAt345

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (digAt)
open VerifiableInference.Desc.K9 (mergeOf)
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **At a state reached at border 345 the merge has no slot**, at the constant's description. -/
theorem k03_merge_none_head_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ a : (ProofFile.InstPub × VerifiableInference.Desc.First.S) × (FrD).E.Str,
      RchAt (F0T OnBytes.secondHashFunction Zp Np cF) 345 a → a.1.2.failed = none → mergeOf a.1.2 = none := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P1K11.noMerge_rchAt h.scope h.reads O h.laid.planOk

/-- **hmerge BEHIND THE DIGITS' LOOKUP AT THE OUTPUT HEAD's SEGMENT: FROM THE HEAD, A VALUE OF
`Free` AND ITS THREE EQUATIONS.** -/
theorem k03_mergeAt_digits_head_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ y tl, digAt (At.X Zp) 24 = some (y, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ G, (VerifiableInference.Desc.K3.seatDigits K3Lot.ofForm).heard v.1 = some G →
        ∀ f ∈ G.rows.toList, ∀ t ∈ f.slots.toList, mergeOf v.1 ≠ some t.1 :=
  k03_mergeAt_digits_head h 𝔏 q₁ q₂ q₃ (k03_merge_none_head_digits h)

end P5J

#print axioms P5J.k03_merge_none_head_digits
#print axioms P5J.k03_mergeAt_digits_head_paid
