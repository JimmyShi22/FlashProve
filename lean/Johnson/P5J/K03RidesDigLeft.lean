-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03RidesDigLeft.lean: THE KIND "LOOKUP" (K3): THE FIELD rides AT ALL 25 DIGITS'
PLACES, AT THE CLOSED CONSTANT, WITH EVERYTHING LAID IN THAT HAS A PAYER: WHAT IS LEFT IS FIVE
PREMISES ON THE STATES THAT ARE NOT SHOWN AT THE CONSTANT: UNTIL THEY HAVE PAYERS THE ROWS BUY
NOTHING. AND THE OUTPUT HEAD's ROW MAY BE EMPTY: ONE OF ITS THREE PREMISES (hrP) MAY BE FALSE AT A
STATE UNDER THE PROMISE: see Limits. Five theorems: calls.
  `k03_digAt_some`, `k03_link_some`: under the head, at every segment: `digAt` answers; the head's
    own chain has a link.
  `k03_rides_dig_lay_own`: at the layers' segment 2 g: from hOwn (the calling kind's runs "front",
    "back" go forward across the accept).
  `k03_rides_dig_att_own`: at attention's segment 2 g + 1: from hOwn ("first", "keys", "second").
  `k03_rides_dig_head_three`: at the output head's: from hrP (the run "planes" itself answers in
    front: at the head's own chain's link), hJoin, hOwn ("norm", "policy", "logits").
Each ends in the form in which the kind's condition asks the field: at a piece of the row and a
value of the kind's constant alone. Laid in: that `digAt` answers (`K3PlanR.digB`, off two closed
tests that are theorems under the head) · that the attention plan is there (another author's
`planAt_all`, Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean) · that the head's own chain has the
link · the find at "join" (`k03_joinFind_att`, Johnson/P5J/K03JoinFindAt.lean) · the window
(`k03_hWin`, Johnson/P5J/K03WinAt.lean) · the sentence on the weights (`k03_hWt`,
Johnson/P5J/K03WtBackAt.lean) · "objects" and "guests" answer
(Johnson/P5J/K03RunAnswersHeadAt.lean).
Limits: calls. The head h and the free letters' three equations are premises. hrP MAY BE FALSE (by
reading; no state is shown): it asks that the run "planes" itself answers at the state in front;
that run refuses where the calling kind's tables are not laid in the state; what the promise holds
is only that the link's reader answers, which at the head's segment may be its second hole (the
run at the state with the tables laid). Another file goes round it (whichever of
the run and the hole answers): the head's row is to be called over that file. The full size
alone. No soundness is claimed.

-/
import Johnson.P5J.K03RunAnswersHeadAt
import Johnson.P5J.K03JoinFindAt
import Johnson.P5J.K03WinAt
import Johnson.P5J.K03WtBackAt
import Johnson.P5J.K03HeadModelHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (statesOfLink readerOf)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- Under the head `digAt` answers at every segment. -/
theorem k03_digAt_some (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25) :
    ∃ y tl, VerifiableInference.Desc.First.Look.digAt (At.X Zp) l = some (y, tl) := by
  letI := k3SizesAt (At.X Zp)
  letI := k3PolicyAt (At.X Zp)
  have P := k03_planR_at h (k03_digRow_at h.toAtMg) (k03_headRow_at h.toAtMg)
  obtain ⟨y, tl, hy, -⟩ := P.digB (fun _ => 0) l hl
  exact ⟨y, tl, hy⟩

/-- The head's own chain has a link at every segment. -/
theorem k03_link_some (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25) :
    ∃ Lk, cF.links[l]? = some Lk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, e, -⟩ := k03_objects_raw h.scope h.reads O l hl false
  exact ⟨Lk, e⟩

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE LAYERS' TWELVE, FROM hOwn ALONE.** -/
theorem k03_rides_dig_lay_own : ∀ g < 12,
    ∀ q, (h.toAtMg.row 𝔏)[k3K (2 * g) true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b' →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g) true) u →
      h.toAtMg.rch (k3K (2 * g) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g) true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g)) p.1 p.2 u.1 v.1) →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K (2 * g) true) q b' := by
  intro g hg q hq b' hb' hOwn
  obtain ⟨y, tl, hy⟩ := k03_digAt_some h (l := 2 * g) (by omega)
  exact k03_rides_dig_layers h 𝔏 q₁ q₂ q₃ (2 * g) (by omega) (by omega) y tl hy q hq b' hb' hOwn

/-- **ATTENTION's TWELVE, FROM hOwn ALONE.** -/
theorem k03_rides_dig_att_own : ∀ g < 12,
    ∀ q, (h.toAtMg.row 𝔏)[k3K (2 * g + 1) true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true) u →
      h.toAtMg.rch (k3K (2 * g + 1) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g + 1) true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "first"), (2, "keys"), (2, "second")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g + 1)) p.1 p.2 u.1 v.1) →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K (2 * g + 1) true) q b' := by
  intro g hg q hq b' hb' hOwn
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨y, tl, hy⟩ := k03_digAt_some h hl
  obtain ⟨A, hA⟩ := H2K5.Door.planAt_all h hg
  obtain ⟨Lk, hLk⟩ := k03_link_some h hl
  exact k03_rides_dig_att h 𝔏 q₁ q₂ q₃ g hg A hA y tl hy q hq b' hb' Lk hLk
    (k03_joinFind_att h g hg A hA Lk hLk) (k03_hWin h hl hb') hOwn

/-- **THE OUTPUT HEAD's, FROM THREE.** -/
theorem k03_rides_dig_head_three :
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    (∀ Lk, cF.links[24]? = some Lk →
      ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink Lk) 2 "planes" u.1).isSome = true) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) 3 "join" u.1 v.1) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) p.1 p.2 u.1 v.1) →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K 24 true) q b' := by
  intro q hq b' hb' hrP hJoin hOwn
  have hl : 24 < 25 := by omega
  obtain ⟨y, tl, hy⟩ := k03_digAt_some h hl
  obtain ⟨Lk, hLk⟩ := k03_link_some h hl
  exact k03_rides_dig_head_five h 𝔏 q₁ q₂ q₃ y tl hy q hq b' hb' Lk hLk (hrP Lk hLk)
    (k03_hWin h hl hb') hJoin hOwn (k03_hWt h 𝔏 q₁ q₂ q₃ b' hb')

end

end P5J

#print axioms P5J.k03_digAt_some
#print axioms P5J.k03_link_some
#print axioms P5J.k03_rides_dig_lay_own
#print axioms P5J.k03_rides_dig_att_own
#print axioms P5J.k03_rides_dig_head_three
