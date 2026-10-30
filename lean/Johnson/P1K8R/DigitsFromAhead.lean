-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K8R/DigitsFromAhead.lean: THE FIELD "digits" OF `K8LeftT` (Johnson/P1K8R/TightAt.lean),
TO THE LETTER, AT EACH OF THE 25 LINKS, FROM THE HEAD `P5J.AtMgA` AND `DigAheadOk` BEHIND
THE DRAW ALONE: the closed premise hx of `k08_digits_of_ahead` (DigitsAtDraw.lean) is paid by
`digThere_at_head` (DigThereAll.lean). One theorem: a joining.
  `k08_digits_from_ahead`: K is asked at whatever place x and parameters tl `digAt`
    returns at link l; that it returns is shown inside.
Limits. THE WEIGHT STAYS IN K: `DigAheadOk` is shown at no state. A member of the head is proved at
`storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At `OnBytes.secondHashFunction` alone.
Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.DigitsAtDraw
import Johnson.P1K8R.DigThereAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD "digits", TO THE LETTER, FROM THE HEAD AND `DigAheadOk` ALONE.** -/
theorem k08_digits_from_ahead (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    (K : ∀ (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2),
      VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) l = some (x, tl) →
      ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
      (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs =
        .ok b.1) →
      VerifiableInference.OnPublicFiles.DigAheadOk x tl h.𝔇.sent h.𝔇.l3.rad
        (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr h.𝔇.ms h.𝔇.N l b.1 w) :
    ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str) w,
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs =
        .ok b.1) →
      (mgAtAll h).constr l .lookDigits (z, b.1) (strsOf Fr b.2) w →
      DigitsAt (cellsAhead (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
        (z, b.1)) b.1 w := by
  obtain ⟨x, tl, hx⟩ := digThere_at_head h hl
  exact k08_digits_of_ahead h hG hl e3 hRch hx (K x tl hx)

end P1K8T

#print axioms P1K8T.k08_digits_from_ahead
