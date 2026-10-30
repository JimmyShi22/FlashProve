-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03HeadModelHead.lean: THE KIND "LOOKUP" (K3): THE FIELD model AT THE OUTPUT HEAD's
CALLS, AT THE CLOSED CONSTANT, FROM THE HEAD AND ONE CLOSED TEST ON PUBLIC DATA. Three theorems:
joinings.
  `k03_hOK_at h`: `HeadOK` at `headAt`'s place and the floor at which
    Johnson/P5J/K03HeadModelAt.lean asks it: from the entry tests' rows on the digits and on the
    output head (`k03_digRow_at`, `k03_headRow_at`, Johnson/P5J/K03TestsAt.lean), `k03_planR_at`
    (Johnson/P5J/K03PlanAt.lean), another author's `headOK_at`
    (Johnson/Desc/First/Look/K3HeadStated.lean) and `k03_floor`.
  `k03_head_model_at h FF hcalls hrows hbits …`: `k03_head_model` with hk6 by `k03_pads_at` and
    hOK by the first.
  `k03_head_model_head h hcalls …`: the same with hrows and hbits by another author's
    `hrows_at_head` and `hbits_at_head` (Johnson/P2LawR/HeadTabsAtHead.lean) and the facts on
    reached states by `atMgR_rch_of_head` (Johnson/P5J/StartAtHead.lean).
Limits: joinings. THE TESTS THAT ARE PAID HAVE MOVED INTO THE HEAD (its field on the entry tests
says that all their rows accept; its scope pins the head's layout). IN FRONT STAYS hcalls :
`callsSeatedC … = true` at the constant's terms: a test with code on public data. The head h is a
premise: no head is shown here. All the weight lies in other files. No soundness is claimed.

-/
import Johnson.P5J.K03HeadModelAt
import Johnson.P5J.K03TestsAt
import Johnson.P5J.K03PlanAt
import Johnson.P5J.StartAtHead
import Johnson.P2LawR.HeadTabsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Lp : VerifiableInference.Desc.K12.Door.Laid}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "WT" => Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT

/-- **`HeadOK` at the head's place, from the head.** -/
theorem k03_hOK_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    @HeadOK (k3SizesAt (At.X Zp)) (OnBytes.Params.settingOf (At.X Zp).P.frame) x
      (parOf (At.X Zp).hS 0).floor := by
  letI := k3SizesAt (At.X Zp)
  letI := k3PolicyAt (At.X Zp)
  letI : Request := ⟨fun _ => 0, 0, 0⟩
  obtain ⟨x', hx', hB, -⟩ :=
    (k03_planR_at h (k03_digRow_at h.toAtMg) (k03_headRow_at h.toAtMg)).head
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans h.headAt)
  exact headOK_at h.headAt hB

/-- **The field model, with the two paid.** -/
theorem k03_head_model_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (FF : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Lp) At.reqW At.links At.ps)
    (hcalls : AtFold.callsSeatedC (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link
      ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true)
    (hrows : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      rowsOk (rowH x) = true)
    (hbits : ∀ c, c < 6 → Cb.LdLkp.Port.kOf x.fs c = bitsOf c)
    {Cl : Type} (claim : Aff → Cl) (seats : List (ℕ × ℕ))
    (s₀ : VerifiableInference.Desc.First.S)
    (q : Piece (Run.ckP .two) FrD (ProofFile.InstPub × VerifiableInference.Desc.First.S) Cl WT)
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S Cl) :
    ∀ B', SeatOf b' B' → ∀ z : ProofFile.InstPub,
      letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      letI := (h.toAtMg.𝔇 h.𝔇).rq z
      HeadModelR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).G (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl
        (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
        (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
        (OnBytes.Params.settingOf (At.X Zp).P.frame)
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
        (smpCalls seats (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
          (h.toAtMg.𝔇 h.𝔇).l3.seat x)
        (Stored.smpWc (rows := numsFull.rows) (cols := colsAt numsFull))
        (Stored.strWc (h.toAtMg.𝔇 h.𝔇).decT s₀ z) (h.toAtMg.𝔇 h.𝔇).l3.msgW k3QAny
        (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
        (fun u => h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2)) claim (h.toAtMg.𝔇 h.𝔇).N
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS z (k3K 24 false) 24
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) :=
  k03_head_model h FF (k03_pads_at h.toAtMg).1 hcalls (k03_hOK_at h) hrows hbits claim seats s₀ q
    b'

/-- **THE FIELD model FROM THE HEAD AND ONE CLOSED TEST.** -/
theorem k03_head_model_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hcalls : AtFold.callsSeatedC (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp)
      (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad x.link
      ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true)
    {Cl : Type} (claim : Aff → Cl) (seats : List (ℕ × ℕ))
    (s₀ : VerifiableInference.Desc.First.S)
    (q : Piece (Run.ckP .two) FrD (ProofFile.InstPub × VerifiableInference.Desc.First.S) Cl WT)
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S Cl) :
    ∀ B', SeatOf b' B' → ∀ z : ProofFile.InstPub,
      letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      letI := (h.toAtMg.𝔇 h.𝔇).rq z
      HeadModelR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).G (k3AdrAt (At.X Zp)) x (At.X Zp).H.tl
        (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad (h.toAtMg.𝔇 h.𝔇).l3.oW
        (h.toAtMg.𝔇 h.𝔇).l3.wOf (h.toAtMg.𝔇 h.𝔇).l3.nr (h.toAtMg.𝔇 h.𝔇).l3.nc
        (OnBytes.Params.settingOf (At.X Zp).P.frame)
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link false j.1) (h.toAtMg.𝔇 h.𝔇).l3.arr
        (smpCalls seats (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
          (h.toAtMg.𝔇 h.𝔇).l3.seat x)
        (Stored.smpWc (rows := numsFull.rows) (cols := colsAt numsFull))
        (Stored.strWc (h.toAtMg.𝔇 h.𝔇).decT s₀ z) (h.toAtMg.𝔇 h.𝔇).l3.msgW k3QAny
        (fun w => VerifiableInference.OnPublicFiles.Flat.InRange w.cells)
        (fun u => h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2)) claim (h.toAtMg.𝔇 h.𝔇).N
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS z (k3K 24 false) 24
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v) := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  exact k03_head_model_at h R.fold hcalls (P2Law.K3.hrows_at_head h) (P2Law.K3.hbits_at_head h)
    claim seats s₀ q b'

end P5J

#print axioms P5J.k03_hOK_at
#print axioms P5J.k03_head_model_at
#print axioms P5J.k03_head_model_head
