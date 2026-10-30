-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03FoldAt.lean: THE KIND "LOOKUP" (K3): WHAT ITS LEDGERS ASK OF EVERY REACHED STATE,
ALL FROM THE ONE STRUCTURE OF FACTS ON REACHED STATES (`FoldFacts`,
Johnson/Desc/First/FoldFacts.lean) AT THE CLOSED PUBLIC NUMBERS `At.foldD Zp cF L`
(Johnson/P5J/FoldAt.lean). One closed test with code and fourteen theorems (two of them by the
kernel, one a negative test; the others joinings); two examples.
Why. `K3Fold` (Johnson/Desc/Sound/MgAt/K3OwnIn.lean), four fields of `ObjShortR`
(Johnson/P5J/K03ObjAt.lean) at each of the lookups on a segment's calls, and seven fields of
`DigShortR` (Johnson/P5J/K03DigAt.lean) at each of the 25 lookups on the digits are facts on
reached states. The head of a counted statement has `FoldFacts` as one field already: with this
file these debts are that one condition.
  `k03_fold h F : K3Fold h.toAtMg.rch 𝔇.sent`.
  `k03_hLive`, `k03_hGroups`, `k03_hSeats`, `k03_hShapes`: AT EVERY BORDER k, each in the two
    structures' own text; the listed seats are L, the list of shapes is that of the planner's
    first chain's oracle messages.
  `k3DigMomentB`, `k3DigMoment_full`, `k3DigMoment_at`, `k3DigMoment_control`: at the digits'
    place of each of the 25 segments the frame's moment by the plan is 3 and the piece lies where
    the frame's number and "next" are booked: by the kernel; at the calls' place of segment 0 the
    moment is not 3.
  `k03_open`: at a lookup's border a reached state without a mark has an open segment (from the
    field ownIs).
  `k03_frame`, and from it `k03_hLink`, `k03_hNext`, `k03_hOwn`: at the digits' border of segment
    l < 25: the live frame's number is l, its "next" is laterOrClose, its own messages' numbers
    are `(At.foldD Zp cF L).ownAt l 3`. `k03_hLink_at`: the first with x.link for l, where `lookAt
    (At.X Zp) l true = some x`.
How the last three go: the field frameIs asks that a segment be open; at the kind's own places the
field ownIs gives that.
Two examples at the end are tests of fit: the four, and the seven, are laid into the two
structures' own fields beside letters for the other fields: so Lean holds that they are these
fields' texts.
Limits: joinings. F IS A PREMISE (the head's own field). The other fields of the two structures
(tests on the plan, what the other authors' public tests do behind the sub-protocol, the riders)
are not touched. The full size alone. No soundness is claimed.

-/
import Johnson.P5J.K03ObjAt
import Johnson.P5J.K03DigAt
import Johnson.P5J.FoldAt
import Johnson.Desc.Sound.MgAt.K3OwnIn

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
open VerifiableInference.Desc.First (FoldFacts momentAt shiftAt)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)

/-- At the digits' place of every segment: the plan's moment is 3, and the piece lies where the
frame's number and "next" are booked. -/
def k3DigMomentB : Bool :=
  (List.range 25).all fun l =>
    momentAt (shiftAt linksFull l) (IM.k3Ix l true + 1) == 3 &&
      decide (IM.k3Ix l true + 1 ≤ 11 + 2 * shiftAt linksFull l)

theorem k3DigMoment_full : k3DigMomentB = true := by decide +kernel

/-- **A negative test**: at the calls' place of segment 0 the moment is not 3. -/
theorem k3DigMoment_control :
    (momentAt (shiftAt linksFull 0) (IM.k3Ix 0 false + 1) == 3) = false := by decide +kernel

theorem k3DigMoment_at {l : ℕ} (hl : l < 25) :
    momentAt (shiftAt linksFull l) (IM.k3Ix l true + 1) = 3 ∧
      IM.k3Ix l true + 1 ≤ 11 + 2 * shiftAt linksFull l := by
  have h := List.all_eq_true.1 k3DigMoment_full l (List.mem_range.2 hl)
  simpa using h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {L : Laid}

set_option quotPrecheck false in
local notation "StrK" =>
  (frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
    (D.at OnBytes.Slice.frS.P.T.a).key₁ 0).E.Str

/-- **What the kind's paid fields spend of the facts along the fold.** -/
theorem k03_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps) :
    K3Fold h.toAtMg.rch (h.toAtMg.𝔇 h.𝔇).sent :=
  k3Fold_of_foldFacts F

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (F : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps)
include F

theorem k03_hLive (k : ℕ) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch k ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.shape = (h.toAtMg.𝔇 h.𝔇).sent.shape :=
  fun z a hr hu => F.liveShape k ((z, a.1), a.2) hr hu

theorem k03_hGroups (k : ℕ) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch k ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.groups = reqGroups a.1.live.frame.shape :=
  fun z a hr hu => F.liveGroups k ((z, a.1), a.2) hr hu

theorem k03_hSeats (k : ℕ) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch k ((z, a.1), a.2) → a.1.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstSeats L a.1 = true :=
  fun z a hr hu => F.seatsCarried k ((z, a.1), a.2) hr hu

theorem k03_hShapes (k : ℕ) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch k ((z, a.1), a.2) → a.1.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstShapes (msgsOfChain Zp.made.proof.1) a.1 = true :=
  fun z a hr hu => F.msgShapes k ((z, a.1), a.2) hr hu

/-- At a lookup's border a reached state without a mark has an open segment. -/
theorem k03_open {l : ℕ} (hl : l < 25) (dg : Bool) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch (k3K l dg) ((z, a.1), a.2) → a.1.failed = none → ∃ L', a.1.link? = some L' := by
  intro z a hr hu
  have O := k3_ownIs_of_fold F l hl dg ((z, a.1), a.2) hr hu
  unfold VerifiableInference.Desc.First.Look.OwnIs VerifiableInference.Desc.First.Look.ownOf at O
  obtain ⟨L', hL, -⟩ := Option.map_eq_some_iff.1 O
  exact ⟨L', hL⟩

/-- The three facts on the frame at the digits' border, at once. -/
theorem k03_frame {l : ℕ} (hl : l < 25) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch (k3K l true) ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.link = l ∧ a.1.live.frame.next = .laterOrClose ∧
      a.1.live.frame.own = (At.foldD Zp cF L).ownAt l 3 := by
  intro z a hr hu
  obtain ⟨L', hL⟩ := k03_open h F hl true z a hr hu
  have T := F.frameIs (k3K l true) ((z, a.1), a.2) (IM.k3Place l true) l L' hr hu
    (K3Lot.k03_at_full l hl true) rfl hL
  have e : a.1.live = L'.check := by
    unfold VerifiableInference.Desc.First.S.live
    rw [hL]
  obtain ⟨m3, hp⟩ := k3DigMoment_at hl
  obtain ⟨-, hown, -, hrest⟩ := T
  rw [e]
  refine ⟨(hrest hp).1, (hrest hp).2, ?_⟩
  rw [hown]
  exact congrArg _ m3

theorem k03_hLink {l : ℕ} (hl : l < 25) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch (k3K l true) ((z, a.1), a.2) → a.1.failed = none → a.1.live.frame.link = l :=
  fun z a hr hu => (k03_frame h F hl z a hr hu).1

theorem k03_hLink_at {l : ℕ} (hl : l < 25) {x : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (At.X Zp) l true = some x) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch (k3K l true) ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.link = x.link := by
  intro z a hr hu
  rw [IM.lookAt_link hx]
  exact k03_hLink h F hl z a hr hu

theorem k03_hNext {l : ℕ} (hl : l < 25) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch (k3K l true) ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.next = .laterOrClose :=
  fun z a hr hu => (k03_frame h F hl z a hr hu).2.1

theorem k03_hOwn {l : ℕ} (hl : l < 25) : ∀ (z : ProofFile.InstPub) (a : TS × StrK),
    h.toAtMg.rch (k3K l true) ((z, a.1), a.2) → a.1.failed = none →
    a.1.live.frame.own = (At.foldD Zp cF L).ownAt l 3 :=
  fun z a hr hu => (k03_frame h F hl z a hr hu).2.2

/-- A test of fit: the four go into `ObjShortR`'s own fields, at the calls' border of segment l. -/
example (l : ℕ) (x : VerifiableInference.Desc.First.Look.Place) (q) (b') :=
  fun hB pubSent pubFree hTests h6 hBare =>
    (⟨hB, k03_hLive h F _, k03_hGroups h F _, k03_hSeats h F _, k03_hShapes h F _, pubSent,
      pubFree, hTests, h6, hBare⟩ :
      ObjShortR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l x q b' L
        (msgsOfChain Zp.made.proof.1))

/-- A test of fit: the seven go into `DigShortR`'s own fields, at the digits' border. -/
example (l : ℕ) (hl : l < 25) (x : VerifiableInference.Desc.First.Look.Place)
    (hx : lookAt (At.X Zp) l true = some x) (q) (b') (n : ℕ) :=
  fun othersPub othersP rides hB pubFree hnS hTests h6 =>
    (⟨othersPub, othersP, rides, hB, k03_hLive h F _, k03_hGroups h F _,
      k03_hLink_at h F hl hx, k03_hNext h F hl, k03_hOwn h F hl, k03_hSeats h F _,
      k03_hShapes h F _, pubFree, hnS, hTests, h6⟩ :
      DigShortR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l x q b' ((At.foldD Zp cF L).ownAt l 3) n L
        (msgsOfChain Zp.made.proof.1))

end

end P5J

#print axioms P5J.k3DigMoment_full
#print axioms P5J.k3DigMoment_control
#print axioms P5J.k3DigMoment_at
#print axioms P5J.k03_fold
#print axioms P5J.k03_hLive
#print axioms P5J.k03_hGroups
#print axioms P5J.k03_hSeats
#print axioms P5J.k03_hShapes
#print axioms P5J.k03_open
#print axioms P5J.k03_frame
#print axioms P5J.k03_hLink
#print axioms P5J.k03_hLink_at
#print axioms P5J.k03_hNext
#print axioms P5J.k03_hOwn
