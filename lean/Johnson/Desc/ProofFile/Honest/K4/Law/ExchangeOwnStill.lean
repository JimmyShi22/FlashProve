-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExchangeOwnStill.lean: CONDITIONAL: on the library's hypothesis
h on the public files and on every hypothesis named. THE FULL SIZE ALONE.

What is here. The thread's debt `ExchangeAtS` at the own item of the member of the feed-forward
layers' own rounds (sub-protocol K4), WITH THE HYPOTHESIS hc ASKED AT THE CHALLENGES HEARD ALONE,
not at every continuation of them: `k4_exchange_own_at` (Law/ExchangeOwnAt.lean) and
`k4_exchange_own_ready` (Law/ExchangeOwnReady.lean), each with hc had from `cellIsList_thr`
(Law/W/CellsStill.lean). hc (`CellIsList`, Law/W/CellsTieOf.lean) holds the honest cells against the
list of integers that the library's meaning reads off the script's witness for the group; asked at
every continuation it also forces that list's images to stand still. They do, where the thread
stands, if the frame's test with code on the script accepts (hQf) and each message AT A SEAT OF
`pinSeats N m` is born at or in front of K4's member (hb0): the seats of the segment's first moment,
`N.sent m 0`, and the seat of the index (Johnson/Road/K4/K4Pins.lean). So in hc's stead stand hc0
(the same sentence at what was heard), hQf and hb0. Nothing new is shown: one call each.

  `k4_exchange_own_still`   **`ExchangeAtS T Said k (Item.formsT m 3 "own")`** at a prover at large.
  `k4_exchange_own_still_ready`   **the same** at the maker's prover and a ready run's thread.

Not shown here. hc0: THAT THE HONEST CELLS ARE THE LIST's, at what was heard: a hypothesis on the
script and the trace: all that hc says of values is left in it. hQf (`Script.msgsFit`,
Honest/Thread/ScriptFit.lean) and hb0: hypotheses on the script and on that test's two parameters.
WHETHER hb0 AND hQf CAN HOLD TOGETHER AT AN HONEST SCRIPT IS NOT SHOWN AND NOT TESTED: it has been
read for; nothing holds born against the library's table. The seats are those of `.pin m 0` and
`.pinI`. Of that table: `.pinI` is open in front of K4's sub-protocol at all twelve places of the
written list (`k4_pinI_front_full`, Johnson/Road/K4/W/PinIFront.lean, by Lean's kernel); `.pin m 1`
and `.pin m 2` are open there at none of the twelve: said here without a theorem; no theorem of this
folder shows it. TWO LAYINGS OF THE PARAMETERS WOULD MAKE THE PAIR FALSE, by a reading: nMsg must
count no more than the first chain's messages: the numbers `arr` run over all three chains, and hQf
stands at the first chain's thread, where a later chain's message cannot fit; and born n, at a
message that is sent again as a kept copy under the same number, must be the border behind its FIRST
sender (Honest/Thread/ScriptFit.lean's own words: the first at which an item may speak of it). By
the same reading the seats of `N.sent m 0` hold the carried message, kept copies, the segment's own
arrays and a fresh mask, and in segment 0 the messages at the start (`rolesOf`,
Johnson/P5T/PlanSeats.lean). A premise over the segment's whole group of seats would take in the
seats of `.pin m 1` and `.pin m 2`, which are put out behind K4's member: said here without a
theorem; no theorem of this folder shows it. The library has, under h, its own test on the fence
(`P5J.AtMg.fence`, Johnson/P5T/FenceAtMg.lean; `fencedB_at_k4`, Johnson/Road/K4/K4PinsFence.lean):
every sampled tenant of an open pin sits in a tree that members in front have told; it is not called
here, and nothing ties it to born. EVERY OTHER HYPOTHESIS, AND EVERY LIMIT, IS THAT OF
Law/ExchangeOwnAt.lean AND Law/ExchangeOwnReady.lean: above all: b1, THE LOOKUP's OWN SENTENCE, IS
MOVED, NOT SHOWN (Law/ExchangeOfTies.lean's head says whither: it is had out of a clause of `ThrS`):
THE CONCLUSION SPEAKS ONLY WHERE A THREAD STANDS THAT HOLDS IT ALREADY; WHETHER ALL THE HYPOTHESES
CAN STAND TOGETHER AT AN HONEST SCRIPT HAS NOT BEEN TESTED: of h together with hRdIs, Lh, half,
fits, hb₀, hKp, hMask, hQf, hb0, hc0, hI, hVd, hW4, hA, hR, hx, hM, hE and ho no example is known to
us, and nothing here was evaluated (the side library AtFullSide proves, with no hypothesis, that h
has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth)); the conclusion speaks only where `ThrS` stands and a step
accepts; where none does, it holds emptily. NOT COMPLETENESS. THE FULL SIZE ALONE, and the format's
second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. It
imports files of the frame's authors and of the authors of the kind "lookup". A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeOwnReady
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsStill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block First.S)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open OnBytes.Road.K4 (k4PlaceAt)

open OnBytes.Road.K4 (pinSeats)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)

/-- CONDITIONAL: on every hypothesis named; the head lists them. **THE EXCHANGE AT THE MEMBER's OWN
ITEM, WITH THE HONEST CELLS HELD AGAINST THE LIST AT WHAT WAS HEARD ALONE**, at a prover H at large.
ν, st, Rr: the parameters of the frame's list `csHead`. born, nMsg: the parameters of the frame's
test on the script. -/
theorem k4_exchange_own_still (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
    (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (ν : Nat) (st : Nat → TS → Prop) (Rr : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st Rr))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens k4LookAt (k4PubAt cF k x)))
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits (k4PubAt cF k x) (k4LookAt (k4PubAt cF k x) fr) (k4Tokens w₁.x) = true)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells
        weights k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    {born : Nat → Nat} {nMsg : Nat}
    (hQf : Q.msgsFit (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.front
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs born nMsg = true)
    (hb0 : ∀ y ∈ pinSeats h.𝔇.N m,
      h.𝔇.arr y.1 y.2 < nMsg ∧ born (h.𝔇.arr y.1 y.2) ≤ k)
    (hc0 : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      CellIsList (k4PubAt cF k x)
        (k4Wit (k4PubAt cF k x) cells weights k4Tokens (k4LookAt (k4PubAt cF k x)) mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input mm.st.heard)).MG g) x.2.hp.tl)
    (hI : Vd w₁ → K4IndexIs Q weights w₁)
    (hVd : Vd w₁ →
      (Zp.s₀.withReq (Verify.words32 w₁.x.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true)
    (hW4 : Vd w₁ → w₁.x.pub.request.size % 4 = 0) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.formsT m 3 "own") :=
  k4_exchange_own_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ ν st Rr hRdIs Said Lh half fits
    hb₀ hKp hMask
    (fun c s mm E hT d =>
      cellIsList_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQf hb0 hT.1
        (hc0 c s mm E hT) d)
    hI hVd hW4

/-- CONDITIONAL: on every hypothesis named; the head lists them. **THE SAME AT THE MAKER's PROVER
AND THE THREAD OF A READY RUN.** -/
theorem k4_exchange_own_still_ready {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {kc : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X'}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk A.H w₀ rc ξ kc = .ok R)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true)
    (ν : Nat) (st : Nat → TS → Prop) (Rr : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st Rr))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread cells
        weights k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    {born : Nat → Nat} {nMsg : Nat}
    (hQf : Q.msgsFit (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.front
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.bs born nMsg = true)
    (hb0 : ∀ y ∈ pinSeats h.𝔇.N m,
      h.𝔇.arr y.1 y.2 < nMsg ∧ born (h.𝔇.arr y.1 y.2) ≤ k)
    (hc0 : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread Said k c s mm E →
      CellIsList (k4PubAt cF k x)
        (k4Wit (k4PubAt cF k x) cells weights k4Tokens (k4LookAt (k4PubAt cF k x)) mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input mm.st.heard)).MG g) x.2.hp.tl)
    (hI : Vd R.own → K4IndexIs Q weights R.own) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread Said k
      (Item.formsT m 3 "own") :=
  k4_exchange_own_ready h Q test carryX item n₁ n₂ b₀ Vd Rd Kp hA hR hx ν st Rr hRdIs Said Lh
    cells weights hM hE ho hb₀ hKp hMask
    (fun c s mm E hT d =>
      cellIsList_thr h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own Lh hQf hb0 hT.1
        (hc0 c s mm E hT) d)
    hI

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_exchange_own_still
#print axioms ProofFile.Honest.K4.W.k4_exchange_own_still_ready
