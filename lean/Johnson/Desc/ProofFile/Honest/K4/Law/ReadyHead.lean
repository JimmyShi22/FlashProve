-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ReadyHead.lean: CONDITIONAL.

What is here. THE STATE IN FRONT OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol
K4; `K4ReadyS`, Law/HearsShape.lean) WHEREVER A THREAD OF THE FIRST CHAIN STANDS THERE, at the
public files' own data, any prover and a run's input (`lettersHead`, Honest/Thread/FirstHead.lean);
and so the thread's debt `AcceptedS` at that member. Definitions (a test on the table, a
hypothesis's form), statements and proofs: decisions of Lean's kernel, then calls.

  `k4PrevFitAt`, `k4_prev_full`, `k4_prev_other`, `prev_at`   a test: right in front of every place
      of the sub-protocol stands piece 2 of the same segment; BY LEAN's KERNEL: true; asked with
      piece 1 (a negative test): false.
  `K4LookLaid bs st j par`   the hypothesis on the member number j. `k4ReadyS_head` and
      `k4_accepted_head` ask it under what `prev_at` says of the written place number j. That the
      chain's member number j stands at that place and passes its test on the plan is not shown
      here: Law/LookMemberHead.lean has it under h.
  `k4ReadyS_head`   **K4ReadyS wherever the thread stands in front of the member**: all but
      K4LookRest and the tokens out of the promise in front (`k4ReadyS_of_promise`,
      Law/LookOfPromise.lean; the open public items' tests by `thr_pub`,
      Honest/Thread/FormLaw.lean); K4LookRest one step back along the thread (`thr_back_head`,
      Honest/Thread/ReachFacts.lean).
  `k4_heard_head`   **the sixth fact of `K4Fence` wherever the thread stands there**: out of the
      promise in front: in the form of the hypothesis heard of `k4_behind_head`
      (Law/BehindHead.lean).
  `k4_accepted_head`   **`AcceptedS` at the member.**

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: this file gives no example (by binder, beside
h: `k4ReadyS_head`: hH, A, Sx, Sd, hn, h1, h2, h3, hb, hLook, hT, htk · `k4_heard_head`: hH, A, Sx,
Sd · `k4_accepted_head`: Se, hBk, hPl, hSh, hH, A, Sx, Sd, hn, h2, hb, hLook, hTok, hf). WHAT IS
ASKED, WITH WHERE IT IS SHOWN OR WHO IS MEANT TO PROVE IT: the hypothesis h : AtMgA · four of the
library's `eleven_at_all`'s hypotheses (hH · AtK4 · K4OnX · K4OnD: by name in Law/PromiseAll.lean's
head; Law/ElevenHead.lean shows them under h and `LaidK4`) · four comparisons of public numbers (hn
· la ≤ dT · lt ≤ dT · the shape's calls are as many as the layout's; in `k4_accepted_head` the
second and the fourth come out of `k4ShapeB`) · that k is a border of the chain · **`K4LookLaid`:
behind the accepting step of the member that stands right in front of ours, from a reached state,
what the lookup has heard has `K4LookRest`** (Law/LookOfPromise.lean: the calls' points end as the
lookup's own; its weights are as many as its shape's calls): IT STANDS UNDER h AND `LaidK4`
(Law/LookMemberHead.lean; Law/LookJoin.lean, by a statement of the writers of Honest/K3/) · the test
on the state's tokens wherever the thread stands: it stands under h and `LaidK4`
(Law/TokensHead.lean). For `AcceptedS` beside: `K4SeatedA` (Law/SeatedA.lean) · `K4SitsBack`
(Law/Accepted.lean) · the tests on the plan `k4PlanB` and `k4ShapeB` (an evaluation gives no term;
under h and `LaidK4` the proof of `k4_accepted_one`, Law/PublicOne.lean, has both from the test
`k4PublicX`, which Law/DearX.lean has under h (`publicX_head`)) · the fall's tie. THE MEMBER's STEP
TESTS NO SENT VALUE: it accepts every play of the right shape, a false one too. THE FULL SIZE ALONE,
and at `OnBytes.secondHashFunction`, the format's second hash function, alone. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one: its imports reach Johnson/Goal/.
Following import lines, and stopping unopened at every module under Johnson/Goal/, Johnson/D/,
Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its imports reach 57
modules under Johnson/Goal/, 6 under Johnson/Bridge/ and 1 whose name begins Cb.Bridge, and none of
the others; what lies behind these is not counted; 46 of the modules that it reaches have RecCompile
in their names, none of them RecCompile's Honest*, Both or PassH*. An earlier walk, which opened
every module that it reached, counted 152 modules under Johnson/Goal/, 53 whose name holds
RecCompile and 140 under ThirdParty/; another, which stopped unopened at Johnson/Goal/, Johnson/D/
and ThirdParty/ alone, met 2 modules under ThirdParty/. `Behind` and `AcceptedS` speak only where
the thread stands: that it stands at any run is not shown. NOT COMPLETENESS.

Kin. `k4PrevFitAt` is the library's `atK4s` (Johnson/Road/K4/Riders/PlanTests.lean: at every place
of K4's a test on the border's number and the segment's) at a test of its own; `k4NumsFitAt`
(Law/SeatedHead.lean) is it at another. `k4_accepted_head` calls `k4_accepted_ready_said`
(Law/HearsSeated.lean), which has the debt at any thread; `k4_accepted_all` (Law/ElevenHead.lean)
has Se, hBk, hH, A, Sx, Sd and hb from `LaidK4`, hQ and half. Another kind's like law at its own
member, at the same thread: `k13_accepted_at_head_filler` (Honest/K13/AcceptedAtHeadFiller.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LookOfPromise
import Johnson.Desc.ProofFile.Honest.K4.Law.HearsSeated
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.FormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Road.K4 (AtK4 K4OnX K4OnD)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.Riders (atK4s atK4s_at)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Block)
open VerifiableInference.Desc.First (S onAt openSets pubSets start)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT WideData linksFull mgAll_more_base)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_back_head thr_pub noStrs)

/-! ## 1 What stands right in front -/

/-- A TEST ON THE TABLE, at the full size's written lists: right in front of every place of the
sub-protocol stands piece number c of the same segment. -/
def k4PrevFitAt (c : Nat) : Bool :=
  atK4s linksFull PS fun k m =>
    decide (0 < k) && (PS[k - 1]?).any fun q => q.link == some m && q.piece == c

set_option maxRecDepth 1000000 in
theorem k4_prev_full : k4PrevFitAt 2 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test. -/
theorem k4_prev_other : k4PrevFitAt 1 = false := by decide +kernel

theorem prev_at {k m : Nat} {pl : Place} (H : AtK4 linksFull PS k m pl) :
    ∃ j q, k = j + 1 ∧ PS[j]? = some q ∧ q.link = some m ∧ q.piece = 2 := by
  have h0 := k4_prev_full
  unfold k4PrevFitAt at h0
  have h := atK4s_at H h0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hq⟩ := h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hq
  cases e : PS[j]? with
  | none =>
    rw [e] at hq
    cases hq
  | some q =>
    rw [e] at hq
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hq
    exact ⟨j, q, rfl, e, hq.1, hq.2⟩

/-- **Behind the accepting step of the member number j, from a reached state, what the lookup has
heard has what stays to be asked of it.** This defines a hypothesis; the definition claims nothing.
-/
def K4LookLaid {P : Type} (bs : List (Block S Claim)) (st : P → S) (j : Nat) (par : Par) : Prop :=
  ∀ blk, bs[j]? = some blk → ∀ (z : P) s₀ s, Reach 0 bs st j (z, s₀) → StepYes 0 blk s₀ s →
    ∀ fo, seatS.look s = some fo → K4LookRest par fo

/-! ## 2 At the thread -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE STATE IN FRONT, AT A STAND OF THE THREAD THERE.** E₀: any value serves. -/
theorem k4ReadyS_head (E₀ : WideData ProofFile.InstPub) {k m : ℕ} {pl : Place} {par : Par} {n k' : ℕ}
    {pol KL : ByteArray} {layout : Option ByteArray}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) (Sd : K4OnD h.𝔇 m par n)
    (hn : n + (k4Takes par.P par.hp par.g + k') ≤ par.hp.ns)
    (h1 : par.P.y.h.la ≤ par.P.y.fo.dT) (h2 : par.P.y.h.lt ≤ par.P.y.fo.dT)
    (h3 : par.P.y.fo.calls.size = par.P.y.calls.size) (hb : k ≤ cF.blocksInOrder.length)
    (hLook : ∀ j q, k = j + 1 → PS[j]? = some q → q.link = some m → q.piece = 2 →
      K4LookLaid cF.blocksInOrder (ProofFile.startS Zp) j par) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E)
    (htk : tokensFit { par.P with tokv := seatS.tokv s } par.g = true) : K4ReadyS par s := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -⟩ := hT'
  have hm : s.failed = none := by
    have e : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.mp e
  have ha : onAt (P5J.At.N Zp cF) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
      linksFull PS[k]? ((openSets linksFull PS (start linksFull))[k]?.getD [])
      ((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more linksFull
        PS)[k]?.getD []) (mm.st.input.x.pub, s) noStrs := hF.2
  have hB := (ha.2.resolve_left fun e => e hm).1
  simp only [Bool.and_eq_true] at hB
  have b1 := hB.1.1.1.1.1
  rw [A.here] at b1
  refine k4ReadyS_of_promise (Dm := h.𝔇) E₀
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP) rfl
    (mgAll_more_base h.𝔇) hH A Sx Sd hm b1
    (fun q hq => thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT hq) hn h1 h2 h3
    ?_ htk
  obtain ⟨j, q, rfl, q1, q2, q3⟩ := prev_at A
  obtain ⟨s₀, blk, hblk, hr, hy⟩ :=
    thr_back_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  exact hLook j q rfl q1 q2 q3 blk hblk _ s₀ s hr hy

/-- **THE SIXTH FACT OF `K4Fence`, WHEREVER THE THREAD STANDS IN FRONT OF THE MEMBER**: in the very
form of `k4_behind_head`'s hypothesis heard (Law/BehindHead.lean). E₀: any value serves. -/
theorem k4_heard_head (E₀ : WideData ProofFile.InstPub) {k m : ℕ} {pl : Place} {par : Par} {n : ℕ}
    {pol KL : ByteArray} {layout : Option ByteArray}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) (Sd : K4OnD h.𝔇 m par n) :
    ∀ c s mm E, Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E →
      ∀ al fo', s.here = .lay al → al.fo = some fo' → fo'.shape = (P5J.At.X Zp).y.fo := by
  intro c s mm E hT
  obtain ⟨t1, t2⟩ := two_tests (Dm := h.𝔇) E₀
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP) rfl
    (mgAll_more_base h.𝔇) hH A Sx Sd
    (fun q hq => thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT hq)
  exact heard_of_tests Sx t1 t2

/-- **`AcceptedS` AT THE MEMBER, AT THAT THREAD.** CONDITIONAL: see the head. -/
theorem k4_accepted_head (E₀ : WideData ProofFile.InstPub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m : ℕ} {pl : Place}
    {par : Par} {n k' : ℕ} {pol KL : ByteArray} {layout : Option ByteArray} {cells : Tr → Cells}
    {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {blk₀ : Block S Claim} {fall : Nat → S → List Fmt.Drawn → Option String}
    (Se : K4SeatedA (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      tokens look Qp par blk₀)
    (hBk : K4SitsBack (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k par)
    (hPl : k4PlanB par = true) (hSh : k4ShapeB par = true)
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) (Sd : K4OnD h.𝔇 m par n)
    (hn : n + (k4Takes par.P par.hp par.g + k') ≤ par.hp.ns)
    (h2 : par.P.y.h.lt ≤ par.P.y.fo.dT) (hb : k ≤ cF.blocksInOrder.length)
    (hLook : ∀ j q, k = j + 1 → PS[j]? = some q → q.link = some m → q.piece = 2 →
      K4LookLaid cF.blocksInOrder (ProofFile.startS Zp) j par)
    (hTok : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said k c s mm E →
      tokensFit { par.P with tokv := seatS.tokv s } par.g = true)
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero Qp ds = none) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k := by
  have e := hSh
  unfold k4ShapeB at e
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at e
  have h1 : par.P.y.h.la ≤ par.P.y.fo.dT := e.1.2
  have h3 : par.P.y.fo.calls.size = par.P.y.calls.size := e.2
  exact k4_accepted_ready_said Said Se hBk hPl
    (fun c s mm E hTS => k4ReadyP_of_S hSh
      (k4ReadyS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w E₀ hH A Sx Sd hn h1 h2 h3 hb
        hLook hTS.1 (hTok c s mm E hTS))) hf

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.k4PrevFitAt
#print axioms ProofFile.Honest.K4.k4_prev_full
#print axioms ProofFile.Honest.K4.k4_prev_other
#print axioms ProofFile.Honest.K4.prev_at
#print axioms ProofFile.Honest.K4.K4LookLaid
#print axioms ProofFile.Honest.K4.k4ReadyS_head
#print axioms ProofFile.Honest.K4.k4_heard_head
#print axioms ProofFile.Honest.K4.k4_accepted_head
