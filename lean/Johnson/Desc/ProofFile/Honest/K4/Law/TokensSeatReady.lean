-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokensSeatReady.lean: CONDITIONAL.

What is here. hVd, hTk AND `K4Seated` (Law/TokensSeatMark.lean) FROM THE PREMISE hmark OF
`enters_head` (Honest/Thread/EntersHead.lean) TO THE LETTER. hVd: a valid input's request passes
the verifier's public test on its words (reqFine). hTk: the test on the tokens holds at the
member's public data and the lot's own reader of the tokens. That lemma has hmark at the instance ξ
of the run: the chain's first state at ξ.pub bears no mark. Law/TokensSeatMark.lean asks it at the
input's own instance, w.x.pub, and the thread stands at w := R.own, the input of a run that is
ready. That R.own.x is ξ is no unfolding: it comes of `ready_ok` (Honest/Law/Run.lean). Here it is
a lemma by name (own_x_of_ready), and the three laws are stated at hR and at hmark as `enters_head`
has them. The example at the foot calls `enters_head` and k4Seated_ready at one hR and one hmark.
reqFine_blank ties reqFine to the state at which Law/ReqEnds.lean tries the verifier's test.

  `own_x_of_ready`   the instance in a ready run's input is the run's. General in the description.
  `hmark_own`        hmark at the input's own instance.
  `hVd_ready`, `hTk_ready`   **hVd, at every Vd; hTk.**
  `k4Seated_ready`   **`K4Seated` at tokens := `k4Tokens`, from hR, half, hLk and hmark.**
  `reqFine_blank`    reqFine is the verifier's test at the blank state with the request laid.

Not shown here. hR AND hmark ARE HYPOTHESES: that a run is ready; that the start bears no mark: it
bears one at a request that the verifier's test on its words refuses, and wherever the public
part's first state bears one. That h can hold: no example of h is shown here. half and hLk:
hypotheses, as in Law/SeatedMember.lean. It reads only the public request: nothing on the model's
values at these tokens. hTk_ready and k4Seated_ready: only for the full-size model and the format's
second hash function (h); the four other names are general in the sizes.

No property is claimed. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: its imports reach modules under Johnson/Goal/, as those of
Law/TokensSeat.lean do.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensSeatMark
import Johnson.Desc.ProofFile.Honest.K4.Law.ReqEnds
import Johnson.Desc.ProofFile.Honest.Thread.EntersHead
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead enters_head)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **The instance in a ready run's input is the run's.** General in the description, the book and
the prover. CONDITIONAL: on hR. -/
theorem own_x_of_ready {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {B : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {ξ : Xi} {kc : Coins B}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (hR : ready F B H w₀ rc ξ kc = .ok R) : R.own.x = ξ := by
  obtain ⟨-, _, -, hown, -, -, -, -⟩ := ready_ok hR
  rw [hown]

/-- reqFine is the verifier's test at the library's blank state with the request's words laid. -/
theorem reqFine_blank (Zp : ProofFile.Pub) (p : ProofFile.InstPub) :
    reqFine Zp p = (S.blank.withReq (Verify.words32 p.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V := by
  show (Zp.s₀.withReq (Verify.words32 p.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = _
  exact reqOk_req rfl _ _

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
  {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {kc : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X'}

/-- hmark at the input's own instance. CONDITIONAL: on hR and hmark. -/
theorem hmark_own {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X'}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    (ProofFile.startS Zp R.own.x.pub).failed = none := by
  rw [own_x_of_ready hR]
  exact hmark

/-- CONDITIONAL on hR and hmark. **hVd**, at every Vd. -/
theorem hVd_ready {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X'}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    Vd R.own → reqFine Zp R.own.x.pub = true :=
  hVd_of_mark Vd R.own (hmark_own hR hmark)

include h in
/-- CONDITIONAL on h, `LaidK4`, hR and hmark. **hTk.** -/
theorem hTk_ready {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X'} (Lh : LaidK4 Zp cF k m g x blk)
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    Vd R.own → k4TokensFit (k4PubAt cF k x) (k4Tokens R.own.x) = true :=
  hTk_of_mark h Vd R.own Lh (hmark_own hR hmark)

/-- CONDITIONAL on h, `LaidK4`, hR, half, hLk and hmark. **`K4Seated` AT THE THREAD OF A READY RUN,
AT THE LOT's OWN READER OF THE TOKENS.** -/
theorem k4Seated_ready (Lh : LaidK4 Zp cF k m g x blk)
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ kc = .ok R) {cells : Tr → Cells}
    {weights : W₀ → Weights} {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens look (k4PubAt cF k x)))
    (hLk : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true →
      k4LookFits (k4PubAt cF k x) (look (k4PubAt cF k x) fr) = true)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k cells weights
      k4Tokens look (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_mark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own Lh half hLk (hmark_own hR hmark)

/- one hR and one hmark serve `enters_head` and k4Seated_ready -/
example (Lh : LaidK4 Zp cF k m g x blk)
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ kc = .ok R) (hb₀ : 0 < b₀)
    (hV : Vd R.own) (hRd : Rd 0 R.own (ProofFile.startS Zp ξ.pub))
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none)
    (hP : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.formP 0
      (ξ.pub, ProofFile.startS Zp ξ.pub))
    (hItems : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.Items
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.opened 0) kc
      (ProofFile.startS Zp ξ.pub) (R.start₁ H) (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens look (k4PubAt cF k x)))
    (hLk : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true →
      k4LookFits (k4PubAt cF k x) (look (k4PubAt cF k x) fr) = true) :
    Enters₁ (F0T OnBytes.secondHashFunction Zp Np cF) H
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread w₀ rc ξ kc R ∧
      K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k cells weights
        k4Tokens look (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  ⟨enters_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp hR hb₀ hV hRd hmark hP hItems,
    k4Seated_ready h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp Lh hR half hLk hmark⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.own_x_of_ready
#print axioms ProofFile.Honest.K4.reqFine_blank
#print axioms ProofFile.Honest.K4.hmark_own
#print axioms ProofFile.Honest.K4.hVd_ready
#print axioms ProofFile.Honest.K4.hTk_ready
#print axioms ProofFile.Honest.K4.k4Seated_ready
