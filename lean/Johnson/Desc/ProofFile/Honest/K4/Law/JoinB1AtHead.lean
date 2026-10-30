-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinB1AtHead.lean: CONDITIONAL.

What is here. `K4JoinB1` (Law/W/JoinLeftB1.lean: the seven sentences that `k4JoinLeft_of_b1` asks,
at every state behind the step of the member of the feed-forward layers' own rounds, sub-protocol
K4), AT THE THREAD WITH THE LIBRARY's OWN VALUES (`lettersHead`, Honest/Thread/FirstHead.lean), in
the form in which `k4JoinLeft_b1_head` (Law/JoinLeftAtHead.lean) asks it: that statement asks it
behind a guard (for every s0 with JoinPubLeft at s0); hs0 here is that guard's field shape0. At each
state: the structure `K4Stand` (`stand_own_head`, Law/OwnItemHead.lean) and `joinB1_stand_head`
(Law/W/JoinB1Head.lean). One assembly. THE LOOKUP's OWN SENTENCE (the field b1) IS MOVED BY THIS,
NOT SHOWN: it rests on the thread's open item on the keys' worth; the head of Law/W/JoinB1Head.lean
says who owes that.

  `k4JoinB1_head`   **K4JoinB1 at the thread.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). WHAT STAYS, BY
NAME. hW (`K4LayersTieAt`, Law/W/LayersTie.lean), wherever `ThrS` stands: THE LAYERS' MATRICES THAT
THE LOOKUP's CALLER READS OFF THE WITNESS ARE THOSE OF THE INPUT's WEIGHTS: a hypothesis on the
thread's Script and on the private input's weights, asked at every number l of a layer, without a
bound (that file's head says what it asks outside the table of weights); that an honest Script and a
valid input meet it is not shown. hMask (`K4MaskTieAt`, Law/ScriptAt.lean), wherever `ThrS` stands.
half, fits: on the prover's list of halves, and on a public test under the hypothesis that the input
is valid (Vd w₁). Lh, hQ, hx, hs0: on public lists and numbers. OF WHAT ANOTHER SUB-PROTOCOL OWES,
TWO CLAUSES OF THE THREAD ARE SPENT: the sentence of the open item on the keys' worth, in which no
file of K4's honest side ends, and what the public item `.left m` says beside its test; both are
owed behind the member of the lookup on the calls. THAT THE THREAD HOLDS AT ANY RUN, OR THAT ANY
STEP OF THE MEMBER ACCEPTS: the conclusion speaks only where `ThrS` stands and a step accepts. No
example is known of all the hypotheses together; nothing here was evaluated. THE FULL SIZE ALONE,
and the format's second hash function alone (`OnBytes.secondHashFunction`). The import closure holds what the closures
of Law/OwnItemHead.lean and Law/W/JoinB1Head.lean hold. WHAT THIS FILE's IMPORTS REACH, by a
program's walk from import to import that stops, unopened, at every module under Johnson/Goal/,
Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose name begins Cb.Bridge, and at the
names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…: it stopped at 81 modules under
Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/ and none of the three names. What lies
behind the 89 is not counted: all the numbers are floors. THE STATEMENT RESTS ON STATEMENTS OF FILES
UNDER Johnson/Goal/: those that the heads of Law/W/JoinB1Head.lean and Law/OwnItemHead.lean name. A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnItemHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.JoinB1Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Road.K4 (parOf)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt)
open VerifiableInference.Desc.Sound (MsgT matsOfData seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **K4JoinB1 AT THE THREAD.** xl: the lookup's place at the segment. CONDITIONAL: on every
hypothesis named; the head lists them. -/
theorem k4JoinB1_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits Qp (look Qp fr) (tokens w₁.x) = true)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
        tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hW : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4LayersTieAt Q weights xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
        h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW g c mm)
    {s0 : Forest.Shape} (hs0 : Forest.shape Qp.P.y.cl Qp.P.y.h.lidb = .ok s0) :
    K4JoinB1 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k) k cells
      weights tokens look Qp (fun _ Dt => matsOfData x.2.hp.tl (P5J.At.names3 Zp m) Dt)
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) x.2.hp.tl (parOf x)
      (Verify.layerShape (P5J.At.X Zp).P) DF Inst.Model.Layout.kRef Inst.Model.tbRef s0 := by
  intro blk hblk c s mm E ds y cols s' hA _ hS ds' A' hseg o _ F₁ ho hfr
  have Zs := stand_own_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ half fits hblk hA.1
    (hMask c s mm E hA) hS hseg ho
  have hfr' := hfr
  rw [seg_fork hseg ho] at hfr'
  exact joinB1_stand_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ Zs hA.1 hx
    (hW c s mm E hA) ds' hs0 (OnBytes.Desc.First.K4.formsFrontWith_later hfr')

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4JoinB1_head
