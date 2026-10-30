-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OwnItemHead.lean: CONDITIONAL: on the library's hypothesis h
on the public files, on LaidK4 and on what each statement names. THE FULL SIZE ALONE.

What is here. Nine lemmas about the thread built by `lettersHead` (Honest/Thread/FirstHead.lean),
at the step of sub-protocol K4 (the feed-forward layers' own rounds). Each is a premise of one of
two laws, `k4JoinLeft_of_b1` (Law/W/JoinLeftB1.lean) and `k4_exchangeAtS_own_of_join`
(Law/W/FootJoin.lean), or a step to such a premise. seated_own_head, lookTie_all_head,
cellsTie_all_head and k4Front_own_head are what both take as hSeat, hLook, hCells and hF;
wsFacts_pub_head's eight are the second's hws, hd, hfe, hdq, hf, hfef, hNE and hlt, of which the
first takes hws and hdq; rd_step_head, behind_own_head and symsTie_all_head are steps to these;
stand_own_head is a binder of neither: laws at one state take it. `k4_exchange_tenth`
(Law/ExchangeTenth.lean) makes the same nine inside its own proof and does not call these; the
proofs here are taken from that proof. Nothing new is shown. hSit is `k4Sits_head`
(Law/SeatedHead.lean), the plan is `plan_head` (Law/W/PlanHead.lean), hM is rfl, hAt is the first
half of ThrS; hMask stays a hypothesis.

  `rd_step_head`   the riders' clause passes the member's step, at the frame's list csHead.
  `behind_own_head`   Behind at the member.
  `lookTie_all_head`   K4LookTieAt wherever the thread stands, from LookIsK3.
  `symsTie_all_head`   K4SymsTieAt wherever the thread stands.
  `cellsTie_all_head`   K4CellsTieAt wherever the thread stands, from hA and hc.
  `seated_own_head`   K4Seated at every block laid at the member's number.
  `k4Front_own_head`   **K4Front at ThrS.**
  `wsFacts_pub_head`   eight facts on the layout of the committed weights, in the letters of Qp.
  `stand_own_head`   K4Stand at a state behind the member's step.

Not shown here. THAT ANY HYPOTHESIS HOLDS: half, fits, hb₀, hKp, hRdIs, hL, hA, hc and the tie on
the mask row (hMk) are hypotheses, as in Law/ExchangeTenth.lean, whose head says of each what it
asks. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean) on the public files; the
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with Lh, hQ, half, fits, hb, hT, hMk, hS, hseg and ho (`stand_own_head`)
no example is known to us; nor of h together with what one of the seven lemmas before it that take h
asks: each a part of Lh, hQ, half, fits, hRdIs, hb₀, hKp, hl, hL, hx, hA and hc, as the lemma's own
statement has it. `rd_step_head` takes no h. No test that can fail stands beside them. THAT THE
THREAD HOLDS AT ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: where ThrS stands nowhere, or no
step accepts, the statements at a state hold emptily. THE FULL SIZE ALONE, and the format's second
hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. Every
module that the walk saw lies in the import closure of Law/ExchangeTenth.lean, by the same walk.
THE STATEMENTS REST ON STATEMENTS OF FILES UNDER Johnson/Goal/; of those that
Law/ExchangeTenth.lean's head names, `Meaning.P34.pub34_all` is reached here through
`wsFacts_head`, `P5J.pins_of_laid` through `front_head`, and `Meaning.scope_plans` and
`OnBytes.Road.Hd.core_of_scope` through `symsTie_head`. Through Law/LookPtsHead.lean it imports
Honest/K3/Law/Thread/LayersTieHead.lean, and through Law/RdAtCsHead.lean Honest/Thread/CsHead.lean:
files of two other authors. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ExchangeParts
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ReadersHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OneTie
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsTieOf
import Johnson.Desc.ProofFile.Honest.K4.Law.W.TestHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.WsFactsHead
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontHead
import Johnson.Desc.ProofFile.Honest.K4.Law.StatedHead
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Desc.ProofFile.Honest.K4.Law.LookPtsHead
import Johnson.Desc.ProofFile.Honest.K4.Law.RdAtCsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road (cellsOf cellsAt pt)
open OnBytes.Road.K4 (entryTrue parOf)
open OnBytes.Road.K4.W (OwnBack LookLeft uEOf)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim xS)
open VerifiableInference.Desc (Place Chain Strs Block Link Claim First.S)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Look (layAt MatsAre)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgT MsgQ dataQ matsOfData seatTab)
open VerifiableInference.Desc.Plain.K04 (frontRun)
open VerifiableInference.OnPublicFiles (layMs)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Sits_head)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4 (StatedAt readsArrayB k4PlaceAt)
open VerifiableInference.Desc.K9 (LinkHoles)
open VerifiableInference.Desc.Sound (Stated second)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Model.Layer (ClaimEnv)
open ProofFile.Honest.K4.SeatedHead (pub_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The riders' clause passes the member's step.** CONDITIONAL: on hRdIs and Lh. -/
theorem rd_step_head (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st R))
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    ∀ v s s', Rd k v s → K4KeepsM s s' → Rd (k + 1) v s' := by
  intro v _ s₂ _ hK
  rw [hRdIs, Lh.num]
  exact rd_csHead ν st R Lh.lt v hK

/-- **Behind at the member.** CONDITIONAL: on h and every hypothesis named. -/
theorem behind_own_head (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st R))
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s') :
    Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k :=
  k4_behind_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ (atK4_of_laid Lh) hb₀ hKp
    (rd_step_head Rd ν st R hRdIs Lh)

/-- **The tie on what the lookup has heard, wherever the thread stands.** CONDITIONAL: on h, Lh and
hL. -/
theorem lookTie_all_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hL : ∀ ξ, LookIsK3 look Qp Zp cF g ξ) : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4LookTieAt look Qp s mm :=
  fun _ _ mm _ hT => lookTie_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT.1
    (hL mm.st.input.x)

/-- **The tie of the two readers of one witness, wherever the thread stands.** CONDITIONAL: on h,
Lh and hx. -/
theorem symsTie_all_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl) :
    ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4SymsTieAt Q xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
        (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW (P5J.At.names3 Zp m)
        (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm :=
  fun _ _ _ _ hT => symsTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT.1 hx

/-- **The tie on the cells, wherever the thread stands.** CONDITIONAL: on h, Lh, hx, hA and hc. -/
theorem cellsTie_all_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (hA : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∀ d, MatsAre xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
        (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1)
          h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ d)))
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g))
    (hc : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∀ d, CellIsList Qp (k4Wit Qp cells weights tokens (look Qp) mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) x.2.hp.tl) :
    ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4CellsTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells
        weights tokens look Qp x.2.hp.tl (P5J.At.names3 Zp m) (h.𝔇.N.sent m 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm :=
  fun c s mm E hT => cellsTie_of_tie h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (symsTie_all_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Said Lh hx c s mm E hT)
    (hA c s mm E hT) (hc c s mm E hT)

/-- **K4Seated at every block laid at the member's number.** CONDITIONAL: on h, Lh, hQ, half and
fits. -/
theorem seated_own_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits Qp (look Qp fr) (tokens w₁.x) = true) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells weights
        tokens look Qp (parOf x) blk :=
  seated_all_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ half
    (front_head h Lh hQ) fits

/-- **K4Front AT ThrS.** CONDITIONAL: on h and every hypothesis named. l: the link at the member's
segment. -/
theorem k4Front_own_head (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st R))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    {l : Link TS ProofFile.Cl} (hl : h.𝔇.lk m = some l) :
    K4Front (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k) k
      (fun _ Dt => matsOfData x.2.hp.tl (P5J.At.names3 Zp m) Dt) (holesK4 Zp m l) l h.𝔇.St
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) x.2.hp.tl (parOf x) :=
  k4Front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hl
    (At := ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k)
    (M := fun _ Dt => matsOfData x.2.hp.tl (P5J.At.names3 Zp m) Dt) (Hh := holesK4 Zp m l)
    (St := h.𝔇.St) (own := h.𝔇.N.sent m 0) (rdOf := seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms)
    (tl := x.2.hp.tl)
    (fun _ hb _ _ _ _ _ _ _ _ hT hd hS _ =>
      ⟨asks_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT.1 hS,
        ProofFile.Honest.K4.names_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT.1 hS,
        reads_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT.1 hS,
        fun A' o cc h1 h2 h3 h4 =>
          stated_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT.1 hS A' o cc h1 h2 h3
            h4 _ _,
        test_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
          (behind_own_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ ν st R hRdIs Lh hb₀ hKp)
          Lh hl hb hT.1 hd hS⟩)

/-- **Eight facts on the layout of the committed weights, in the letters of Qp.** CONDITIONAL: on
h, Lh and hQ. h is bound in the statement itself: nothing else in it names the variable h. -/
theorem wsFacts_pub_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) :
    wsLayOf (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y) true Inst.Model.Layout.kRef =
        .ok Qp.P.wsLay ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).d = Qp.P.y.h.d ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).fe = Qp.P.y.h.fe ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).dq ≤ Qp.P.y.dq ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).f ≤ Qp.P.y.h.f ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).fe ≤ Qp.P.y.h.f ∧
      (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y).NE ≤ Qp.P.y.h.NE ∧
      1 ≤ Qp.P.y.h.lt := by
  obtain ⟨⟨eP, _, _, _, _⟩, _, _, _⟩ := pub_of Lh hQ
  have eP' : (parOf x).P = Qp.P := eP
  have W := wsFacts_head h Lh
  rw [eP'] at W
  exact W

/-- **K4Stand at a state behind the member's step.** CONDITIONAL: on h and every hypothesis named.
hMk: the tie on the mask row at that state. -/
theorem stand_own_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits Qp (look Qp fr) (tokens w₁.x) = true)
    {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk)
    {c : Coins Bk} {s s' : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hMk : K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells
      weights tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds
      y cols s')
    {A' : VerifiableInference.Desc.K9.Part} (hseg : segAt? s' = some A') {o : Own}
    (ho : seatS.own s' = some o) :
    K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells weights
      tokens look Qp (parOf x) blk (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm E ds
      y cols s' A' o := by
  obtain ⟨_, _, Ak⟩ := asks_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hb hT hS
  exact ⟨seated_own_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ half fits blk hb,
    k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh, Ak.sized, hMk, hS, hseg, ho⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.rd_step_head
#print axioms ProofFile.Honest.K4.W.behind_own_head
#print axioms ProofFile.Honest.K4.W.lookTie_all_head
#print axioms ProofFile.Honest.K4.W.symsTie_all_head
#print axioms ProofFile.Honest.K4.W.cellsTie_all_head
#print axioms ProofFile.Honest.K4.W.seated_own_head
#print axioms ProofFile.Honest.K4.W.k4Front_own_head
#print axioms ProofFile.Honest.K4.W.wsFacts_pub_head
#print axioms ProofFile.Honest.K4.W.stand_own_head
