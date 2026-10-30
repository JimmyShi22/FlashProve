-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/JoinB1Head.lean: CONDITIONAL.

What is here. `JoinB1At` (Law/W/JoinLeftB1.lean: the seven sentences that `k4JoinLeft_of_b1` asks at
a state behind the step of the member of the feed-forward layers' own rounds, sub-protocol K4), AT
THE THREAD WITH THE LIBRARY's OWN VALUES (`lettersHead`, Honest/Thread/FirstHead.lean), at a state
with an accepted step of the member (`K4Stand`, Law/SlotsTrue.lean). Beside the hypotheses of
`b1_thread_head` (Law/W/B1Head.lean) it asks one more: the tie on the weights (`K4LayersTieAt`,
Law/W/LayersTie.lean). The five sentences on what the lookup has heard are the library's
`LookLines`, by its `look_of_left` (Johnson/Road/K4/LookOfLeft.lean) from `K3Left`, which the public
item `.left m` holds (`left_of_promise`, Law/W/StandsHead.lean). The rotary table: `rope_head`
(Law/W/RopeHead.lean). The lookup's own sentence b1: `b1_thread_head`, out of the thread's open item
on the keys' worth, at the key vectors of `keyVec_stand` (Law/W/KeysLettersHead.lean), with three
rewritings (the environment's points are the heard ones; the padding's number has two names; a
return of the run "back" leaves a later ledger); the data's matrices are what the lookup's caller
reads (`mats_of_syms`, with `symsTie_head`, as in Law/W/NuCutHead.lean). b1 IS SO MOVED, NOT SHOWN:
see below. The proofs are chains of calls.

  `trees_head`   the plan's trees are the library's at the reference sizes; eight calls.
  `lookLines_head`   the library's LookLines at such a state.
  `joinB1_stand_head`   **JoinB1At at such a state.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN, OR
THAT ANY STEP OF THE MEMBER ACCEPTS: hT and Zs are hypotheses; Zs holds a tie on the thread's Script
(its field mask). OF WHAT ANOTHER SUB-PROTOCOL OWES, TWO CLAUSES OF hT ARE SPENT. (1) THE SENTENCE
OF THE OPEN ITEM ON THE KEYS' WORTH: it is owed behind the member of the lookup on the calls, and no
file of K4's honest side ends in it: whoever shows it must show that the lookup's join is worth 0 at
the reading of the places that the lookup's caller makes off the witness and at the caller's key
vectors off the witness, at every continuation of the challenges. (2) What the public item `.left m`
says beside its test: the library proves that a yes of the lookup's block leaves it
(`k3LeavesAtCalls`, Johnson/Top/H/K3CEnd.lean); that it stands in the thread is not shown here.
Beside these, clauses of the frame's own are spent: the form's public tests, what the thread says of
how the state was made, and the runs that it says were made (through `maskCut_head`, `symsTie_head`,
`lookTie_head`, `joinAt_shown`). tieW: THE LAYERS' MATRICES THAT THE LOOKUP's CALLER READS OFF THE
WITNESS ARE THOSE OF THE INPUT's WEIGHTS: a hypothesis on the thread's Script and on the private
input's weights; it is asked at every number l of a layer, without a bound: by the head of
Law/W/LayersTie.lean, where the library's layerR reads outside the table of weights it is a sentence
on the input's reader there, which a reader that is 0 there meets and another may fail; that an
honest Script and a valid input meet it is not shown. Lh, hQ, hx, hs0: on public lists and numbers.
No example is known of all the hypotheses together; nothing here was evaluated. THE FULL SIZE ALONE,
and the format's second hash function alone (`OnBytes.secondHashFunction`). The import closure holds what the closures
of Law/W/B1Head.lean, Law/W/JoinLeftB1.lean, Law/W/RopeHead.lean, Law/W/KeysLettersHead.lean and
Johnson/Road/K4/LookOfLeft.lean hold. WHAT THIS FILE's IMPORTS REACH, by a program's walk
from import to import that stops, unopened, at every module under Johnson/Goal/, Johnson/D/,
Johnson/Bridge/ or ThirdParty/, at every module whose name begins Cb.Bridge, and at the names
RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…: it stopped at 71 modules under
Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/ and none of the three names. What lies
behind the 79 is not counted: all the numbers are floors. THE STATEMENTS REST ON STATEMENTS OF FILES
UNDER Johnson/Goal/: `trees_head` calls `refPub_in_scope` (Johnson/Road/K4/RefInScope.lean), whose
lines and rotary tables' fit are, by that file's own head, the landed `Meaning.P34.pub34_all`, field
for field; `rope_head` and `lam_head` rest on the same; `symsTie_head` and, through
`b1_thread_head`, `maskCut_head` on `Meaning.scope_plans` and `OnBytes.Road.Hd.core_of_scope`
(Law/W/ReadersHead.lean's head names the files). A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one. Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.B1Head
import Johnson.Desc.ProofFile.Honest.K4.Law.W.JoinLeftB1
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RopeHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.KeysLettersHead
import Johnson.Road.K4.LookOfLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own HPlan2)
open OnBytes.Desc.First.K4 (Par formsBack_later)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road (TreesFit sclOf)
open OnBytes.Road.K4 (eAll refPub_in_scope LookLines look_of_left steps_ok env_of_hear entryTrue)
open OnBytes.Road.K4.W (mats_of_syms syms_of_plain)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt matsOfE msgLay)
open VerifiableInference.Desc.Sound (MsgT dataQ matsOfData mgAll_more_base seatTab)
open VerifiableInference.OnPublicFiles (layMs layMu)
open VerifiableInference.PlanWritten (publicSteps_of)
open Inst.Model (tbRef)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pubP)
open ProofFile.Honest.K4.SeatedHead (LaidK4 pub_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **The plan's trees are the library's at the reference sizes; there are eight calls.**
CONDITIONAL: on h, hg and hG. -/
theorem trees_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) :
    TreesFit (P5J.At.X Zp).y.fo DF ∧ (P5J.At.X Zp).y.fo.NC = 8 := by
  obtain ⟨_, HL, _⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have PL := HL #[]
  obtain ⟨h8, Hc⟩ := OnBytes.Road.lines_calls PL.hN
  have T : TreesFit (P5J.At.X Zp).y.fo DF :=
    OnBytes.Road.treesFit_of_layout
      (v := ⟨(P5J.At.X Zp).y, (P5J.At.X Zp).layers.sc, g, 0, 0, [], #[]⟩) PL.hy PL.S PL.Z PL.hc h8
      fun cc => by
        obtain ⟨cd, a1, a2⟩ := Hc cc
        exact ⟨cd, a1, a2, PL.hfl cc⟩
  exact ⟨T, (OnBytes.Road.fo_of_layout PL.hy).2.1.trans
    ((OnBytes.Road.fo_of_layout PL.hy).2.2.trans h8)⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE LIBRARY's LookLines AT A STATE WITH AN ACCEPTED STEP**: five sentences on what was heard.
CONDITIONAL: on h, Lh, hQ, Zs, hT and hs0. -/
theorem lookLines_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {p : Par} {blk : Block TS ProofFile.Cl} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {s0 : Forest.Shape} (hs0 : Forest.shape Qp.P.y.cl Qp.P.y.h.lidb = .ok s0) :
    LookLines Qp.P o.H.fo s0 := by
  have N := nine_head h Lh
  obtain ⟨eY, _, _⟩ := pub_is Lh hQ
  obtain ⟨_, F1, g₁, rs, _, _, L, hh, _⟩ := left_of_promise (Dm := h.𝔇)
    (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH (atK4_of_laid Lh) N.Sx
    (fun _ hq => thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  obtain ⟨g', hg1, hg2, _⟩ := lookTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT
    (look := fun _ _ => g₁) (Qp := Qp) fun g₂ h2' => by
      obtain rfl : g₁ = g₂ := Option.some.inj (hh.symm.trans h2')
      exact ⟨rfl, rfl, rfl⟩
  obtain rfl : g' = o.H.fo := Option.some.inj (hg2.symm.trans (stand_look Zs))
  obtain rfl : g₁ = o.H.fo := Option.some.inj (hh.symm.trans hg1)
  obtain ⟨s1, pb, h1, e⟩ := OnBytes.Road.shape_of_layout (k4Plan_head h Lh.lt Lh.hp #[]).lay
  have hs0' : Forest.shape (P5J.At.X Zp).y.cl (P5J.At.X Zp).y.h.lidb = .ok s0 := by
    rw [← eY]
    exact hs0
  obtain rfl : s1 = s0 := Except.ok.inj (h1.symm.trans hs0')
  exact (look_of_left L (Pp := Qp.P) (congrArg (·.fo) eY) ⟨pb, e⟩ (_root_.Fo.Later.refl F1)
    (steps_ok (publicSteps_of h.pubOne))).1

/-- **JoinB1At AT A STATE WITH AN ACCEPTED STEP (Zs).** xl: the lookup's place at the segment. ds':
a continuation of the challenges behind the step. F₁: any ledger later than the one that the step
leaves. CONDITIONAL: on h, Lh, hQ, Zs, hT, hx, tieW, hs0 and hF₁. -/
theorem joinB1_stand_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {p : Par} {blk : Block TS ProofFile.Cl} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (tieW : K4LayersTieAt Q weights xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf
      h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW g c mm)
    (ds' : List Fmt.Drawn) {s0 : Forest.Shape}
    (hs0 : Forest.shape Qp.P.y.cl Qp.P.y.h.lidb = .ok s0) {F₁ : Fork}
    (hF₁ : OnBytes.PscRun.Later A'.F F₁) :
    JoinB1At (Verify.layerShape (P5J.At.X Zp).P) DF x.2.hp.tl Qp o F₁
      (dataQ (h.𝔇.N.sent m 0) A' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
        (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))).mask
      (matsOfData x.2.hp.tl (P5J.At.names3 Zp m)
        (dataQ (h.𝔇.N.sent m 0) A' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
        (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Qp cells weights tokens (look Qp) mm.st.input) kRef tbRef s0 := by
  obtain ⟨eY, eS, eG⟩ := pub_is Lh hQ
  obtain ⟨⟨eP, _, _, _, _⟩, _, _, _⟩ := pub_of Lh hQ
  have hP : Qp.P = (P5J.At.X Zp).layers := eP.symm.trans Lh.P
  have Fu := fullAt_stand Zs eY eS (lam_head h)
  have LL := lookLines_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ Zs hT hs0
  obtain ⟨T8, h8⟩ := trees_head h Lh.lt Lh.hp
  obtain ⟨_, hH, _⟩ := joinAt_shown Zs hT
  obtain ⟨_, _, _, vzk⟩ := env_of_hear hH
  -- the data's matrices are what the lookup's caller reads
  obtain ⟨a, _, _, ha, _, _, _, _, hdata⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  have hM : matsOfData x.2.hp.tl (P5J.At.names3 Zp m)
      (dataQ (h.𝔇.N.sent m 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
        (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))) =
      matsOfE (msgLay xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
        (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1)
          h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))) :=
    mats_of_syms xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc _
      (P5J.At.names3 Zp m) _ (syms_of_plain xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW _
        (P5J.At.names3 Zp m) _
        (symsTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT hx a ha (ds ++ ds')))
  have hMm : matsOfE (layMu xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
      h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
      (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds')))) =
      matsOfData x.2.hp.tl (P5J.At.names3 Zp m)
        (dataQ (h.𝔇.N.sent m 0) A' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
        (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))) := by
    rw [hdata, i1, i2, List.append_assoc]
    exact hM.symm
  exact
    { zx := LL.hsx
      zy := LL.hsy
      zk := LL.hzk
      e := LL.he
      pts := LL.hpt
      rope := rope_head h Lh.lt hP eG (Fu.lay.trans eY.symm) (Fu.sc.trans eS.symm) Fu.grp o.K.rs
      b1 := fun _ F₂ hb => by
        have key := b1_thread_head
          (scl := sclOf (Verify.layerShape (P5J.At.X Zp).P) o.v.sc o.v.g o.v.y.Lam)
          h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh Zs hT hx ds' T8 h8 _ tbRef _ _
          (keyVec_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ Zs tieW (ds ++ ds') hMm)
          (entryTrue x.2.hp.tl o (matsOfData x.2.hp.tl (P5J.At.names3 Zp m)
            (dataQ (h.𝔇.N.sent m 0) A' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
        (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))))
          F₂ (hF₁.trans (formsBack_later hb))
        rw [vzk]
        exact key }

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.trees_head
#print axioms ProofFile.Honest.K4.W.lookLines_head
#print axioms ProofFile.Honest.K4.W.joinB1_stand_head
