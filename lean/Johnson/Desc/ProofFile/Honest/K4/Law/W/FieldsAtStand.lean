-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FieldsAtStand.lean: CONDITIONAL.

What is here. The fields hot and idn of the hypotheses `ItemRight` (Law/W/SlotsOfStand.lean),
`RightFoot` (Law/W/ItemRightOf.lean) and `FootRest` (Law/W/FootAtStand.lean), EACH IN ITS OWN TEXT
at D := DF and h := the public parameters' shape of the layers, at the state behind the step of the
member of the feed-forward layers' own rounds (sub-protocol K4), at the matrices that are unpacked
from what the item's sentence reads of the witness there, at every continuation of the challenges
heard: at the thread with the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean).
Against Law/W/HotStand.lean three hypotheses are paid inside: `AtK4` (`atK4_of_laid`,
Law/ElevenHead.lean), and that the public data's layout and scales are the public parameters'
(`pub_of`, Law/SeatedHead.lean). Each proof is a chain of calls.

  `pub_is`   the public data's layout, scales and group are the public parameters' and g.
  `k4_hot_field`   **the field hot.**
  `k4_idn_field`   **the field idn.**

Not shown here. THAT THE THREAD HOLDS AT ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: hT : Thr
and Zs : `K4Stand` (Law/SlotsTrue.lean) are hypotheses. For hot the clause of hT that is spent
beside the open item's sentence is what the public item `.left m` says beside its test: it is owed
behind the member of the lookup on the calls, and no file of the honest side shows it there. hP: AT
EVERY CONTINUATION, AT EACH MATRIX, ROW OF SYMBOLS AND COLUMN INSIDE THE SIZES, THE DATA's CELL IS
WHAT THE LOOKUP's CALLER READS OFF THE WITNESS AT THE SAME ADDRESS: a hypothesis of both statements:
it ties two readers of one witness; Law/W/OneTie.lean has it from the tie `K4SymsTieAt` in front of
the step, and at the library's own list of names, seats and reader that tie holds wherever the
thread stands (`symsTie_head`, Law/W/ReadersHead.lean). AT OTHER LETTERS hP CAN BE FALSE AT AN
HONEST WITNESS, AND CAN HOLD AS 0 = 0: both readers answer 0, without a word, where they find no
seat for an array: where the list own lacks the seat of an array that the segment borrows from an
earlier one the left side is 0 and hP is false at every stream that is not 0; where both find
nothing it holds and says nothing. What own is at the thread's table is held by no statement here.
For idn besides: hA: the matrices that the lookup's caller reads off the witness are the images of
the list that the library reads off it for the group (`MatsAre`,
Johnson/Desc/First/Look/K3CallerLay.lean): an equation of functions: it binds the list to 0 outside
every size; hi: the Script's cells hold an index: these two speak of a run's coins and input and of
no state, and no statement of this folder leads to them. For hot besides: hLk (`K4LookTieAt`,
Law/ScriptAt.lean), of which the first two clauses are read, and hzt (the field zt of `K4Ground`,
Johnson/Road/K4/W/Ground.lean). The matrices stand at the plan `x.2.hp.tl`: that a caller's plan is
this one is the caller's to show. `matsAre_head` (Law/W/MatsAreHead.lean) has hA at the plan
`x.2.hp.tl`, at every witness and in every group, under h, Lh and hx. Lh (`LaidK4`,
Law/SeatedHead.lean), hQ (the public data are made) and hx: on public lists and numbers. The side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with Lh, hQ, Zs, hT, hLk, hzt, hx, hP, hi and hA no example is known to us.
THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness,
on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h and with the files that it joins, most with Law/ElevenHead.lean. BOTH FIELDS REST,
through `lam_head` (Law/W/FullHead.lean), and hot through `public_head` (Law/W/PublicHead.lean) too,
ON A STATEMENT OF A FILE UNDER Johnson/Goal/ (`Meaning.P34.pub34_all`). A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.HotStand
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IdnHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road (sclOf cellsOf cellsAt pt)
open OnBytes.Road.Rows (Addr)
open OnBytes.Road.K4.W (HotPoint IdnHold mats_of_are syms_of_plain)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt szOf sigListCalls seatCalls valAt ownPart MatsAre)
open VerifiableInference.Desc.Sound (MsgT MsgQ WideData dataQ dataByAddr matsOfData)
open VerifiableInference.OnPublicFiles (layMs)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 pub_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- The public data's layout, scales and group. CONDITIONAL: on Lh and hQ. -/
theorem pub_is {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) :
    Qp.P.y = (P5J.At.X Zp).y ∧ Qp.P.sc = (P5J.At.X Zp).layers.sc ∧ Qp.g = g := by
  obtain ⟨⟨eP, _, _, _, _⟩, _, eg, _⟩ := pub_of Lh hQ
  exact ⟨congrArg (fun P => P.y) (eP.symm.trans Lh.P),
    congrArg (fun P => P.sc) (eP.symm.trans Lh.P), eg⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE FIELD hot, BEHIND THE STEP FROM A STAND.** xl: the lookup's place at the segment. E₀: any
value serves: the library's lemma is stated at the wider meaning, which takes it; the conclusion
does not read it. CONDITIONAL: on h, Lh, hQ, Zs, hT, hLk, hzt, hx and hP. -/
theorem k4_hot_field (E₀ : WideData ProofFile.InstPub) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp)
    {p : Par} {blk : Block TS ProofFile.Cl}
    {own : List (ℕ × ℕ)} {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk own rdOf c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hLk : K4LookTieAt look Qp s mm) (hzt : lastOf o.H.fo.zx o.v.y.h.lt = .ok o.H.ztF)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {names : Array (ℕ × String)}
    (hP : ∀ ds' a, a < (szOf x.2.hp.tl).NM → ∀ i, i < Alg.symRows ((szOf x.2.hp.tl).m a) → ∀ c',
      c' < (szOf x.2.hp.tl).k a →
        dataByAddr names (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))
            (Addr.cell (x.2.hp.tl.gtTree.getD a 0) i c') =
          (valAt h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link)
            (seatCalls h.𝔇.sent xl.link)
            (ownPart (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
              (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
              (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))
            (Addr.cell (x.2.hp.tl.gtTree.getD a 0) i c')).getD 0)
    (ds' : List Fmt.Drawn) :
    HotPoint DF
      (cellsOf DF (cellsAt o.v.y (matsOfData x.2.hp.tl names
        (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))))))
      (pt Reading.gl o.H.ztF) := by
  obtain ⟨eY, eS, _⟩ := pub_is Lh hQ
  exact k4_hot_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ E₀ (atK4_of_laid Lh) Lh Zs hT hLk
    eY eS hzt hx hP ds'

/-- **THE FIELD idn, BEHIND THE STEP FROM A STAND.** i: an index that the Script's cells hold. xl: a
place of the lookup: any at which hP and hA hold. CONDITIONAL: on h, Lh, hQ, Zs, hT, hi, hP and hA.
-/
theorem k4_idn_field {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp)
    {p : Par} {blk : Block TS ProofFile.Cl}
    {own : List (ℕ × ℕ)} {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk own rdOf c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {i : Cm.Idx} (hi : Holds (Q.cells mm.st.input) i)
    {xl : VerifiableInference.Desc.First.Look.Place}
    {names : Array (ℕ × String)}
    (hP : ∀ ds' a, a < (szOf x.2.hp.tl).NM → ∀ i, i < Alg.symRows ((szOf x.2.hp.tl).m a) → ∀ c',
      c' < (szOf x.2.hp.tl).k a →
        dataByAddr names (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))
            (Addr.cell (x.2.hp.tl.gtTree.getD a 0) i c') =
          (valAt h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link)
            (seatCalls h.𝔇.sent xl.link)
            (ownPart (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
              (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
              (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))
            (Addr.cell (x.2.hp.tl.gtTree.getD a 0) i c')).getD 0)
    (hA : ∀ ds', MatsAre xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
      h.𝔇.l3.nc
      (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
        (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
        (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))
      ((h.𝔇.H.hid (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))).MG g))
    (ds' : List Fmt.Drawn) :
    IdnHold (scl := sclOf (Verify.layerShape (P5J.At.X Zp).P) o.v.sc o.v.g o.v.y.Lam) DF
      (cellsOf DF (cellsAt o.v.y (matsOfData x.2.hp.tl names
        (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))))) := by
  obtain ⟨eY, eS, eg⟩ := pub_is Lh hQ
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  have Fu := fullAt_stand Zs eY eS (lam_head h)
  rw [eg] at Fu
  have hM : ∀ d, matsOfData x.2.hp.tl names
      (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ d)))) =
      OnBytes.Road.Rows.Norms.castM
        ((h.𝔇.H.hid (Q.wit c y.2.st.input (y.2.st.heard ++ d))).MG g) := fun d =>
    mats_of_are xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc _ names
      _ (syms_of_plain xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW _ names _ (hP d)) (hA d)
  have q := k4_idn_mats h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ (atK4_of_laid Lh) hT hi Lh.lt
    Lh.seg Fu
    (fun d => OnBytes.Road.Rows.Norms.castM
      ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g))
    (fun _ => rfl) (ds ++ ds')
  rw [hM ds', i1, i2, List.append_assoc]
  exact q

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.pub_is
#print axioms ProofFile.Honest.K4.W.k4_hot_field
#print axioms ProofFile.Honest.K4.W.k4_idn_field
