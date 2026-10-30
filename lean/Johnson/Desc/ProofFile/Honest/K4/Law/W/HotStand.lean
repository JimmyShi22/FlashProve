-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/HotStand.lean: CONDITIONAL.

What is here. The field hot of the hypotheses `ItemRight` (Law/W/SlotsOfStand.lean), `RightFoot`
(Law/W/ItemRightOf.lean) and `FootRest` (Law/W/FootAtStand.lean), IN ITS OWN TEXT at D := DF: the
selector's identity at the token point of the feed-forward layers' own rounds (sub-protocol K4), at
the state behind the member's step, at the matrices that are unpacked from what the item's sentence
reads of the witness there, at every continuation of the challenges heard: at the thread with the
library's own values (`lettersHead`, Honest/Thread/FirstHead.lean). `k4_hot_mats`
(Law/W/HotHead.lean) speaks at the state in front; five facts carry it behind the step: `stand_look`
with hLk; `public_head` (Law/W/PublicHead.lean) with `fullAt_stand` (Law/W/FullHead.lean); hzt;
`fullAt_stand`'s layout; `moved_state` (Law/RowBatch.lean). The public hypotheses of `k4_hot_mats`
come from `nine_head` (Law/ElevenHead.lean) and `public_head`; its hC from hP (`cells_of_syms`,
`syms_of_plain`, Johnson/Road/K4/W/MatsOfSyms.lean). One statement; its proof is a chain of calls.

  `k4_hot_stand`   **`HotPoint DF (cellsOf DF (cellsAt o.v.y Mm)) (pt Reading.gl o.H.ztF)`**, Mm :=
      the matrices off the data behind the step.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: hT : Thr
and Zs : `K4Stand` (Law/SlotsTrue.lean) are hypotheses. THE CLAUSE OF hT THAT IS SPENT beside the
open item's sentence is what the public item `.left m` says beside its test: it is owed behind the
member of the lookup on the calls, and no file of the honest side shows it there. hP: AT EVERY
CONTINUATION, AT EACH MATRIX, ROW OF SYMBOLS AND COLUMN INSIDE THE SIZES, THE DATA's CELL IS WHAT
THE LOOKUP's CALLER READS OFF THE WITNESS AT THE SAME ADDRESS: a hypothesis: it ties two readers of
one witness; Law/W/OneTie.lean has it from the tie `K4SymsTieAt` in front of the step, and at the
library's own list of names, seats and reader that tie holds wherever the thread stands
(`symsTie_head`, Law/W/ReadersHead.lean). AT OTHER LETTERS hP CAN BE FALSE AT AN HONEST WITNESS, AND
CAN HOLD AS 0 = 0: both readers answer 0, without a word, where they find no seat for an array:
where the list own lacks the seat of an array that the segment borrows from an earlier one the left
side is 0 and hP is false at every stream that is not 0; where both find nothing it holds and says
nothing. What own is at the thread's table is held by no statement here. The matrices stand at the
plan `x.2.hp.tl`: that a caller's plan is this one is the caller's to show. hLk: `K4LookTieAt`
(Law/ScriptAt.lean), of which the first two clauses are read: what the state holds as heard by the
lookup is what K4's own hearing is handed. hzt: the hearing's token point is cut off what it was
handed, at the layout's number of position bits (the field zt of `K4Ground`,
Johnson/Road/K4/W/Ground.lean). eY, eS: the public data's layout and scales are the public
parameters'. A (`AtK4`), Lh (`LaidK4`, Law/SeatedHead.lean) and hx: on public lists and numbers. The
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with A, Lh, Zs, hT, hLk, eY, eS, hzt, hx and hP no example is known to us.
THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness,
on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h and with the files that it joins, most with Law/ElevenHead.lean. THE STATEMENT RESTS,
through `lam_head` (Law/W/FullHead.lean) and `public_head` (Law/W/PublicHead.lean), ON A STATEMENT
OF A FILE UNDER Johnson/Goal/ (`Meaning.P34.pub34_all`). A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.HotHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PublicHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FullHead
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.Desc.ProofFile.Honest.K4.Law.RowBatch
import Johnson.Road.K4.W.MatsOfSyms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road (cellsOf cellsAt pt)
open OnBytes.Road.Rows (Addr)
open OnBytes.Road.K4 (AtK4)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.W (HotPoint cells_of_syms syms_of_plain)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (pubAt stepOf layAt szOf sigListCalls seatCalls valAt
  ownPart)
open VerifiableInference.Desc.Sound (MsgT MsgQ WideData linksFull dataQ dataByAddr matsOfData
  mgAll_more_base)
open VerifiableInference.OnPublicFiles (layMs)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pubP)
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

/-- **THE FIELD hot, IN ITS OWN TEXT, BEHIND THE STEP FROM A STAND.** xl: the lookup's place at the
segment. E₀: any value serves: the library's lemma is stated at the wider meaning, which takes it;
the conclusion does not read it. CONDITIONAL: on h, A, Lh, Zs, hT, hLk, eY, eS, hzt, hx and hP. -/
theorem k4_hot_stand (E₀ : WideData ProofFile.InstPub)
    {k m g : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} {p : Par} {blk : Block TS ProofFile.Cl}
    {own : List (ℕ × ℕ)} {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk own rdOf c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hLk : K4LookTieAt look Qp s mm) (eY : Qp.P.y = (P5J.At.X Zp).y)
    (eS : Qp.P.sc = (P5J.At.X Zp).layers.sc)
    (hzt : lastOf o.H.fo.zx o.v.y.h.lt = .ok o.H.ztF)
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
  have N := nine_head h Lh
  obtain ⟨T3, _, elt⟩ := public_head h Lh.lt Lh.hp
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  obtain ⟨g', hg1, hg2, _⟩ := hLk
  obtain rfl : g' = o.H.fo := Option.some.inj (hg2.symm.trans (stand_look Zs))
  have Fu := fullAt_stand Zs eY eS (lam_head h)
  obtain ⟨_, F', _, _, _, _, _, _, hF'⟩ := left_of_promise (Dm := h.𝔇) E₀
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH A N.Sx
    (fun _ hq => thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  have hzt' : lastOf o.H.fo.zx DF.lT = .ok o.H.ztF := by
    rw [elt, ← Fu.lay]
    exact hzt
  have hC := cells_of_syms xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
    h.𝔇.l3.nc _ names _ (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) (y := o.v.y) Fu.lay
    (syms_of_plain xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW _ names _ (hP ds'))
  rw [i1, i2, List.append_assoc] at hC ⊢
  exact k4_hot_mats h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ E₀ N.hH A N.Sx hT (ds ++ ds')
    hF' hg1 T3 hzt' hx hC

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_hot_stand
