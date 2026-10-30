-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/OneTie.lean: CONDITIONAL.

What is here. Three hypotheses on what the witness's committed cells are, from one tie on symbols,
each with what the list below names beside it (Law/ExchangeTenth.lean spends the three at one list
and one plan); the tie is stated once, at the stand IN FRONT of the member of the feed-forward
layers' own rounds (sub-protocol K4): `K4CellsTieAt` (Law/ScriptAt.lean), the field hot and the
field idn of `FootRest` (Law/W/FootAtStand.lean). The one: at every continuation of the challenges
heard, at each matrix, row of symbols and column inside the plan's sizes, the cell that the item's
sentence reads of the witness is what the lookup's caller reads of it at the same address. What is
read behind the member's step is what is read in front (`step_tape`'s last clause and `moved_state`,
Law/RowBatch.lean). Each proof is a chain of calls.

  `zt_of_hear`   the hearing's token point is cut off what it was handed, at the layout's number of
      position bits: from the hearing's return alone (after the part of `ground_of_hear`,
      Johnson/Road/K4/W/GroundOfHear.lean, that makes the field zt).
  `K4SymsTieAt`   THE TIE. A definition.
  `cellsTie_of_tie`   **`K4CellsTieAt`**, with hA and hc.
  `k4_hot_tie`   **the field hot**, with hLk and hx.
  `k4_idn_tie`   **the field idn**, with hA at the library's list for the group, and hi.

Not shown here. THAT THE TIE `K4SymsTieAt` HOLDS: a hypothesis here; at the library's own list of
names, seats and reader it holds wherever the thread stands (`symsTie_head`,
Law/W/ReadersHead.lean). IT TIES TWO READERS OF ONE WITNESS AND HOLDS NO HONESTY; AT OTHER LETTERS
IT CAN BE FALSE AT AN HONEST WITNESS, AND CAN HOLD AS 0 = 0: both readers answer 0, without a word,
where they find no seat for an array: where the list own lacks the seat of an array that the segment
borrows from an earlier one the left side is 0 and the tie is false at every stream that is not 0;
where both find nothing it holds and says nothing, and `K4CellsTieAt` beside it is then false. WHAT
own IS AT THE THREAD's TABLE is held by no statement here; that the seats are there is shown here of
no list. THAT THE THREAD HOLDS AT ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: hT : Thr and Zs :
`K4Stand` (Law/SlotsTrue.lean) are hypotheses; for hot the clause of hT that is spent beside the
open item's sentence is what the public item `.left m` says beside its test: it is owed behind the
member of the lookup on the calls, and no file of the honest side shows it there. hA: `MatsAre`
(Johnson/Desc/First/Look/K3CallerLay.lean): the matrices that the lookup's caller reads off the
witness are the images of a list of integer matrices: an equation of functions: it binds the list to
0 outside every size. hc: `CellIsList` (Law/W/CellsTieOf.lean) at every continuation: its left side
reads no continuation, so it forces the list to stand still inside the sizes, off the matrix of the
planes, as elements of the field. hi: the Script's cells hold an index. hLk: `K4LookTieAt`
(Law/ScriptAt.lean), of which the first two clauses are read. The two fields stand at the plan
`x.2.hp.tl`: that a caller's plan is this one is the caller's to show. `matsAre_head`
(Law/W/MatsAreHead.lean) has hA at the plan `x.2.hp.tl`, at every witness and in every group, under
h, Lh and hx. The side library AtFullSide proves, with no hypothesis, that h has a member at one
place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say
what it is worth). Of h together with hh, tie, hA, hc, Lh, hQ, Zs, hT, hLk, hx and hi no example is
known to us. THE FULL SIZE ALONE, ALL BUT `zt_of_hear`: the tie's own Script and witness are typed
at the full size's numbers, so it cannot be stated at a smaller plan; `cellsTie_of_tie`,
`k4_hot_tie` and `k4_idn_tie` take h: the format's second hash function alone (`OnBytes.secondHashFunction`).
Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h and with the files that it joins, most with Law/ElevenHead.lean. THE TWO FIELDS REST,
through `lam_head` (Law/W/FullHead.lean) and `public_head` (Law/W/PublicHead.lean), ON A STATEMENT
OF A FILE UNDER Johnson/Goal/ (`Meaning.P34.pub34_all`). A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FieldsAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsTieOf
import Johnson.Road.K4.K4EAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own HPlan2)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.K4 (Par hear engFl)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road (Mats sclOf cellsOf cellsAt pt)
open OnBytes.Road.Rows (Addr)
open OnBytes.Road.K4 (eAll)
open OnBytes.Road.K4.W (HotPoint IdnHold mats_of_are syms_of_plain)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.First.Look (Sent layAt szOf sigListCalls seatCalls valAt ownPart
  MatsAre)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ dataByAddr matsOfData)
open VerifiableInference.OnPublicFiles (layMs)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **The hearing's token point.** CONDITIONAL: on hh. -/
theorem zt_of_hear {P : Layer.Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hh : hear engFl P hp g fo F t = some (o, G, u)) :
    lastOf o.H.fo.zx o.v.y.h.lt = .ok o.H.ztF := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ev, _, _, _, _, _⟩ :=
    Desc.First.K4.hear_public hh
  obtain ⟨_, H1, _, _, _, _, n1, n2, _⟩ := Desc.First.K4.hear_calls hh
  obtain ⟨_, _, _, _, _, _, q5, q6⟩ := Desc.First.K4.hearNorms_public n1
  obtain ⟨kfo, _, _, _, kzt, _⟩ := Desc.First.K4.hearTerms_keeps n2
  have efo : o.H.fo = fo := by rw [kfo, q6]
  have ezt : o.H.ztF = H1.ztF := kzt
  have vy : o.v.y = P.y := by rw [ev]
  rw [efo, vy, ezt]
  exact Road.ok_of_toOption q5

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X' : Type}

/-- **THE TIE**, at a stand in front of the member: at every part a of the open segment and every
continuation d of the challenges heard, at each matrix a', row of symbols i and column c' inside the
sizes of the plan tl: the data's cell at the address of that symbol is what the lookup's caller
reads off the witness at the same address. xl: the lookup's place. Ds, rad, oW, seatT, arr, msgW:
the lookup's caller's own parameters. This defines a hypothesis; the definition claims nothing. -/
def K4SymsTieAt
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (xl : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (Ds : Sent)
    (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (seatT : Fin (sigListCalls Ds rad xl.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (msgW : WtF → oW.Msg) (names : Array (ℕ × String)) (own : List (ℕ × ℕ))
    (rdOf : WtF → ℕ × ℕ → MsgQ) (c : Coins Bk) (s : TS)
    (mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X') : Prop :=
  ∀ a, segAt? s = some a → ∀ d a', a' < (szOf tl).NM → ∀ i, i < Alg.symRows ((szOf tl).m a') →
    ∀ c', c' < (szOf tl).k a' →
      dataByAddr names (dataQ own a (rdOf (Q.wit c mm.st.input (mm.st.heard ++ d))))
          (Addr.cell (tl.gtTree.getD a' 0) i c') =
        (valAt Ds.codes (sigListCalls Ds rad xl.link) (seatCalls Ds xl.link)
          (ownPart (layMs xl Ds rad oW seatT arr msgW
            (Q.wit c mm.st.input (mm.st.heard ++ d))))
          (Addr.cell (tl.gtTree.getD a' 0) i c')).getD 0

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Ky X₀ : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`K4CellsTieAt` FROM THE TIE.** L d: a list of integer matrices at the continuation d.
CONDITIONAL: on tie, hA and hc. -/
theorem cellsTie_of_tie {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {xl : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} {names : Array (ℕ × String)}
    {own : List (ℕ × ℕ)} {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    (tie : K4SymsTieAt Q xl tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW names own rdOf c s mm)
    {L : List Fmt.Drawn → Mats ℤ}
    (hA : ∀ d, MatsAre xl tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
      (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr
      h.𝔇.l3.msgW
        (Q.wit c mm.st.input (mm.st.heard ++ d))) (L d))
    (hc : ∀ d, CellIsList Qp (k4Wit Qp cells weights tokens (look Qp) mm.st.input) (L d) tl) :
    K4CellsTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells
      weights tokens look Qp tl names own rdOf c s mm :=
  cellsTie_of_mats (fun a ha d =>
    mats_of_are xl tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc _ names _
      (syms_of_plain xl tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW _ names _ (tie a ha d)) (hA d)) hc

/-- **THE FIELD hot FROM THE TIE**, behind the step from a stand. CONDITIONAL: on h, Lh, hQ, Zs, hT,
hLk, hx and tie. -/
theorem k4_hot_tie {k m g : ℕ} {x : Bool × Par}
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
    (hLk : K4LookTieAt look Qp s mm)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {names : Array (ℕ × String)}
    (tie : K4SymsTieAt Q xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW names own rdOf c s mm)
    (ds' : List Fmt.Drawn) :
    HotPoint DF
      (cellsOf DF (cellsAt o.v.y (matsOfData x.2.hp.tl names
        (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))))))
      (pt Reading.gl o.H.ztF) := by
  obtain ⟨a, _, _, ha, _, _, _, hh, hdata⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  refine k4_hot_field h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull) Lh hQ Zs hT hLk (zt_of_hear hh) hx
    (fun d a' h1 i h2 c' h3 => ?_) ds'
  rw [hdata, i1, i2, List.append_assoc]
  exact tie a ha (ds ++ d) a' h1 i h2 c' h3

/-- **THE FIELD idn FROM THE TIE**, behind the step from a stand. i: an index that the Script's
cells hold. CONDITIONAL: on h, Lh, hQ, Zs, hT, hi, tie and hA. -/
theorem k4_idn_tie {k m g : ℕ} {x : Bool × Par}
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
    {xl : VerifiableInference.Desc.First.Look.Place} {names : Array (ℕ × String)}
    (tie : K4SymsTieAt Q xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW names own rdOf c s mm)
    (hA : ∀ d, MatsAre xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
      h.𝔇.l3.nc
      (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr
      h.𝔇.l3.msgW
        (Q.wit c mm.st.input (mm.st.heard ++ d)))
      ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g))
    (ds' : List Fmt.Drawn) :
    IdnHold (scl := sclOf (Verify.layerShape (P5J.At.X Zp).P) o.v.sc o.v.g o.v.y.Lam) DF
      (cellsOf DF (cellsAt o.v.y (matsOfData x.2.hp.tl names
        (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))))) := by
  obtain ⟨a, _, _, ha, _, _, _, _, hdata⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  refine k4_idn_field h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ Zs hT hi (xl := xl)
    (fun d a' h1 j h2 c' h3 => ?_) (fun d => ?_) ds'
  · rw [hdata, i1, i2, List.append_assoc]
    exact tie a ha (ds ++ d) a' h1 j h2 c' h3
  · rw [i1, i2, List.append_assoc]
    exact hA (ds ++ d)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.zt_of_hear
#print axioms ProofFile.Honest.K4.W.cellsTie_of_tie
#print axioms ProofFile.Honest.K4.W.k4_hot_tie
#print axioms ProofFile.Honest.K4.W.k4_idn_tie
