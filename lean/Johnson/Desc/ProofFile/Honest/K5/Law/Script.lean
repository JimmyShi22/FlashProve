-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Script.lean: the ties between the witness of which the table
of joints' items speak and the honest side of an attention segment's own rounds (kind K5), as the
fields of one structure. Definitions, and one small theorem. Every law of this folder on a VALUE
takes the structure as a premise, so each such law is CONDITIONAL on it.

Why. An item "the forms of a run are worth 0" (formsTQ, Johnson/Desc/Sound/FormsQ.lean) is said in
a world that is read off the witness's tables: under slot j lies what the ledger shows there less
the slot's factor times entry j of the segment's mask row; an array's cell is the witness's cell.
The honest side (Honest/K5/Row.lean) is typed over other letters: the coins that the book of coins
lends its parts, the cells of the input's trace, and key points made of the challenges heard. The
fields say that these are the same values.

  runsE, spentOf   the coins that the parts of a row spend, as the program's elements, in one list:
                   part by part, and in a part run by run, in the order in which they are stated
  K5Script T b cells Z A blk own rdOf
      maskTie entry number (the ledger's next free slot in front of the member) + j of the
              segment's mask row, read off the witness, is coin number j of spentOf
      cellsTie  the cell that the stated function of the second sending's array reads off the
              witness's first sending (matsOfData, Johnson/Desc/Sound/DataMats.lean) is the cell
              that the honest side reads off the trace: at every matrix of the smallness test's
              list but the one of the lookup's planes, every row and every column inside it

      keyTie  the verifier's state holds what the lookup on the calls heard; its three points
              follow the lookup's own rule (K3Pts, Johnson/Desc/First/Att/K05LookAll.lean); its key
              points are, element for element, those that the seat makes of the challenges heard,
              also when some of the member's own challenges have been heard
  PlanesTie        a premise of its own, outside the structure: the same as cellsTie at the matrix
                   of the lookup's planes, which no name of a cell reaches: no law on the member's
                   own values takes it
  cellAt           the trace's cell by (the matrix's number in the list, row, column)
  AddrIn           a premise on public numbers: the library's rule addrA lays every valid name of a
                   cell inside its matrix, which is not the matrix of the lookup's planes
  cells_named      CONDITIONAL on the structure and on AddrIn: the field cellsTie, name by name
  dataQ_behind, link_behind   what the two first ties read of the verifier's state is the same
                   behind the member's lay as in front of it
  K5ScriptAt       the structure at the library's own letters of the first chain's thread: own is
                   the first sending's seats of segment 2 g + 1, rdOf the witness's table at a seat

At which state and challenges. All are asked at the border IN FRONT of the member; the item's
sentence speaks at the state behind it: dataQ_behind and link_behind carry the two first across.
maskTie, cellsTie and PlanesTie are asked at every continuation ds of the challenges heard: the
thread's own clause on items (Thread.Items, Honest/Thread/Thr.lean) asks an item so. keyTie: at the
first n, for every n, of every list that the member's rounds can draw: these are the lists in front
of the row's parts. At longer lists, behind the member, nothing is asked: that is another border's
matter.

What the structure does not hold. That the cells meet the segment's identities. That the verifier's
hearing holds the prover's challenges: that is a theorem (Johnson/Desc/K5/Honest/Law/HeardIs.lean).
Anything on the slots of the lookup on the calls.

Who is meant to show each field. maskTie: whoever lays the book of coins and the sender of the
segment's mask row. cellsTie, PlanesTie: whoever lays the witness's first sending and the reader of
the trace.
keyTie: whoever states what the lookup's hearing holds, and whoever carries it to this border.
NONE OF THEM IS SHOWN. No member of the structure is known.

Limits. A premise's form: no property is claimed by a definition. Nothing says that the row's
coins are as many as the member takes slots; that is a law's matter. Nothing ties the seat's shape
and numbers to the plan A's: these are public facts, which a law takes as premises of its own. At
a name that is not valid, and at a place outside a matrix, nothing is said. AddrIn is not shown
here: Johnson/Desc/K5/Honest/Law/AddrIn.lean shows it of a planner's plan of which six numbers are
not 0 (in AddrIn's name: Honest/K5/Law/AddrInAt.lean).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Seated
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.First.Att.K05StatedArm
import Johnson.Desc.First.Att.K05FormsKept
import Johnson.Desc.First.Att.K05LookAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Block Chain Claim Strs First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgQ dataQ matsOfData seatTab)
open VerifiableInference.Desc.First.Att.P (K3Pts partAt behind link_front)
open ProofFile.Honest.FirstThread (Script WtF lettersAt)
open P5J (AtMgA TS CellsM)

/-! ## 1 The coins that a row spends, in one list -/

/-- The coins of a list of runs, as the program's elements, run by run. -/
def runsE : (ds : List (String × Due)) → CsAll ds → List E
  | [], _ => []
  | d :: ds, c =>
    let c' : Cs d.2 × CsAll ds := c
    coinsE c'.1 ++ runsE ds c'.2

/-- **The coins that the parts of a row spend**, part by part. -/
def spentOf {V W X : Type} : (ps : List (Part V W X)) → RowCoins ps → List E
  | [], _ => []
  | p :: ps, c =>
    let c' : p.Coins × RowCoins ps := c
    runsE p.spends c'.1.2.1 ++ spentOf ps c'.2

/-! ## 2 The ties -/

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- The trace's cell by the matrix's number a in the segment's list, the row and the column. l: the
segment's number. -/
def cellAt (S : OnBytes.Attention.Shape) (l : Nat) (cells : Cells) (a r c : Nat) : E :=
  eOfF (cells.cell l (labelOf S a) r c)

/-- **The ties.** T: the thread; b: the number of the member at the kind's place; blk: that member;
cells: the reader of the trace; Z: the seat; A: the attention plan of the segment's group; own: the
seats that the item's sentence may read; rdOf: the witness's table at a seat. THE ELDER FORM: the
road stands on `K5ScriptQ` (Honest/K5/Law/ScriptQ.lean), which gives this one under premises
(`k5Script_of_Q`, there). In each of the three fields the state m of the prover's run is bound under
`Thr` alone, which does not read m's field `opened` (`thr_took`, Honest/Thread/ThrField.lean: the
two sides are one term): so each is asked at every value of that field, `none` too; each reads m.st
alone. It is a definition: a premise's form. Nothing is claimed of it, and nothing shows that it can
be met. -/
structure K5Script (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (b : Nat) (cells : Tr → Cells) (Z : Seat5) (A : OnBytes.Attention.Plan)
    (blk : Block First.S Claim) (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) :
    Prop where
  /-- THE MASK ROW's ENTRY UNDER A SLOT OF THE MEMBER IS THE COIN THAT THE BOOK LENT. a: the open
  segment's part IN FRONT of the member, so a.F.next is the first slot that the member takes; c:
  what the book lends the row at the run's coins k -/
  maskTie : ∀ k s m E, Thr T b k s m E → ∀ a c, segAt? s = some a →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = .ok c →
    ∀ ds j, j < (spentOf _ c).length →
      (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))).mask (a.F.next + j) =
        Reading.gl.val ((spentOf _ c).getD j zeroE)
  /-- THE WITNESS's CELL IS THE TRACE's, inside every matrix of the smallness test's list but the
  lookup's planes'. i: the matrix's number; r, c: the row and the column -/
  cellsTie : ∀ k s m E, Thr T b k s m E → ∀ a, segAt? s = some a → ∀ ds i r c,
    i ≠ Z.P.S.cf.NAs + 2 →
    r < (A.seam.tl.mats.getD i {}).m → c < (A.seam.tl.mats.getD i {}).k →
      Reading.gl.val (cellAt Z.P.S Z.link (cells m.st.input.trace) i r c) =
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
          (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))) i r c
  /-- THE STATE's KEY POINTS ARE THE SEAT's -/
  keyTie : ∀ k s m E, Thr T b k s m E → ∀ att, s.here = .att att →
    ∃ g, att.g = some g ∧ K3Pts A.fs g.zx g.zy g.zk (OnBytes.Slice.readV (g.zx ++ g.zy)) ∧
      ∀ ds n, drawsFit blk.rounds ds = true → Z.keyAt (m.st.heard ++ ds.take n) = g.zk

/-- **The witness's cell is the trace's inside the matrix of the lookup's planes.** A premise of its
own: the law on the array that is sent behind the member takes it, and no law on the member's own
values. The state m is bound under `Thr` alone, which does not read m's field `opened` (`thr_took`,
Honest/Thread/ThrField.lean: the two sides are one term): so it is asked at every value of that
field, `none` too; it reads m.st alone. It is a definition: a premise's form. Nothing is claimed of
it, and it is not shown. -/
def PlanesTie (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (Z : Seat5) (A : OnBytes.Attention.Plan) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) : Prop :=
  ∀ k s m E, Thr T b k s m E → ∀ a, segAt? s = some a → ∀ ds r c,
    r < (A.seam.tl.mats.getD (Z.P.S.cf.NAs + 2) {}).m →
    c < (A.seam.tl.mats.getD (Z.P.S.cf.NAs + 2) {}).k →
      Reading.gl.val (cellAt Z.P.S Z.link (cells m.st.input.trace) (Z.P.S.cf.NAs + 2) r c) =
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
          (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))) (Z.P.S.cf.NAs + 2) r c

/-- **The library's rule lays every valid name of a cell inside its matrix, which is not the
matrix of the lookup's planes.** On public numbers alone. It is a definition: a premise's form;
whoever makes the plan is meant to show it. -/
def AddrIn (S : OnBytes.Attention.Shape) (tl : OnBytes.Model.HTailF2) : Prop :=
  ∀ q : Inst.Model.AttSeg.Raw, q.Valid (OnBytes.Road.L5.dimOf S) →
    (OnBytes.Road.L5.addrA S q).1 ≠ S.cf.NAs + 2 ∧
    (OnBytes.Road.L5.addrA S q).2.1 < (tl.mats.getD (OnBytes.Road.L5.addrA S q).1 {}).m ∧
      (OnBytes.Road.L5.addrA S q).2.2 < (tl.mats.getD (OnBytes.Road.L5.addrA S q).1 {}).k

/-- **The witness's cell is the trace's, name by name.** CONDITIONAL: on the ties, which
are not shown; on `AddrIn`; and on the thread in front of the member. -/
theorem cells_named {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {Z : Seat5} {A : OnBytes.Attention.Plan}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    (H : K5Script T b cells Z A blk own rdOf) (hA : AddrIn Z.P.S A.seam.tl)
    {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hT : Thr T b k s m E) {a : VerifiableInference.Desc.K9.Part} (ha : segAt? s = some a)
    (ds : List Fmt.Drawn) (q : Inst.Model.AttSeg.Raw)
    (hq : q.Valid (OnBytes.Road.L5.dimOf Z.P.S)) :
    OnBytes.Road.Rows.cellsK Z.P.S
        (matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
          (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds))))) q =
      Reading.gl.val ((inOf Z.P.S Z.link (cells m.st.input.trace)).cell q) :=
  (H.cellsTie k s m E hT a ha ds _ _ _ (hA q hq).1 (hA q hq).2.1 (hA q hq).2.2).symm

/-- The data that are read off the witness hang on the open segment's context and on the statement,
not on the ledger: so they are the same behind the member's lay as in front of it. No premise. -/
theorem dataQ_behind (own : List (Nat × Nat)) (s : First.S)
    (att : VerifiableInference.Desc.First.AttOwn) (F G : OnBytes.Model.Fork) (o o' : Option Nat)
    (rd : Nat × Nat → MsgQ) :
    dataQ own (partAt s att G o') rd = dataQ own (partAt s att F o) rd := rfl

/-- The open segment's context is the same behind the member's lay. CONDITIONAL: an attention
segment is open. -/
theorem link_behind {s : First.S} {att : VerifiableInference.Desc.First.AttOwn}
    (e : s.here = .att att) (hd : VerifiableInference.Desc.First.Att.P.Heard)
    (G : OnBytes.Model.Fork) : (behind s att hd G).link? = s.link? := by
  rw [link_front e]
  exact link_front (s := behind s att hd G) (a := { att with F := G, heard5 := some hd }) rfl

/-! ## 3 At the library's own letters -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **The ties at the kind's member of group g of the first chain's thread**, in the letters
in which that thread's items "the forms of a run are worth 0, in front of the second sending" read
the witness. It is a definition: a premise's form. Nothing is claimed of it. -/
def K5ScriptAt (g : Nat) (cells : Tr → Cells) (Z5 : Seat5) (A : OnBytes.Attention.Plan)
    (blk : Block TS ProofFile.Cl) : Prop :=
  K5Script (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
    (borderOf g) cells Z5 A blk (h.𝔇.N.sent (2 * g + 1) 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.cells_named
#print axioms ProofFile.Honest.K5.dataQ_behind
#print axioms ProofFile.Honest.K5.link_behind
