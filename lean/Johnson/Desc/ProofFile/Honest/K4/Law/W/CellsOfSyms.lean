-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CellsOfSyms.lean: CONDITIONAL: IT MOVES A DEBT, IT
PAYS NONE.

What is here. THE SECOND STONE OF A BRIDGE TO THE HYPOTHESIS `CellIsList` (Law/W/CellsTieOf.lean) OF
THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), AT A SCRIPT's WITNESS: it follows from a
sentence on public data, a sentence on the trace's cells and an equation in the script's own
letters. The verifier's side reads no cell off a message: a message holds symbols, three cells of
one column packed at the radix 2 ^ 20, and a column is read as the small integer column whose
packing the symbols are, or as 0 where there is none. Another house has made that step for an
attention segment's own rounds (Honest/K5/Law/CellsQRaw.lean); its law `mats_of_syms` and its form
`SymsRoom` are general in the place and the plan and are called here as they lie. Two definitions of
premises' forms, which are that file's `CellsSmallQ` and `ESymsRaw` with K4's plan, K4's number of
the planes' matrix and K4's cell laid for K5's (the second asks below the plan's number of matrices
alone, which `ESymsRaw` does not say; both bear three letters more, weights, tokens and look, which
K4's cell does not read); and two statements with their proofs. The first proof has the lines of
that file's `eCells_of_raw`; the second is a call of `cellIsList_of_att`
(Law/W/CellsOfAttReading.lean).

  `K4CellsSmall`   on the trace alone: at an input that meets Vd each column of each matrix of the
      plan's list but the planes' is the image of a small integer column. A premise's form.
  `K4SymsRaw`   on the script: at a symbol's seat the message holds the packing of the honest side's
      three cells. A premise's form.
  `k4_att_of_raw`   the reading `matsOfMsg` over `attMs` is the honest side's cell.
  `cellIsList_of_raw`   **`CellIsList` at the script's witness**, at every list of at least N
      challenges.

Not shown here. R: `SymsRoom` at every matrix of the plan's list but the planes': each symbol has a
seat, inside its message's main table, off the pad: on public data; a hypothesis here
(Law/W/SymsRoomK4.lean, not imported here, has it under h). hS: `K4CellsSmall`: shown of no trace
here (Law/W/CellsSmallFullIn.lean, which stands over this file, has it at the frame's full-size
choice of fields). hE: `K4SymsRaw`: shown of no script here. WHETHER hE CAN BE MET is not shown;
what Honest/K5/Law/CellsQRaw.lean's head says of `ESymsRaw` holds of it too, but for one thing:
K4's honest side reads a matrix that an earlier segment has committed under its owner's segment and
name (`k4Owner`, Honest/K4/Part.lean). NOT TRIED FOR EMPTINESS: no instance of R, hS and hE
together is exhibited. h: the library's hypothesis `P5J.AtMgA` on the public files; Lh (`LaidK4`,
Law/SeatedHead.lean) and hx follow from it at each of the twelve groups, as
Law/W/MatsAreHead.lean's head says. Qp is a free letter: nothing here ties it to the member's
parameters. The bound of `K4CellsSmall` is the library's own for the packing to be unique (twice 2
^ 17), not the format's bound on a cell. The matrix of the lookup's planes is left out, as in
`CellIsList`. All limits of the heads of the files that it imports hold here; among them: closed
facts by evaluation in Lean's kernel lie beneath; no independent checker that its writers know of
has replayed them; through its imports it stands over files under Johnson/Goal/. THE FULL SIZE
ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsOfAttReading
import Johnson.Desc.ProofFile.Honest.K5.Law.CellsQRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2 Reading)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt Seat sigListCalls seatCalls szOf)
open VerifiableInference.Desc.First.Att.P (matsOfMsg)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (attMs)
open H2K5.Door (seatAll)
open ProofFile.Honest.K5 (SymsRoom mats_of_syms msgNo5)
open ProofFile.Honest.FirstThread (Script)
open P5J (AtMgA TS CellsM)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **The trace's cells are small**: at an input that meets Vd each column of each matrix of the
plan's list but the lookup's planes' is the image of an integer column whose entries are below twice
2 ^ 17 in absolute value. The cell is the honest side's (`k4Wit`, Honest/K4/Part.lean), whose field
cell reads Qp, cells and the trace alone: weights, tokens and look are idle letters here. Beyond the
plan's list it asks nothing: there `getD` answers the default entry, whose number of columns is 0
(`TMat`, OnBytes/Model/Frame.lean), and no c is below 0. It is a definition: a premise's form, on
the trace alone; it is proved of nothing here. It is a premise on the private input. A RIDER ON ITS
USE: it stands in front of no sentence on hiding as a
bare premise: there it is had from Vd, by name, or the sentence says that its range is cut by a
condition on the trace. -/
def K4CellsSmall (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (tl : HTailF2) (Qp : K4Pub)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) : Prop :=
  ∀ v, Vd v → ∀ i c, i ≠ (OnBytes.Model.Layer.matIx Qp.P.y).iB → c < (tl.mats.getD i {}).k →
    ∃ a : Fin (tl.mats.getD i {}).m → ℤ, Alg.Small (((szOf tl).beta : Nat) : ℤ) a ∧
      ∀ r, ((a r : ℤ) : Cb.Gl.E) =
        Reading.gl.val
          (OnBytes.ofF ((k4Wit Qp cells weights tokens (look Qp) v).cell i r.val c))

/-- **The equation in the script's own letters**: at the seat of symbol (row of symbols i', column
c) of matrix number i the message of the seat's member's number holds, in its main table, the
packing of the honest side's cells of rows 3 i', 3 i' + 1 and 3 i' + 2 of that column. xl: the
lookup's place at the segment. It is asked below the plan's number of matrices alone: the form that
it follows (`ESymsRaw`, Honest/K5/Law/CellsQRaw.lean) lacks that premise; the library's
`PubLines.hNM` (Johnson/Road/K4/PubAt.lean: a plan's number of matrices is its list's length) would
serve the form without it. Its right side has no k, nor has it hd: so it also says that these
entries of the message's main table are the same at all coins and at all lists of at least N
challenges: a sentence on the script's text at a seat, not on what a run shows; that a part sends
what the script says is not treated here. weights, tokens and look are idle letters here, as in
`K4CellsSmall`. It is a definition: a premise's form; it is proved of nothing. -/
def K4SymsRaw (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat)
    (xl : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (Qp : K4Pub)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) : Prop :=
  ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn), Vd v → N ≤ hd.length →
    ∀ i i' c, i < tl.NM → i ≠ (OnBytes.Model.Layer.matIx Qp.P.y).iB →
    i' < Alg.symRows (tl.mats.getD i {}).m → c < (tl.mats.getD i {}).k →
    ∀ (s : Seat) (hk : s.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).length),
      seatCalls h.𝔇.sent xl.link (.cell (tl.gtTree.getD i 0) i' c) = some s →
      Q.msg (msgNo5 h xl s.msg hk) k v (hd.take (Q.fixedMsg (msgNo5 h xl s.msg hk))) false s.row
          s.place =
        Alg.pack (((szOf tl).rad : Nat) : ℤ)
          (fun r : Fin (tl.mats.getD i {}).m =>
            Reading.gl.val
              (OnBytes.ofF ((k4Wit Qp cells weights tokens (look Qp) v).cell i r.val c))) i'

variable {h Q}

/-- CONDITIONAL: on R, hS and hE. **The reading `matsOfMsg` over `attMs` off the script's witness is
the honest side's cell**, inside the plan's sizes, off the matrix of the planes. It moves the debt:
none of the three is shown here. -/
theorem k4_att_of_raw {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    {xl : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2} {Qp : K4Pub}
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (R : ∀ i, i ≠ (OnBytes.Model.Layer.matIx Qp.P.y).iB → i < tl.NM →
      SymsRoom h.𝔇.sent h.𝔇.l3.rad xl tl i)
    (hS : K4CellsSmall Vd tl Qp cells weights tokens look)
    (hE : K4SymsRaw h Q Vd N xl tl Qp cells weights tokens look)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn) (hv : Vd v)
    (hN : N ≤ hd.length) (i a b : Nat) (hiN : i < tl.NM)
    (hi : i ≠ (OnBytes.Model.Layer.matIx Qp.P.y).iB) (hr : a < (tl.mats.getD i {}).m)
    (hc : b < (tl.mats.getD i {}).k) :
    matsOfMsg xl tl h.𝔇.sent h.𝔇.l3.rad
        (attMs xl h.𝔇.sent h.𝔇.l3.rad (seatAll h xl) h.𝔇.arr (Q.wit k v hd)) i a b =
      Reading.gl.val
        (OnBytes.ofF ((k4Wit Qp cells weights tokens (look Qp) v).cell i a b)) := by
  obtain ⟨col, hcol, hcast⟩ := hS v hv i b hi hc
  rw [mats_of_syms (seatAll h xl) h.𝔇.arr (Q.wit k v hd) hiN hr hc (R i hi hiN) hcol
    fun i' hi' s hk hs => by
      rw [← Alg.pack_intCast]
      refine (hE k v hd hv hN i i' b hiN hi hi' hc s hk hs).trans ?_
      congr 1
      funext r'
      exact (hcast r').symm]
  exact hcast ⟨a, hr⟩

/-- CONDITIONAL: on h, Lh, hx, R, hS and hE. **`CellIsList` AT THE SCRIPT's WITNESS, AT EVERY INPUT
THAT MEETS Vd AND EVERY LIST OF AT LEAST N CHALLENGES.** It moves the debt. -/
theorem cellIsList_of_raw {k₀ m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k₀ m g x blk₀) {xl : VerifiableInference.Desc.First.Look.Place}
    (hx : layAt (P5J.At.X Zp) m = some xl) {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    {Qp : K4Pub} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard}
    (R : ∀ i, i ≠ (OnBytes.Model.Layer.matIx Qp.P.y).iB → i < x.2.hp.tl.NM →
      SymsRoom h.𝔇.sent h.𝔇.l3.rad xl x.2.hp.tl i)
    (hS : K4CellsSmall Vd x.2.hp.tl Qp cells weights tokens look)
    (hE : K4SymsRaw h Q Vd N xl x.2.hp.tl Qp cells weights tokens look)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn) (hv : Vd v)
    (hN : N ≤ hd.length) :
    CellIsList Qp (k4Wit Qp cells weights tokens (look Qp) v)
      ((h.𝔇.H.hid (Q.wit k v hd)).MG g) x.2.hp.tl :=
  cellIsList_of_att h Lh hx (Q.wit k v hd) fun i a b h1 h2 h3 h4 =>
    k4_att_of_raw R hS hE k v hd hv hN i a b h1 h2 h3 h4

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.K4CellsSmall
#print axioms ProofFile.Honest.K4.W.K4SymsRaw
#print axioms ProofFile.Honest.K4.W.k4_att_of_raw
#print axioms ProofFile.Honest.K4.W.cellIsList_of_raw
