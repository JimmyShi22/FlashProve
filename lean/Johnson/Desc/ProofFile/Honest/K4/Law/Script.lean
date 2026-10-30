-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Script.lean: SIX DEFINITIONS: two functions of coins and four
hypotheses' forms. No statement.

What is here. THE TIES BETWEEN THE WITNESS OF WHICH THE TABLE OF JOINTS' ITEMS SPEAK AND THE HONEST
SIDE OF K4, EACH AS A DEFINITION OF A PROPOSITION. K4 is the sub-protocol of the feed-forward
layers' own rounds. They are meant as hypotheses of the statements that lead to `K4Values`
(Law/Table.lean): each such statement is CONDITIONAL on those that it names. EACH TIE IS A SEPARATE
HYPOTHESIS: a statement depends only on those that it names.

Why. An item "the forms of a run are worth 0" (`formsTQ`, Johnson/Desc/Sound/FormsQ.lean) is said
in a world that is read off the witness's tables: under slot j lies what the ledger shows there
less the slot's factor (the ledger's field mf) times entry j of the segment's mask row; an array's
cell is the witness's cell. The honest side (Honest/K4/Part.lean) is typed over other parameters:
the coins that the book of coins lends its parts, the cells of the input's trace, the committed
weights, and what the lookup in front has sampled. The ties say that these are the same values.

  `runsE`, `spentOf`   the coins that the parts of a row spend, as the program's elements, in one
      list: part by part, and in a part run by run, in the order in which they are stated. OF A
      RUN's COINS THOSE OF THE EXTENSION FIELD ALONE (`coinsE` reads no other): a base-field coin of
      a run is left out without a word. The runs that a part spends alone: not the coins that it
      takes as its own, nor those that it carries.
  `K4MaskTie`   entry number (the ledger's next free slot in front of the member) + j of the
      segment's mask row, read off the witness, is coin number j of `spentOf`: for every j but the
      last. THE LAST COIN THAT THE ROW SPENDS IS NO ENTRY OF THE MASK ROW, AND IS TIED TO NOTHING
      HERE: the merge's end value is laid under an entry of the index-mask message; of the mask
      row's entry under that scalar's own slot nothing is said.
  `K4CellsTie`   the cell that the stated function of the second sending's array reads off the
      witness's first sending (`matsOfData`, Johnson/Desc/Sound/DataMats.lean) is the cell that the
      honest side reads off the trace (`k4Wit`): at every matrix of the segment's list but the one
      of the lookup's planes, every row and column inside it. tl, names: the plan's list of the
      segment's matrices and the list of the arrays' names: PARAMETERS: the item's stated function
      reads them off the public parameters, not off the state. A MATRIX THAT AN EARLIER SUB-PROOF
      HAS COMMITTED TO is read on the left under its owner's segment and name, on the right through
      this segment's own array for it: where one of the look-ups on that road finds nothing the
      right side is 0, and the tie is false of a cell that is not 0.
  `K4LookTie`   the verifier's state holds what the lookup in front heard, at both fields at which
      it is read (the items': `lookHeard?`; K4's hearing's: `seatS.look`); the three fields of it
      that K4's parts read are, element for element, those that `look` makes of the challenges in
      front of the member.
  `K4TokensTie`   the tokens that the verifier's state holds are the instance's.

At which state and challenges. All are asked at border b, meant as the one IN FRONT of the member:
no tie asks that. Where no segment is open there the first two ask nothing; so does the first where
the book lends the row nothing. The last two name no segment: they ask the same wherever the thread
stands at b. The first two are asked at every continuation ds of the challenges heard: the thread's
own clause on items (`Thread.Items`, Honest/Thread/Thr.lean) asks an item so.

Kin. `runsE` AND `spentOf` ARE, TO THE LETTER BUT FOR THEIR COMMENTS AND ONE BINDER,
`ProofFile.Honest.runsE` AND `ProofFile.Honest.spentOf` (Honest/Law/Rule/Spent.lean, of other writers); a third
copy stands in Honest/K5/Law/Script.lean. `runs_same` and `spent_same` (Law/TieIs.lean) show, with
no hypothesis, that these here are the first's. Spent.lean is not imported here: by a walk of import
lines it would lay 25 further modules beneath every file above this one; they declare names under
ProofFile.Honest (Cell and Item among them) that, inside this namespace, win over a name that a file opens
by name. `K4MaskTie` is the common form `MaskTie` (Honest/Law/Rule/Ties.lean) at K4's parameters:
`k4MaskTie_iff` (Law/TieIs.lean). `K4CellsTie` has the shape of that file's other common form,
`CellsTie`; that it is an instance is not shown here. The same four ties at one stand:
Law/ScriptAt.lean. A tie's form for an entry of the index-mask message, in which the coin is a
letter, meant as the last coin's reading, and one for the committed weights: `K4IndexTieAt`,
`K4WeightsTieAt` (Law/WoTies.lean).

Not shown here. HYPOTHESES' FORMS: this file proves none of them and gives no example. `K4CellsTie`
IS A PREMISE OF COMPLETENESS's KIND: it is not meant to stand in front of a law over coins. THE
ROAD FROM THE TIES TO `K4Values` IS NOT HERE; it wants three bridges besides, since the ties speak
in front of the member and `K4Values` behind it: the witness's data are read behind the step as in
front; the challenges heard behind are those in front and the member's own; and the matrices of
`K4Values` are `K4CellsTie`'s right side. Nothing says that the cells meet the segment's
identities. Nothing on the slots of the lookup in front. Who is meant to prove each. K4MaskTie:
whoever lays the book of coins, and the sender of the segment's mask row. K4CellsTie: whoever lays
the witness's first sending, and the reader of the trace. K4LookTie: whoever states what the
lookup's hearing holds, whoever carries it to this border, and whoever fills `look`. K4TokensTie:
whoever lays the chain's first state of the instance. Following import lines, and stopping unopened
at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module
whose name begins Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/ and none of the
others; what lies behind these is not counted. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Seated
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.Sound.DataMats
import Johnson.Desc.First.K4.SeatS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgQ dataQ matsOfData)

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

/-- **The mask row's entry under a slot of the member is the coin that the book lent.** a: the open
segment's part IN FRONT of the member, so a.F.next is the first slot that the member takes. c: what
the book lends the row at the run's coins k. own: the seats that the item's sentence may read. rdOf:
the witness's table at a seat. At every coin that the row spends but the last (j + 1 below their
number): the last is tied to nothing here. A hypothesis's form. Nothing is claimed by the
definition. -/
def K4MaskTie (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) : Prop :=
  ∀ k s m E, Thr T b k s m E → ∀ a c, segAt? s = some a →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c →
    ∀ ds j, j + 1 < (spentOf _ c).length →
      (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))).mask (a.F.next + j) =
        Reading.gl.val ((spentOf _ c).getD j zeroE)

/-- **The witness's cell is the trace's**, inside every matrix of the segment's list but the
lookup's planes'. tl: the plan's list of the segment's matrices. names: the arrays' names. i: the
matrix's number; r, c: the row and the column. A hypothesis's form. Nothing is claimed by
the definition. -/
def K4CellsTie (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (tl : OnBytes.Model.HTailF2) (names : Array (Nat × String)) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) : Prop :=
  ∀ k s m E, Thr T b k s m E → ∀ a, segAt? s = some a → ∀ ds i r c,
    i < tl.NM → i ≠ (OnBytes.Model.Layer.matIx Q.P.y).iB →
    r < (tl.mats.getD i {}).m → c < (tl.mats.getD i {}).k →
      Reading.gl.val
          (OnBytes.ofF ((k4Wit Q cells weights tokens (look Q) m.st.input).cell i r c)) =
        matsOfData tl names (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ ds)))) i r c

/-- **What the lookup has sampled, as the state holds it, is what `look` makes**, at the three
fields that K4's parts read. A hypothesis's form. Nothing is claimed by the definition. -/
def K4LookTie (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub) : Prop :=
  ∀ k s m E, Thr T b k s m E → ∃ g, s.lookHeard? = some g ∧
    OnBytes.Desc.First.K4.seatS.look s = some g ∧
    (look Q m.st.heard).zx = g.zx ∧ (look Q m.st.heard).zk = g.zk ∧ (look Q m.st.heard).e = g.e

/-- **The tokens that the state holds are the instance's.** A hypothesis's form. Nothing is claimed
by the definition. -/
def K4TokensTie (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (tokens : Xi → Array Nat) : Prop :=
  ∀ k s m E, Thr T b k s m E → s.tokv = tokens m.st.input.x

end ProofFile.Honest.K4
#print axioms ProofFile.Honest.K4.runsE
#print axioms ProofFile.Honest.K4.spentOf
#print axioms ProofFile.Honest.K4.K4MaskTie
#print axioms ProofFile.Honest.K4.K4CellsTie
#print axioms ProofFile.Honest.K4.K4LookTie
#print axioms ProofFile.Honest.K4.K4TokensTie
