-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/Wo.lean: CONDITIONAL: K4's share of a thread's debt `Exchange`
(Honest/Thread/Pays.lean) at the pending row's item: "the row on the committed matrix of weights
that the merge leaves holds of the witness". Definitions of hypotheses, and one statement with its
proof.

Not shown here. THAT THE ROW HOLDS ANYWHERE: `K4WoHolds` is a hypothesis, and no statement yet leads
to it. `woAt` HOLDS FOR NOTHING WHERE THE READER OF THE STATE GIVES NO ROW: that it gives one behind
K4's step is shown nowhere. That the hypotheses can hold together: no example is known. Nothing on
the nine members past which the item then rides. Nothing on soundness, on completeness or on any
other property.
WHAT THIS FILE's IMPORTS REACH, by a program's walk of import lines that stops, unopened, at every
module under Johnson/Goal/, Johnson/D/ or ThirdParty/ and at the names RecCompile.Honest…, Both… and
PassH…: 28 modules whose names hold RecCompile; none under Johnson/Goal/ or ThirdParty/; none under
Johnson/D/, none of the three names.

  `K4WoTable T iWo d rw m`   the library's sentence `woAt d rw m` (Johnson/Top/H0/Fill/FillP1.lean:
      the row that the reader of the verifier's state gives, if it gives one, holds of the witness's
      matrix and mask entries as rw reads them) GIVES the thread's sentence at iWo. d: the public
      data; rw: the reader of the witness; m: the segment's number.
  `K4WoHolds T At b d rw m`   that sentence at every state behind the member's step and every
      continuation of the challenges. At: which stands in front are meant, as in `K4Values`
      (Law/Table.lean).
  `k4_wo_share`: `ShareAt T At b [iWo]`, under these two.

Who is meant to prove each. K4WoTable: whoever lays the thread. K4WoHolds: K4's writers: from the
statement that the pending row holds where the merge's shown end value is its function at the
merge's point plus the factor times one entry of the index masks' message
(Johnson/Road/K4/W/Wo.lean); from what the reader gives at the state behind the step; and from two
ties that are not typed yet: the last coin that the row spends is that entry, and the witness's
matrix is the committed weights. That statement's own hypotheses are owed too: the equation on the
end value, what the merge leaves of its claims, and that the verifier's function for the pending row
returns.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Table
import Johnson.Top.H0.Fill.FillP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.First.FillP1 (PileWit woAt PubData)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **The table's parameters at the pending row's item.** A hypothesis's form. Nothing is claimed by
the definition. -/
structure K4WoTable (T : Thread Bk First.S Claim V W X Pb) (iWo : T.ι) {nR kC : Nat} (d : PubData)
    (rw : T.P × First.S → T.Wt → PileWit nR kC) (m : Nat) : Prop where
  /-- the library's sentence gives the thread's -/
  wo : ∀ w a y v, woAt d rw m a y v → T.means w iWo a y v

/-- **THE PENDING ROW HOLDS**, at every state behind the member's step, at every continuation. A
hypothesis's form. Nothing is claimed by the definition. -/
def K4WoHolds (T : Thread Bk First.S Claim V W X Pb)
    (At : Coins Bk → First.S → Mid W X → Env → Prop) (b : Nat) {nR kC : Nat} (d : PubData)
    (rw : T.P × First.S → T.Wt → PileWit nR kC) (m : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s mm E ds y cols s', At k s mm E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s mm E ds y cols s' → ∀ ds',
    woAt d rw m (T.seat k y.2 s') (T.strs (E.add y.1))
      (T.wit k y.2.st.input (y.2.st.heard ++ ds'))

/-- **K4's SHARE OF `Exchange` AT THE PENDING ROW's ITEM.** CONDITIONAL: on the table's parameters
and on the row's holding. -/
theorem k4_wo_share {T : Thread Bk First.S Claim V W X Pb} {iWo : T.ι} {nR kC : Nat} {d : PubData}
    {rw : T.P × First.S → T.Wt → PileWit nR kC} {m : Nat} (Tb : K4WoTable T iWo d rw m)
    {At : Coins Bk → First.S → Mid W X → Env → Prop} {b : Nat}
    (hW : K4WoHolds T At b d rw m) : ShareAt T At b [iWo] := by
  intro blk hblk k s mm E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  exact Tb.wo _ _ _ _ (hW blk hblk k s mm E ds y cols s' hA hd hS ds')

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_wo_share
