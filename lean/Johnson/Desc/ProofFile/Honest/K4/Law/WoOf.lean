-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoOf.lean: CONDITIONAL: the hypothesis `K4WoHolds`
(Law/Wo.lean: the pending row on the committed matrix of weights, which K4's merge leaves, holds)
brought down to seven clauses on what the merge has left and on the witness. A definition of a
hypothesis, and statements with their proofs: calls of the library's `row_tie`
(Johnson/Top/H0/MergeLaw/WoRow.lean) and of `wo_holds` (Johnson/Road/K4/W/Wo.lean).

Not shown here. THAT ONE OF THE SEVEN HOLDS AT AN HONEST RUN. That the reader of the state gives a
row behind K4's step: where it gives none the sentence holds for nothing. THE READER rw OF THE
PILE OF PENDING ROWS IS TYPED HERE AT d.lay.lk COLUMN BITS; the library's own reader at its
full-size structure is typed at another term for that number, equal to it by a public fact alone:
SO THESE STATEMENTS CANNOT BE CALLED AT THAT READER AS THEY STAND: the forms to call are
Law/WoShareK.lean (general in the number of column bits) and, at the first chain's thread,
Law/WoHead.lean and Law/WoTop.lean. No example is known. Nothing on soundness, on completeness or
on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk of the imports that stops, unopened, at every
module under Johnson/Goal/, Johnson/D/ or ThirdParty/ and at the names RecCompile.Honest…, Both…
and PassH…: 28 modules whose names hold RecCompile; none under Johnson/Goal/ or ThirdParty/; none
under Johnson/D/, none of the three names.

  `K4WoAsks d s' wit`   whatever the open segment's sub-protocol has left at s' (w0), and whichever
      entry c the index masks' ledger gives next there: there are a matrix M, the merge's claims
      with their coefficients cr, and entries idx of the index masks, with:
        recs   what is left of the claims is made of cr at the merge's point;
        value  THE SHOWN END VALUE IS THE MERGE's FUNCTION OF M AT THAT POINT PLUS THE FACTOR TIMES
               ENTRY c: the one clause that speaks of what the prover has sent;
        point  the merge's point has as many coordinates as a column's number has bits;
        rows, zero   the witness's matrix has at most 2 ^ kRow rows, kRow the shape's number; M is
               0 beyond the witness's rows;
        mat    the witness's matrix is M;
        mask   the witness's mask entry at the index masks' message and c is idx c.
  `woAt_of_asks`: so the library's sentence `woAt` at that state and witness.
  `k4_woHolds_of_asks`: so K4WoHolds, where K4WoAsks holds behind the member's step at every
      continuation.

Who is meant to prove each. recs, point: whoever shows what K4's hearing returns. value: K4's
writers, in two halves: the shown word is the merge's end value plus the factor times the last
coin that the row spends; and that end value is the merge's function of the committed weights.
mask: a tie of that last coin to the witness: `K4IndexTieAt`. mat, rows, zero: a tie of the
witness's matrix to the committed weights: `K4WeightsTieAt` (both Law/WoTies.lean: hypotheses'
forms). WHAT LIES SINCE: Law/W/IndexOfOwn.lean (`k4IndexTie_of_own`) has `K4IndexTieAt` at the first
chain's thread from one equation on the Script's messages; Law/WoAtStand.lean has three of the seven
clauses from a stand; Law/WoJoin.lean and Law/WoTies.lean have `K4WoAsks` from parts. Of
`K4WeightsTieAt` nobody is known to us to prove it.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Wo
import Johnson.Road.K4.W.Wo
import Johnson.Top.H0.MergeLaw.WoRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E mulE)
open OnBytes.Model (Reading WsClaim wsRowPart wsEpsT)
open OnBytes.Road (Wm fmAt)
open OnBytes.Road.K4.W (rowOf wo_holds)
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.First.FillP1 (PileWit woAt PubData)
open VerifiableInference.Desc.First.MergeLaw (row_tie)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K13.Law (lowBits)
open Johnson.Desc.First.Walk.Law (leftOf ledgerAt rowAt)

/-- **What is asked of what the merge has left, and of the witness.** This defines a hypothesis; the
definition claims nothing. -/
def K4WoAsks (d : PubData) {nR : Nat} (s' : First.S) (wit : PileWit nR d.lay.lk) : Prop :=
  ∀ w0 l c l', leftOf s' = some w0 → ledgerAt s' = some l → takeEntry l = some (c, l') →
    ∃ (M : Wm Cb.Gl.E) (cr : List (WsClaim × E)) (idx : Nat → Cb.Gl.E),
      w0.recs = cr.map (fun y => wsRowPart d.lay y.1 (mulE y.2 (wsEpsT d.lay y.1 w0.rm))) ∧
      Reading.gl.val w0.fvp =
        fmAt Reading.gl d.lay M cr w0.rm + idx c * Reading.gl.val w0.beta ∧
      w0.rm.size = d.lay.lk ∧ nR ≤ 2 ^ d.lin.kRow ∧ (∀ j, nR ≤ j → ∀ C, M j C = 0) ∧
      (∀ (i : Fin nR) (C : Nat), C < 2 ^ d.lay.lk → wit.mat i (lowBits d.lay.lk C) = M i C) ∧
      wit.mask ⟨s'.out.indexMasks, c⟩ = idx c

/-- **The library's sentence on the pending row**, from the seven. CONDITIONAL. -/
theorem woAt_of_asks {P Wt : Type} {d : PubData} {nR : Nat}
    {rw : P × First.S → Wt → PileWit nR d.lay.lk} {m : Nat} {a : P × First.S}
    {y : VerifiableInference.Desc.Strs} {w : Wt} (h : K4WoAsks d a.2 (rw a w)) :
    woAt d rw m a y w := by
  intro r hr
  obtain ⟨w0, wp, l, c, l', b1, b2, b3, b4, rfl, -, -, -⟩ := row_tie hr
  obtain ⟨M, cr, idx, h1, h2, h3, h4, h5, h6, h7⟩ := h w0 l c l' b1 b3 b4
  exact wo_holds d.lay M w0 (d.ncl m) d.lin cr h1 b2 idx a.2.out.indexMasks c h2 (rw a w) h3 h4 h5
    h6 h7

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **`K4WoHolds`, from the seven behind the member's step.** CONDITIONAL. -/
theorem k4_woHolds_of_asks {T : Thread Bk First.S Claim V W X Pb}
    {At : Coins Bk → First.S → Mid W X → Env → Prop} {b : Nat} {d : PubData} {nR : Nat}
    {rw : T.P × First.S → T.Wt → PileWit nR d.lay.lk} {m : Nat}
    (h : ∀ blk, T.bs[b]? = some blk → ∀ k s mm E ds y cols s', At k s mm E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s mm E ds y cols s' → ∀ ds',
      K4WoAsks d (T.seat k y.2 s').2
        (rw (T.seat k y.2 s') (T.wit k y.2.st.input (y.2.st.heard ++ ds')))) :
    K4WoHolds T At b d rw m :=
  fun blk hblk k s mm E ds y cols s' hA hd hS ds' =>
    woAt_of_asks (h blk hblk k s mm E ds y cols s' hA hd hS ds')

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.woAt_of_asks
#print axioms ProofFile.Honest.K4.k4_woHolds_of_asks
