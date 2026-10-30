-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoTies.lean

What is here. The two ties on the witness that the pending row's item asks at the member of the
layers' own rounds (kind K4), each as its sentence at one state behind the member's step; and
`K4WoAsks` (Law/WoOf.lean) from them and three sentences on what the merge has left. Two
definitions, and one statement with its proof: a call of Law/WoJoin.lean.

  `K4IndexTieAt`: whichever entry the index masks' ledger gives next at the state behind, the
      witness's mask entry, as rw reads it, at the index masks' message and that entry is coin, at
      every continuation of the challenges. coin is meant as the reading of the last coin that
      K4's row spends: `K4MaskTieAt` (Law/ScriptAt.lean) stops one coin short of it.
  `K4WeightsTieAt`: three conjuncts, OF WHICH THE FIRST TWO READ NO STATE: the witness's matrix
      has at most 2 ^ kRow rows (a public number); M IS 0 BEYOND THEM (M is meant as the committed
      weights as the honest side reads them: so this is a fact on the honest INPUT: by the
      threads' rule it must come from `T.valid` or stay a named hypothesis); and, at the state,
      the witness's matrix, as rw reads it, is M on its own rows.
  `k4WoAsks_of_ties`: K4WoAsks at every continuation, from the two ties and recs · value · point.

Limits. HYPOTHESES' FORMS: nothing shows either tie of any thread. Both speak of the thread's
parameter wit, the witness that the items' sentences read, through the reader rw: so they are
meant for whoever defines that parameter from what the committing program has written: the first
says what stands under the index masks' message, the second that the stored table is the weights'.
THE READER rw OF THE PILE OF PENDING ROWS IS TYPED HERE AT d.lay.lk COLUMN BITS; the library's own
reader at its full-size structure is typed at another term for that number, equal to it by a
public fact alone: SO THESE STATEMENTS CANNOT BE CALLED AT THAT READER AS THEY STAND: the forms to
call are Law/WoShareK.lean (general in the number of column bits) and, at the first chain's
thread, Law/WoHead.lean and Law/WoTop.lean. No example is known. Nothing on soundness, on
completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E mulE)
open OnBytes.Model (Reading WsClaim WsForkOut wsRowPart wsEpsT)
open OnBytes.Road (Wm fmAt)
open VerifiableInference.Desc (Claim First.S)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K13.Law (lowBits)
open Johnson.Desc.First.Walk.Law (leftOf ledgerAt)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **The witness's mask entry under the index masks' next entry is the coin.** This defines a
hypothesis; the definition claims nothing. -/
def K4IndexTieAt (T : Thread Bk First.S Claim V W X Pb) {nR kC : Nat}
    (rw : T.P × First.S → T.Wt → PileWit nR kC) (k : Coins Bk) (y : Mid W X) (s' : First.S)
    (coin : Cb.Gl.E) : Prop :=
  ∀ ds' l c l', ledgerAt (T.seat k y s').2 = some l → takeEntry l = some (c, l') →
    (rw (T.seat k y s') (T.wit k y.st.input (y.st.heard ++ ds'))).mask
      ⟨(T.seat k y s').2.out.indexMasks, c⟩ = coin

/-- **The witness's matrix is M.** This defines a hypothesis; the definition claims nothing. -/
def K4WeightsTieAt (T : Thread Bk First.S Claim V W X Pb) (d : PubData) {nR : Nat}
    (rw : T.P × First.S → T.Wt → PileWit nR d.lay.lk) (k : Coins Bk) (y : Mid W X) (s' : First.S)
    (M : Wm Cb.Gl.E) : Prop :=
  nR ≤ 2 ^ d.lin.kRow ∧ (∀ j, nR ≤ j → ∀ C, M j C = 0) ∧
    ∀ ds' (i : Fin nR) (C : Nat), C < 2 ^ d.lay.lk →
      (rw (T.seat k y s') (T.wit k y.st.input (y.st.heard ++ ds'))).mat i (lowBits d.lay.lk C) =
        M i C

/-- **`K4WoAsks` AT EVERY CONTINUATION, FROM THE TWO TIES.** CONDITIONAL. -/
theorem k4WoAsks_of_ties {T : Thread Bk First.S Claim V W X Pb} {d : PubData} {nR : Nat}
    {rw : T.P × First.S → T.Wt → PileWit nR d.lay.lk} {k : Coins Bk} {y : Mid W X}
    {s' : First.S} {wo : WsForkOut} (hleft : leftOf (T.seat k y s').2 = some wo)
    (M : Wm Cb.Gl.E) (cr : List (WsClaim × E)) (coin : Cb.Gl.E)
    (recs : wo.recs = cr.map (fun z => wsRowPart d.lay z.1 (mulE z.2 (wsEpsT d.lay z.1 wo.rm))))
    (value : Reading.gl.val wo.fvp =
      fmAt Reading.gl d.lay M cr wo.rm + coin * Reading.gl.val wo.beta)
    (point : wo.rm.size = d.lay.lk) (Ix : K4IndexTieAt T rw k y s' coin)
    (Wt : K4WeightsTieAt T d rw k y s' M) (ds' : List Fmt.Drawn) :
    K4WoAsks d (T.seat k y s').2
      (rw (T.seat k y s') (T.wit k y.st.input (y.st.heard ++ ds'))) :=
  k4WoAsks_of hleft M cr coin recs value point Wt.1 Wt.2.1 (Wt.2.2 ds') (Ix ds')

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4WoAsks_of_ties
