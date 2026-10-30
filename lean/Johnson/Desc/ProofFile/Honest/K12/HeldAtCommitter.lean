-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/HeldAtCommitter.lean

What of the premises of `onFreeT_head_U_left` (OnFreeTAtHeadULeft.lean) is had at the shared rounds'
authors' own readers of the input and at the committer in Lean (Johnson/Bind/ForProver/). Five
theorems.

  `sendShapes_head`: `SendShapes` (Honest/K14/SendingsShows.lean) under the head.
  `rows_held`: `LeftAt`'s field rows, where the senders are handed the rows whole (`witOf`,
      Honest/K14/PaidAll.lean).
  `held_rows_read`: under the head, at the filling's reader of the index committer's coins
      (`randNow`, Honest/K14/AtFilling.lean): `heldAt`'s rows are `rowsRead`
      (ValuesAtCommitter.lean).
  `answers_held`, `columns_held`: `OwnAnswers` and `OwnColumns` at `heldAt`, at the committer's own
      key and columns.

By what. `written_at_head`, `qAt_written` (FitAtHead.lean); the shared rounds' authors'
`sendShapes_real` (Honest/K14/SendingsShowsAt.lean), and the two lines of their `holds2_rows`
(Honest/K14/Holds2.lean), typed anew at `heldAt`; `ownAnswers_made`, `ownColumns_made`
(ValuesAtCommitter.lean).

Beside it, by report of the shared rounds' authors (those files were not read for this one):
their Honest/K14/FiveFields.lean (ownAnswers_of) and FiveFieldsAsks.lean
(five_gives), and eight files of the committer's authors under Johnson/Bind/ForProver/, take the
same step from the same fifth field of `fiveFields_inScope` as `ownAnswers_made`, over a structure
of their own, and end at a thread's letters with the key a letter.

Limits.
- `LeftAt`'s field answers stands at the instance's key, a letter. `answers_held` stands at the term
  that the committer makes. That an instance's key is that term is said of no prover and no instance
  here; how such a tie may be taken is what FiveAt.lean's paragraph "A limit on the coins, before
  the others" is about (ValuesAtCommitter.lean quotes four sentences of it).
- `columns_held` takes hV: that a view's columns for "LOC" are the committer's columns' words. That
  a run's view has such columns is not shown here.
- The fields coin and tie are not treated.
- All limits of ValuesAtCommitter.lean's and Sim/ShownAtRun.lean's heads stand. It moves no count.
  Nothing on completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShownAtRun
import Johnson.Desc.ProofFile.Honest.K12.ValuesAtCommitter
import Johnson.Desc.ProofFile.Honest.K14.SendingsShowsAt
import Johnson.Desc.ProofFile.Honest.K14.AtFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (E TableKey)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (P14)
open Desc.K14.Honest (OwnAnswers OwnColumns View8)
open ProofFile.Honest (Common Weights TableRand)
open ProofFile.Honest.K14 (SendShapes sendShapes_real Data entriesOf rowsOf witOf randNow)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The three public facts on the sendings' shapes hold under the head.** -/
theorem sendShapes_head (h : P5J.AtMg o Z D r₀ Zp Np cF) : SendShapes (K1.qAt Zp Np) := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨x', hx', hS⟩ := sendShapes_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (hx.symm.trans hx'))
  rw [qAt_written Wr Np]
  exact hS 0 _

/-- **`LeftAt`'s field rows at the shared rounds' authors' own reader.** Where the senders are
handed the rows whole (`witOf`, Honest/K14/PaidAll.lean) at the reader wts of the index that
"SPLIT"'s part has too: at the places that hold the matrix, what `heldAt` holds is the entries that
"SPLIT"'s part is handed, read. General in the parameters, the input and the coins. -/
theorem rows_held {W₀ Rc : Type} (Q : P14) (A : Data) (hS : A.S = Q.par.S) (wts : W₀ → Weights)
    (rand : Rc → TableRand) (c : Common W₀ Rc TableKey) (csU csO : Array E) (r j : ℕ)
    (hj : j < Q.par.S.matrixRows * 2 ^ Q.par.S.kLo) :
    (heldAt Q (witOf Q wts rand c) csU csO).Rw r j = rdE.val (entriesOf A.S (wts c.w₀) r j) := by
  have hj' : j < Q.S.matrixRows * 2 ^ Q.S.kLo := hj
  show rdE.val (rowsOf Q.S (wts c.w₀) (rand c.rc) r j) = _
  unfold rowsOf
  rw [if_pos hj', hS]
  rfl

/-- Under the head, at the filling's own reader of the index committer's coins (`randNow`,
Honest/K14/AtFilling.lean): `heldAt`'s rows are `rowsRead` (ValuesAtCommitter.lean): the plan's item
is the item 0. -/
theorem held_rows_read {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF) (wts : W₀ → Weights)
    (c : Common W₀ (ℕ → TableRand) TableKey) (csU csO : Array E) :
    (heldAt (K1.qAt Zp Np) (witOf (K1.qAt Zp Np) wts (randNow (K1.qAt Zp Np)) c) csU csO).Rw =
      rowsRead (K1.qAt Zp Np) (wts c.w₀) c.rc := by
  obtain ⟨x, -, Wr⟩ := written_at_head h
  have e0 : (K1.qAt Zp Np).item = 0 := by rw [qAt_written Wr Np]
  funext r j
  show rdE.val (rowsOf (K1.qAt Zp Np).S (wts c.w₀)
    ⟨(c.rc (K1.qAt Zp Np).item).pad, (c.rc (K1.qAt Zp Np).item).tail⟩ r j) = _
  rw [e0]
  rfl

/-- **`OwnAnswers` at `heldAt`, at the key that the committer in Lean makes.** Under the head, at
every index, all coins and every seed: the key is the term made of these, no letter. Of that form
Johnson/Bind/ForProver/FiveAt.lean's head, under "A limit on the coins, before the others", says:
"In a safe form the key is never a letter: it is written as the term made of index, coins and seed."
Whether that suffices is that folder's authors' and the review's to say, not this file's. The letter
c holds a key too (c.key): nothing here reads it, and nothing ties it to the term. -/
theorem answers_held {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF) (wts : W₀ → Weights)
    (c : Common W₀ (ℕ → TableRand) TableKey)
    (sd : Bind.ForProver.Seed (Bind.ForProver.shapeOf Zp) × ℕ) (csU csO : Array E) :
    OwnAnswers (K1.qAt Zp Np)
      (Bind.ForProver.oodSh (Bind.ForProver.shapeOf Zp) Zp ⟨wts c.w₀, c.rc, sd⟩)
      (heldAt (K1.qAt Zp Np) (witOf (K1.qAt Zp Np) wts (randNow (K1.qAt Zp Np)) c) csU csO) :=
  ownAnswers_made h (wts c.w₀) c.rc sd _ (held_rows_read h wts c csU csO)

/-- **`OwnColumns` at `heldAt`**, where each column that a view holds for "LOC" is the words of the
committer's column at its position. -/
theorem columns_held {W₀ : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF) (wts : W₀ → Weights)
    (c : Common W₀ (ℕ → TableRand) TableKey) (csU csO : Array E) (V : View8)
    (hV : ∀ x col, V.cols.lookup x = some col →
      col = (Bind.ForProver.storedW Zp (wts c.w₀) c.rc (K1.qAt Zp Np).item x).getD []) :
    OwnColumns (K1.qAt Zp Np) V
      (heldAt (K1.qAt Zp Np) (witOf (K1.qAt Zp Np) wts (randNow (K1.qAt Zp Np)) c) csU csO) :=
  ownColumns_made h (wts c.w₀) c.rc _ (held_rows_read h wts c csU csO) V hV

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.sendShapes_head
#print axioms ProofFile.Honest.K12.Light.rows_held
#print axioms ProofFile.Honest.K12.Light.held_rows_read
#print axioms ProofFile.Honest.K12.Light.answers_held
#print axioms ProofFile.Honest.K12.Light.columns_held
