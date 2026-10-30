-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FiveFields.lean: kind K14: THE FIVE FIELDS OF K14Asks
(Honest/K14/Asks.lean) THAT SPEAK OF THE COMMITTED TABLE AND THE KEY (cols, tab, key, seeds, ans),
AS ONE STRUCTURE ON LETTERS (free parameters: valid, stored, weights, rand), IN A FILE THAT STANDS
OVER NO THREAD: so that whoever writes an index committer in Lean can import it and state these five
by this kind's own names. It imports Honest/K14/KeySeeds.lean (noZeroFactor),
Johnson/Desc/K14/Honest/ItemsEach.lean (OwnAnswers; through it Inputs,
Johnson/Desc/K14/Honest/ChainHolds.lean, and RowAnswer, Johnson/Desc/K14/Honest/Values.lean) and
Honest/K14/Parts.lean (rowsOf): of the frame only what Parts.lean imports. Definitions, and
statements with their proofs.

  rowsK           the committed table's rows before encoding, as the kind's two readers make them of
                  an input, read in the field: what K14Asks names as the field Rw of holds2. Its
                  limits are rowsOf's: Limits, below
  FiveFields Q valid stored weights rand **the structure**: five implications from valid. valid:
                  which inputs are meant. stored: the committed table's columns, by the input, the
                  statement's item and the position
  ownAnswers_of   the field ans gives OwnAnswers at every Inputs whose rows are rowsK
  fiveFields_of_texts **the structure from the five sentences WRITTEN OUT**: noZeroFactor, RowAnswer
                  and rowsK unfolded, the reading under its library's name: each by unfolding

HOW IT PARTS FROM K14Asks' OWN TEXT. There tab names (holds2 Q weights rand k w).Rw, at every run's
coins k, and ans names OwnAnswers at holds2 whole, which reads of it that field alone; holds2
(Honest/K14/Holds2.lean) stands over the thread's files. Its field Rw reads none of the run's coins
k; the index committer's coins it reads, through rand: it is rowsK by that definition's own line.
Here rowsK stands in its place, k is gone, and OwnAnswers' body is written out. That the two say the
same: Honest/K14/FiveFieldsAsks.lean.

A LINE ON THIS FILE AND ITS FELLOW (Honest/K14/FiveFields.lean,
Honest/K14/FiveFieldsAsks.lean), set here to the letter: «K14's five fields on the committed table
and the key, as one structure over letters (valid · stored · weights · rand): the stored columns at
their width, the table as the encoding of the rows made of the weights and the committer's
randomness, the key's sizes and seeds, and each answer as its row's own: what an honest committer's
outputs ARE, each an implication from valid; completeness's kind; no run's coin is read; no measure,
no simulator; NOT IN FRONT OF A LAW OVER THE COMMITTER's RANDOMNESS UNLESS THE KEY AND THE STORED
TABLE ARE MADE OF THE COINS: under a valid that leaves them letters, ans and tab fix the pads and
tails (the limit in Johnson/Bind/ForProver/FiveAt.lean's head)»

Limits at these fields; all but the last as Honest/K14/Asks.lean's head and Honest/K14/Parts.lean's
Limits have them. rowsOf is the committed rows' text only where the library's test on the shape
accepts (LinShape.ok, OnBytes/Iop/Lin.lean): elsewhere its first clause lays an entry of the matrix
where a pad is due; what stands in a row between the matrix's entries and the pads is laid as 0 and
held against no page; nothing holds rowsOf against the program that makes a committed table. Q is a
free parameter here, and no field asks that test. tab reads with defaults: a column that stored does
not return counts as the empty list, an entry beyond a column's end as 0. cols names its range by
readsAtLoc, tab by the code's logN: no field says that the two agree. seeds is a test on the three
WORDS of a factor (allZero, Johnson/Desc/Own/Rows.lean); ans reads the factor as a RESIDUE
(Reading.gl, OnBytes/Model/HideLaws.lean): a factor spelled with the prime in each word passes seeds
and reads as 0 in ans (reckoned by hand off the two texts; no theorem); no field asks words below
the prime.

What is not claimed. That the structure holds at any valid and stored: at valid := fun _ => False it
holds for nothing (vacuously: each field is an implication from valid). EACH OF THE FIVE IS A DEBT
THAT AN INDEX COMMITTER's MAKE IS TO MEET; none is met by laying the fact into valid: THAT IS A RULE
OF USE AND NO THEOREM (Honest/Thread/Thr.lean's head, (V); Honest/K14/Asks.lean's head repeats it):
at the type valid is a free parameter, and at a valid that is the conjunction of the five facts
there is a term of the structure. WHAT valid MUST BEAR ALL THE SAME, though (V) means valid to bear
no clause on a key: w.key is a free component of w (Common, Honest/Frame.lean), which the type ties
to w.w₀ and w.rc in no way: at a valid that is not empty and says nothing of the key, the fields key
and seeds are false, and ans too where the shape has a row (reckoned by hand; no theorem). That the
key is the one MADE of the index, the committer's coins and a seed is such a clause, and is none of
the five facts: validAt (Johnson/Bind/ForProver/FiveAt.lean) is that.
WHO MEETS THE FIVE. fiveFields_at and fiveFields_inScope (Johnson/Bind/ForProver/FiveAt.lean) prove
the five sentences in the form of fiveFields_of_texts' premises (by a comparison of the two texts;
compiled in neither file), at validAt and the columns storedW, at Q the shared chain's own
parameters off a value Z of ProofFile.Pub (Desc.K14.p14Of), the index read as it is and the coins as rc
0's pads and tails: the first where the test rowsFit passes and the code has at most 2^32 positions;
the second at every Z that the maker of the public part (ProofFile.pubPlain) returns of public files in
scope, with no other premise on Z; that it returns at any files is not shown there. How rowsFit
stands to LinShape.ok (Limits, above) is not said here. validAt_oodSh: at every index, all coins and
every seed there is a valid input. By that file's own head: it builds no term of this structure, and
that the forms fit a caller is not compiled there; that a thread's own valid implies validAt, that
the key which a prover reads is the made key, and that a prover's stored table is storedW, it does
not say.

Of this file: nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.KeySeeds
import Johnson.Desc.ProofFile.Honest.K14.Parts
import Johnson.Desc.K14.Honest.ItemsEach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey zeroE thetaE ofF)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc.Own (keyFits allZero)
open Desc.K14 (P14)
open Desc.K14.Honest (Inputs OwnAnswers RowAnswer)
open Desc.K14.Law (genK eqK)

variable {W₀ Rc : Type}

/-- The committed table's rows before encoding, as the two readers make them of an input, read in
the field. Its limits are rowsOf's: this file's head, Limits. -/
noncomputable def rowsK (Q : P14) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (w : Common W₀ Rc TableKey) (r j : ℕ) : Cb.Gl.E :=
  rdE.val (rowsOf Q.S (weights w.w₀) (rand w.rc) r j)

/-- **The five fields on the committed table and the key.** -/
structure FiveFields (Q : P14) (valid : Common W₀ Rc TableKey → Prop)
    (stored : Common W₀ Rc TableKey → ℕ → ℕ → Option (List UInt64)) (weights : W₀ → Weights)
    (rand : Rc → TableRand) : Prop where
  /-- every column that "LOC" can read is at hand, at its width -/
  cols : ∀ w, valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
    ∃ u, stored w (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
      u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W
  /-- each column holds the rows' own symbols (read with defaults: this file's head, Limits) -/
  tab : ∀ w, valid w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
    ∀ r < Q.par.S.fold.index.rows,
      rdE.val (ofF (((stored w Q.item x).getD []).toArray.getD r 0)) =
        genK rdE Q.par.S.fold x (rowsK Q weights rand w r)
  /-- the key's answers and seeds have the planned sizes -/
  key : ∀ w, valid w → keyFits w.key Q.par.S.fold.index = true
  /-- no seed of the key has the factor 0 (a test on its three words: this file's head, Limits) -/
  seeds : ∀ w, valid w → noZeroFactor w.key = true
  /-- each answer of the key is its row's own -/
  ans : ∀ w, valid w → ∀ x ∈ w.key.seeds.zipIdx, ∀ r < Q.par.S.fold.index.rows,
    RowAnswer Q.par.S.fold.index (x.1.z.map rdE.val) (rdE.val x.1.beta)
      (fun t => rdE.val (thetaE t)) x.2 (rowsK Q weights rand w r)
      (rdE.val (w.key.record.getD (r * Q.par.S.fold.index.answers + x.2) zeroE))

variable {Q : P14} {valid : Common W₀ Rc TableKey → Prop}
  {stored : Common W₀ Rc TableKey → ℕ → ℕ → Option (List UInt64)} {weights : W₀ → Weights}
  {rand : Rc → TableRand}

/-- The field ans gives OwnAnswers at every Inputs whose rows are rowsK: OwnAnswers reads no other
field. -/
theorem ownAnswers_of (F : FiveFields Q valid stored weights rand) (w : Common W₀ Rc TableKey)
    (hw : valid w) (H : Inputs) (hH : H.Rw = rowsK Q weights rand w) : OwnAnswers Q w.key H := by
  intro x hx r hr
  rw [hH]
  exact F.ans w hw x hx r hr

/-- **The structure from the five sentences written out.** The fourth is noZeroFactor's text; the
fifth RowAnswer's; rowsK is unfolded in the second and the fifth; the reading stands under its
library's name. -/
theorem fiveFields_of_texts
    (cols : ∀ w, valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
      ∃ u, stored w (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W)
    (tab : ∀ w, valid w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        OnBytes.Model.Reading.gl.val (ofF (((stored w Q.item x).getD []).toArray.getD r 0)) =
          genK OnBytes.Model.Reading.gl Q.par.S.fold x (fun j => OnBytes.Model.Reading.gl.val
            (rowsOf Q.S (weights w.w₀) (rand w.rc) r j)))
    (key : ∀ w, valid w → keyFits w.key Q.par.S.fold.index = true)
    (seeds : ∀ w, valid w → (w.key.seeds.all (!allZero ·.beta)) = true)
    (ans : ∀ w, valid w → ∀ x ∈ w.key.seeds.zipIdx, ∀ r < Q.par.S.fold.index.rows,
      (∑ j ∈ Finset.range Q.par.S.fold.index.plain,
          eqK (x.1.z.map OnBytes.Model.Reading.gl.val) j *
            OnBytes.Model.Reading.gl.val (rowsOf Q.S (weights w.w₀) (rand w.rc) r j)) +
        ∑ t ∈ Finset.range 3,
          OnBytes.Model.Reading.gl.val x.1.beta * OnBytes.Model.Reading.gl.val (thetaE t) *
            OnBytes.Model.Reading.gl.val (rowsOf Q.S (weights w.w₀) (rand w.rc) r
              (Q.par.S.fold.index.padPlace x.2 t)) =
      OnBytes.Model.Reading.gl.val
        (w.key.record.getD (r * Q.par.S.fold.index.answers + x.2) zeroE)) :
    FiveFields Q valid stored weights rand :=
  ⟨cols, tab, key, seeds, ans⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.rowsK
#print axioms ProofFile.Honest.K14.FiveFields
#print axioms ProofFile.Honest.K14.ownAnswers_of
#print axioms ProofFile.Honest.K14.fiveFields_of_texts
