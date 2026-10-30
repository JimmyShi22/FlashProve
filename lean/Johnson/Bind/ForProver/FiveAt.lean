-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/FiveAt.lean: THE FIVE THINGS THAT THE LAWS ON THE HONEST SIDE OF THE LINEAR
CLAIM'S SHARED ROUNDS (THE SHARED CHAIN) TAKE FROM "THE INPUT IS VALID", SHOWN TOGETHER AT ONE SUCH
PREDICATE, WHERE THE TEST `rowsFit` PASSES AND THE CODE HAS AT MOST 2^32 POSITIONS: the committed
table has its columns, of the declared width (cols); each holds the rows' own symbols (tab); the
key's sizes fit (key); no seed of it has the factor 0 (seeds); each of its OOD answers is its row's
own (ans). A definition, statements and proofs.

Why. These five are proved in four files of this folder, of two terms: `storedW`
(Johnson/Bind/ForProver/TabCols.lean) and `oodSh` (Johnson/Bind/ForProver/Ood.lean, RecRows.lean,
RecRowsK14.lean). Whoever lays a thread of the shared chain needs them of one input. Here the input
is the frame's `ProofFile.Honest.Common`: the index, the stored tables' pads and encoding randomness, the
key (`OnBytes.TableKey`: a committed table's OOD sample, seeds and answers, with the item's number).

Main names (namespace `Bind.ForProver`).
  `validAt sh Z w`: the input's key is the key that this folder makes of the input's own index and
    coins, at some seed of the OOD sample and some copy's number, which `oodSh` does not read:
    `oodSh sh Z`. `validAt_oodSh`: at every index, all coins and every seed there is a valid input:
    the one with that key.
  **`fiveFields_at`**: at a value Z of `ProofFile.Pub`, where the test `rowsFit` passes and the code has
    at most 2^32 positions; Q: the shared chain's own parameters off Z (`Desc.K14.p14Of`): the five,
    each at every input that is valid at Z's own shape, the committed table's columns being `storedW
    Z` at the input's index and coins, the rows `ProofFile.Honest.K14.rowsOf` at these.
  **`fiveFields_inScope`**: at public files in the goals' scope, at every Z that the maker of the
    public part (`ProofFile.pubPlain`) returns of them: the same with no other premise on Z.

The form. Each of the five is written at these letters: the reader of the index the identity, the
reader of the coins `fun rc => ⟨(rc 0).pad, (rc 0).tail⟩`, the reading `Reading.gl`. Three things
are written out by their texts and not by the names that other files give them: the rows as read;
"no seed has the factor 0" (`noZeroFactor`, Johnson/Desc/ProofFile/Honest/K14/KeySeeds.lean); "each
answer is its row's own" (`Desc.K14.Honest.OwnAnswers` over `RowAnswer`,
Johnson/Desc/K14/Honest/ItemsEach.lean, Johnson/Desc/K14/Honest/Values.lean).

A limit on the coins, before the others. UNDER validAt, AT A FIXED INDEX AND KEY, THE PADS THAT THE
ANSWERS READ ARE NO COINS. answerAt = Σ over the plain places of entry · eq + factor · (pad 3 i, pad
3 i + 1, pad 3 i + 2) (`Bind.Twin.answerAt`, Johnson/Bind/Twin.lean); the factor is not 0 by type:
so (index, key) FIX these three pads of each row for each seed (reckoned by hand off the texts; no
theorem of this file says it; below, cut is the place where a row's pads begin, as in
`Bind.Column.Agree`, Johnson/Bind/ColumnDefs.lean). AT THE FULL SIZE s = 1 AND l − cut = 3: ALL PADS
OF EVERY ROW ARE FIXED; the tails alone stay free. That is the protocol's own state and no fault.
BUT: a law that takes the committer's pads as uniform and independent and ranges over w.rc with
w.key a letter under validAt (the form hw : Vd wr → validIdxAt … wr) would range over one point in
the pads: hollow in them, in silence. THE FORMS THAT ARE SAFE: among these files validAt_oodSh |
validIdxAt_oodIdxSh; in later files of this folder …_made | …_key | …_instOf: the coins come first
and the key is MADE of them. In a safe form the key is never a letter: it is written as the term
made of index, coins and seed. Where a statement stands at single values, the seed may be a letter,
bound with index and coins. Where it states a distribution over the coins, the seed too is written
as the term made of index and coins, at the run's own name (Johnson/Bind/ForProver/Ood.lean,
Limits): no letter for the seed beside the coins. And no strategy or simulator may branch on
validAt: it reads index and pads.

Limits. Columns and key are one committed table's; which of the protocol's tables it is, the first
or a copy, is not said here. The item 0 is a session's numbering, not the link's
(Johnson/Bind/ForProver/Enc.lean, Limits, "Which item"). THIS FILE NAMES NO STRUCTURE THAT ASKS
THESE FIVE AND BUILDS NO TERM OF ONE: THAT THEIR FORMS FIT A CALLER IS NOT COMPILED HERE. Of the
shared chain's honest side this file reaches Johnson/Desc/ProofFile/Honest/K14/Parts.lean and,
beneath it, Johnson/Desc/K14/Honest/Coded.lean (definitions alone). `validAt` is a predicate of this
file: that any thread's own "valid" implies it is not said; that the key which a prover reads is
`oodSh` is said here of no prover. The columns are `storedW Z`, not a prover's field `stored`. At
inputs whose index is read as `ProofFile.Honest.Weights` alone; at `Cm.Idx`:
Johnson/Bind/ForProver/FiveAtIndex.lean. `key` and `seeds` hold by make: the seed is typed, its
factors of a type without 0, and is spelled with words below the prime. Nothing on seeds that are
read off bytes. `cols` and `tab` hold at every input, valid or not. Z ranges over all values of the
structure `ProofFile.Pub` in `fiveFields_at`. In `fiveFields_inScope`: one direction, from a maker that
returns; that it returns at any files is no theorem of this file. The limits of the files named
above stand. At the reading `Reading.gl` and at no other. No completeness of any protocol, no index
privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.InScope
import Johnson.Bind.ForProver.RecRowsK14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (TableKey zeroE thetaE)
open OnBytes.Model (Reading)
open ProofFile.Honest (TableRand Weights Common)
open VerifiableInference.Desc.Own (keyFits allZero)
open Desc.K14.Law (genK eqK)

/-- **The input's key is the key of the input's own index and coins**, at some seed σ and some
copy's number n. Of the coins it reads `w.rc 0` alone. σ is fixed by the key (said here without a
theorem); n alone is free, and unread.
UNDER validAt, AT A FIXED INDEX AND KEY, THE PADS THAT THE ANSWERS READ ARE NO COINS.
Why, and which forms are safe: this file's head, «A limit on the coins». -/
def validAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (w : Common Weights (ℕ → TableRand) TableKey) :
    Prop :=
  ∃ sd : Seed sh × ℕ, w.key = oodSh sh Z ⟨w.w₀, w.rc, sd⟩

/-- At every index, all coins and every seed there is a valid input. -/
theorem validAt_oodSh (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (w₀ : Weights) (rc : ℕ → TableRand)
    (sd : Seed sh × ℕ) : validAt sh Z ⟨w₀, rc, oodSh sh Z ⟨w₀, rc, sd⟩⟩ :=
  ⟨sd, rfl⟩

/-- **The five at one valid.** -/
theorem fiveFields_at (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) (Q : Desc.K14.P14)
    (hQ : Q = Desc.K14.p14Of Z.p.chains l)
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true)
    (ha : (shapeOf Z).a ≤ 32) :
    (∀ w, validAt (shapeOf Z) Z w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
      ∃ u, storedW Z w.w₀ w.rc (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W) ∧
    (∀ w, validAt (shapeOf Z) Z w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        Reading.gl.val (OnBytes.ofF (((storedW Z w.w₀ w.rc Q.item x).getD []).toArray.getD r 0)) =
          genK Reading.gl Q.par.S.fold x (fun j => Reading.gl.val
            (ProofFile.Honest.K14.rowsOf Q.S w.w₀ ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j))) ∧
    (∀ w, validAt (shapeOf Z) Z w → keyFits w.key Q.par.S.fold.index = true) ∧
    (∀ w, validAt (shapeOf Z) Z w → (w.key.seeds.all (!allZero ·.beta)) = true) ∧
    (∀ w, validAt (shapeOf Z) Z w → ∀ x ∈ w.key.seeds.zipIdx, ∀ r < Q.par.S.fold.index.rows,
      (∑ j ∈ Finset.range Q.par.S.fold.index.plain, eqK (x.1.z.map Reading.gl.val) j *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S w.w₀ ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j)) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S w.w₀ ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r
            (Q.par.S.fold.index.padPlace x.2 t)) =
      Reading.gl.val (w.key.record.getD (r * Q.par.S.fold.index.answers + x.2) zeroE)) := by
  subst hQ
  refine ⟨fun w _ p hp => cols_at Z hfit w.w₀ w.rc l p hp,
    fun w _ x hx r hr => tab_at Z hfit w.w₀ w.rc ha x hx r hr, ?_, ?_, ?_⟩
  · rintro w ⟨sd, hk⟩
    rw [hk]
    exact keyFits_oodSh_of (shapeOf Z) Z _ rfl
  · rintro w ⟨sd, hk⟩
    rw [hk]
    exact factorsOwn_oodSh (shapeOf Z) Z _
  · rintro w ⟨sd, hk⟩
    rw [hk]
    exact ownAnswers_rowsOf_sh (shapeOf Z) Z rfl ⟨w.w₀, w.rc, sd⟩ hfit

/-- **The five at one valid, at files in scope.** -/
theorem fiveFields_inScope {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true) {o : ProofFile.SecondHashFunctionArgument}
    {Z : ProofFile.Pub} (h : ProofFile.pubPlain o P.pol P.lay P.KL = .ok Z) (l : List (ℕ × ℕ))
    (Q : Desc.K14.P14) (hQ : Q = Desc.K14.p14Of Z.p.chains l) :
    (∀ w, validAt (shapeOf Z) Z w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
      ∃ u, storedW Z w.w₀ w.rc (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W) ∧
    (∀ w, validAt (shapeOf Z) Z w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        Reading.gl.val (OnBytes.ofF (((storedW Z w.w₀ w.rc Q.item x).getD []).toArray.getD r 0)) =
          genK Reading.gl Q.par.S.fold x (fun j => Reading.gl.val
            (ProofFile.Honest.K14.rowsOf Q.S w.w₀ ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j))) ∧
    (∀ w, validAt (shapeOf Z) Z w → keyFits w.key Q.par.S.fold.index = true) ∧
    (∀ w, validAt (shapeOf Z) Z w → (w.key.seeds.all (!allZero ·.beta)) = true) ∧
    (∀ w, validAt (shapeOf Z) Z w → ∀ x ∈ w.key.seeds.zipIdx, ∀ r < Q.par.S.fold.index.rows,
      (∑ j ∈ Finset.range Q.par.S.fold.index.plain, eqK (x.1.z.map Reading.gl.val) j *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S w.w₀ ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j)) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S w.w₀ ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r
            (Q.par.S.fold.index.padPlace x.2 t)) =
      Reading.gl.val (w.key.record.getD (r * Q.par.S.fold.index.answers + x.2) zeroE)) :=
  fiveFields_at Z l Q hQ (rowsFit_inScope hP h) (a_inScope hP h)

end Bind.ForProver

#print axioms Bind.ForProver.validAt_oodSh
#print axioms Bind.ForProver.fiveFields_at
#print axioms Bind.ForProver.fiveFields_inScope
#print axioms Bind.ForProver.validAt
