-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/FiveAtIndex.lean: THE FIVE OF Johnson/Bind/ForProver/FiveAt.lean AT INPUTS
WHOSE INDEX IS READ AS `Cm.Idx`, the index type of the frame's filling at the full size, WHERE THE
TEST `rowsFit` PASSES AND THE CODE HAS AT MOST 2^32 POSITIONS: the committed table has its columns,
of the declared width (cols); each holds the rows' own symbols (tab); the key's sizes fit (key); no
seed of it has the factor 0 (seeds); each of its OOD answers is its row's own (ans). A definition,
statements and proofs.

Main names (namespace `Bind.ForProver`).
  `validIdxAt sh Z w`: the input's key is `oodIdxSh sh Z` (Johnson/Bind/ForProver/OodAtIndex.lean)
    at the input's own index and coins, at some seed of the OOD sample and some copy's number, which
    `oodIdxSh` does not read. `validIdxAt_oodIdxSh`: at every index, all coins and every seed there
    is a valid input.
  **`fiveFieldsIdx_at`**: as `fiveFields_at`, the reader of the index being
    `fun i => ⟨OnBytes.HonestTrace.entryOf i⟩`.
  **`fiveFieldsIdx_inScope`**: at public files in the goals' scope, at every Z that the maker of the
    public part (`ProofFile.pubPlain`) returns of them: the same with no other premise on Z.

A limit on the coins, before the others. UNDER validAt, AT A FIXED INDEX AND KEY, THE PADS THAT THE
ANSWERS READ ARE NO COINS. (Alike under `validIdxAt`; why: Johnson/Bind/ForProver/FiveAt.lean, under
the same heading.) That is the protocol's own state and no fault. BUT: a law that takes the
committer's pads as uniform and independent and ranges over w.rc with w.key a letter under validAt
(the form hw : Vd wr → validIdxAt … wr) would range over one point in the pads: hollow in them, in
silence. THE FORMS THAT ARE SAFE: among these files validAt_oodSh | validIdxAt_oodIdxSh; in later
files of this folder …_made | …_key | …_instOf: the coins come first and the key is MADE of them. In
a safe form the key is never a letter: it is written as the term made of index, coins and seed.
Where a statement stands at single values, the seed may be a letter, bound with index and coins.
Where it states a distribution over the coins, the seed too is written as the term made of index and
coins, at the run's own name (Johnson/Bind/ForProver/Ood.lean, Limits): no letter for the seed
beside the coins. And no strategy or simulator may branch on validAt: it reads index and pads.

Limits. Those of Johnson/Bind/ForProver/FiveAt.lean, each read at this index type: above all, this
file names no structure that asks these five and builds no term of one: that their forms fit a
caller is not compiled here. The item 0 is a session's numbering, not the link's
(Johnson/Bind/ForProver/Enc.lean, Limits, "Which item"). All of it means something at the full
size's shape alone: `Cm.Idx` is typed at the reference sizes. No completeness of any protocol, no
index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.FiveAt
import Johnson.Bind.ForProver.RecRowsAtIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (TableKey zeroE thetaE)
open OnBytes.Model (Reading)
open ProofFile.Honest (TableRand Common)
open VerifiableInference.Desc.Own (keyFits allZero)
open Desc.K14.Law (genK eqK)

/-- **The input's key is the key of the input's own index and coins**, the index read as `Cm.Idx`,
at some seed σ and some copy's number n. Of the coins it reads `w.rc 0` alone. σ is fixed by the key
(said here without a theorem); n alone is free, and unread. Of `validAt`
(Johnson/Bind/ForProver/FiveAt.lean), and alike of this form of it: UNDER validAt, AT A FIXED INDEX
AND KEY, THE PADS THAT THE ANSWERS READ ARE NO COINS. Why, and which forms are safe: that file's
head, «A limit on the coins». -/
def validIdxAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (w : Common Cm.Idx (ℕ → TableRand) TableKey) :
    Prop :=
  ∃ sd : Seed sh × ℕ, w.key = oodIdxSh sh Z ⟨w.w₀, w.rc, sd⟩

/-- At every index, all coins and every seed there is a valid input. -/
theorem validIdxAt_oodIdxSh (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (i : Cm.Idx)
    (rc : ℕ → TableRand) (sd : Seed sh × ℕ) :
    validIdxAt sh Z ⟨i, rc, oodIdxSh sh Z ⟨i, rc, sd⟩⟩ :=
  ⟨sd, rfl⟩

/-- **The five at one valid, the index read as `Cm.Idx`.** -/
theorem fiveFieldsIdx_at (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) (Q : Desc.K14.P14)
    (hQ : Q = Desc.K14.p14Of Z.p.chains l)
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true)
    (ha : (shapeOf Z).a ≤ 32) :
    (∀ w, validIdxAt (shapeOf Z) Z w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
      ∃ u, storedW Z ⟨OnBytes.HonestTrace.entryOf w.w₀⟩ w.rc
          (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        Reading.gl.val (OnBytes.ofF
            (((storedW Z ⟨OnBytes.HonestTrace.entryOf w.w₀⟩ w.rc Q.item x).getD
              []).toArray.getD r 0)) =
          genK Reading.gl Q.par.S.fold x (fun j => Reading.gl.val
            (ProofFile.Honest.K14.rowsOf Q.S ⟨OnBytes.HonestTrace.entryOf w.w₀⟩
              ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j))) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → keyFits w.key Q.par.S.fold.index = true) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → (w.key.seeds.all (!allZero ·.beta)) = true) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → ∀ x ∈ w.key.seeds.zipIdx, ∀ r < Q.par.S.fold.index.rows,
      (∑ j ∈ Finset.range Q.par.S.fold.index.plain, eqK (x.1.z.map Reading.gl.val) j *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S ⟨OnBytes.HonestTrace.entryOf w.w₀⟩
            ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j)) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S ⟨OnBytes.HonestTrace.entryOf w.w₀⟩
            ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r (Q.par.S.fold.index.padPlace x.2 t)) =
      Reading.gl.val (w.key.record.getD (r * Q.par.S.fold.index.answers + x.2) zeroE)) := by
  subst hQ
  refine ⟨fun w _ p hp => cols_at Z hfit _ w.rc l p hp,
    fun w _ x hx r hr => tab_at Z hfit _ w.rc ha x hx r hr, ?_, ?_, ?_⟩
  · rintro w ⟨sd, hk⟩
    rw [hk]
    exact keyFits_oodIdxSh_of (shapeOf Z) Z _ rfl
  · rintro w ⟨sd, hk⟩
    rw [hk]
    exact factorsOwn_oodIdxSh (shapeOf Z) Z _
  · rintro w ⟨sd, hk⟩
    rw [hk]
    exact ownAnswers_rowsOf_idx (shapeOf Z) Z ⟨w.w₀, w.rc, sd⟩ rfl hfit

/-- **The same at files in scope.** -/
theorem fiveFieldsIdx_inScope {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true) {o : ProofFile.SecondHashFunctionArgument}
    {Z : ProofFile.Pub} (h : ProofFile.pubPlain o P.pol P.lay P.KL = .ok Z) (l : List (ℕ × ℕ))
    (Q : Desc.K14.P14) (hQ : Q = Desc.K14.p14Of Z.p.chains l) :
    (∀ w, validIdxAt (shapeOf Z) Z w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
      ∃ u, storedW Z ⟨OnBytes.HonestTrace.entryOf w.w₀⟩ w.rc
          (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        Reading.gl.val (OnBytes.ofF
            (((storedW Z ⟨OnBytes.HonestTrace.entryOf w.w₀⟩ w.rc Q.item x).getD
              []).toArray.getD r 0)) =
          genK Reading.gl Q.par.S.fold x (fun j => Reading.gl.val
            (ProofFile.Honest.K14.rowsOf Q.S ⟨OnBytes.HonestTrace.entryOf w.w₀⟩
              ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j))) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → keyFits w.key Q.par.S.fold.index = true) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → (w.key.seeds.all (!allZero ·.beta)) = true) ∧
    (∀ w, validIdxAt (shapeOf Z) Z w → ∀ x ∈ w.key.seeds.zipIdx, ∀ r < Q.par.S.fold.index.rows,
      (∑ j ∈ Finset.range Q.par.S.fold.index.plain, eqK (x.1.z.map Reading.gl.val) j *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S ⟨OnBytes.HonestTrace.entryOf w.w₀⟩
            ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r j)) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          Reading.gl.val (ProofFile.Honest.K14.rowsOf Q.S ⟨OnBytes.HonestTrace.entryOf w.w₀⟩
            ⟨(w.rc 0).pad, (w.rc 0).tail⟩ r (Q.par.S.fold.index.padPlace x.2 t)) =
      Reading.gl.val (w.key.record.getD (r * Q.par.S.fold.index.answers + x.2) zeroE)) :=
  fiveFieldsIdx_at Z l Q hQ (rowsFit_inScope hP h) (a_inScope hP h)

end Bind.ForProver

#print axioms Bind.ForProver.validIdxAt_oodIdxSh
#print axioms Bind.ForProver.fiveFieldsIdx_at
#print axioms Bind.ForProver.fiveFieldsIdx_inScope
#print axioms Bind.ForProver.validIdxAt
