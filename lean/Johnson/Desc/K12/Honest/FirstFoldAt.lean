-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstFoldAt.lean: the single rows that a fold of the proximity test returns
on the term's own rounds are true at the three folded messages, at any statement. One theorem with
its proof, general in every parameter. `first_V` (Johnson/Desc/K12/Honest/FirstValues.lean) calls it
at the first stage. It depends on no frame for an honest side.

The twin of `fold_at` (Johnson/Prover/Link/BodyStepAt.lean), which asks the whole of `FoldFront` of
the verifier's state in front; here one clause of it is asked, at a statement that is a letter: so
the law serves the arm in which the fold's own first message brings the fresh table too. In Lean's
names: `fold_at` has this conclusion at S := `t.st`, the statement of a state t (`T12`), and at
F := `ioppFoldShape c L`, under `FoldFront` (Johnson/Prover/Link/FormFold.lean), a structure of
hypotheses on t, and under hypotheses like hk to hpk below. Here S is a free parameter. The one
clause is `FoldFront.rowFits`, in the form of hok below: the two forms are equal by
`Own.foldRowFits_agrees` (Johnson/Desc/Own/FoldAgree.lean) and `foldRowFits_spent`
(Johnson/Prover/Link/FormFoldLaws.lean). The clause `FoldFront.mask`, which is `t.mask = some id`,
is not among the hypotheses here.

In the list: the term is `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean); `aFold` is its list of
one fold's rounds, and `aPoint` is the point read off the sampled challenges D. s is `sgOf cur`
(Johnson/Desc/K12/Law/ChainOf.lean): the sizes of the stage cur. P (`PS`,
Johnson/Prover/Link/BodyState.lean) is what a prover holds at a stage: `μOf s P` is its message, and
the fresh table is its field `fM`, read as `φOf s P`. W is `K.W s j`: a family of coefficients, a
field of K (`BCoins`, Johnson/Prover/Link/BodyAll.lean). S (`Statement`, OnBytes/Iop/Ground.lean)
has codes, oracle messages and groups; `spent S id` (FormFold.lean) is S with the oracle message
number id marked as spent as a mask. F (`FoldShape`, OnBytes/Iop/Fold.lean) is the fold's shape: the
numbers of two codes, a layout, a class of leaves. "The claim in front" is row (`GroupRow`,
Ground.lean): the claim before the fold. The single rows (`SingleRows`, Fold.lean) are computed by
`foldOutAt` (FormFold.lean) from S, F, row, id and the rounds; `stmS` (OnBytes/Slice/BlkRead.lean)
reads them as one claim on three rows. A claim is true at a message (`Slf.Holds` at `Slf.idf`,
Cb/Ld/LdRel.lean) if its coefficients, each multiplied with the message's entry and added up, give
its target. The three folded messages are `foldMsg` (Johnson/Prover/Link/FoldEnc.lean) at
`μOf s P`, `φOf s P` and the point. `noDigest` (Johnson/Desc/Block.lean) sets the digest in a
round's field `drawn` to `none`.

  `fold_at_S`: the row fits the fold's shape at the statement with the fresh table spent · the mask
    code has the stage's message length there · the claim in front is true at `μOf s P` · the fresh
    table is W's packing, and there is room ⟹ the rows `foldOutAt S F row id` on `aFold`, shown
    without digest, are true at the three folded messages at `aPoint`

By what. `fold_holds` (Johnson/Prover/Link/FoldHolds.lean) is the same statement at any rounds,
under two hypotheses on the rounds, one of them `Shows`, and under `Pairs` on the table (both
defined in that file). The two come from `foldRV_sigma` and `foldRV_shows`
(Johnson/Prover/Link/FoldSay.lean), the second carried to the rounds without digest by
`shows_noDigest` (Johnson/Prover/Link/BodyHelps.lean). `Pairs` comes from hl and hpk by
`pairs_packedN` (Johnson/Prover/Link/BodyPack.lean). `claimOf_shows` (FoldHolds.lean) says that the
point read off these rounds is the point of `fold_holds`. `point_eq` and `fold_eq` (Stages.lean) and
`gam_at` (BodyStepAt.lean) turn `aPoint` and `aFold` into that point and these rounds.

Hypotheses of `fold_at_S`, in the theorem's order. The entry in the list names all but hk and hh.
hk, hh: `F.layout.k` is s.h + s.g, and `F.layout.h` is s.h. hok: `foldRowOk` (Fold.lean) passes at
`spent S id`, F and row: the row's coefficients have the lengths of the group's two tables, and each
of its separate forms is on a kept member of the layout and fits that member's main table. hZ: in
`spent S id` the mask code number `F.maskCode` has messages of `s.Z.l` entries; where there is no
mask code of that number, the default code is read. hin: row, read with the stage's numbers of rows
(`stmG`, BlkRead.lean), is true at `μOf s P`. hl: s.h + 2 * s.g + 1 ≤ `s.Z.l`; where this fails,
`packedN` is 0. hpk: `P.fM` is `packedN s W` (BodyPack.lean).

Limits. Every hypothesis is assumed: none is proved here, at any plan, state or run. All parameters
are free, also K, P, D, S, F, row and id: the theorem also holds at values that no run reaches.
Nothing says that id is the number of the fresh table in S; where S has no oracle message of that
number, `spent S id` is S. Nothing is stated on how K is chosen. `foldOutAt` is a function of the
rounds: that the test's fold accepts these rounds is not shown here; that a fold which accepts
passes on rows of this form is `fold_exact` (Johnson/Desc/K12/Honest/FirstSeenExact.lean). Nothing
on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Stages
import Johnson.Prover.Link.BodyStepAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- **The fold's output on the term's rounds is true at the three folded messages.** The rounds are
`aFold`, each without its digest (`noDigest`); the point is `aPoint`. S, F and id are free
parameters. What each hypothesis says: the head of this file. -/
theorem fold_at_S (K : BCoins) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (P : PS) (row : GroupRow)
    (D : ℕ → Fmt.Drawn) (S : Statement) (F : FoldShape) (id : ℕ)
    (hk : F.layout.k = (sgOf cur).h + (sgOf cur).g) (hh : F.layout.h = (sgOf cur).h)
    (hok : foldRowOk (spent S id) F row = true)
    (hZ : ((spent S id).codes.mask.getD F.maskCode default).ell = (sgOf cur).Z.l)
    (hin : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmG (sgOf cur) row)
      (μOf (sgOf cur) P))
    (hl : (sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l)
    (hpk : P.fM = packedN (sgOf cur) (K.W (sgOf cur) j)) :
    (Slf.idf (E := GE) (J := (sgOf cur).cMid.J)).Holds
      (stmS (sgOf cur) (foldOutAt S F row id ((aFold K j cur o P row D).map noDigest)))
      (foldMsg (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P) (aPoint cur o D)) := by
  have hR := shows_noDigest _ _ _ _ (foldRV_shows (sgOf cur) (vecG (sgOf cur) row)
    (μOf (sgOf cur) P) (K.W (sgOf cur) j) fun n => D (o + n))
  have i2 := (claimOf_shows _ _ _ _ zeroE hR).2.1
  have hF := fold_holds (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P) (K.W (sgOf cur) j) _ S F
    row id
    (noDigest ⟨[.e (ofE (hMu (sVars GE 2 ((sgOf cur).h + (sgOf cur).g)) (K.W (sgOf cur) j)))],
      D (o + 0)⟩) _ hk hh hok hZ hin (pairs_packedN (sgOf cur) hl _ P hpk)
    (foldRV_sigma (sgOf cur) (K.W (sgOf cur) j) _) hR
  rw [← i2] at hF
  rw [← point_eq K j cur o P row D, gam_at, ← fold_eq K j cur o P row D]
  exact hF

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.fold_at_S
