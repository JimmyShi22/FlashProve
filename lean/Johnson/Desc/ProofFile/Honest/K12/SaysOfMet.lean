-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SaysOfMet.lean

The sentence on values at a proximity test's entry (`SaysAt`, AsksWhole.lean: the rows that the test
takes in say true things of the words that the job's own rows make), from "the statement is in order
and all that it claims holds of the honest words" (`AllMet`, Johnson/Desc/Means/Forth/AllMet.lean);
and so, at the test on G_u of the shared chain, from the premises of the library's own law on the
eight sub-protocols in front (`eight_steps_hold`, Johnson/Desc/K14/Honest/ChainSteps.lean). One
definition; three theorems.

  `WordsTied`: the tie of the words, by name: on the tables of the group's members the words are
      those that the job's plain rows make.
  `allSay_of_met`: `AllMet`, no open row marked as a sample row, and the tie ⟹ the clause on values.
      No frame, no job.
  `saysAt_of_met`: the same at a job's own state on entry ⟹ `SaysAt`.
  `saysAt_of_eight`: at a job whose state on entry is `doorUF` (DoorsByShape.lean): the eight steps
      and the fold return; the state on entry is what the seat's way in makes of the fold's state,
      not the fall-back; and seven premises on values ⟹ `AllMet` there and `SaysAt`.

Why. `onFreeT_head_U` (OnFreeTAtHeadU.lean) takes `SaysAt` as a premise on a run. At that law's
letters the prover is free but for the test's own half, and the targets of the rows that the test
takes in are made of what the chain's other halves have shown and of the columns at "LOC"; the eight
sub-protocols take whatever has the right form. So the sentence hangs on what was shown. This file
says on what: five premises of the library's (the key's record holds the rows' answers; the columns
at "LOC" hold the rows' symbols; the two sendings' answers and the scalar at "SPLIT" are the honest
ones), one fact of shape (`OpenKinds`), and the tie.

By what. `runRows_iff_items` (Johnson/Desc/Means/ItemsAt.lean), `allSay_begun` (ItemsBegun.lean),
`says_members` (Johnson/RunOne/Law/GrowsOfAllSay.lean): the road of `allSay_of_holds`
(GrowsSays.lean in this folder), which starts from the key file's sentence.

Limits.
- IT PAYS NONE OF THE SEVEN. That they can be had together is shown by no example here.
- `SaysAt` holds at `doorUF`'s fall-back too, for nothing (SaysAtFall.lean): so `saysAt_of_eight`
  carries the fold's return and the state on entry beside it.
- H, what an honest prover holds, is a letter. The tie picks its rows and coins by the job's; the
  five then say that what was shown is honest at that H.
- That the front shows just the eight's rounds, and that the job's reader of columns returns the
  columns of "LOC" in front, are premises (hseen, hcols, hcs).
- No frame: nothing of a run, a book or lent coins. At the test on G_u alone.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.K14.Honest.ChainSteps
import Johnson.RunOne.Law.GrowsOfAllSay
import Johnson.Desc.Means.ItemsBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means Cb
open VerifiableInference.Desc (Block OpenedColumn roundsFit groupsOf foldBlocks)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Johnson.RunOne.Law.GrowsOfAllSay (says_members)
open H2K.First
open Desc.K14 (P14 St blocks first)
open Desc.K14.Law (locations genK parU parO)
open Desc.K14.Honest
open ProofFile.Honest.K12 (TestCoins PlainRows)

/-- **The tie of the words, by name**: on the tables of the group's members the words m are the
words that the plain rows R make behind the test's beginning. Off the members nothing is asked. -/
def WordsTied (S : Statement) (g : ℕ) (G : Group) (m : Words GE) (Ly : GroupLayout)
    (R : PlainRows) : Prop :=
  ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize S o pt,
    m o pt i = ProofFile.Honest.K12.wordsAt (begun S g G) Ly R o pt i

/-- **From "the statement is in order and all that it claims holds of the words m" to the clause on
values.** No frame, no job. The rows that a proximity test on the group G takes in say true things
of the words that the plain rows make, where these are m on the members' tables. -/
theorem allSay_of_met (S : Statement) (g : ℕ) (G : Group) (hG : S.groups[g]? = some G)
    (hK : OpenKinds S) (m : Words GE) (hM : AllMet rdE S m) (Ly : GroupLayout) (R : PlainRows)
    (hw : WordsTied S g G m Ly R) :
    AllSay rdE (begun S g G) (runRows S G).toList
      (ProofFile.Honest.K12.wordsAt (begun S g G) Ly R) := by
  have hval : AllSay rdE S (runRows S G).toList m := by
    refine (runRows_iff_items rdE hK g hG _).2 ⟨fun i r hr => ?_, fun o ho x hx r hr => ?_⟩
    · obtain ⟨G', hG', hi⟩ := rowAt_iff.1 hr
      rw [hG] at hG'
      obtain rfl := Option.some.inj hG'
      exact hM.2.rows g G hG r (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))
    · exact hM.2.samples o x hx r hr
  exact (allSay_begun rdE hM.1 g hG _).2 fun r hr =>
    (says_members (hM.1.runRows g G hG r hr) _ _ hw).1 (hval r hr)

/-- **`SaysAt` (AsksWhole.lean) from these**, at the job's own state on entry. -/
theorem saysAt_of_met {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (m : Words GE) (hM : AllMet rdE (A.rec₀ w fr).st m) (hK : OpenKinds (A.rec₀ w fr).st)
    (hw : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
      WordsTied (A.rec₀ w fr).st (A.rec₀ w fr).g G m (layoutOf (A.rec₀ w fr).st G)
        (plainMany A w fr C)) :
    SaysAt A w fr C :=
  fun G hG => allSay_of_met _ _ G hG hK m hM _ _ (hw G hG)

/-- **At the test on G_u behind the shared chain's eight: `SaysAt` from seven premises on values,
each by name, beside the state that the fold returns.** In front of these stand sixteen premises on
the plan, the job, the key's form and the form of what was shown (hP to hcs). The first nine clauses
are `eight_steps_hold`'s (Johnson/Desc/K14/Honest/ChainSteps.lean), to the letter, at the first
tree's number 0, the input's key and no round behind: the eight steps and the fold return, whatever
values of the right form were shown. The tenth: the job's state on entry is what the seat's way in
makes of d8: not the fall-back. The last, an implication as there: the library's five premises on
values (the key's record holds the rows' answers; the columns at "LOC" hold the rows' symbols; the
two sendings' answers and the scalar at "SPLIT" are the honest ones), that no open row of d8's
statement is marked as a sample row, and the tie of the words ⟹ all that d8's statement claims holds
of the honest words, and `SaysAt`. -/
theorem saysAt_of_eight {W X : Type} (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (A : ManyJob W X)
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (hA : A.rec₀ = doorUF P sentU [b1, b2, b3, b4, b5, b6, b7, b8] key cols) (w : W)
    (fr : Front X) (C : TestCoins) (hkey : keyFits (key w) P.par.S.fold.index = true)
    (hbeta : ((key w).seeds.all (!allZero ·.beta)) = true)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView) (cs cs' : List OpenedColumn)
    (hseen : fr.seen.rounds = [R1, R2a, R2b, R4, R5a, R5b, R7, R8])
    (hcols : cols w fr = cs ++ cs')
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hcs : cs.map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (groupsOf 0 b4.rounds [R4.drawn]).flatMap id) (H : Inputs) :
    ∃ d1 d2 d3 d4 d5 d6 d7 d8 : St,
      b1.step 0 (first P.codes (key w)) [R1] (cs ++ cs') = .ok (d1, 0) ∧
      b2.step 0 d1 [R2a, R2b] (cs ++ cs') = .ok (d2, 0) ∧
      b3.step 0 d2 [] (cs ++ cs') = .ok (d3, 0) ∧
      b4.step 0 d3 [R4] (cs ++ cs') = .ok (d4, cs.length) ∧
      b5.step 0 d4 [R5a, R5b] cs' = .ok (d5, 0) ∧ b6.step 0 d5 [] cs' = .ok (d6, 0) ∧
      b7.step 0 d6 [R7] cs' = .ok (d7, 0) ∧ b8.step 0 d7 [R8] cs' = .ok (d8, 0) ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first P.codes (key w)) fr.seen.rounds
        (cols w fr) = .ok (d8, [], cs') ∧
      A.rec₀ w fr = { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU,
                      pass := .nothing, mask := d8.loc.firstMask } ∧
      ((∀ x ∈ (key w).seeds.zipIdx, ∀ r < P.par.S.fold.index.rows,
          RowAnswer P.par.S.fold.index (x.1.z.map rdE.val) (rdE.val x.1.beta)
            (fun t => rdE.val (thetaE t)) x.2 (H.Rw r)
            (rdE.val ((key w).record.getD (r * P.par.S.fold.index.answers + x.2) zeroE))) →
        (∀ x ∈ locations P.par R4, ∀ col,
          (cs.map fun c => (c.2.1, c.2.2)).lookup x = some col → ∀ q < P.par.S.fold.index.rows,
            rdE.val (ofF (col.toArray.getD q 0)) = genK rdE P.par.S.fold x (H.Rw q)) →
        R2b.vals = answersAt (parU P sentU) d1.st R2a H.w₀
          (rowsU P (first P.codes (key w)) R1 H) →
        R5b.vals = answersAt (parO P) d4.st R5a (words1 P sentU (first P.codes (key w)) R1 H)
          (rowsO P (first P.codes (key w)) R1 H) →
        R8.vals = [.e (Slice.ofE (muRun P (first P.codes (key w)) R1 R7 H))] →
        OpenKinds d8.st →
        (∀ G, d8.st.groups[d8.loc.gU]? = some G →
          WordsTied d8.st d8.loc.gU G (words2 P sentU (first P.codes (key w)) R1 H)
            (layoutOf d8.st G) (plainMany A w fr C)) →
        Means.AllMet rdE d8.st (words2 P sentU (first P.codes (key w)) R1 H) ∧
          SaysAt A w fr C) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, s1, s2, s3, s4, s5, s6, s7, s8, hf, himp⟩ :=
    eight_steps_hold P sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb (key w) hkey hbeta R1 R2a
      R2b R4 R5a R5b R7 R8 cs cs' [] 0 f1 f2 f4 f5 f7 f8 hcs H
  rw [List.append_nil] at hf
  have hf' : foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first P.codes (key w)) fr.seen.rounds
      (cols w fr) = .ok (d8, [], cs') := by
    rw [hseen, hcols]
    exact hf
  have hrec : A.rec₀ w fr = { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU,
                              pass := .nothing, mask := d8.loc.firstMask } := by
    rw [hA]
    unfold doorUF doorOf
    rw [hf']
    rfl
  refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, s1, s2, s3, s4, s5, s6, s7, s8, hf', hrec,
    fun p1 p2 p3 p4 p5 hK hT => ?_⟩
  have hM := himp p1 p2 p3 p4 p5
  refine ⟨hM, saysAt_of_met A w fr C (words2 P sentU (first P.codes (key w)) R1 H) ?_ ?_ ?_⟩
  · rw [hrec]
    exact hM
  · rw [hrec]
    exact hK
  · rw [hrec]
    exact hT

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.WordsTied
#print axioms ProofFile.Honest.K12.Light.allSay_of_met
#print axioms ProofFile.Honest.K12.Light.saysAt_of_met
#print axioms ProofFile.Honest.K12.Light.saysAt_of_eight
