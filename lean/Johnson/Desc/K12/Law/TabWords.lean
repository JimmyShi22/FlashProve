-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TabWords.lean: a bridge between the relation in front of the proximity test's
chain and what the batched rows mean, in the rows' own words. Statements and proofs.

On one side stands a witness's message as tables (`tabOf`, Johnson/Desc/K12/Law/RInSays.lean); on
the other what the batched rows mean (Johnson/Desc/K12/Law/BatMeans.lean and, under
Johnson/Desc/Means/, words, `tablesOf`, `Laid`, `Padded`).
Main names:
  `PadMain`, `PadMask`: the row of an index lies in a member's block, beyond that member's real
    rows. (`OffMain`, `OffMask`, Johnson/Desc/Means/Says.lean: in no member's block.)
  `Blank S L T`: the tables are 0 on every row that is no member's real row, and have no kept part.
  `RowsBlank s S L y`: the premise on how the word is made (public data and a definition; no view in
    it): the word y has the symbol 0, at every position, in every such row.
  `blank_of_near`: from `s.Sized`, e < s.d, `RowsBlank` and a witness within e positions of y:
    `Blank S L (tabOf s w.1)`, by Johnson/Desc/K12/Law/ZeroRows.lean: the code pays it, at every
    radius below the distance, of every witness in the list.
  `wordsOf S L T`, `laid_wordsOf`, `padded_wordsOf`: the words that blank tables hold (each member's
    entry read where the program's `groupIndex` puts it) meet `Laid` and `Padded`.
  `groupSays_words`: on blank tables: `GroupSays … R T ↔ GroupSays … R (tablesOf S L (wordsOf S L
    T))` (by `groupValue_laid`).
  `rIn_rows`: of a yes of `bat` (Johnson/Desc/First/Close/Closing.lean): every witness of `Sg.RIn e
    (stmG s row, y)` holds words m with `Padded S' m`, `Laid S' L m (tabOf s w.1)` and hornerSum
    (readE x) (what the batched rows are short of on m) = 0.
Read backwards: if for no words that are 0 beyond the real rows and are laid in tables whose
encoding is within e of y the Horner sum at x vanishes, the claim at which the law of the proximity
test starts has no witness: the premise of `chain_many` (OnBytes/Slice/ManySem.lean).
Limits:
(1) `RowsBlank` is shown here of no word. Johnson/Desc/K12/Law/RowsBlankWord.lean shows it of the
library's `Gp.word` under `SeatsAre`; Johnson/Desc/K12/Law/RowsBlankGp.lean shows `SeatsAre`, and
`RowsBlank`, of the group that the law of the proximity test names (`seatsAre_gpG`,
`rowsBlank_law`).
(2) From "the Horner sum at x is 0" to "every row holds" is the batching's converse: to be carried
(see the head of Johnson/Desc/K12/Law/BatMeans.lean), for each member of the list of witnesses.
(3) The yes of `combineAt` and the layout's four numbers are held by runs alone (evaluated at the
proximity tests of the two example proofs).
(4) As in the files under Johnson/Desc/Means, which lie beneath: nothing on how words or tables are
tied to what a prover has sent.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `groupIndex_row`
(OnBytes/Iop/RowLaws.lean); `groupValue_laid` (Johnson/Desc/Means/Tables.lean), `layFacts`
(Johnson/Desc/Means/Layout.lean), `combine_means`, `groupSays_iff_short`
(Johnson/Desc/Means/Combine.lean), `combineAt_gives` (Johnson/Desc/Means/TestsLaw.lean);
`zero_row_main`, `zero_row_mask`, `rIn_iff`, `bat_ok`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.ZeroRows
import Johnson.Desc.K12.Law.BatMeans
import Johnson.Desc.Means.Tables

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc
open OnBytes.Means

/-- The row of the index J of the group's main table is in a member's block, beyond that member's
real rows. -/
def PadMain (S : Statement) (L : GroupLayout) (J : Nat) : Prop :=
  ∃ o i first, L.find o = some i ∧ L.kept.getD i false = false ∧ L.mainFirst.getD i none = some
      first ∧
    first + realRows S o .main ≤ J % 2 ^ L.k ∧ J % 2 ^ L.k < first + 2 ^ S.rowBits o .main

def PadMask (S : Statement) (L : GroupLayout) (J : Nat) : Prop :=
  ∃ o i first, L.find o = some i ∧ L.maskFirst.getD i none = some first ∧
    first + realRows S o .mask ≤ J % 2 ^ L.h ∧ J % 2 ^ L.h < first + 2 ^ S.rowBits o .mask

/-- The tables are 0 on every row that is no member's real row, and have no kept part. -/
structure Blank (S : Statement) (L : GroupLayout) (T : Tables GE) : Prop where
  main : ∀ J, OffMain S L J ∨ PadMain S L J → T.main J = 0
  mask : ∀ J, OffMask S L J ∨ PadMask S L J → T.mask J = 0
  kept : ∀ o idx, T.kept o idx = 0

/-- The premise on the word's make: the word y has the symbol 0, at every position, in every row
that is no member's real row. (The row's number is taken modulo 2 ^ (s.h + s.g) | 2 ^ s.h here and
modulo 2 ^ L.k | 2 ^ L.h in Off… | Pad…: they are one under L.k = s.h + s.g and L.h = s.h, which
rIn_rows has among its premises and this text has not: elsewhere the premise is a strange one.) Paid
for the library's group's word in Johnson/Desc/K12/Law/RowsBlankWord.lean. -/
structure RowsBlank (s : Sg) (S : Statement) (L : GroupLayout) (y : s.cIn.Word) : Prop where
  main : ∀ J, OffMain S L J ∨ PadMain S L J → ∀ x : s.Ps,
    s.cIn.T y x (.inl (fun t => (J % 2 ^ (s.h + s.g)).testBit t.val, ())) = 0
  mask : ∀ J, OffMask S L J ∨ PadMask S L J → ∀ x : s.Ps,
    s.cIn.T y x (.inr (fun t => (J % 2 ^ s.h).testBit t.val, ())) = 0

/-- The code makes every witness's tables blank where the word is. -/
theorem blank_of_near (s : Sg) (hs : s.Sized) (e : ℕ) (he : e < s.d) (S : Statement) (L :
    GroupLayout)
    (y : s.cIn.Word) (hy : RowsBlank s S L y) (w : s.cIn.N.Wit)
    (hw : offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e) : Blank S L (tabOf s w.1) where
  main := fun J hJ => by
    show tabBack (s.h + s.g) s.C.l (fun x => w.1 (.inl x)) J = 0
    unfold tabBack
    split
    · exact (zero_row_main s hs e he y w hw _ (hy.main J hJ)).1 _
    · rfl
  mask := fun J hJ => by
    show tabBack s.h s.Z.l (fun x => w.1 (.inr x)) J = 0
    unfold tabBack
    split
    · exact (zero_row_mask s hs e he y w hw _ (hy.mask J hJ)).1 _
    · rfl
  kept := fun _ _ => rfl

/-- The words that tables hold: each member's entry is read where the program's groupIndex puts it.
-/
def wordsOf (S : Statement) (L : GroupLayout) (T : Tables GE) : Words GE := fun o part idx =>
  match L.find o with
  | none => 0
  | some i =>
    match part with
    | .main =>
      if L.kept.getD i false then T.kept o idx
      else match L.mainFirst.getD i none with
        | some first => T.main (groupIndex idx (S.rowBits o .main) first L.k)
        | none => 0
    | .mask =>
      match L.maskFirst.getD i none with
      | some first => T.mask (groupIndex idx (S.rowBits o .mask) first L.h)
      | none => 0

theorem laid_wordsOf (S : Statement) (L : GroupLayout) (T : Tables GE) (hT : Blank S L T) :
    Laid S L (wordsOf S L T) T where
  main_at := fun o i first hf hk hm idx _ => by
    simp only [wordsOf, hf, hk, hm, Bool.false_eq_true, if_false]
  main_else := fun J _ hJ => hT.main J (.inl hJ)
  mask_at := fun o i first hf hm idx _ => by
    simp only [wordsOf, hf, hm]
  mask_else := fun J _ hJ => hT.mask J (.inl hJ)
  kept_at := fun o i hf hk idx _ => by
    simp only [wordsOf, hf, hk, if_true]
  kept_else := fun o _ idx => hT.kept o idx

theorem padded_wordsOf {S : Statement} {G : Group} {L : GroupLayout} (F : LayFacts S G L)
    (T : Tables GE) (hT : Blank S L T) : Padded S (wordsOf S L T) := by
  intro o part i h
  unfold wordsOf
  cases hf : L.find o with
  | none => rfl
  | some n =>
    cases part with
    | main =>
      dsimp only
      by_cases hk : L.kept.getD n false = true
      · rw [if_pos hk]
        exact hT.kept o i
      · rw [if_neg hk]
        have hk' : L.kept.getD n false = false := by simpa using hk
        cases hm : L.mainFirst.getD n none with
        | none => rfl
        | some first =>
          have hb := (F.main_block o n first hf hm).2.2
          have hr := groupIndex_row i (S.rowBits o .main) first L.k hb
          have hlt := Nat.mod_lt i (Nat.two_pow_pos (S.rowBits o .main))
          exact hT.main _ (.inr ⟨o, n, first, hf, hk', hm, by rw [hr]; omega, by rw [hr]; omega⟩)
    | mask =>
      dsimp only
      cases hm : L.maskFirst.getD n none with
      | none => rfl
      | some first =>
        have hb := (F.mask_block o n first hf hm).2
        have hr := groupIndex_row i (S.rowBits o .mask) first L.h hb
        have hlt := Nat.mod_lt i (Nat.two_pow_pos (S.rowBits o .mask))
        exact hT.mask _ (.inr ⟨o, n, first, hf, hm, by rw [hr]; omega, by rw [hr]; omega⟩)

/-- The bridge tabOf ↔ tablesOf: on blank tables a group's row says of the tables what it says of
the group's tables as the tables' own words fill them. -/
theorem groupSays_words {S : Statement} {G : Group} {L : GroupLayout} (F : LayFacts S G L)
    (T : Tables GE) (hT : Blank S L T) (R : GroupRow) :
    GroupSays rdE S L R T ↔ GroupSays rdE S L R (tablesOf S L (wordsOf S L T)) := by
  unfold GroupSays
  rw [groupValue_laid rdE F R _ T (laid_wordsOf S L T hT)]

/-- What comes in front of the proximity test, in the rows' own words. Of a yes of the batching's
plain text: under the test at the statement behind, the layout's four numbers, "no kept form", the
stage's sizes
in order, a radius below the distance, and the premise on the word's make that y is 0 in every row
that is no member's real row: every witness of the library's relation before the fold at the claim q
:= stmG s row and the word y holds words m, 0 beyond the real rows, laid in the witness's own
tables, at which the Horner sum at the drawn x of what the batched rows are short of is 0. -/
theorem rIn_rows (s : Sg) (hs : s.Sized) (e : ℕ) (he : e < s.d) (S S' : Statement) (g : Nat)
    (en : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout)
    (h : First.Close.bat S g en r = .ok (row, L, S')) :
    ∃ (G : Group) (x : E), S.groups[g]? = some G ∧ S' = begun S g G ∧
      r.drawn.elems.map E.ofTriple = [x] ∧
      (combineAt S' g ⟨L, runRows S G⟩ = true → L.k = s.h + s.g → L.h = s.h → 2 ^ L.logEll = s.C.l →
        2 ^ L.logEllZk = s.Z.l → row.kept = #[] → ∀ y : s.cIn.Word, RowsBlank s S' L y →
        ∀ w : s.cIn.N.Wit, s.RIn e (stmG s row, y) w →
          ∃ m : Words GE, Padded S' m ∧ Laid S' L m (tabOf s w.1) ∧
            hornerSum (readE x) ((runRows S G).toList.map fun r => short rdE S' r m) = 0) := by
  obtain ⟨G, x, h1, _, h3, h4, h5⟩ := bat_ok S S' g en r row L h
  refine ⟨G, x, h1, h3, h4, fun ht hk hh hl hz h0 y hy w hw => ?_⟩
  obtain ⟨hnear, hsays⟩ := (rIn_iff s S' L row e y w hk hh hl hz h0).1 hw
  obtain ⟨G', hG, hL, hOk, hr⟩ := combineAt_gives ht
  have F := layFacts hG hL hOk
  have hT := blank_of_near s hs e he S' L y hy w hnear
  refine ⟨wordsOf S' L (tabOf s w.1), padded_wordsOf F _ hT, laid_wordsOf S' L _ hT, ?_⟩
  obtain ⟨out, c1, _, _, c2⟩ := combine_means rdE S' g G' L (runRows S G) x hG hL hOk hr
  rw [h5] at c1
  obtain rfl := Option.some.inj c1
  exact (c2 _).symm.trans
    ((groupSays_iff_short rdE S' L row _).1 ((groupSays_words F _ hT row).1 hsays))

end H2K.ClaimSays

#print axioms H2K.ClaimSays.rIn_rows
#print axioms H2K.ClaimSays.groupSays_words
#print axioms H2K.ClaimSays.blank_of_near
