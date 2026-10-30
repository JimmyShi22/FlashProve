-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Values.lean: THE VALUES' HALF OF THE CLOSING OF A SEGMENT: if every row that
the test takes in holds of words, and the rounds show what the shared fold's second core says, THE
SINGLE ROWS THAT THE FOLD RETURNS (`foldOutAt`) ARE TRUE, their kept forms with them. One definition and
theorems; no prover's moves are named (`foldQK`: the other house's honest round polynomials).

It joins two laws that lie elsewhere, by one bridge of its own.
  the batching   `combine_all` (Johnson/Desc/Means/Combine.lean): if all rows hold of the words, the
                 batched row holds of the group's tables as the words fill them (`GroupSays`,
                 `tablesOf`): the main table, the mask table and each kept member's own table
  the fold       `fold_holds_kept` (Johnson/Prover/Link/FoldKept.lean):
                 from the claim in front as a bare equation,
                 with the kept forms' value (`keptVal`) beside
  THE BRIDGE     `kept_term`, `groupValue_kept`, `groupSays_kept`: IN FRONT OF THE FOLD what a group's row
                 says of tables IS that equation: at the message `msgOf s T`
                 (Johnson/Desc/K12/Law/ClaimSays.lean), the tables κ := T.kept and the lengths
                 N o := the number of entries of o's main table (0 if it has none)

  `close_holds`   the three joined

Limits. BEHIND THE FOLD the kept forms' value stays in the other house's letters (`keptVal`): that
it is what the soundness side reads of the kept forms there is not shown. All premises on form are
asked, not shown: the group, its layout, `GroupOk`, `RowIn`, that the batching returns the row, the
fold's test on the row, the numbers of the stage, the mask code's length:
Johnson/Desc/K10/Honest/Holds.lean pays them, but for the stage's four numbers, from the facts on
the record in front. That `foldOutAt` is what the closing's decision lays into the frame:
Johnson/Desc/K10/Honest/Leaves.lean. "True" is said of `foldMsg` of the words' tables and a fresh
table φ. φ IS A LETTER: it is asked to pair with W (`Pairs`), not to be the table of the oracle
message number id. The words are any words: that they are 0 where nobody sent anything is not asked.
That the rounds show the honest round polynomials is a premise (`rounds_show`,
Johnson/Prover/Link/FoldWordsShows.lean, has the like for rounds that send the shared fold's words,
under a premise on the sizes, AT ITS OWN LETTERS: the ties to the letters of this file's premise are
the caller's still, by that file's Limits; that a prover sends these words is shown by neither
file). A member: Johnson/Desc/K10/Honest/HoldsToy.lean. Nothing on soundness, completeness or hiding
of the protocol.

-/
import Johnson.Prover.Link.FoldKept
import Johnson.Desc.K12.Law.ClaimSays
import Johnson.Desc.Means.Combine
import Johnson.Desc.Means.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Values
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb

/-- The number of entries of each oracle message's main table; 0 if it has none. -/
def keptLen (S : Statement) : ℕ → ℕ := fun o => tableSize S o .main

/-- **The kept forms' part of what a group's row says is `keptVal`.** -/
theorem kept_list (n : ℕ) (N : ℕ → ℕ) (κ : ℕ → ℕ → GE) (hN : ∀ o, n ≤ o → N o = 0) :
    ∀ (l : List KeptForm),
    (∑ o ∈ Finset.range n, ∑ i ∈ Finset.range (N o), keptSum rdE o i l * κ o i) =
      (l.map fun f => ∑ i ∈ Finset.range (N f.oracle), formAt f.c i * κ f.oracle i).sum
  | [] => by simp [keptSum]
  | a :: l => by
    have ih := kept_list n N κ hN l
    have e : ∀ o i, keptSum rdE o i (a :: l) =
        (if a.oracle = o then formAt a.c i else 0) + keptSum rdE o i l := fun o i => by
      unfold keptSum
      rw [List.map_cons, List.sum_cons]
      rfl
    simp only [e, add_mul, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [Finset.sum_eq_single a.oracle]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hn
      rw [hN _ (Nat.not_lt.1 fun c => hn (Finset.mem_range.2 c))]
      simp

/-- The same at a statement's tables. -/
theorem kept_term (S : Statement) (T : Tables GE) (Ks : Array KeptForm) :
    (∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
      keptSum rdE o i Ks.toList * T.kept o i) = keptVal (keptLen S) T.kept Ks :=
  kept_list S.oracles.size (keptLen S) T.kept (fun o ho => by
    unfold keptLen tableSize
    rw [if_neg fun c => absurd (lt_of_has c) (Nat.not_lt.2 ho)]) Ks.toList

/-- **THE BRIDGE**: a group's row applied to tables, its kept forms with it. -/
theorem groupValue_kept (s : Sg) (S : Statement) (L : GroupLayout) (row : GroupRow) (T : Tables GE)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l)
    (hz : 2 ^ L.logEllZk = s.Z.l) :
    groupValue rdE S L row T =
      ∑ j : s.cIn.J, vecG s row j * msgOf s T j + keptVal (keptLen S) T.kept row.kept := by
  have h0 := groupValue_vecG s S L { row with kept := #[] } T hk hh hl hz rfl
  have e : groupValue rdE S L row T = groupValue rdE S L { row with kept := #[] } T +
      ∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
        keptSum rdE o i row.kept.toList * T.kept o i := by
    unfold groupValue
    simp [keptSum]
  rw [e, h0, kept_term S T row.kept]
  rfl

/-- The bridge as a "just if": what a group's row says of tables is the bare equation. -/
theorem groupSays_kept (s : Sg) (S : Statement) (L : GroupLayout) (row : GroupRow) (T : Tables GE)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l)
    (hz : 2 ^ L.logEllZk = s.Z.l) :
    GroupSays rdE S L row T ↔
      ∑ j : s.cIn.J, vecG s row j * msgOf s T j + keptVal (keptLen S) T.kept row.kept =
        readE row.target := by
  unfold GroupSays
  rw [groupValue_kept s S L row T hk hh hl hz]
  exact Iff.rfl

/-- **THE SINGLE ROWS THAT THE FOLD RETURNS ARE TRUE.** s: a stage of the library with the layout's four
numbers. S: the statement behind the beginning of the test; g, G, L: the group's number, the group and
its layout there; rows: the rows that the test takes in. x: the element that "BAT" drew; row: the
batched row. m: the words. F: the fold's shape; id: the number of the fresh mask's oracle message; φ: a
fresh table; W: the coefficients of the hiding polynomial. rE, rR: the rounds "FOLD epsilon" and "FOLD
round"; γ: the point that the rounds "FOLD round" drew. -/
theorem close_holds (s : Sg) (S : Statement) (g : ℕ) (G : Group) (L : GroupLayout)
    (rows : Array Row) (x : E) (row : GroupRow) (hG : S.groups[g]? = some G)
    (hL : S.layout g = some L) (hOk : GroupOk S G) (hr : ∀ r ∈ rows.toList, RowIn S G r)
    (hb : Bat.combine S g ⟨L, rows⟩ x = some row) (m : Words GE)
    (hs : AllSay rdE S rows.toList m) (hk : L.k = s.h + s.g) (hh : L.h = s.h)
    (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk = s.Z.l)
    (F : FoldShape) (id : ℕ) (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (fk : F.layout.k = s.h + s.g)
    (fh : F.layout.h = s.h) (hok : foldRowOk (spent S id) F row = true)
    (hZ : ((spent S id).codes.mask.getD F.maskCode default).ell = s.Z.l)
    (φ : s.cFr.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (γ : HPt (sVars GE 2 (s.h + s.g))) (hP : Pairs s s.Z.l W φ)
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (s.h + s.g)) W)
    (hR : Shows (s.h + s.g) rR (foldQK s (vecG s row) (msgOf s (tablesOf S L m)) W
      (readE (drawnOf rE)) (keptVal (keptLen S) (tablesOf S L m).kept row.kept) γ) γ) :
    ∑ j, vecS s (foldOutAt S F row id (rE :: rR)) j *
          foldMsg s (msgOf s (tablesOf S L m)) φ (sPt 2 (s.h + s.g) γ) j +
        keptVal (keptLen S) (tablesOf S L m).kept (foldOutAt S F row id (rE :: rR)).kept =
      readE (foldOutAt S F row id (rE :: rR)).target := by
  have h1 : GroupSays rdE S L row (tablesOf S L m) :=
    combine_all rdE S g G L rows x row hG hL hOk hr hb m hs
  unfold GroupSays at h1
  rw [groupValue_kept s S L row _ hk hh hl hz] at h1
  exact fold_holds_kept s _ φ W γ (keptLen S) (tablesOf S L m).kept S F row id rE rR fk fh hok hZ h1
    hP hσ hR

end ProofFile.Honest.K10.Values

#print axioms ProofFile.Honest.K10.Values.kept_term
#print axioms ProofFile.Honest.K10.Values.groupValue_kept
#print axioms ProofFile.Honest.K10.Values.groupSays_kept
#print axioms ProofFile.Honest.K10.Values.close_holds
