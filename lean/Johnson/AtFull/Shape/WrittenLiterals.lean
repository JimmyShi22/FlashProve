-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/WrittenLiterals.lean: FOUR WRITTEN VALUES OF THE FIRST CHAIN, IN NUMERALS: the
kind K13's numbers `where13W` (BackNumbersAtHead.lean); the kinds K9's and K10's numbers at the 25
segments, `k9WhereE xsW l` and its k10ParE (Johnson/AtFull/Desc/Lots/K9RowAt.lean;
LinkNumbersAtHead.lean); the count `sentAtC? cutWritten esW "H.8.call"`, which the merge (the kind
K11) uses (SpentReadersAtHead.lean). Five closed facts by Lean's kernel (`decide +kernel`), six
controls, four general theorems. No statement here has a hypothesis on public files: each is closed
or general.

Purpose. A table of steps on shapes, one for each of the 358 blocks in the first chain's blocksInOrder list,
is to be evaluated at closed terms. It is not in the library yet, so nothing about what it reads is
claimed here. To evaluate one of its steps at these four closed terms is costly: each term goes
through the 48,293 written entries, at every step anew. Here each is evaluated once, and the value
stands as a numeral.

Where the numerals come from. They were read off Lean's evaluator. THAT IS NOT WHAT HOLDS THEM: each
is held by the kernel's line beside it.

The spelling that the kernel evaluates. The count of roots before a round has three spellings: a
fold from the left over `take` (`rootsC`), a sum (the library's K13.whereOf), and the library's
`rootsE`, which forces the carried number at each step. The kernel's lines here use rootsE.
`rootsE_foldl` (by recursion on the list), `rootsC_eq` (by unfolding) and `sum_roots` (by induction)
tie the three. (In trials outside this file the first two spellings overran the kernel's stack;
nothing here shows that.)

Main names.
* General: `rootsE_foldl`, `rootsC_eq`, `sum_roots`; `whereT` (K9's numbers as a tuple, so that they
  can be compared by code), `whereT_inj`.
* By the kernel: `roots_48270` (82), `roots_48202` (76), `k9_written`, `close_written`, `before_H8`
  (48202).
* Controls, by the kernel too: each is the same decision with one number changed, and it says no.
  The value changed: `roots_48202_no`, `k9_written_no`, `close_written_no`, `before_H8_no`. The
  round changed: `roots_48266_no`, `roots_48236_no`. A control follows from the fact beside it, or
  rules out one round: what it shows is that the kernel's decision is not constant; it is no further
  evidence for the fact.
* `where13L`, **`where13_lit`**: where13W = where13L. `k9L`, **`k9_lit`**: for l < 25: k9WhereE xsW
  l = some (k9L l). `closeL`, **`close_lit`**: for l < 25: (k9WhereE xsW l).bind (k10ParE groupsW
  xsW) = some (closeL l). **`sent_H8`**: sentAtC? cutWritten esW "H.8.call" = some 76.

Limits. CLOSED FACTS ON WRITTEN LISTS. That the public part's own numbers are these written values
is said in the three files named at the top, under the hypothesis P5J.AtMg. where13L's field lin is
still the written record's term, no numeral. THE TWO COUNTS DO NOT PIN THEIR ROUNDS. The kernel
holds here 82 at round 48270 and 76 at round 48202, and refuses 82 at 48266 and 76 at 48236. By
Lean's evaluator the count is 82 at every round from 48267 to 48290. It is 76 over a far longer
stretch: from round 47456 at the latest to 48235, by the written table of K8MsgsWritten.lean and the
takes of cutWritten, added up by a program outside Lean. The rounds' numbers come from elsewhere
(before_H8; where13W's text). The controls at K9 and K10 change one field at all 25 segments at once
and ask that none passes. K8's messages' numbers: K8MsgsWritten.lean. Nothing says that a step of
the table succeeds. Only the full-size parameters are covered. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.SpentReadersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.First.Close (Par)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc.Lots (rootsE esW xsW groupsW k9WhereE k10ParE)

/-! ## 1 The roots before a round, in the spelling that Lean's kernel can evaluate -/

/-- The library's count of roots, which forces the carried number at each step, is the fold from the
left. -/
theorem rootsE_foldl : ∀ (es : List Fmt.Entry) (a : Nat),
    rootsE a es = es.foldl (fun a e => a + e.roots) a
  | [], _ => rfl
  | e :: es, a => by
    show Johnson.G.force (a + e.roots) (fun b => rootsE b es) = _
    rw [Johnson.G.force_eq, rootsE_foldl es]
    rfl

/-- The fold over `take` (rootsC, SpentReadersAtHead.lean) is that count at the first k entries. -/
theorem rootsC_eq (es : List Fmt.Entry) (k : Nat) : rootsC es k = rootsE 0 (es.take k) := by
  unfold rootsC
  rw [rootsE_foldl]

/-- The sum of the roots, as the library's K13.whereOf spells it, is that count. -/
theorem sum_roots (es : List Fmt.Entry) : (es.map (·.roots)).sum = rootsE 0 es := by
  have key : ∀ (l : List Fmt.Entry) (a : Nat),
      l.foldl (fun a e => a + e.roots) a = a + (l.map (·.roots)).sum := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons e l ih =>
      intro a
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ih, Nat.add_assoc]
  rw [rootsE_foldl, key, Nat.zero_add]

/-- BY THE KERNEL: the written entries before round 48270 send 82 roots. -/
theorem roots_48270 : rootsE 0 (esW.take 48270) = 82 := by decide +kernel

/-- A control at another round: four rounds earlier the count is not 82: refused. It rules out that
one round, no more. -/
theorem roots_48266_no : decide (rootsE 0 (esW.take 48266) = 82) = false := by decide +kernel

/-- BY THE KERNEL: those before round 48202 send 76. -/
theorem roots_48202 : rootsE 0 (esW.take 48202) = 76 := by decide +kernel

/-- A control: the same count against a number one higher: refused. -/
theorem roots_48202_no : decide (rootsE 0 (esW.take 48202) = 77) = false := by decide +kernel

/-- A control at another round: 34 rounds further on the count is not 76: refused. It rules out that
one round, no more. -/
theorem roots_48236_no : decide (rootsE 0 (esW.take 48236) = 76) = false := by decide +kernel

/-! ## 2 The kind K13's numbers -/

/-- where13W with its last field a numeral. -/
def where13L : VerifiableInference.Desc.K13.Where :=
  { chain := 1, piece := 3, pieceRows := 4, rows := 13, lin := proofSizedFull.batch.shape,
    work := (0, 0, 0), sent := 82 }

/-- **The kind K13's written record is the record with the numeral 82.** -/
theorem where13_lit : where13W = where13L := by
  have e : ((P5T.esFull.1.take 48270).map (·.roots)).sum = 82 :=
    (sum_roots _).trans roots_48270
  unfold where13W where13L
  rw [e]

/-! ## 3 K9's and K10's numbers at the 25 segments -/

/-- K9's numbers as a tuple of numbers: for a comparison with code. -/
def whereT (w : Where) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  (w.chain, w.link, w.piece, w.pieceEq, w.rows, w.work, w.sent)

/-- The tuple tells the record: two records with one tuple are one. General. -/
theorem whereT_inj {a b : Where} (h : whereT a = whereT b) : a = b := by
  cases a
  cases b
  simp only [whereT, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- K9's numbers at segment l, in numerals. -/
def k9L (l : Nat) : Where :=
  { chain := 1, link := l, piece := if l == 24 then 10 else 8
    pieceEq := if l == 24 then 12 else 10
    rows := if l == 24 then 24653737 else if l % 2 == 1 then 14166783
      else if l == 0 then 32005923 else 32005793
    work := 0, sent := 3 * l + 4 }

/-- BY THE KERNEL: at each of the 25 segments K9's numbers off the written lists are k9L's. -/
theorem k9_written : ((List.range 25).all fun l =>
    (k9WhereE xsW l).map whereT == some (whereT (k9L l))) = true := by decide +kernel

/-- A control: with the count of messages one too high no segment passes. -/
theorem k9_written_no : ((List.range 25).any fun l =>
    (k9WhereE xsW l).map whereT == some (whereT { k9L l with sent := 3 * l + 5 })) = false := by
  decide +kernel

/-- **K9's numbers at segment l < 25 are numerals.** -/
theorem k9_lit (l : Nat) (hl : l < 25) : k9WhereE xsW l = some (k9L l) := by
  have h := eq_of_beq (List.all_eq_true.1 k9_written l (List.mem_range.2 hl))
  obtain ⟨w, hw, e⟩ := Option.map_eq_some_iff.1 h
  rw [hw, whereT_inj e]

/-- K10's numbers at segment l, in numerals. -/
def closeL (l : Nat) : Par :=
  { link := l, piece := if l == 24 then 13 else 11, k := if l % 2 == 1 then 7 else 8, h := 0
    rows := if l == 24 then 1322 else if l % 2 == 1 then 3295 else if l == 0 then 6 else 1324
    workField := 0, workClose := 0, sent := List.range (3 * l + 4) }

/-- BY THE KERNEL: at each of the 25 segments K10's numbers off the written lists are closeL's. -/
theorem close_written : ((List.range 25).all fun l =>
    decide (((k9WhereE xsW l).bind fun p => k10ParE groupsW xsW p) = some (closeL l))) = true := by
  decide +kernel

/-- A control: with the number of rows one too high no segment passes. -/
theorem close_written_no : ((List.range 25).any fun l =>
    decide (((k9WhereE xsW l).bind fun p => k10ParE groupsW xsW p) =
      some { closeL l with rows := (closeL l).rows + 1 })) = false := by
  decide +kernel

/-- **K10's numbers at segment l < 25 are numerals.** -/
theorem close_lit (l : Nat) (hl : l < 25) :
    ((k9WhereE xsW l).bind fun p => k10ParE groupsW xsW p) = some (closeL l) :=
  of_decide_eq_true (List.all_eq_true.1 close_written l (List.mem_range.2 hl))

/-! ## 4 The count that the merge (the kind K11) uses -/

/-- BY THE KERNEL, on the 477 written rows: the step "H.8.call" begins at round 48202. -/
theorem before_H8 : roundsBeforeC? cutWritten "H.8.call" = some 48202 := by decide +kernel

/-- A control: another number: refused. -/
theorem before_H8_no : decide (roundsBeforeC? cutWritten "H.8.call" = some 46927) = false := by
  decide +kernel

/-- **Before the step "H.8.call" the written entries send 76 roots.** -/
theorem sent_H8 : sentAtC? cutWritten esW "H.8.call" = some 76 := by
  unfold sentAtC?
  rw [before_H8, Option.map_some, rootsC_eq, roots_48202]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.rootsE_foldl
#print axioms Johnson.AtFull.Shape.rootsC_eq
#print axioms Johnson.AtFull.Shape.sum_roots
#print axioms Johnson.AtFull.Shape.roots_48270
#print axioms Johnson.AtFull.Shape.roots_48266_no
#print axioms Johnson.AtFull.Shape.roots_48202
#print axioms Johnson.AtFull.Shape.roots_48202_no
#print axioms Johnson.AtFull.Shape.roots_48236_no
#print axioms Johnson.AtFull.Shape.where13_lit
#print axioms Johnson.AtFull.Shape.whereT_inj
#print axioms Johnson.AtFull.Shape.k9_written
#print axioms Johnson.AtFull.Shape.k9_written_no
#print axioms Johnson.AtFull.Shape.k9_lit
#print axioms Johnson.AtFull.Shape.close_written
#print axioms Johnson.AtFull.Shape.close_written_no
#print axioms Johnson.AtFull.Shape.close_lit
#print axioms Johnson.AtFull.Shape.before_H8
#print axioms Johnson.AtFull.Shape.before_H8_no
#print axioms Johnson.AtFull.Shape.sent_H8
