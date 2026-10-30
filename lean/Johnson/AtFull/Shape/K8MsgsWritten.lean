-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K8MsgsWritten.lean: THE NUMBERS OF THE ORACLE MESSAGES THAT A STEP OF THE FIRST
CHAIN's TABLE OF STEPS SENDS (`k8MsgsC`, SpentReadersAtHead.lean: the library's ProofFile.k8Msgs on the
table of steps and the entries) ARE, AT THE TWO WRITTEN LISTS, A ROW OF A WRITTEN TABLE OF 477 ROWS.
Eleven general theorems, ten of them auxiliary; the eleventh: one pass along the steps gives what
k8MsgsC gives, name by name. Two closed facts by Lean's kernel, one control, and two theorems that
carry these to k8MsgsC at the written lists. No statement here has a hypothesis on public files.

Purpose. The kind K8's numbers at a link name two steps (`k8ParWC`, SpentReadersAtHead.lean). For
each name k8MsgsC's text calls the count of roots `rootsC` three times: six calls for a link, each
over up to 48,293 written entries. Here the numbers of all steps are computed in one pass, once.

How. `msgsE` goes along the steps, cuts the entries by the library's `splitE`
(Johnson/AtFull/Desc/Lots/K9RowWritten.lean), which forces the carried count, and gives for each
step its name and its numbers. `msgsSpec` is k8MsgsC's text with a count added to each number. At a
step of the name asked no round stands before it (`spec_hit`); at another step the rounds before
shift by its take and the roots by what it sends (`spec_miss`, by `rootsC_add`, `before_miss`).
`msgsE_spec`: by recursion along the steps.

Main names.
* `msgsE`: the one pass. `msgsAt tab look`: the first row of that name; the empty list where there
  is none. **`k8MsgsC_pass`**: general: k8MsgsC cuts es look = msgsAt (msgsE cuts es 0) look.
* `msgsW`: the 477 rows. `msgs_written`: BY THE KERNEL: msgsE cutWritten esW 0 = msgsW.
  `msgsW_nodup`: BY THE KERNEL: no name stands twice among the 477. `msgs_written_no`: a control:
  one number changed: refused; it follows from msgs_written, and shows only that the kernel's
  decision is not constant.
* **`k8Msgs_lit`**: k8MsgsC cutWritten esW look = msgsAt msgsW look, at every name. `k8ParWC_lit`:
  so K8's numbers at a link read the written table.
* Auxiliary: `rootsE_from`, `rootsC_add`, `takes_from`, `before_hit`, `before_miss`; `msgsSpec`,
  `k8MsgsC_spec`, `spec_hit`, `spec_miss`; `msgsE_cons`, `msgsE_spec`.

Limits. msgsW was read off Lean's evaluator; what holds it is msgs_written. msgsAt takes the FIRST
row of a name, as k8MsgsC does; k8MsgsC_pass and k8Msgs_lit do not use msgsW_nodup. One control, at
one row. Which names K8's numbers ask depends on the names of the links' records, which are not
written here. A closed fact on written lists: that the public part's own lists are these is said in
LinkNumbersAtHead.lean, under the hypothesis P5J.AtMg. Only the full-size parameters are covered.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.WrittenLiterals
import Johnson.AtFull.Desc.Lots.K9RowWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc.First (Cut)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc.Lots (rootsE esW splitE splitE_eq)

/-! ## 1 Auxiliary theorems -/

/-- The library's count of roots with n carried in is n more than the count from 0. -/
theorem rootsE_from (es : List Fmt.Entry) (n : Nat) : rootsE n es = n + rootsE 0 es := by
  have key : ∀ (l : List Fmt.Entry) (a : Nat),
      l.foldl (fun a e => a + e.roots) a = a + l.foldl (fun a e => a + e.roots) 0 := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons e l ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + e.roots), Nat.zero_add, Nat.add_assoc]
  rw [rootsE_foldl, rootsE_foldl, key]

/-- The roots of the first a + j entries: those of the first a, and those of the next j. -/
theorem rootsC_add (es : List Fmt.Entry) (a j : Nat) :
    rootsC es (a + j) = rootsC es a + rootsC (es.drop a) j := by
  rw [rootsC_eq, rootsC_eq, rootsC_eq, List.take_add, rootsE_foldl, List.foldl_append,
    ← rootsE_foldl, ← rootsE_foldl, rootsE_from]

/-- The sum of the steps' takes with a carried in is a more than the sum from 0. -/
theorem takes_from (l : List Cut) (a : Nat) :
    l.foldl (fun n c => n + c.take) a = a + l.foldl (fun n c => n + c.take) 0 := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + c.take), Nat.zero_add, Nat.add_assoc]

variable {c : Cut} {cs : List Cut} {look : String}

/-- Where the first step has the name asked, no round stands before it. -/
theorem before_hit (h : (c.look == look) = true) : roundsBeforeC? (c :: cs) look = some 0 := by
  have h' : (c.look != look) = false := by simp [bne, h]
  unfold roundsBeforeC?
  simp [h, h']

/-- Where the first step has another name, its take is added to the rounds before the name in the
rest. -/
theorem before_miss (h : (c.look == look) = false) :
    roundsBeforeC? (c :: cs) look = (roundsBeforeC? cs look).map (c.take + ·) := by
  have h' : (c.look != look) = true := by simp [bne, h]
  unfold roundsBeforeC?
  rw [List.any_cons, h, Bool.false_or, List.takeWhile_cons, if_pos h', List.foldl_cons,
    takes_from, Nat.zero_add]
  split <;> rfl

/-! ## 2 The one pass -/

/-- k8MsgsC's text with a count n added to each number. -/
def msgsSpec (cuts : List Cut) (es : List Fmt.Entry) (n : Nat) (look : String) : List Nat :=
  match cuts.find? (·.look == look), roundsBeforeC? cuts look with
  | some c, some k =>
    (List.range (rootsC es (k + c.take) - rootsC es k)).map (· + (n + rootsC es k))
  | _, _ => []

/-- k8MsgsC is msgsSpec with the count 0. -/
theorem k8MsgsC_spec (cuts : List Cut) (es : List Fmt.Entry) (look : String) :
    k8MsgsC cuts es look = msgsSpec cuts es 0 look := by
  unfold k8MsgsC msgsSpec
  cases cuts.find? (·.look == look) <;> cases roundsBeforeC? cuts look <;>
    simp only [Nat.zero_add]

/-- At a step of the name asked: the numbers are n, n + 1, … , as many as the step's rounds send
roots. -/
theorem spec_hit (es : List Fmt.Entry) (n : Nat) (h : (c.look == look) = true) :
    msgsSpec (c :: cs) es n look = (List.range (rootsC es c.take)).map (· + n) := by
  have e : (c :: cs).find? (·.look == look) = some c := by simp [h]
  unfold msgsSpec
  rw [e, before_hit h]
  have e0 : rootsC es 0 = 0 := rfl
  simp only [Nat.zero_add, e0, Nat.sub_zero, Nat.add_zero]

/-- At a step of another name: go on behind its rounds, with the roots that they send added to the
count. -/
theorem spec_miss (es : List Fmt.Entry) (n : Nat) (h : (c.look == look) = false) :
    msgsSpec (c :: cs) es n look = msgsSpec cs (es.drop c.take) (n + rootsC es c.take) look := by
  unfold msgsSpec
  rw [List.find?_cons_of_neg (by simp [h]), before_miss h]
  cases cs.find? (·.look == look) <;> cases roundsBeforeC? cs look <;>
    simp only [Option.map_some, Option.map_none, Nat.add_assoc, rootsC_add, Nat.add_sub_add_left]

/-- **One pass along the table of steps**: step by step its name and the numbers of the roots that
its rounds send; n: the roots sent before. The entries are cut by the library's splitE, which forces
the carried count. -/
def msgsE : List Cut → List Fmt.Entry → Nat → List (String × List Nat)
  | [], _, _ => []
  | c :: cs, es, n =>
    match splitE c.take es n [] with
    | (_, rest, m) => (c.look, (List.range (m - n)).map (· + n)) :: msgsE cs rest m

/-- The first row of a name; nothing where there is none. -/
def msgsAt (tab : List (String × List Nat)) (look : String) : List Nat :=
  ((tab.find? (·.1 == look)).map (·.2)).getD []

/-- One step of msgsE, with the library's splitE spelled by drop and rootsC. -/
theorem msgsE_cons (c : Cut) (cs : List Cut) (es : List Fmt.Entry) (n : Nat) :
    msgsE (c :: cs) es n = (c.look, (List.range (rootsC es c.take)).map (· + n)) ::
      msgsE cs (es.drop c.take) (n + rootsC es c.take) := by
  show (match splitE c.take es n [] with
    | (_, rest, m) => (c.look, (List.range (m - n)).map (· + n)) :: msgsE cs rest m) = _
  rw [splitE_eq, rootsE_from, ← rootsC_eq]
  show (c.look, (List.range (n + rootsC es c.take - n)).map (· + n)) :: _ = _
  rw [Nat.add_sub_cancel_left]

/-- The row that msgsAt finds in msgsE's table is msgsSpec's list: by recursion along the steps. -/
theorem msgsE_spec (look : String) : ∀ (cuts : List Cut) (es : List Fmt.Entry) (n : Nat),
    msgsAt (msgsE cuts es n) look = msgsSpec cuts es n look
  | [], _, _ => rfl
  | c :: cs, es, n => by
    rw [msgsE_cons]
    cases h : c.look == look with
    | true =>
      rw [spec_hit es n h]
      unfold msgsAt
      simp [h]
    | false =>
      rw [spec_miss es n h, ← msgsE_spec look cs]
      unfold msgsAt
      rw [List.find?_cons_of_neg (by simp [h])]

/-- **K8's MESSAGES' NUMBERS ARE THE ONE PASS's ROW.** General. -/
theorem k8MsgsC_pass (cuts : List Cut) (es : List Fmt.Entry) (look : String) :
    k8MsgsC cuts es look = msgsAt (msgsE cuts es 0) look := by
  rw [k8MsgsC_spec, msgsE_spec]

/-! ## 3 At the written lists -/

/-- What the one pass lays at the written table of steps and the written entries: 477 rows. Read off
Lean's evaluator; held by msgs_written. -/
def msgsW : List (String × List Nat) :=
  [("G0.0.call", [0, 1]), ("G0.0.quiet", []), ("G0.1.call", []), ("G0.1.quiet", []),
   ("G0.2.call", []), ("G0.3.call", [2]), ("G0.3.quiet", []), ("G0.4.call", []),
   ("G0.5.call", [3]), ("G0.6.call", []), ("G0.6.quiet", []), ("G0.7.call", []),
   ("G0.7.front", []), ("G0.7.objects", []), ("G0.7.back", []), ("G0.7.quiet", []),
   ("G0.8.call", []), ("G0.8.quiet", []), ("A0.0.call", [4]), ("A0.0.quiet", []),
   ("A0.1.call", []), ("A0.2.scores", []), ("A0.2.divide", []), ("A0.2.call", []),
   ("A0.3.call", [5]), ("A0.3.quiet", []), ("A0.4.call", []), ("A0.5.call", [6]),
   ("A0.6.call", []), ("A0.6.quiet", []), ("A0.7.call", []), ("A0.7.claims", []),
   ("A0.7.objects", []), ("A0.7.quiet", []), ("A0.8.call", []), ("A0.8.quiet", []),
   ("G1.0.call", [7]), ("G1.0.quiet", []), ("G1.1.call", []), ("G1.1.quiet", []),
   ("G1.2.call", []), ("G1.3.call", [8]), ("G1.3.quiet", []), ("G1.4.call", []),
   ("G1.5.call", [9]), ("G1.6.call", []), ("G1.6.quiet", []), ("G1.7.call", []),
   ("G1.7.front", []), ("G1.7.objects", []), ("G1.7.back", []), ("G1.7.quiet", []),
   ("G1.8.call", []), ("G1.8.quiet", []), ("A1.0.call", [10]), ("A1.0.quiet", []),
   ("A1.1.call", []), ("A1.2.scores", []), ("A1.2.divide", []), ("A1.2.call", []),
   ("A1.3.call", [11]), ("A1.3.quiet", []), ("A1.4.call", []), ("A1.5.call", [12]),
   ("A1.6.call", []), ("A1.6.quiet", []), ("A1.7.call", []), ("A1.7.claims", []),
   ("A1.7.objects", []), ("A1.7.quiet", []), ("A1.8.call", []), ("A1.8.quiet", []),
   ("G2.0.call", [13]), ("G2.0.quiet", []), ("G2.1.call", []), ("G2.1.quiet", []),
   ("G2.2.call", []), ("G2.3.call", [14]), ("G2.3.quiet", []), ("G2.4.call", []),
   ("G2.5.call", [15]), ("G2.6.call", []), ("G2.6.quiet", []), ("G2.7.call", []),
   ("G2.7.front", []), ("G2.7.objects", []), ("G2.7.back", []), ("G2.7.quiet", []),
   ("G2.8.call", []), ("G2.8.quiet", []), ("A2.0.call", [16]), ("A2.0.quiet", []),
   ("A2.1.call", []), ("A2.2.scores", []), ("A2.2.divide", []), ("A2.2.call", []),
   ("A2.3.call", [17]), ("A2.3.quiet", []), ("A2.4.call", []), ("A2.5.call", [18]),
   ("A2.6.call", []), ("A2.6.quiet", []), ("A2.7.call", []), ("A2.7.claims", []),
   ("A2.7.objects", []), ("A2.7.quiet", []), ("A2.8.call", []), ("A2.8.quiet", []),
   ("G3.0.call", [19]), ("G3.0.quiet", []), ("G3.1.call", []), ("G3.1.quiet", []),
   ("G3.2.call", []), ("G3.3.call", [20]), ("G3.3.quiet", []), ("G3.4.call", []),
   ("G3.5.call", [21]), ("G3.6.call", []), ("G3.6.quiet", []), ("G3.7.call", []),
   ("G3.7.front", []), ("G3.7.objects", []), ("G3.7.back", []), ("G3.7.quiet", []),
   ("G3.8.call", []), ("G3.8.quiet", []), ("A3.0.call", [22]), ("A3.0.quiet", []),
   ("A3.1.call", []), ("A3.2.scores", []), ("A3.2.divide", []), ("A3.2.call", []),
   ("A3.3.call", [23]), ("A3.3.quiet", []), ("A3.4.call", []), ("A3.5.call", [24]),
   ("A3.6.call", []), ("A3.6.quiet", []), ("A3.7.call", []), ("A3.7.claims", []),
   ("A3.7.objects", []), ("A3.7.quiet", []), ("A3.8.call", []), ("A3.8.quiet", []),
   ("G4.0.call", [25]), ("G4.0.quiet", []), ("G4.1.call", []), ("G4.1.quiet", []),
   ("G4.2.call", []), ("G4.3.call", [26]), ("G4.3.quiet", []), ("G4.4.call", []),
   ("G4.5.call", [27]), ("G4.6.call", []), ("G4.6.quiet", []), ("G4.7.call", []),
   ("G4.7.front", []), ("G4.7.objects", []), ("G4.7.back", []), ("G4.7.quiet", []),
   ("G4.8.call", []), ("G4.8.quiet", []), ("A4.0.call", [28]), ("A4.0.quiet", []),
   ("A4.1.call", []), ("A4.2.scores", []), ("A4.2.divide", []), ("A4.2.call", []),
   ("A4.3.call", [29]), ("A4.3.quiet", []), ("A4.4.call", []), ("A4.5.call", [30]),
   ("A4.6.call", []), ("A4.6.quiet", []), ("A4.7.call", []), ("A4.7.claims", []),
   ("A4.7.objects", []), ("A4.7.quiet", []), ("A4.8.call", []), ("A4.8.quiet", []),
   ("G5.0.call", [31]), ("G5.0.quiet", []), ("G5.1.call", []), ("G5.1.quiet", []),
   ("G5.2.call", []), ("G5.3.call", [32]), ("G5.3.quiet", []), ("G5.4.call", []),
   ("G5.5.call", [33]), ("G5.6.call", []), ("G5.6.quiet", []), ("G5.7.call", []),
   ("G5.7.front", []), ("G5.7.objects", []), ("G5.7.back", []), ("G5.7.quiet", []),
   ("G5.8.call", []), ("G5.8.quiet", []), ("A5.0.call", [34]), ("A5.0.quiet", []),
   ("A5.1.call", []), ("A5.2.scores", []), ("A5.2.divide", []), ("A5.2.call", []),
   ("A5.3.call", [35]), ("A5.3.quiet", []), ("A5.4.call", []), ("A5.5.call", [36]),
   ("A5.6.call", []), ("A5.6.quiet", []), ("A5.7.call", []), ("A5.7.claims", []),
   ("A5.7.objects", []), ("A5.7.quiet", []), ("A5.8.call", []), ("A5.8.quiet", []),
   ("G6.0.call", [37]), ("G6.0.quiet", []), ("G6.1.call", []), ("G6.1.quiet", []),
   ("G6.2.call", []), ("G6.3.call", [38]), ("G6.3.quiet", []), ("G6.4.call", []),
   ("G6.5.call", [39]), ("G6.6.call", []), ("G6.6.quiet", []), ("G6.7.call", []),
   ("G6.7.front", []), ("G6.7.objects", []), ("G6.7.back", []), ("G6.7.quiet", []),
   ("G6.8.call", []), ("G6.8.quiet", []), ("A6.0.call", [40]), ("A6.0.quiet", []),
   ("A6.1.call", []), ("A6.2.scores", []), ("A6.2.divide", []), ("A6.2.call", []),
   ("A6.3.call", [41]), ("A6.3.quiet", []), ("A6.4.call", []), ("A6.5.call", [42]),
   ("A6.6.call", []), ("A6.6.quiet", []), ("A6.7.call", []), ("A6.7.claims", []),
   ("A6.7.objects", []), ("A6.7.quiet", []), ("A6.8.call", []), ("A6.8.quiet", []),
   ("G7.0.call", [43]), ("G7.0.quiet", []), ("G7.1.call", []), ("G7.1.quiet", []),
   ("G7.2.call", []), ("G7.3.call", [44]), ("G7.3.quiet", []), ("G7.4.call", []),
   ("G7.5.call", [45]), ("G7.6.call", []), ("G7.6.quiet", []), ("G7.7.call", []),
   ("G7.7.front", []), ("G7.7.objects", []), ("G7.7.back", []), ("G7.7.quiet", []),
   ("G7.8.call", []), ("G7.8.quiet", []), ("A7.0.call", [46]), ("A7.0.quiet", []),
   ("A7.1.call", []), ("A7.2.scores", []), ("A7.2.divide", []), ("A7.2.call", []),
   ("A7.3.call", [47]), ("A7.3.quiet", []), ("A7.4.call", []), ("A7.5.call", [48]),
   ("A7.6.call", []), ("A7.6.quiet", []), ("A7.7.call", []), ("A7.7.claims", []),
   ("A7.7.objects", []), ("A7.7.quiet", []), ("A7.8.call", []), ("A7.8.quiet", []),
   ("G8.0.call", [49]), ("G8.0.quiet", []), ("G8.1.call", []), ("G8.1.quiet", []),
   ("G8.2.call", []), ("G8.3.call", [50]), ("G8.3.quiet", []), ("G8.4.call", []),
   ("G8.5.call", [51]), ("G8.6.call", []), ("G8.6.quiet", []), ("G8.7.call", []),
   ("G8.7.front", []), ("G8.7.objects", []), ("G8.7.back", []), ("G8.7.quiet", []),
   ("G8.8.call", []), ("G8.8.quiet", []), ("A8.0.call", [52]), ("A8.0.quiet", []),
   ("A8.1.call", []), ("A8.2.scores", []), ("A8.2.divide", []), ("A8.2.call", []),
   ("A8.3.call", [53]), ("A8.3.quiet", []), ("A8.4.call", []), ("A8.5.call", [54]),
   ("A8.6.call", []), ("A8.6.quiet", []), ("A8.7.call", []), ("A8.7.claims", []),
   ("A8.7.objects", []), ("A8.7.quiet", []), ("A8.8.call", []), ("A8.8.quiet", []),
   ("G9.0.call", [55]), ("G9.0.quiet", []), ("G9.1.call", []), ("G9.1.quiet", []),
   ("G9.2.call", []), ("G9.3.call", [56]), ("G9.3.quiet", []), ("G9.4.call", []),
   ("G9.5.call", [57]), ("G9.6.call", []), ("G9.6.quiet", []), ("G9.7.call", []),
   ("G9.7.front", []), ("G9.7.objects", []), ("G9.7.back", []), ("G9.7.quiet", []),
   ("G9.8.call", []), ("G9.8.quiet", []), ("A9.0.call", [58]), ("A9.0.quiet", []),
   ("A9.1.call", []), ("A9.2.scores", []), ("A9.2.divide", []), ("A9.2.call", []),
   ("A9.3.call", [59]), ("A9.3.quiet", []), ("A9.4.call", []), ("A9.5.call", [60]),
   ("A9.6.call", []), ("A9.6.quiet", []), ("A9.7.call", []), ("A9.7.claims", []),
   ("A9.7.objects", []), ("A9.7.quiet", []), ("A9.8.call", []), ("A9.8.quiet", []),
   ("G10.0.call", [61]), ("G10.0.quiet", []), ("G10.1.call", []), ("G10.1.quiet", []),
   ("G10.2.call", []), ("G10.3.call", [62]), ("G10.3.quiet", []), ("G10.4.call", []),
   ("G10.5.call", [63]), ("G10.6.call", []), ("G10.6.quiet", []), ("G10.7.call", []),
   ("G10.7.front", []), ("G10.7.objects", []), ("G10.7.back", []), ("G10.7.quiet", []),
   ("G10.8.call", []), ("G10.8.quiet", []), ("A10.0.call", [64]), ("A10.0.quiet", []),
   ("A10.1.call", []), ("A10.2.scores", []), ("A10.2.divide", []), ("A10.2.call", []),
   ("A10.3.call", [65]), ("A10.3.quiet", []), ("A10.4.call", []), ("A10.5.call", [66]),
   ("A10.6.call", []), ("A10.6.quiet", []), ("A10.7.call", []), ("A10.7.claims", []),
   ("A10.7.objects", []), ("A10.7.quiet", []), ("A10.8.call", []), ("A10.8.quiet", []),
   ("G11.0.call", [67]), ("G11.0.quiet", []), ("G11.1.call", []), ("G11.1.quiet", []),
   ("G11.2.call", []), ("G11.3.call", [68]), ("G11.3.quiet", []), ("G11.4.call", []),
   ("G11.5.call", [69]), ("G11.6.call", []), ("G11.6.quiet", []), ("G11.7.call", []),
   ("G11.7.front", []), ("G11.7.objects", []), ("G11.7.back", []), ("G11.7.quiet", []),
   ("G11.8.call", []), ("G11.8.quiet", []), ("A11.0.call", [70]), ("A11.0.quiet", []),
   ("A11.1.call", []), ("A11.2.scores", []), ("A11.2.divide", []), ("A11.2.call", []),
   ("A11.3.call", [71]), ("A11.3.quiet", []), ("A11.4.call", []), ("A11.5.call", [72]),
   ("A11.6.call", []), ("A11.6.quiet", []), ("A11.7.call", []), ("A11.7.claims", []),
   ("A11.7.objects", []), ("A11.7.quiet", []), ("A11.8.call", []), ("A11.8.quiet", []),
   ("H.0.front", []), ("H.0.call", []), ("H.1.call", [73]), ("H.1.quiet", []), ("H.2.call", []),
   ("H.3.call", []), ("H.3.quiet", []), ("H.4.call", [74]), ("H.4.quiet", []), ("H.5.call", []),
   ("H.6.call", [75]), ("H.7.call", []), ("H.7.quiet", []), ("H.8.call", []), ("H.8.quiet", []),
   ("H.9.call", []), ("H.9.front", []), ("H.9.objects", []), ("H.9.back", []), ("H.9.quiet", []),
   ("H.10.call", []), ("H.10.quiet", []), ("F.0.front", []), ("F.0.call", [76]), ("F.0.quiet", []),
   ("F.1.front", []), ("F.1.call", []), ("F.1.quiet", []), ("F.2.call", [77]), ("F.2.quiet", []),
   ("F.3.call", [78]), ("F.3.quiet", []), ("F.4.call", [79]), ("F.4.quiet", []),
   ("F.5.call", [80]), ("F.5.quiet", []), ("F.6.call", [81]), ("F.6.quiet", []), ("F.7.call", []),
   ("M.0.front", []), ("M.0.call", []), ("M.0.quiet", []), ("M.1.call", [82]), ("M.1.quiet", []),
   ("seal.behind", [])]

/-- BY THE KERNEL: the one pass at the two written lists gives the written table. -/
theorem msgs_written : msgsE cutWritten esW 0 = msgsW := by decide +kernel

/-- A control: with one number changed, at the row "H.4.call": refused. -/
theorem msgs_written_no :
    decide (msgsE cutWritten esW 0 = msgsW.set 439 ("H.4.call", [75])) = false := by
  decide +kernel

/-- BY THE KERNEL: no name stands twice in the written table. -/
theorem msgsW_nodup : (msgsW.map (·.1)).Nodup := by decide +kernel

/-- **K8's MESSAGES' NUMBERS AT THE WRITTEN LISTS ARE A ROW OF A WRITTEN TABLE**, at every name. -/
theorem k8Msgs_lit (look : String) : k8MsgsC cutWritten esW look = msgsAt msgsW look := by
  rw [k8MsgsC_pass, msgs_written]

/-- So K8's numbers at a link, at the written lists, read the written table. -/
theorem k8ParWC_lit (G : ProofFile.Ground) (X : OnBytes.Model.Stages.LinkH) (l : Nat) :
    k8ParWC (k8MsgsC cutWritten esW) G X l = k8ParWC (msgsAt msgsW) G X l := by
  rw [funext k8Msgs_lit]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.rootsE_from
#print axioms Johnson.AtFull.Shape.rootsC_add
#print axioms Johnson.AtFull.Shape.takes_from
#print axioms Johnson.AtFull.Shape.before_hit
#print axioms Johnson.AtFull.Shape.before_miss
#print axioms Johnson.AtFull.Shape.k8MsgsC_spec
#print axioms Johnson.AtFull.Shape.spec_hit
#print axioms Johnson.AtFull.Shape.spec_miss
#print axioms Johnson.AtFull.Shape.msgsE_cons
#print axioms Johnson.AtFull.Shape.msgsE_spec
#print axioms Johnson.AtFull.Shape.k8MsgsC_pass
#print axioms Johnson.AtFull.Shape.msgs_written
#print axioms Johnson.AtFull.Shape.msgs_written_no
#print axioms Johnson.AtFull.Shape.msgsW_nodup
#print axioms Johnson.AtFull.Shape.k8Msgs_lit
#print axioms Johnson.AtFull.Shape.k8ParWC_lit
