-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanNine.lean: THE TEST AT A GROUP OF LAYERS WITHOUT THE PUBLIC PARAMETERS X.
`firstLabCoreB` (Johnson/Road/K4/K4PlanLab.lean) still reads of X, a matrix: the label's owner and
entry, and the sizes m and k; and how many matrices the group has. At the reference sizes these are
nine pairs of numerals and a rule (`sizeW`, `ownerW`). `XNine X` says so of X; under it the test is
`firstClosedCoreB`, which reads the codes, the request's shape and layout, the plan's seats and
nothing else. Five definitions (one a Lean structure of three conditions) and three theorems. Glue;
no draw, no count.

  `sizeW μ`: the rows and columns of matrix μ of a feed-forward link, μ < 9.
  `ownerW g μ`: the link that owns matrix μ of group g, and its entry there: the group's own link
    and μ; but the stream that comes in (μ = 8) at a later group: the group before, entry 7.
  `XNine X`: at the twelve groups X has nine matrices, these owners, and these rows of symbols and
    columns (the rows of symbols, which is all that the test reads of m).
  `symClosedB`, `firstClosedCoreB`: `symLabB`, `firstLabCoreB` at these numerals.
  `symLab_eq_closed`, `firstClosed_eq`: under `XNine X` the tests are one: EQUATIONS.
  `firstCore_of_closed`: under `XNine X` and the names' tie at g, a yes of `firstClosedCoreB` is a
    yes of `firstCoreB`.

Limits. K04_law IS NOT PROVED BY THIS. `XNine X` IS A PREMISE: that the goals' scope gives it is
shown by nothing yet (a run at the full-size public files prints just these numbers). The reference
sizes alone.
-/
import Johnson.Road.K4.K4PlanLab

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls)
open VerifiableInference.Desc.Sound (Mem)
open Meaning (labAt ownerK ownerA nameOf)

/-- The rows and the columns of matrix μ of a feed-forward link, at the reference sizes. -/
def sizeW (μ : ℕ) : ℕ × ℕ :=
  [(65536, 5990), (65536, 5990), (65536, 5990), (32768, 3200), (8192, 324), (65536, 256),
    (65536, 1536), (65536, 400), (65536, 400)].getD μ (0, 0)

/-- The link that owns matrix μ of group g, and the matrix's entry in that link's list. -/
def ownerW (g μ : ℕ) : ℕ × ℕ := if μ = 8 ∧ g ≠ 0 then (2 * (g - 1), 7) else (2 * g, μ)

/-- **At the twelve groups the public parameters have nine matrices, these owners, these sizes.** -/
structure XNine (X : Public) : Prop where
  nm : ∀ g, g < 12 → (Meaning.sizesOf X (2 * g)).NM = 9
  own : ∀ g, g < 12 → ∀ μ, μ < 9 →
    (ownerK (labAt X (2 * g) μ), ownerA (labAt X (2 * g) μ)) = ownerW g μ
  size : ∀ g, g < 12 → ∀ μ, μ < 9 →
    (Alg.symRows ((Meaning.sizesOf X (2 * g)).m μ), (Meaning.sizesOf X (2 * g)).k μ) =
      (Alg.symRows (sizeW μ).1, (sizeW μ).2)

section
variable {Cells : Type} (A : PinPlan Cells) (num arr : ℕ → ℕ → ℕ) (N : Numbers)

/-- The test at one matrix, at the numerals: nothing of X is read. -/
def symClosedB (g μ : ℕ) : Bool :=
  arrAtB A.D (sigListCalls A.D A.rad A.link) A.link (ownerW g μ).1 (nameOf (ownerW g μ).2)
      (Alg.symRows (sizeW μ).1) (sizeW μ).2 &&
    tenantB A num arr N (2 * g) (ownerW g μ).1 (nameOf (ownerW g μ).2)

/-- **Under `XNine X` the test at a matrix is the one at the numerals.** -/
theorem symLab_eq_closed {X : Public} (H : XNine X) {g μ : ℕ} (hg : g < 12) (hμ : μ < 9) :
    symLabB A num arr N (2 * g) X (Meaning.sizesOf X) μ = symClosedB A num arr N g μ := by
  have o := H.own g hg μ hμ
  have s := H.size g hg μ hμ
  have o1 : ownerK (labAt X (2 * g) μ) = (ownerW g μ).1 := congrArg Prod.fst o
  have o2 : ownerA (labAt X (2 * g) μ) = (ownerW g μ).2 := congrArg Prod.snd o
  have s1 : Alg.symRows ((Meaning.sizesOf X (2 * g)).m μ) = Alg.symRows (sizeW μ).1 :=
    congrArg Prod.fst s
  have s2 : (Meaning.sizesOf X (2 * g)).k μ = (sizeW μ).2 := congrArg Prod.snd s
  unfold symLabB symClosedB
  rw [o1, o2, s1, s2]

end

/-- **The test at a group, at the numerals**: it reads D's codes, shape and layout, the seats, N,
the members and the numbering. -/
def firstClosedCoreB (D : Sent) (ps : List P5T.PSeat) (N : Numbers) (ms : List Mem) (g : ℕ)
    (num arr : ℕ → ℕ → ℕ) : Bool :=
  sitsInB (sigListCalls D (fun _ => 0) (2 * g)) (pinsCore D ps (2 * g)).seatT ms N (2 * g) &&
    (List.range 9).all fun μ => symClosedB (pinsCore D ps (2 * g)) num arr N g μ

/-- **Under `XNine X` the test at a group is the one at the numerals.** -/
theorem firstClosed_eq {X : Public} (H : XNine X) {g : ℕ} (hg : g < 12) (D : Sent)
    (ps : List P5T.PSeat) (N : Numbers) (ms : List Mem) (num arr : ℕ → ℕ → ℕ) :
    firstLabCoreB D ps N ms X g num arr = firstClosedCoreB D ps N ms g num arr := by
  unfold firstLabCoreB firstClosedCoreB
  rw [H.nm g hg]
  congr 1
  exact P5T.all_congr_mem _ _ _ fun μ hμ =>
    symLab_eq_closed (pinsCore D ps (2 * g)) num arr N H hg (List.mem_range.1 hμ)

/-- **A yes at the numerals is a yes of `firstCoreB`**, under `XNine X` and the names' tie at g. -/
theorem firstCore_of_closed {X : Public} (H : XNine X) {g : ℕ} (hg : g < 12) {D : Sent}
    (hN : NamesAt D X g) (ps : List P5T.PSeat) (N : Numbers) (ms : List Mem)
    (num arr : ℕ → ℕ → ℕ) (h : firstClosedCoreB D ps N ms g num arr = true) :
    firstCoreB D ps N ms X g num arr = true :=
  (firstLab_eq hN ps N ms num arr).trans ((firstClosed_eq H hg D ps N ms num arr).trans h)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.symLab_eq_closed
#print axioms OnBytes.Road.K4.firstClosed_eq
#print axioms OnBytes.Road.K4.firstCore_of_closed
