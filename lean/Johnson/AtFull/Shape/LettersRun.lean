-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LettersRun.lean: WHERE THE LETTERS AT Z AND G ARE ALIKE TO A RECORD L
(`LettersAlike`, TabLetters.lean), THE FRAME's LETTERS OVER THE TABLE AT Z AND G ARE THOSE OVER THE
SECOND TEXT AT L: ONE EQUATION OF TWO RECORDS OF THE TYPE `Shape S`
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean); so "the run on shapes returns" (`Shape.yes`) at
the one is that at the other. General in Z, G and L; no head; nothing is evaluated.

What it is for. The rule's public premise is (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes
startShA 358 = true. Whoever shows the like at `shapeL L`, whole or from its pieces
(`yes_of_pieces`, ShapeRun.lean, at Z := shapeL L), at a record L to which the letters are alike,
has it.

Main names.
* `shapeL L`: the frame's letters over TabL.cells L. `yes_congr`, `run_congr`, `runFrom_congr`:
  tools, at steps and tests that are letters. `g_of_alike`, `vals_of_alike`.
* **`shape_of_alike`**: firstZA (Tab.g Z G) (Tab.vals Z G) = shapeL L. **`yes_of_alike`**. Between
  two records: `shape_alike`, `yes_alike`.

Limits. EQUATIONS OF TERMS UNDER A PREMISE. Nothing says that a run returns at any record. THE
PREMISE hv : v = v' OF yes_congr, run_congr AND runFrom_congr IS IDLE: a run reads the steps alone:
a caller pays an equation of tests on values for a fact that never reads them; and "the run on
shapes returns" at shapeL L says nothing of the second half of any cell. run_congr has no caller.
The run and the run from a border are not stated at the table's own steps: typed so, Lean ran into
its recursion limit while it held the two sides' types together; shape_of_alike gives them by
rewriting. That the letters at any Z and G are alike to a record: LettersAtHead.lean's implication,
whose plans' half nobody pays there; LettersAtX.lean's lw_alike pays it, under the head, at an
opening, at the record LW Zp.p.X. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TabLetters
import Johnson.Desc.ProofFile.Honest.Thread.ShapeRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open ProofFile.Honest (Shape)
open VerifiableInference.Desc.First (S)

/-- The frame's letters over the second text of the table at a record of letters. -/
abbrev shapeL (L : TabLetters) : Shape S :=
  firstZA (fun n => (TabL.cells L n).1) fun n => (TabL.cells L n).2

section
variable {g g' : Nat → ShA → Except String ShA}
  {v v' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}

theorem yes_congr (hg : g = g') (hv : v = v') (a : ShA) (n : Nat) :
    (firstZA g v).yes a n = (firstZA g' v').yes a n := by
  subst hg hv
  rfl

theorem run_congr (hg : g = g') (hv : v = v') (n : Nat) (a : ShA) :
    (firstZA g v).run n a = (firstZA g' v').run n a := by
  subst hg hv
  rfl

theorem runFrom_congr (hg : g = g') (hv : v = v') (m n : Nat) (a : ShA) :
    (firstZA g v).runFrom m n a = (firstZA g' v').runFrom m n a := by
  subst hg hv
  rfl

end

variable {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : TabLetters}

theorem g_of_alike (h : LettersAlike (lettersOf Z G) L) :
    Tab.g Z G = fun n => (TabL.cells L n).1 :=
  funext fun n => congrArg Prod.fst (tab_of_alike h n)

theorem vals_of_alike (h : LettersAlike (lettersOf Z G) L) :
    Tab.vals Z G = fun n => (TabL.cells L n).2 :=
  funext fun n => congrArg Prod.snd (tab_of_alike h n)

/-- **LETTERS ALIKE: THE FRAME's LETTERS OVER THE TABLE ARE THOSE OVER THE SECOND TEXT**: one
equation of the two records: so every run over the one is that run over the other. -/
theorem shape_of_alike (h : LettersAlike (lettersOf Z G) L) :
    firstZA (Tab.g Z G) (Tab.vals Z G) = shapeL L := by
  rw [g_of_alike h, vals_of_alike h]

/-- **LETTERS ALIKE: "THE RUN ON SHAPES RETURNS" AT THE TABLE IS THAT AT THE SECOND TEXT.** -/
theorem yes_of_alike (h : LettersAlike (lettersOf Z G) L) (a : ShA) (n : Nat) :
    (firstZA (Tab.g Z G) (Tab.vals Z G)).yes a n = (shapeL L).yes a n :=
  yes_congr (g_of_alike h) (vals_of_alike h) a n

/-- The like between two records. -/
theorem shape_alike {L' : TabLetters} (h : LettersAlike L L') : shapeL L = shapeL L' := by
  have e1 : (fun n => (TabL.cells L n).1) = fun n => (TabL.cells L' n).1 :=
    funext fun k => congrArg Prod.fst (cells_alike h k)
  have e2 : (fun n => (TabL.cells L n).2) = fun n => (TabL.cells L' n).2 :=
    funext fun k => congrArg Prod.snd (cells_alike h k)
  show firstZA _ _ = firstZA _ _
  rw [e1, e2]

theorem yes_alike {L' : TabLetters} (h : LettersAlike L L') (a : ShA) (n : Nat) :
    (shapeL L).yes a n = (shapeL L').yes a n :=
  yes_congr (funext fun k => congrArg Prod.fst (cells_alike h k))
    (funext fun k => congrArg Prod.snd (cells_alike h k)) a n

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.yes_congr
#print axioms Johnson.AtFull.Shape.run_congr
#print axioms Johnson.AtFull.Shape.runFrom_congr
#print axioms Johnson.AtFull.Shape.g_of_alike
#print axioms Johnson.AtFull.Shape.vals_of_alike
#print axioms Johnson.AtFull.Shape.shape_of_alike
#print axioms Johnson.AtFull.Shape.yes_of_alike
#print axioms Johnson.AtFull.Shape.shape_alike
#print axioms Johnson.AtFull.Shape.yes_alike
#print axioms Johnson.AtFull.Shape.shapeL
