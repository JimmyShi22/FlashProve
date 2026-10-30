-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/RunsMade.lean: THE ATTENTION's TWO RUNS THAT MAKE FORMS (`P.Runs.firstRun`,
`P.Runs.secondRun`: Johnson/Desc/First/Att/RunsP.lean) ONCE MORE, WITH EVERY MAKING OF A FORM
REWRITTEN BY THE LAWS OF AddMulL.lean: ONE APPEND IN THE PLACE OF ONE PUSH AN ENTRY. THE SECOND
TEXTS ARE WRITTEN NOWHERE: LEAN MAKES THEM. No premise. Two definitions, each a pair (a function,
and the proof that the library's run is equal to it at all arguments); two theorems that say the
ties as laws.

Purpose. The two runs lay their forms by Aff.addMul, by the sum and the difference of forms and by
Aff.scale, through 29 and 14 definitions of RunsP.lean. What that costs Lean's kernel, and why, is
told in AddMulL.lean. Whoever evaluates a text that calls the runs may rewrite by firstRun_L and
secondRun_L first.

How. `⟨_, fun h K => by delta …; simp -zeta only [addMul_eq, add_eq, sub_eq, scale_eq]; rfl⟩`: delta
lays open the named definitions' own texts: all that lie between the run and Aff.addMul, as a
program outside the library listed them; simp rewrites by the four laws; the closing rfl fills the
hole with the term that then stands there. So the made terms follow the library's texts at every
build, and nobody types them.

Main names.
* `firstRunL`, `firstRun_L : P.Runs.firstRun h K = firstRunL.1 h K`.
* `secondRunL`, `secondRun_L : P.Runs.secondRun h K = secondRunL.1 h K`.

Limits. WHAT A READER LOSES: THE LIGHT TEXTS CAN BE READ NOWHERE IN THIS FILE; `#print
Johnson.AtFull.Shape.firstRunL` shows one. THE TWO TYPES ARE MET BY THE RUNS THEMSELVES: they say
"equal", never "light"; what the build forces is that at least one rewriting took place in each.
THAT NO Aff.addMul IS LEFT BENEATH THE MADE RUNS IS NOT STATED HERE AND CANNOT BE: it is seen by a
walk over the made terms' constants, outside the library. IF A LATER TEXT OF RunsP.lean REACHES
Aff.addMul THROUGH A DEFINITION THAT THE TWO LISTS DO NOT NAME, THIS FILE STILL COMPILES AND THAT
MAKING STAYS AS IT WAS: the walk shows it. Where a run lays entries one by one onto a long form, the
law does not help (AddMulL.lean's Limits); `weighted` and `lessPieces` (RunsP.lean) are folds that
add onto a growing form. Equalities of functions: nothing says that a run returns, and nothing is
evaluated here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.RunsP
import Johnson.AtFull.Shape.AddMulL

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- For the elaboration of the made terms, which are deep.
set_option maxRecDepth 100000

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open AddMulL (addMul_eq add_eq sub_eq scale_eq)

/-- The run «first» (Johnson/Desc/First/Att/RunsP.lean) with every making of a form rewritten by
the laws of AddMulL.lean: SO BY THE RECIPE; THE TYPE SAYS "EQUAL" ALONE. The first field is made by
Lean: the closing rfl fills it. -/
def firstRunL : { f : P.Runs.In → Nat → Option (List Aff × P.Runs.JoinsP) //
    ∀ h K, P.Runs.firstRun h K = f h K } :=
  ⟨_, fun h K => by
    delta P.Runs.firstRun P.Runs.claim3 P.Runs.claim4 P.Runs.claim5 P.Runs.callKR P.Runs.callKFD
      P.Runs.unitKFD P.Runs.linPlanes P.Runs.lessPieces P.Runs.plane P.Runs.weighted P.Runs.shV
      P.Runs.xl P.Runs.overG P.Runs.readDenominator P.Runs.readGroup P.Runs.readHead
      P.Runs.readIndexBit P.Runs.readMaximum P.Runs.remForm P.Runs.indexForm P.Runs.joinR16
      P.Runs.keyIX P.Runs.keyKFD P.Runs.keyKR P.Runs.keyWH P.Runs.keyWL P.Runs.endValues
      P.Runs.endValuesE
    simp -zeta only [addMul_eq, add_eq, sub_eq, scale_eq]
    rfl⟩

/-- The tie, as a law for a rewriting. -/
theorem firstRun_L (h : P.Runs.In) (K : Nat) : P.Runs.firstRun h K = firstRunL.1 h K :=
  firstRunL.2 h K

/-- The run «second» likewise. -/
def secondRunL : { f : P.Runs.In → Nat → Option (List Aff) //
    ∀ h K, P.Runs.secondRun h K = f h K } :=
  ⟨_, fun h K => by
    delta P.Runs.secondRun P.Runs.claim6 P.Runs.claim7 P.Runs.claim8 P.Runs.valueProduct
      P.Runs.overG P.Runs.plane P.Runs.readGroup P.Runs.readHead P.Runs.readIndexBit
      P.Runs.readMaximum P.Runs.shV P.Runs.weighted P.Runs.xl
    simp -zeta only [addMul_eq, add_eq, sub_eq, scale_eq]
    rfl⟩

/-- The tie, as a law for a rewriting. -/
theorem secondRun_L (h : P.Runs.In) (K : Nat) : P.Runs.secondRun h K = secondRunL.1 h K :=
  secondRunL.2 h K

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.firstRunL
#print axioms Johnson.AtFull.Shape.firstRun_L
#print axioms Johnson.AtFull.Shape.secondRunL
#print axioms Johnson.AtFull.Shape.secondRun_L
