-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/PlanListsSum.lean: the rounds that the planner's routines for sumchecks, product
trees and lookups add, as lists.

For each of these routines of OnBytes/Params/Planner.lean this file gives a list of descriptions of
rounds (`RoundSpec`, OnBytes/Params/PlanningLaws.lean), made with `++`, `map` and `replicate` from
the routine's own arguments, and proves that the routine, wherever it ends well from a state in
which nothing is open, adds the rounds of that list and leaves nothing open (`Runs`). The lists name
the bound by which each round is priced. In a list the same description stands for every turn of a
loop whose variable the round does not read: all rounds of a sumcheck's variables of one degree are
one description.

Main definitions: `pscVariable`, `pscList`, `treeList`, `lookupList`.
Main theorems: `runs_pscRounds`, `runs_psc`, `runs_zero`, `runs_line`, `runs_shift`, `runs_join`,
`runs_lkp`, `runs_treeLevels`, `runs_productTree`, `runs_batSigma`, `runs_batt`, `runs_split`,
`runs_lookup`.
What is not claimed: that a routine ends well, or what its own tests found. Nothing on the routines
for sending, folding and positions, nor on the smallness test (`planRng`), which no chain of a key
or an entry calls. Nothing on the C++ planner, of which OnBytes/Params/ is a rendering. For proofs
only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.PlanningLaws

set_option autoImplicit false

namespace OnBytes.Params

section
variable {s : Setting} {c : Scope}

/-- The prover sends n elements where no bytes are open. -/
theorem runs_scalars0 (n r a : Nat) : Runs s c 0 r a (planScalars n) () [] (24 * n) r a := by
  have h := runs_scalars (s := s) (c := c) n 0 r a
  rw [Nat.zero_add] at h
  exact h

end

/-- The round of one variable of a sumcheck whose round polynomial has a degree below g. -/
def pscVariable (s : Setting) (g : Nat) : RoundSpec :=
  .said "PSC round" .field (fieldError s (g - 1)) { drawE := 1, priced := .roundItself }
    (24 * (g - 1)) 0 0

/-- The first round of a sumcheck. -/
def pscEpsilon (s : Setting) : RoundSpec :=
  .said "PSC epsilon" .field (fieldError s 1) { drawE := 1, priced := .settingAlone } (24 * 1) 0 0

/-- The round of the further variable of a sumcheck. -/
def pscY (s : Setting) (degreeY : Nat) : RoundSpec :=
  .said "PSC Y" .field (fieldErrorNonzero s degreeY)
    { drawE := 1, drawNZ := 1, priced := .roundItself } (24 * degreeY) 0 0

/-- The rounds of a sumcheck: the first; one for each variable; and, with a further variable, that
variable's round and the silent round of the end values. -/
def pscList (s : Setting) (x : PscSize) : List RoundSpec :=
  pscEpsilon s :: (x.degree.map (pscVariable s) ++
    (if x.withY = true then [pscY s x.degreeY, .silent "PSC values" (24 * x.values) 0] else []))

/-- The round LINE. -/
def lineRound (s : Setting) : RoundSpec :=
  .said "LINE" .field (fieldError s 1) { drawE := 1, priced := .settingAlone } 0 0 0

/-- The levels of a product tree from level l on, as many as the fuel: for level l, l + 1, … a
sumcheck with that number and `more` variables, of degree below 3, and LINE. -/
def treeList (s : Setting) (more : Nat) : Nat → Nat → List RoundSpec
  | 0, _ => []
  | fuel + 1, l =>
    pscList s { degree := List.replicate (l + more) 3 } ++
      (lineRound s :: treeList s more fuel (l + 1))

/-- The live planes of a lookup. -/
def lookupLive (x : LookupSize) : Nat := if x.live != 0 then x.live else 2 ^ min x.mu 6

/-- The logarithms of the keys of a lookup's parts. -/
def lookupParts (x : LookupSize) : List Nat := if x.parts.isEmpty then [x.v] else x.parts

/-- The rounds of one lookup, in the order of `planLookup`. -/
def lookupList (s : Setting) (x : LookupSize) : List RoundSpec :=
  (if x.shifted = true then
      [.said "LKP shift" .field (fieldError s (2 ^ x.d)) { drawE := 1, priced := .callersWord }
        0 0 0]
    else []) ++
  (.said "LKP" .field (Bound.ratio (sumT ((lookupParts x).map (2 ^ ·)) - 1) s.cardE)
      { drawE := 1, priced := .callersWord } 0 0 0 ::
  (pscList s { degreeY := 3, values := 3 } ++
  ((List.replicate (lookupLive x - 2) (pscList s { degreeY := 3, values := 2 })).flatten ++
  ((List.replicate ((lookupParts x).length - 1) (pscList s {})).flatten ++
  (.said "JOIN" .field (fieldError s x.mu) { drawE := x.mu, priced := .roundItself } 0 0 0 ::
  (((lookupParts x).map fun v => treeList s 0 v 0).flatten ++
  (treeList s x.mu x.d 0 ++
  (pscList s { degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false } ++
  (.said "ZERO" .field (fieldError s (x.mu + x.d))
      { drawE := x.mu + x.d, priced := .roundItself } 0 0 0 ::
  pscList s { degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 })))))))))

section
variable {s : Setting} {c : Scope}

/-- The rounds of the variables of a sumcheck. -/
theorem runs_pscRounds :
    ∀ gs : List Nat, Runs s c 0 0 0 (planPscRounds s gs) () (gs.map (pscVariable s)) 0 0 0
  | [] => runs_pure () 0 0 0
  | g :: gs => by
      unfold planPscRounds
      exact Runs.cast (runs_bind (runs_scalars0 (g - 1) 0 0)
        (runs_bind (runs_close _ _ _ _ _ _ _) (runs_pscRounds gs))) (by simp [pscVariable])

/-- A sumcheck. -/
theorem runs_psc (x : PscSize) : Runs s c 0 0 0 (planPsc x) () (pscList s x) 0 0 0 := by
  unfold planPsc
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_scalars0 1 0 0)
    (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_pscRounds x.degree)
      (runs_ite
        (fun _ => runs_bind (runs_scalars0 x.degreeY 0 0) (runs_bind (runs_close _ _ _ _ _ _ _)
          (runs_bind (runs_scalars0 x.values 0 0) (runs_closeNone _ _ _ _))))
        (fun _ => runs_pure () 0 0 0))))))
    (by simp [pscList, pscEpsilon, pscY])

/-- ZERO. -/
theorem runs_zero (vars : Nat) : Runs s c 0 0 0 (planZero vars) ()
    [.said "ZERO" .field (fieldError s vars) { drawE := vars, priced := .roundItself }
      0 0 0] 0 0 0 := by
  unfold planZero
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_close _ _ _ _ _ _ _)) (by simp)

/-- LINE. -/
theorem runs_line : Runs s c 0 0 0 planLine () [lineRound s] 0 0 0 := by
  unfold planLine
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_close _ _ _ _ _ _ _)) (by simp [lineRound])

/-- LKP shift. -/
theorem runs_shift (unionEntries : Nat) : Runs s c 0 0 0 (planShift unionEntries) ()
    [.said "LKP shift" .field (fieldError s unionEntries) { drawE := 1, priced := .callersWord }
      0 0 0] 0 0 0 := by
  unfold planShift
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_close _ _ _ _ _ _ _)) (by simp)

/-- JOIN. -/
theorem runs_join (vars : Nat) : Runs s c 0 0 0 (planJoin vars) ()
    [.said "JOIN" .field (fieldError s vars) { drawE := vars, priced := .roundItself }
      0 0 0] 0 0 0 := by
  unfold planJoin
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_close _ _ _ _ _ _ _)) (by simp)

/-- LKP. -/
theorem runs_lkp (keysLog : Nat) : Runs s c 0 0 0 (planLkp keysLog) ()
    [.said "LKP" .field (Bound.ratio (2 ^ keysLog - 1) s.cardE)
      { drawE := 1, priced := .callersWord } 0 0 0] 0 0 0 := by
  unfold planLkp
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_close _ _ _ _ _ _ _)) (by simp)

/-- The levels of a product tree. -/
theorem runs_treeLevels (more : Nat) :
    ∀ fuel l : Nat, Runs s c 0 0 0 (planTreeLevels more fuel l) () (treeList s more fuel l) 0 0 0
  | 0, _ => runs_pure () 0 0 0
  | fuel + 1, l => by
      unfold planTreeLevels
      exact Runs.cast
        (runs_bind (runs_psc _) (runs_bind runs_line (runs_treeLevels more fuel (l + 1))))
        (by simp [treeList])

/-- A product tree. -/
theorem runs_productTree (levels more : Nat) :
    Runs s c 0 0 0 (planProductTree levels more) () (treeList s more levels 0) 0 0 0 :=
  runs_treeLevels more levels 0

/-- BAT-sigma. -/
theorem runs_batSigma (rows : Nat) : Runs s c 0 0 0 (planBatSigma rows) ()
    [.said "BAT-sigma" .field (powersError s rows) { drawE := 1, rows := rows, priced := .asSaid }
      0 0 0] 0 0 0 := by
  unfold planBatSigma
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_close _ _ _ _ _ _ _)) (by simp)

/-- Several pending rows into one. -/
theorem runs_batt (rows kCol : Nat) : Runs s c 0 0 0 (planBatt rows kCol) ()
    (.said "BAT-sigma" .field (powersError s rows) { drawE := 1, rows := rows, priced := .asSaid }
      0 0 0 :: pscList s { degree := List.replicate kCol 3, withY := false }) 0 0 0 := by
  unfold planBatt
  exact Runs.cast (runs_bind (runs_batSigma rows) (runs_psc _)) (by simp)

/-- SPLIT. -/
theorem runs_split : Runs s c 0 0 0 planSplit () [.silent "SPLIT" (24 * 1) 0] 0 0 0 := by
  unfold planSplit
  exact Runs.cast (runs_bind (runs_scalars0 1 0 0) (runs_closeNone _ _ _ _)) (by simp)

/-- One lookup. -/
theorem runs_lookup (x : LookupSize) : Runs s c 0 0 0 (planLookup x) () (lookupList s x) 0 0 0 := by
  unfold planLookup
  exact Runs.cast (runs_bind (runs_setting 0 0 0) (runs_bind (runs_needs _ _ 0 0 0)
    (runs_bind (runs_needs _ _ 0 0 0)
    (runs_when (runs_shift _)
    (runs_bind (runs_close _ _ _ _ _ _ _) (runs_bind (runs_psc _)
    (runs_bind (runs_times (runs_psc _) _) (runs_bind (runs_times (runs_psc _) _)
    (runs_bind (runs_join _) (runs_bind (runs_forEach (fun v => runs_productTree v 0) _)
    (runs_bind (runs_productTree _ _) (runs_bind (runs_psc _)
    (runs_bind (runs_zero _) (runs_psc _))))))))))))))
    (by simp [lookupList, lookupLive, lookupParts])

end

end OnBytes.Params

#print axioms OnBytes.Params.runs_lookup
#print axioms OnBytes.Params.runs_psc
#print axioms OnBytes.Params.runs_treeLevels
#print axioms OnBytes.Params.runs_batt
