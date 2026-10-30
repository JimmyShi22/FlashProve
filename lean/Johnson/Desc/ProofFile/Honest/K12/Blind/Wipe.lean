-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/Wipe.lean: The record inside a proximity test (`T12`,
Johnson/Desc/K12/Join.lean) with every row's target set to zero, and what it means that two such
records agree but for targets. The wipes of a row, a statement, a batched claim, single rows and the
ground's carried record are the kind K10's authors' own, by import: one text for both kinds.
Definitions with code, and three lemmas on them.

  `wipeP`        what passes from a part to the next, its target set to zero
  `wipeT`        the record. A target has four homes in it: a group's rows and a message's sample
                 rows (`wipeSt`), the claim behind a batching (`wipeG`), the single rows behind a
                 fold (`singleRowsWithZeroTarget`)
  `Agree`        two records agree but for targets: wiped, they are one
  `wipePS`       the plain state of a test's stretch (`H2K.PS`): its carried record wiped (`wipeD`)
  `pass_cases`   what two records that agree pass on has one constructor, and agrees but for the
                 target
  `wipeP_wipeP`, `wipeT_wipeT`   each wipes twice as once

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: StAtZero, WipeFold, BatWipe, WipeS, Wipe/).

Limits. Definitions and lemmas on them: nothing is said of any part of the test here. Coefficients,
kinds, marks, the book of trees, the count of roots, the group's number and the mask's are not
wiped: `Agree` holds them equal. `wipeD` leaves the opened columns as they are. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK10
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open VerifiableInference.Desc.K12 (T12 Passing)
open ProofFile.Honest.K10 (wipeSt wipeG singleRowsWithZeroTarget wipeD wipeSt_idem)

/-- What passes from a part to the next, its target set to zero. -/
def wipeP : Passing → Passing
  | .nothing => .nothing
  | .claim r L => .claim (wipeG r) L
  | .single R n => .single (singleRowsWithZeroTarget R) n
  | .switched out theta n => .switched out theta n

/-- **The record inside a proximity test with every target set to zero.** -/
def wipeT (t : T12) : T12 := { t with st := wipeSt t.st, pass := wipeP t.pass }

/-- **Two records agree but for targets.** -/
def Agree (t t' : T12) : Prop := wipeT t = wipeT t'

/-- The plain state of a test's stretch. -/
def wipePS (s : H2K.PS) : H2K.PS :=
  { s with d := wipeD s.d, cur := s.cur.map fun x => (x.1, wipeG x.2.1, x.2.2) }

theorem wipeP_wipeP (x : Passing) : wipeP (wipeP x) = wipeP x := by cases x <;> rfl

theorem wipeT_wipeT (t : T12) : wipeT (wipeT t) = wipeT t := by
  unfold wipeT
  simp only [wipeSt_idem, wipeP_wipeP]

/-- What two records that agree but for targets pass on has one constructor, and agrees but for the
target. -/
theorem pass_cases (x x' : Passing) (h : wipeP x = wipeP x') :
    (x = .nothing ∧ x' = .nothing) ∨
    (∃ r r' L, x = .claim r L ∧ x' = .claim r' L ∧ wipeG r = wipeG r') ∨
    (∃ R R' n, x = .single R n ∧ x' = .single R' n ∧ singleRowsWithZeroTarget R = singleRowsWithZeroTarget R') ∨
    ∃ out theta n, x = .switched out theta n ∧ x' = .switched out theta n := by
  cases x with
  | nothing =>
    cases x' with
    | nothing => exact Or.inl ⟨rfl, rfl⟩
    | claim _ _ => cases h
    | single _ _ => cases h
    | switched _ _ _ => cases h
  | claim r L =>
    cases x' with
    | claim r' L' =>
      have h' : Passing.claim (wipeG r) L = Passing.claim (wipeG r') L' := h
      injection h' with h1 h2
      subst h2
      exact Or.inr (Or.inl ⟨r, r', L, rfl, rfl, h1⟩)
    | nothing => cases h
    | single _ _ => cases h
    | switched _ _ _ => cases h
  | single R n =>
    cases x' with
    | single R' n' =>
      have h' : Passing.single (singleRowsWithZeroTarget R) n = Passing.single (singleRowsWithZeroTarget R') n' := h
      injection h' with h1 h2
      subst h2
      exact Or.inr (Or.inr (Or.inl ⟨R, R', n, rfl, rfl, h1⟩))
    | nothing => cases h
    | claim _ _ => cases h
    | switched _ _ _ => cases h
  | switched out theta n =>
    cases x' with
    | switched out' theta' n' =>
      have h' : Passing.switched out theta n = Passing.switched out' theta' n' := h
      injection h' with h1 h2 h3
      subst h1 h2 h3
      exact Or.inr (Or.inr (Or.inr ⟨out, theta, n, rfl, rfl⟩))
    | nothing => cases h
    | claim _ _ => cases h
    | single _ _ => cases h

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.wipeP
#print axioms ProofFile.Honest.K12.Blind.wipeT
#print axioms ProofFile.Honest.K12.Blind.Agree
#print axioms ProofFile.Honest.K12.Blind.wipePS
#print axioms ProofFile.Honest.K12.Blind.wipeP_wipeP
#print axioms ProofFile.Honest.K12.Blind.wipeT_wipeT
#print axioms ProofFile.Honest.K12.Blind.pass_cases
