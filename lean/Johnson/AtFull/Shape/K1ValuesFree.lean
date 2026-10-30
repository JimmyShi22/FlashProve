-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/K1ValuesFree.lean: THE KIND K1 IN THE TABLE OF STEPS ON SHAPES OF THE FIRST CHAIN
(Johnson/AtFull/Shape/TableOfSteps.lean): THE 38 OF ITS 51 MEMBERS WHOSE CELL HAS NO TEST ON VALUES:
number 2 (the opening), the 25 digits' commitments, the 12 reads' commitments at the even links
below the head. At these numbers the debt ValuesJ of the file's rule
(Johnson/Desc/ProofFile/Honest/Thread/ShapeJV.lean) holds at every thread, Said, J and fall: the
cell's test is noVals.

Limits. Nothing at the 12 attention links' reads or at the head's reads, whose cells do test values.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableOfSteps
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc.First (S)
open ProofFile.Honest (Thread Coins Mid ProverCoinCounts ValuesJ)

theorem vals_at_link (Z : ProofFile.Pub) (G : ProofFile.Ground) (l j : Nat) (hl : l < 24) (hj : j < 14) :
    Tab.vals Z G (14 * l + j + 1) = ((Tab.linkRow Z G l).at j).2 := by
  unfold Tab.vals Tab.cells
  rw [table_link _ _ _ _ l j hl hj]

theorem vals_at_head (Z : ProofFile.Pub) (G : ProofFile.Ground) (j : Nat) (hj : j < 16) :
    Tab.vals Z G (337 + j) = ((Tab.headRow Z G).at j).2 := by
  unfold Tab.vals Tab.cells
  rw [table_head _ _ _ _ j hj]

theorem opening_noVals (Z : ProofFile.Pub) (G : ProofFile.Ground) : (Tab.opening Z G).2 = noVals := by
  unfold Tab.opening
  split
  · split <;> rfl
  · rfl

theorem digits_noVals (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) : (Tab.digits Z G l).2 = noVals := by
  unfold Tab.digits
  split <;> rfl

theorem reads_noVals (Z : ProofFile.Pub) (G : ProofFile.Ground) {l : Nat} (he : l % 2 = 0) :
    (Tab.reads Z G l).2 = noVals := by
  unfold Tab.reads
  split
  · rw [if_pos (by simpa using he)]
    split <;> rfl
  · rfl

/-- **The cell's test at number 2.** -/
theorem vals_two (Z : ProofFile.Pub) (G : ProofFile.Ground) : Tab.vals Z G 2 = noVals := by
  have e := vals_at_link Z G 0 1 (by omega) (by omega)
  rw [show 14 * 0 + 1 + 1 = 2 from rfl] at e
  rw [e]
  exact opening_noVals Z G

/-- **The cell's test at the digits' commitment of every link.** -/
theorem vals_digits (Z : ProofFile.Pub) (G : ProofFile.Ground) {l : Nat} (hl : l < 25) :
    Tab.vals Z G (VerifiableInference.Desc.K1.noL l true) = noVals := by
  by_cases h : l = 24
  · subst h
    have e := vals_at_head Z G 7 (by omega)
    rw [show 337 + 7 = VerifiableInference.Desc.K1.noL 24 true from by decide] at e
    rw [e]
    exact digits_noVals Z G 24
  · have e := vals_at_link Z G l 6 (by omega) (by omega)
    rw [show 14 * l + 6 + 1 = VerifiableInference.Desc.K1.noL l true from by
      simp [VerifiableInference.Desc.K1.noL, IM.k1Ix, h]] at e
    rw [e]
    exact digits_noVals Z G l

/-- **The cell's test at the reads' commitment of an even link below the head.** -/
theorem vals_reads_even (Z : ProofFile.Pub) (G : ProofFile.Ground) {l : Nat} (hl : l < 24) (he : l % 2 = 0) :
    Tab.vals Z G (VerifiableInference.Desc.K1.noL l false) = noVals := by
  have e := vals_at_link Z G l 4 hl (by omega)
  rw [show 14 * l + 4 + 1 = VerifiableInference.Desc.K1.noL l false from by
    have : l ≠ 24 := by omega
    simp [VerifiableInference.Desc.K1.noL, IM.k1Ix, this]] at e
  rw [e]
  exact reads_noVals Z G he

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **Where the cell has no test on values the debt is free**: at every thread, Said, J and fall. -/
theorem valuesJ_of_noVals (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (J : Nat → S → Prop) (fall : Nat → S → List Fmt.Drawn → Option String) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) {b : Nat} (hv : Tab.vals Z G b = noVals) :
    ValuesJ T Said J (firstZA (Tab.g Z G) (Tab.vals Z G)) fall b := by
  intro blk _ k s m E ds y cols _ _ _ _ _ _
  show Tab.vals Z G b s _ _ = true
  rw [hv]
  rfl

/-- **(V1) THE 38 FREE MEMBERS OF K1.** -/
theorem k1_valuesJ_free (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (J : Nat → S → Prop) (fall : Nat → S → List Fmt.Drawn → Option String) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) {b : Nat}
    (hb : b = 2 ∨ (∃ l, l < 25 ∧ b = VerifiableInference.Desc.K1.noL l true) ∨
      (∃ l, l < 24 ∧ l % 2 = 0 ∧ b = VerifiableInference.Desc.K1.noL l false)) :
    ValuesJ T Said J (firstZA (Tab.g Z G) (Tab.vals Z G)) fall b := by
  refine valuesJ_of_noVals T Said J fall Z G ?_
  rcases hb with rfl | ⟨l, hl, rfl⟩ | ⟨l, hl, he, rfl⟩
  · exact vals_two Z G
  · exact vals_digits Z G hl
  · exact vals_reads_even Z G hl he

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.vals_at_link
#print axioms Johnson.AtFull.Shape.vals_at_head
#print axioms Johnson.AtFull.Shape.opening_noVals
#print axioms Johnson.AtFull.Shape.digits_noVals
#print axioms Johnson.AtFull.Shape.reads_noVals
#print axioms Johnson.AtFull.Shape.vals_two
#print axioms Johnson.AtFull.Shape.vals_digits
#print axioms Johnson.AtFull.Shape.vals_reads_even
#print axioms Johnson.AtFull.Shape.valuesJ_of_noVals
#print axioms Johnson.AtFull.Shape.k1_valuesJ_free
