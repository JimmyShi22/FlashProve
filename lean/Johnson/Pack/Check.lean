-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/Check.lean: a test that runs for the conditions on numbers of Johnson/Pack/PortF.lean.

Definitions, statements, proofs and guards. `MeetsAt` (Johnson/Pack/PortF.lean) is a condition on
numbers, shape by shape. A hypothesis that asks it of a list of shapes is worth nothing if it is
false at the programs' numbers. This file has a Boolean test, a theorem that its value true gives
`MeetsAt`, and guards at four shapes.
Main names:
  `dOf`: the distance of a shape's code as read: the smaller of its two tables'; a table without a
    row does not count.
  `lOf`: the library's `listMax` at that distance.
  `pbase_dOf`, `meets_of`: from `CodeOK`, one answer, `CaseE` or `CaseF`, `PadFits` and `InJohnson`:
    `MeetsAt cs s e (dOf cs s) (lOf cs s e)`.
  `meetsB`, `meetsB_sound`: the test: these five, and that the distance is at most the number of
    positions (which `MeetsAt` does not ask: with natural subtraction `InJohnson` would else hold
    cheaply); its value true gives `MeetsAt`.
  `allMeet`, `allMeet_sound`: the same of a list.
Limits: a guard runs compiled code: it is evidence by evaluation, no proof. The four shapes, their
codes and their radii are typed here by hand, after a run of the planner (OnBytes/Params/) on the
example prover/examples/target_small_f2; that they are that example's is stated by nothing in this
file. Which radius goes with which message is not derived here: each shape is given the radius of
the group of rows that has the shape's main code, the upper end of the planner's distance, in
positions, rounded up; for the shape with a mask row alone no radius was taken from the run.
OnBytes/Params/JohnsonLaws.lean has the upper end rounded down (`Params.upperRadius`); the radii
typed here, rounded up, serve the guards of this file alone, and nothing says that they are the ones
that a chain's joints carry. At the code (18, 16384, 98) and the radius 196177 `lOf` is 415, which
is the list size that the run shows for that group. The test offers the arms below the Johnson
radius alone: a message that is not sampled does not pass.
-/
import Johnson.Pack.PortF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood OnBytes.Slice

section
variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape)

/-- The distance of a shape's code as read. -/
def dOf : ℕ :=
  if s.mainRows = 0 then distAt (cMask cs s) (aOf cs s)
  else if s.maskRows = 0 then distAt (cMain cs s) (aOf cs s)
  else min (distAt (cMain cs s) (aOf cs s)) (distAt (cMask cs s) (aOf cs s))

/-- The library's bound on the list. -/
def lOf (e : ℕ) : ℕ := listMax (2 ^ aOf cs s) (dOf cs s) e

theorem pbase_dOf (h : CodeOK cs s) : PBase cs s (dOf cs s) := by
  refine ⟨h, ?_, ?_⟩
  · by_cases h1 : s.mainRows = 0
    · exact Or.inl h1
    · right
      unfold dOf
      rw [if_neg h1]
      by_cases h2 : s.maskRows = 0
      · rw [if_pos h2]
      · rw [if_neg h2]
        exact min_le_left _ _
  · by_cases h2 : s.maskRows = 0
    · exact Or.inl h2
    · right
      unfold dOf
      by_cases h1 : s.mainRows = 0
      · rw [if_pos h1]
      · rw [if_neg h1, if_neg h2]
        exact min_le_right _ _

theorem meets_of (e : ℕ) (h1 : CodeOK cs s) (h2 : s.answers = 1) (h3 : CaseE s ∨ CaseF s)
    (h4 : PadFits cs s) (h5 : InJohnson (2 ^ aOf cs s) (dOf cs s) e) :
    MeetsAt cs s e (dOf cs s) (lOf cs s e) :=
  ⟨pbase_dOf cs s h1, Or.inr ⟨h2, h3, h4, by rw [Fintype.card_fin]; exact h5, by
    rw [Fintype.card_fin]
    rfl⟩⟩

instance : Decidable (CodeOK cs s) :=
  decidable_of_iff ((cMain cs s).a ≤ 32 ∧ (cMain cs s).r + (cMain cs s).l ≤ 2 ^ (cMain cs s).a ∧
      (cMask cs s).a ≤ 32 ∧ (cMask cs s).r + (cMask cs s).l ≤ 2 ^ (cMask cs s).a)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.a1, h.k1, h.a2, h.k2⟩⟩

instance : Decidable (CaseE s) := by unfold CaseE; infer_instance
instance : Decidable (CaseF s) := by unfold CaseF; infer_instance
instance : Decidable (PadFits cs s) := by unfold PadFits; infer_instance
instance (n d e : ℕ) : Decidable (InJohnson n d e) := by unfold InJohnson; infer_instance

/-- The test. -/
def meetsB (e : ℕ) : Bool :=
  decide (CodeOK cs s) && decide (s.answers = 1) && decide (CaseE s ∨ CaseF s) &&
    decide (PadFits cs s) && decide (InJohnson (2 ^ aOf cs s) (dOf cs s) e) &&
    decide (dOf cs s ≤ 2 ^ aOf cs s)

theorem meetsB_sound (e : ℕ) (h : meetsB cs s e = true) :
    MeetsAt cs s e (dOf cs s) (lOf cs s e) := by
  unfold meetsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact meets_of cs s e h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2

end

/-- The test, of a list. -/
def allMeet (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) : Bool :=
  l.all fun x => meetsB cs x.1 x.2

theorem allMeet_sound (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (h : allMeet cs l = true) (i : Fin l.length) :
    MeetsAt cs (l.get i).1 (l.get i).2 (dOf cs (l.get i).1) (lOf cs (l.get i).1 (l.get i).2) :=
  meetsB_sound cs _ _ (List.all_eq_true.1 h _ (List.get_mem l i))

/-! ### At four shapes of a small example -/

/-- Nine codes of main rows and one code of mask rows, as (logN, ell, r). -/
def csSmall : OnBytes.Codes where
  base := #[⟨17, 32768, 97⟩, ⟨14, 2048, 66⟩, ⟨18, 16384, 98⟩, ⟨14, 1024, 49⟩, ⟨15, 1024, 39⟩,
    ⟨22, 262144, 49⟩, ⟨19, 16384, 39⟩, ⟨17, 2048, 33⟩, ⟨20, 2048, 22⟩]
  mask := #[⟨13, 64, 146⟩]

/-- Code 2, one main row over the extension field, no mask row, one answer. -/
def shW : OnBytes.OracleShape :=
  { code := 2, mainRows := 1, mainDeg := 3, maskRows := 0, maskCode := OnBytes.noId, answers := 1 }
/-- Code 0, 18 main rows over the extension field. -/
def shU : OnBytes.OracleShape :=
  { code := 0, mainRows := 18, mainDeg := 3, maskRows := 0, maskCode := OnBytes.noId, answers := 1 }
/-- Code 2, 4 main rows over the extension field. -/
def shO : OnBytes.OracleShape :=
  { code := 2, mainRows := 4, mainDeg := 3, maskRows := 0, maskCode := OnBytes.noId, answers := 1 }
/-- One mask row under mask code 0, one answer. -/
def shOz : OnBytes.OracleShape :=
  { code := OnBytes.noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 1 }
/-- The same without an answer: a message that is not sampled. -/
def shRide : OnBytes.OracleShape :=
  { code := OnBytes.noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 0 }

#guard meetsB csSmall shW 196177
#guard meetsB csSmall shO 196177
#guard meetsB csSmall shU 65305
#guard lOf csSmall shW 196177 == 415
#guard dOf csSmall shW == 2 ^ 18 - (98 + 16384) + 1
-- Controls: beyond the Johnson radius; not sampled; no room for message and tail.
#guard !meetsB csSmall shW 196500
#guard !meetsB csSmall shRide 100
#guard !meetsB { base := #[⟨4, 16, 1⟩], mask := #[] }
  { code := 0, mainRows := 1, mainDeg := 3, answers := 1 } 1
-- The mask row alone, at the radius 1: this shows only that the clauses other than InJohnson hold.
#guard meetsB csSmall shOz 1

end Johnson.Pack

#print axioms Johnson.Pack.meets_of
#print axioms Johnson.Pack.meetsB_sound
#print axioms Johnson.Pack.allMeet_sound
