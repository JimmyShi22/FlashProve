-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.TieOkMade
import Johnson.Desc.K12.Law.BatOneOk
/-
Johnson/Desc/K12/Law/BatOneMade.lean: batOneOk and batFreeOk are theorems: two tests on the plan of a proximity test (the kind K12), BatOneOk.lean, say yes wherever the written rounds are there; so wherever the block's own test on the plan does. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  written_bat_eq: wherever the written rounds are there, the first is "BAT" as the maker lays it: the entry of Fmt.M1.rBat with the place's number of rows, the kind «elems», no tree.
  batOneOk_made | batFreeOk_made: from writtenOf p.nums = some (w0 :: w) alone. batOneOk_of_planOk | batFreeOk_of_planOk: from (proximityTestKind X p).planOk = true, whatever the parts X.
WHAT IT MEANS: no plan whose written rounds are there can fail these two: they hold the maker's text against the format's list of draws: "BAT" draws one element and nothing else; logN = 0; no bits of work.
WHAT IT PAYS: the premise hb1 : batOneOk π = true of batAtY_pay_at (BatValsPayAt.lean) and of the laws over it; with Like dB w0: Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] and dB.entry.logN ≤ 64 (k12_lawPaid's h1 | hlog).

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf layW)
open H2K.First (batOneOk batOneOn batFreeOk batFreeOn)

/-- The first written round is "BAT" as the maker lays it. -/
theorem written_bat_eq (N : H2U.TestNums) (w0 : WR) (w : List WR)
    (hw : writtenOf N = some (w0 :: w)) :
    w0 = wr ⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ .elems none := by
  unfold writtenOf at hw
  cases hr : H2U.roundsOfNums N with
  | none =>
    rw [hr] at hw
    cases hw
  | some rds =>
    obtain ⟨_, _, _, R, _, _, rfl⟩ := rounds_top N rds hr
    rw [hr, Option.bind_some, told_shapes, layW_quiet _ _ _ .elems kBat rfl] at hw
    obtain ⟨w1, _, e⟩ := Option.map_eq_some_iff.1 hw
    exact (List.cons.inj e).1.symm

theorem batFreeOn_bat (rows : Nat) :
    batFreeOn (wr ⟨{ Fmt.M1.rBat.entry with rows := rows }, [], []⟩ .elems none) = true := rfl

theorem batFreeOk_made (p : P12) (w0 : WR) (w : List WR)
    (hw : writtenOf p.nums = some (w0 :: w)) : batFreeOk p = true := by
  unfold batFreeOk
  rw [hw, Option.any_some, List.head?_cons, Option.any_some, written_bat_eq _ w0 w hw]
  exact batFreeOn_bat _

theorem batOneOk_made (p : P12) (w0 : WR) (w : List WR)
    (hw : writtenOf p.nums = some (w0 :: w)) : batOneOk p = true := by
  unfold batOneOk
  rw [hw, Option.any_some, List.head?_cons, Option.any_some, written_bat_eq _ w0 w hw]
  have h := batFreeOn_bat p.nums.rows
  unfold batFreeOn at h
  exact (Bool.and_eq_true _ _ ▸ h).1

/-- The written rounds are there wherever the block's test on the plan says yes. -/
theorem written_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : ∃ w0 w, writtenOf p.nums = some (w0 :: w) := by
  obtain ⟨rds, hr, hl⟩ := rounds_of_planOk X p hp
  obtain ⟨_, _, w0, w, _, hw, _⟩ := written_made p rds hr hl
    fun s hs => (sizes_of_planOk X p hp s hs).2
  exact ⟨w0, w, hw⟩

theorem batOneOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : batOneOk p = true := by
  obtain ⟨w0, w, hw⟩ := written_of_planOk X p hp
  exact batOneOk_made p w0 w hw

theorem batFreeOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : batFreeOk p = true := by
  obtain ⟨w0, w, hw⟩ := written_of_planOk X p hp
  exact batFreeOk_made p w0 w hw

end H2K.Made

#print axioms H2K.Made.written_of_planOk
#print axioms H2K.Made.batOneOk_of_planOk
#print axioms H2K.Made.batFreeOk_of_planOk
