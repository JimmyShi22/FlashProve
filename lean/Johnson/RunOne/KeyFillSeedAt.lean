-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSeedAt.lean: A FILE OF EVALUATIONS TO Johnson/RunOne/KeyFillSeed.lean: THE SENDING KIND's Tie AT THE SIX; THE SET I OF Johnson/RunOne/KeyFillBase.lean's promise_h_j AGAINST THE PINS THAT ARE OPEN AT THE TABLES' BORDERS.
  readE_one           the two readE (KeyFillBaseAt.lean's own; the one in SeedIs) are one: rfl
  tieB · tie_of_B · tie_six · tie_plant   the sending kind's Tie (Johnson/Desc/K1/Law/Port2.lean: one answer · every code's length a power of two · the shape fits the codes · the pad fits) at the library's csKey and the six real shapes: BY THE KERNEL · a plant (two answers): no
  uniq_six            so (uniq) of the sample's tie holds at all six, with no premise left
  open₁_le | open₂_in | open₃_in   THE TABLES' OWN LISTS, EVALUATED AT EVERY BORDER: the first chain (two lookups) has only pins below 3 open; the shared chain only of 0 · 2 · 3 · 4 · 5; the last only of 0 · 2 · 4
  open₁_num | open₂_num | open₃_num   at every open pin the chain's source has A NUMBER to read at (the first chain's plan below 3; the shared chain's plan at 3 | 4 | 5; at 4 both arms of the last chain's match)
  src₃_none           THE TWIN OF all_six_empty₁: behind the border (no copy of the shared statement) the last chain's source gives 3 and 5 nothing
A NUMBER IS NOT A RECORD: that the statement HOLDS a message there, at the member's shape, marked, with the kind's row, is the promise's and the sending's law's: not said.
OBJECT: the tables' open₁ | open₂ | open₃ · plan₁ | orc₂; the sending kind's Tie · USER: none: a file of evaluations · LETTERS: one (the one-time plan).
Nothing on soundness.
-/
import Johnson.RunOne.KeyFillSeed
import Johnson.RunOne.KeyFillBaseAt
import Johnson.RunOne.KeyRows1At
import Johnson.RunOne.KeyRows23At

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (Tie)
open Cb Johnson.Pack

/-- KeyFillBaseAt.lean's own readE is the one that SeedIs (and so rowIsK) bears. -/
theorem readE_one : (readE : OnBytes.E → OnBytes.Slice.GE) = OnBytes.Slice.readE := rfl

/-! ## The sending kind's Tie at the six -/

def tieB (cs : OnBytes.Codes) (s : OnBytes.OracleShape) : Bool :=
  decide (s.answers = 1) && cs.lengthsOk && OnBytes.Blk.shapeOk cs s && (VerifiableInference.Desc.K1.Msg.of cs s).padFits

theorem tie_of_B (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (h : tieB cs s = true) : Tie cs s := by
  unfold tieB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem tieB_six : (six.all fun p => tieB Johnson.Top.H.csKey p.1) = true := by decide +kernel

theorem tie_six : ∀ i : Fin six.length, Tie Johnson.Top.H.csKey (six.get i).1 := fun i =>
  tie_of_B _ _ (List.all_eq_true.1 tieB_six _ (List.get_mem six i))

/-- A PLANT. -/
theorem tie_plant : ¬ Tie Johnson.Top.H.csKey { Johnson.Top.H.shIdx with answers := 2 } := fun h => absurd h.one (by decide)

/-- **(uniq) OF THE SAMPLE's TIE AT ALL SIX: NO PREMISE LEFT.** -/
theorem uniq_six (i : Fin six.length) : ∀ o x ρ v ρ' v', rowIsK Johnson.Top.H.csKey six i o x ρ v → rowIsK Johnson.Top.H.csKey six i o x ρ' v' →
    (OmAt Johnson.Top.H.csKey six i).Z.val ρ = (OmAt Johnson.Top.H.csKey six i).Z.val ρ' ∧ v = v' := uniqK Johnson.Top.H.csKey six i (tie_six i)

/-! ## The open pins -/

theorem of_sets (rows : List KRow) (start : List KItem) (P : ℕ → Prop) (H : ∀ O ∈ openSets rows start, ∀ q ∈ pinned O, P q) (k : ℕ) :
    ∀ q ∈ pinned (((openSets rows start)[k]?).getD []), P q := by
  intro q hq
  cases h : (openSets rows start)[k]? with
  | none =>
    rw [h] at hq
    exact absurd hq List.not_mem_nil
  | some O =>
    rw [h] at hq
    exact H O (List.mem_of_getElem? h) q hq

theorem open₁_le (k : ℕ) : ∀ q ∈ pinned (KeyRows1.open₁ 2 k), q < 3 :=
  of_sets (rows₁ 2) (start₁ 2) (· < 3) (by decide +kernel) k

theorem open₂_in (k : ℕ) : ∀ q ∈ pinned (open₂ k), q ∈ [0, 2, 3, 4, 5] :=
  of_sets rows₂ seam (· ∈ [0, 2, 3, 4, 5]) (by decide +kernel) k

theorem open₃_in (k : ℕ) : ∀ q ∈ pinned (open₃ k), q ∈ [0, 2, 4] :=
  of_sets rows₃ end₂ (· ∈ [0, 2, 4]) (by decide +kernel) k

theorem plan₁_orc_some (one : OnBytes.Params.OneTime) (q : ℕ) (hq : q < 3) : ((KeyRows1.plan₁ one).orc q).isSome = true := by
  interval_cases q <;> rfl

theorem open₁_num (one : OnBytes.Params.OneTime) (k : ℕ) : ∀ q ∈ pinned (KeyRows1.open₁ 2 k), ((KeyRows1.plan₁ one).orc q).isSome = true :=
  fun q hq => plan₁_orc_some one q (open₁_le k q hq)

theorem open₂_num (one : OnBytes.Params.OneTime) (k : ℕ) : ∀ q ∈ pinned (open₂ k), (if q < 3 then (KeyRows1.plan₁ one).orc q else orc₂ q).isSome = true := by
  intro q hq
  have h := open₂_in k q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- At 0 and 2 the first chain's plan; at 4 the shared chain's plan (in front of the border's end) and the own count (behind it). -/
theorem open₃_num (one : OnBytes.Params.OneTime) (k : ℕ) : ∀ q ∈ pinned (open₃ k), (q < 3 ∧ ((KeyRows1.plan₁ one).orc q).isSome = true) ∨ (q = 4 ∧ (orc₂ q).isSome = true) := by
  intro q hq
  have h := open₃_in k q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact Or.inl ⟨by decide, rfl⟩
  · exact Or.inl ⟨by decide, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **Behind the border the last chain's source gives 3 and 5 nothing.** -/
theorem src₃_none (orc₁ : ℕ → Option ℕ) (a : P₃ × St₃) (hb : a.2.loc.border = none) (k : ℕ) (h3 : 3 ≤ k) (h4 : k ≠ 4) : src₃ orc₁ a k = none := by
  unfold src₃
  rw [if_neg (Nat.not_lt.2 h3), hb]
  show (if (k == 4) = true then _ else none) = none
  rw [if_neg (by simpa using h4)]

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.readE_one
#print axioms Johnson.RunOne.KeyRows23.tieB_six
#print axioms Johnson.RunOne.KeyRows23.tie_six
#print axioms Johnson.RunOne.KeyRows23.tie_plant
#print axioms Johnson.RunOne.KeyRows23.uniq_six
#print axioms Johnson.RunOne.KeyRows23.open₁_le
#print axioms Johnson.RunOne.KeyRows23.open₂_in
#print axioms Johnson.RunOne.KeyRows23.open₃_in
#print axioms Johnson.RunOne.KeyRows23.open₁_num
#print axioms Johnson.RunOne.KeyRows23.open₂_num
#print axioms Johnson.RunOne.KeyRows23.open₃_num
#print axioms Johnson.RunOne.KeyRows23.src₃_none
