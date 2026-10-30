-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyRuns.lean: theorems about the two toy examples of
Honest/Law/ToyRow.lean and Honest/Law/ToyFall.lean: the field `runs` of `Owed` (Honest/Owed.lean),
letter for letter, at both: at every input of the examples' relation, at all coins and at every list
of challenges that the rounds can draw, outside the silent set, fall or not: `runC`
(Honest/Walk.lean) returns. By `runC_returns` (Honest/Law/RunsFile.lean), whose hypotheses are
proved here. The theorems are about these files' own made-up objects alone. None is one of the
library's goals.

  1  `serves_of_sk`   `PlanServes` from the three lists' skeletons (Honest/Law/ToySk.lean)
  2  `runs_row`   the first example: the invariants are those of Honest/Law/ToyTies.lean
  3  `Iv₁`, `Iv₂`, `Iv₃`, `threadV₁`, `threadV₂`, `threadV₃`, `runs_rowV`   the second example, with
     its invariants: at the two sub-protocols that can reject the lemma says: where the sub-protocol
     accepts, the condition holds after it

Limits.
  * A toy example.
  * Whether the description accepts is not said.
  * No part of the two examples reads what it is handed as `Seen`, so none reads the field `opened`:
    what the hypotheses here ask of that field is met for free. Of a prover with a part that reads
    the columns nothing is shown here.
  * The invariants leave the field free: no invariant that speaks of it is carried through a chain
    here (Honest/Law/RunsFile.lean, Limits).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyTies
import Johnson.Desc.ProofFile.Honest.Law.ToyReady
import Johnson.Desc.ProofFile.Honest.Law.ToyFallGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription OpenedColumn)
open VerifiableInference.Desc.BlockToy (St)

/-! ## 1 What the plan declares, from the skeletons -/

/-- `PlanServes`, where the three lists' skeletons pass the two tests of Honest/Law/ToySk.lean and
the stored table's columns are available, two words wide. -/
theorem serves_of_sk {H : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat} {w₀ : Wit₀} {rc : UInt64}
    {R : Ready Wit₀ UInt64 Nat UInt64 Trace Nat Nat}
    (f₁ : skFits (R.first.map sk) = true) (f₂ : skFits (R.shared.map sk) = true)
    (f₃ : skFits (R.second.map sk) = true) (t₁ : inTimeFrom [] (R.first.map sk) = true)
    (t₂ : inTimeFrom [] (R.shared.map sk) = true) (t₃ : inTimeFrom [] (R.second.map sk) = true)
    (hst : ∀ x, ∃ c, H.storedWords w₀ rc 0 x = some c ∧ c.length = 2) : PlanServes H w₀ rc R :=
  { first := ⟨sk_shaped f₁, sk_noRoot f₁, sk_part0 f₁, sk_inTime t₁, sk_stored f₁ hst⟩
    shared := ⟨sk_shaped f₂, sk_noRoot f₂, sk_part0 f₂, sk_inTime t₂, sk_stored f₂ hst⟩
    second := ⟨sk_shaped f₃, sk_noRoot f₃, sk_part0 f₃, sk_inTime t₃, sk_stored f₃ hst⟩
    own₁ := sk_own f₁
    own₂ := sk_own f₂
    taken := fun u hu o ho ch j e => absurd e (sk_own f₃ u hu o ho ch j) }

/-! ## 2 The first example -/

/-- **The field `runs` of `Owed` at the first toy example**, letter for letter. About this folder's
own made-up objects alone; none of the library's goals. -/
theorem runs_row : ∀ w₀ rc x, RelY w₀ rc x → ∀ (k : Coins By) ρ', ρ'.due Fy = true →
    silentAt Fy (Gy.prover Py) w₀ rc x ρ' = none →
    ∃ r, runC Fy By (Gy.prover Py) w₀ rc x k ρ' = .ok r := by
  intro w₀ rc x h k ρ' hρ hs
  obtain ⟨R, hR, h₁, h₂, h₃⟩ := ready_row w₀ rc x k h
  have hP : PlanServes (Gy.prover Py) w₀ rc R :=
    serves_of_sk (by rw [h₁]; exact fits_Ky.1) (by rw [h₂]; exact fits_Ky.2.1)
      (by rw [h₃]; exact fits_Ky.2.2) (by rw [h₁]; exact inTime_Ky.1)
      (by rw [h₂]; exact inTime_Ky.2.1) (by rw [h₃]; exact inTime_Ky.2.2)
      fun _ => ⟨_, rfl, rfl⟩
  exact runC_returns hR (by with_unfolding_all rfl) hρ hs hP Iy₁ Iy₂ Iy₃ thread₁ thread₂ thread₃
    (start₁y k _ _ _) (start₂y k _ _ w₀ rc)
    fun _ m₁ E₁ _ m₂ E₂ s₃ _ _ _ _ _ _ _ => door₃y k s₃ _ E₁ E₂

/-! ## 3 The second example -/

/-- The prover whose sides are the second example's. -/
def Hv : Prover Wit₀ UInt64 Nat UInt64 Trace Nat Nat := Gv.prover Pv

def Iv₁ : Nat → Coins Bv → St → Mid L Nat → Env → Prop := fun _ => anyAt
def Iv₂ : Nat → Coins Bv → St → Mid L₀ Nat → Env → Prop := fun _ => anyAt

/-- The second chain: before its front and before "own a": no tree yet; then `vAt` up to "spend";
then `vSent` up to "late"; `vLate` before "echo"; then nothing. -/
def Iv₃ : Nat → Coins Bv → St → Mid L Nat → Env → Prop
  | 0 => noTree
  | 1 => noTree
  | 2 => vAt
  | 3 => vAt
  | 4 => vSent
  | 5 => vSent
  | 6 => vSent
  | 7 => vSent
  | 8 => vSent
  | 9 => vLate
  | _ => anyAt

theorem threadV₁ : ∀ j b, Fv.first.blocksInOrder[j]? = some b →
    PlaysOn .own Bv 0 0 Hv.first b (Iv₁ j) (Iv₁ (j + 1)) := by
  intro j b hj
  match j, hj with
  | 0, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ _ _ => trivial
  | 1, hj =>
    obtain rfl := Option.some.inj hj
    refine plays_of_bare rfl fun k s m E ds y _ hd _ => ⟨[], ?_, fun _ _ _ => trivial⟩
    have hd' : drawsFit [{ entry := { name := "SEAL" } }] ds = true := hd
    obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
    rfl
  | n + 2, hj => cases hj

theorem threadV₂ : ∀ j b, Fv.shared.blocksInOrder[j]? = some b →
    PlaysOn .shared Bv 1 0 Hv.shared b (Iv₂ j) (Iv₂ (j + 1)) := by
  intro j b hj
  match j, hj with
  | 0, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ _ _ => trivial
  | 1, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ _ _ => trivial
  | n + 2, hj => cases hj

/-- Where "tests" accepts it leaves the state as it was. -/
theorem tests_keeps {s s' : St} (h : vbT.decide s [] [] = .ok s') : s' = s := by
  have h' : (if weightOk s = true then Except.ok s else Except.error "a weight is 0") =
      (Except.ok s' : Except String St) := h
  cases hw : weightOk s with
  | true =>
    rw [if_pos hw] at h'
    exact (Except.ok.inj h').symm
  | false =>
    rw [if_neg (by rw [hw]; exact Bool.false_ne_true)] at h'
    cases h'

theorem threadV₃ : ∀ j b, Fv.second.blocksInOrder[j]? = some b →
    PlaysOn .own Bv 2 Fv.lastChainFirstTreeNumber Hv.second b (Iv₃ j) (Iv₃ (j + 1)) := by
  intro j b hj
  match j, hj with
  | 0, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ hA _ => hA
  | 1, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_vA (pre := [])) rfl
  | 2, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_vB (pre := [])) rfl
  | 3, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_vS (pre := [])) rfl
  | 4, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_vD (pre := [])) rfl
  | 5, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_vM (pre := [])) rfl
  | 6, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_vW (pre := [])) rfl
  | 7, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ hA hd =>
      vSent_on hA rfl (congrArg St.total (tests_keeps hd)) rfl
  | 8, hj =>
    obtain rfl := Option.some.inj hj
    exact playsOn_mono (plays_of_good (good_vL (pre := [])) rfl) (fun _ _ _ _ _ => trivial)
      fun _ _ _ _ h => h
  | 9, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_good (good_vE (pre := [])) rfl
  | 10, hj =>
    obtain rfl := Option.some.inj hj
    exact plays_of_quiet rfl rfl fun _ _ _ _ _ _ _ => trivial
  | n + 11, hj => cases hj

/-- **The field `runs` of `Owed` at the second toy example**, letter for letter: at coins that fall
too. About this folder's own made-up objects alone; none of the library's goals. -/
theorem runs_rowV : ∀ w₀ rc x, RelY w₀ rc x → ∀ (k : Coins Bv) ρ', ρ'.due Fv = true →
    silentAt Fv (Gv.prover Pv) w₀ rc x ρ' = none →
    ∃ r, runC Fv Bv (Gv.prover Pv) w₀ rc x k ρ' = .ok r := by
  intro w₀ rc x h k ρ' hρ hs
  obtain ⟨R, hR, h₁, h₂, h₃⟩ := ready_rowV w₀ rc x k h
  have hR' : ready Fv Bv (Gv.prover Pv) w₀ rc x k = .ok R := hR
  have hP : PlanServes (Gv.prover Pv) w₀ rc R :=
    serves_of_sk (by rw [h₁]; exact fits_Kv.1) (by rw [h₂]; exact fits_Kv.2.1)
      (by rw [h₃]; exact fits_Kv.2.2) (by rw [h₁]; exact inTime_Kv.1)
      (by rw [h₂]; exact inTime_Kv.2.1) (by rw [h₃]; exact inTime_Kv.2.2)
      fun _ => ⟨_, rfl, rfl⟩
  exact runC_returns hR' (by with_unfolding_all rfl) hρ hs hP Iv₁ Iv₂ Iv₃ threadV₁ threadV₂
    threadV₃ trivial trivial fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.serves_of_sk
#print axioms ProofFile.Honest.Toy.runs_row
#print axioms ProofFile.Honest.Toy.threadV₁
#print axioms ProofFile.Honest.Toy.threadV₂
#print axioms ProofFile.Honest.Toy.tests_keeps
#print axioms ProofFile.Honest.Toy.threadV₃
#print axioms ProofFile.Honest.Toy.runs_rowV
#print axioms ProofFile.Honest.Toy.Hv
#print axioms ProofFile.Honest.Toy.Iv₁
#print axioms ProofFile.Honest.Toy.Iv₂
#print axioms ProofFile.Honest.Toy.Iv₃
