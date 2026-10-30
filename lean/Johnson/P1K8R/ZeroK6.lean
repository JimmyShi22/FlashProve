-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroK6.lean: THE HEAD's OWN ROUNDS (K6): THE DECISION STEPS IN `KeepsZero`. MADE BY
PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksK6.lean, WITH THE ROWS' FIRST COLUMNS
(`l0s`, Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN THE PLACE
OF KeepsLooks: every declaration of that file that names the looks, or leans on one that does, under
a new name; the others are called where they lie. None of the library's goals. No prover stands in
it; nothing on completeness, soundness or hiding.

  **`k6_kz`**, `k6_kz_of`, `k6_kz_seated`   there: the same names with "steps"
Limits. THE DECISION ALONE: nothing on K6's runs of claims (Johnson/P1K8R/ZeroRuns.lean has these).
Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroShims
import Johnson.Desc.First.Link.Law.LooksK6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- **K6: the output head's own rounds.** -/
theorem k6_kz (h : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) :
    (blockAt h iU3 work l).Steps KeepsZero := by
  intro s rs gs s' hd
  obtain ⟨F0, F', L, a1, a2, a3, a4⟩ := k6_reads h iU3 work l s s' rs gs hd
  have ht : (s'.fork?.getD {}).trees = (s.fork?.getD {}).trees :=
    blockAt_trees h iU3 work l s s' rs gs hd
  rw [a1, a3] at ht
  refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨F0, L, a1, a2, ?_, ?_⟩
  · rw [Option.some.inj (a4.symm.trans hL')]
  · rw [← Option.some.inj (a3.symm.trans hG)]
    exact congrArg (·.map l0s) ht

/-- So of `blockOf`'s value. -/
theorem k6_kz_of (W : OnBytes.Model.Verify.Public) (l : ℕ)
    (b : Block S Unit) (hb : Kinds.Head.blockOf W l = some b) : b.Steps KeepsZero := by
  unfold Kinds.Head.blockOf at hb
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact k6_kz _ _ _ _

/-- **So of the sub-protocol as a lot seats it.** -/
theorem k6_kz_seated {W : OnBytes.Model.Verify.Public} {l : ℕ}
    {ms : List (ℕ × ℕ)} {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    b.Steps KeepsZero := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  intro s rs gs s' hd
  exact k6_kz W.hS i _ l s rs gs s' ((tested_decide _ _ _ _ _ _ _ _).1 hd).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k6_kz
#print axioms VerifiableInference.Desc.LinkJoin.k6_kz_of
#print axioms VerifiableInference.Desc.LinkJoin.k6_kz_seated
