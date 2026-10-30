-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroK5.lean: AN ATTENTION SEGMENT's OWN ROUNDS (K5): THE DECISION STEPS IN
`KeepsZero`. MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksK5.lean, WITH THE
ROWS' FIRST COLUMNS (`l0s`, Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND
`KeepsZero` IN THE PLACE OF KeepsLooks: every declaration of that file that names the looks, or
leans on one that does, under a new name; the others are called where they lie. None of the
library's goals. No prover stands in it; nothing on completeness, soundness or hiding.

  **`k5_kz`**, `k5_kz_at`   there: k5_steps, k5_steps_at; the ground is the library's
      K5L.hear_arrays: the hearing leaves the arrays
Limits. THE DECISION ALONE: nothing on K5's runs of claims (Johnson/P1K8R/ZeroRuns.lean has these).
Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroShims
import Johnson.Desc.First.Link.Law.LooksK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.K5L
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (hideRun_core)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

variable {α β : Type}

end VerifiableInference.Desc.LinkJoin.K5L

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (attentionKind seatSO k5AtN)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- **K5: an attention segment's own rounds.** -/
theorem k5_kz {Cl : Type}
    (claims : List (String × (ℕ → S → Except String (List Cl × S)))) (p : First.Att.P.Par) :
    (attentionKind seatSO claims p).Steps KeepsZero := by
  intro s rs gs s' h
  have h' : First.Att.P.decide seatSO p s rs = .ok s' := h
  unfold First.Att.P.decide at h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨F, hF, h'⟩ := K9L.ok_bind h'
  obtain ⟨x, hx, h'⟩ := K9L.ok_bind h'
  obtain ⟨hd, G, rest, m⟩ := x
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  have hear1 : First.Att.P.hear p.own (F, rs, 0) = some (hd, G, rest, m) := by
    cases e : First.Att.P.hear p.own (F, rs, 0) with
    | none =>
      rw [e] at hx
      exact nomatch hx
    | some y =>
      rw [e] at hx
      exact congrArg some (Except.ok.inj hx)
  have lay1 : seatSO.lay s hd G = some s' := by
    cases e : seatSO.lay s hd G with
    | none =>
      rw [e] at h'
      exact nomatch h'
    | some y =>
      rw [e] at h'
      exact congrArg some (Except.ok.inj h')
  have led1 : seatSO.ledger s = some F := by
    cases e : seatSO.ledger s with
    | none =>
      rw [e] at hF
      exact nomatch hF
    | some y =>
      rw [e] at hF
      exact congrArg some (Except.ok.inj hF)
  unfold seatSO at lay1 led1
  dsimp only at lay1 led1
  cases hh : s.here with
  | att a =>
    rw [hh] at lay1 led1
    obtain rfl : a.F = F := Option.some.inj led1
    obtain ⟨_, _, lay2⟩ := Option.bind_eq_some_iff.1 lay1
    have lay3 : S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } hd = .ok s' :=
        by
      cases e : S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } hd with
      | error w =>
        rw [e] at lay2
        exact nomatch lay2
      | ok y =>
        rw [e] at lay2
        exact congrArg Except.ok (Option.some.inj lay2)
    obtain ⟨r1, r2⟩ := hear5_reads lay3
    refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, hh]
    · simp [S.link?, hh]
    · rw [r2] at hL'
      exact congrArg (·.link) (Option.some.inj hL')
    · rw [r1] at hG
      rw [← Option.some.inj hG]
      exact congrArg (·.map l0s) (K5L.hear_arrays hear1)
  | lay a =>
    rw [hh] at led1
    exact nomatch led1
  | head a =>
    rw [hh] at led1
    exact nomatch led1
  | between =>
    rw [hh] at led1
    exact nomatch led1
  | fin a =>
    rw [hh] at led1
    exact nomatch led1
  | mem a =>
    rw [hh] at led1
    exact nomatch led1

/-- So of `k5AtN`'s value. -/
theorem k5_kz_at {W : Verify.Public} {l g : ℕ}
    {before : List (ℕ × ℕ)} {b : Block S Claim} (h : k5AtN W l g before = some b) :
    b.Steps KeepsZero := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' hd
  exact k5_kz (Cl := Claim) (First.Att.P.runsN p) _ s rs gs s' hd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k5_kz
#print axioms VerifiableInference.Desc.LinkJoin.k5_kz_at
