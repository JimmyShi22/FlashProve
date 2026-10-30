-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3BoolsAtCalls.lean: the lookup on a link's CALLS: THE PUBLIC TESTS THAT OUR
LAWS ASK, AS BOOLS OF THE PUBLIC RECORD X, THE CALLER's DATA D, THE LINK's NUMBER i AND THE CARRIED
RECORD s: for a walk over a real chain. Definitions with code, and what a yes gives. The calls'
share beside Johnson/Desc/First/Look/K3BoolsAt.lean (k3OnInAt, k3OnOutAt, k3LookInAt at
digits := false).

OBJECT: no text that runs in the verifier: tests for a run beside it.
USER: K3PlaceAtCopies.lean (attBAt, layBAt, attOK_of_attBAt, layOK_of_layBAt), K3PlanAtt.lean
  (attBAt).
LETTERS: X, D, i, s.

Main names:
  `attBAt X i`: at an attention link: AttOK's four tests on public data (there are four calls; the
    planes' columns fit; attFitsB; the masks lie inside the link's scalars), with planesInB (the
    planes' cells lie in the list's matrix). `attOK_of_attBAt`: a yes gives AttOK at attAt's value.
  `layBAt X i`: at a layers' link: layB (LayOK's one Bool) and the planes' columns.
    `layOK_of_layBAt`.
  `k3CallsFront X D i s`, `k3CallsBehind X i s`: the sort's own Bool with lookIn; lookOut.

Limits. False where the link is of the other sort, or the record has no such place. The head's link:
nothing. Nothing has run.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3BoolsAt
import Johnson.Desc.First.Look.K3AttInst
import Johnson.Desc.First.Look.K3AttGuards
import Johnson.Desc.First.Look.K3CallerLayTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The tests at an attention link. -/
def attBAt (X : Verify.Public) (i : Nat) : Bool :=
  (attAt X i).any fun xt =>
    xt.1.fs.NC == 4 && (Forest.planeCols xt.1.fs xt.1.lm).toBool && attFitsB xt.2.1 xt.1.fs &&
      decide (xt.1.F.next + FoNums.nMasks xt.1.fs ≤ xt.1.ns) && planesInB xt.1 xt.2.1 xt.2.2

theorem attOK_of_attBAt {X : Verify.Public} {i : ℕ} (D : Sent) (rad : OracleShape → Nat)
    (h : attBAt X i = true) :
    ∃ x A tl, attAt X i = some (x, A, tl) ∧ AttOK (Params.settingOf X.P.frame) x A tl D rad ∧
      planesInB x A tl = true := by
  unfold attBAt at h
  cases hx : attAt X i with
  | none =>
    rw [hx] at h
    simp at h
  | some xt =>
    obtain ⟨x, A, tl⟩ := xt
    rw [hx] at h
    have h2 : (x.fs.NC == 4 && (Forest.planeCols x.fs x.lm).toBool && attFitsB A x.fs &&
        decide (x.F.next + FoNums.nMasks x.fs ≤ x.ns) && planesInB x A tl) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    exact ⟨x, A, tl, rfl, attOK_at D rad hx h2.1.1.1.1 h2.1.1.1.2 h2.1.1.2 h2.1.2, h2.2⟩

/-- The tests at a layers' link. -/
def layBAt (X : Verify.Public) (i : Nat) : Bool :=
  (layAt X i).any fun x => layB x.fs && (Forest.planeCols x.fs x.lm).toBool

theorem layOK_of_layBAt {X : Verify.Public} {i : ℕ} (h : layBAt X i = true) :
    ∃ x, layAt X i = some x ∧ LayOK (Params.settingOf X.P.frame) x ∧
      (Forest.planeCols x.fs x.lm).toBool = true := by
  unfold layBAt at h
  cases hx : layAt X i with
  | none =>
    rw [hx] at h
    simp at h
  | some x =>
    rw [hx] at h
    have h2 : (layB x.fs && (Forest.planeCols x.fs x.lm).toBool) = true := h
    simp only [Bool.and_eq_true] at h2
    exact ⟨x, rfl, layOK_at hx h2.1, h2.2⟩

/-- In front of the calls' lookup: the link's own sort's test, and the public item lookIn. -/
def k3CallsFront (X : Verify.Public) (D : Sent) (i : Nat) (s : First.S) : Bool :=
  (attBAt X i || layBAt X i) && k3LookInAt X D i false s

/-- Behind it. -/
def k3CallsBehind (X : Verify.Public) (i : Nat) (s : First.S) : Bool := k3OnOutAt X i false s

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.attOK_of_attBAt
#print axioms VerifiableInference.Desc.First.Look.layOK_of_layBAt
