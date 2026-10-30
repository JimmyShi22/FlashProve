-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/OpensB.lean: OpensAre (Johnson/Desc/Link/LinkShown.lean) AS A TEST WITH CODE, on
the plan alone.
  opensB ks ds n    ks: for each stage of the test its number of row variables. A stage's fold (1 +
  k rounds) opens nothing; its switch's two rounds open the tree number n alone; the next stage's
  the tree n + 1; the last
                    stage's rounds the last tree alone. False at no stage.
  opensAre_of_B     its yes at the chain's own stages' numbers gives OpensAre

-/
import Johnson.Desc.Link.LinkShown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

def opensB : List Nat → List Fmt.DeclaredRound → Nat → Bool
  | [], _, _ => false
  | [_], l, n => (ksOf l).all (· == n)
  | k :: k' :: ks, l, n =>
    (ksOf (l.take (1 + k))).isEmpty && (ksOf ((l.drop (1 + k)).take 2)).all (· == n) &&
      opensB (k' :: ks) (l.drop (k + 3)) (n + 1)

theorem stagesOf_cons {s : Sg} (c : Chain s) : ∃ l, stagesOf c = s.st :: l := by
  cases c with
  | last s e dL dB fu fs εb => exact ⟨[], rfl⟩
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next => exact ⟨stagesOf next, rfl⟩

theorem opensAre_of_B : ∀ {s : Sg} (c : Chain s) (l : List Fmt.DeclaredRound) (n : ℕ),
    opensB ((stagesOf c).map (·.k)) l n = true → OpensAre c l n := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro l n h
    have h' : (ksOf l).all (· == n) = true := h
    intro key hk
    have := List.all_eq_true.1 h' key hk
    simpa using this
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro l n h
    obtain ⟨t, ht⟩ := stagesOf_cons next
    have e1 : (stagesOf (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next)).map (·.k) =
        (s.h + s.g) :: s'.st.k :: t.map (·.k) := by
      show (s.st :: stagesOf next).map (·.k) = _
      rw [ht]
      rfl
    rw [e1] at h
    have h' : ((ksOf (l.take (1 + (s.h + s.g)))).isEmpty &&
        (ksOf ((l.drop (1 + (s.h + s.g))).take 2)).all (· == n) &&
        opensB (s'.st.k :: t.map (·.k)) (l.drop (s.h + s.g + 3)) (n + 1)) = true := h
    simp only [Bool.and_eq_true] at h'
    refine ⟨by
      simpa using h'.1.1, fun key hk => by simpa using List.all_eq_true.1 h'.1.2 key hk, ih _ _ ?_⟩
    rw [ht]
    exact h'.2

end Desc.K15

#print axioms Desc.K15.opensAre_of_B
