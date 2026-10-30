-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CountsCovered.lean: typed rounds that are covered one by one by planned rounds have the
clause on counts of OnBytes/Flat/CountsHeld.lean, where every written round of the stretch is read.

`Held.CountsL` (OnBytes/Flat/CountsHeld.lean) asks of each written round that is read as a typed
round: the typed count is at most the plan's error for the round times the number of values of the
written round's draws. `Covered` (OnBytes/Tie/Pv/PortKit.lean) says of a typed round: its count, as
a share of its own number of values, is at most the plan's error. One definition, one statement with
its proof. No protocol occurs here.
Main names, in the namespace `OnBytes.Flat.Held`:
  `ValsLe ds s'`: round by round, the typed round has a value, and at most as many values as the
    written round's draws have; the two lists run out together.
  `countsL_all`: `Covered` pair by pair and `ValsLe` give `CountsL` at the marks that are all true.
Limits: `ValsLe` is a premise. A stretch with a skipped round is not treated. Nothing says that a
count bounds a prover's chance.
-/
import OnBytes.Flat.CountsHeld
import OnBytes.Tie.Pv.PortKit
import Ior.KnowCollRulesChainErr

set_option autoImplicit false

namespace OnBytes.Flat.Held
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Params OnBytes.Slice OnBytes.Flat Cb.Pv

/-- The typed rounds have values, at most as many as the written rounds' draws. -/
def ValsLe : List RD → Shape → Prop
  | [], [] => True
  | d :: ds, r' :: s' => 0 < Fintype.card r'.Chal ∧
      Fintype.card r'.Chal ≤ nVals (Fmt.dsOf d.entry d.kind) ∧ ValsLe ds s'
  | _, _ => False

/-- Covered rounds have the clause on counts. -/
theorem countsL_all (σ : Setting) (c : Scope) :
    ∀ (ds : List RD) (s' : Shape) (ε : Err s') (ys : List RoundSpec),
      List.Forall₂ (Covered σ c) (ε.toList.zip s'.chalList) ys → ValsLe ds s' →
      CountsL ds (ys.map (·.round σ c)) (ds.map fun _ => true) s' ε
  | [], [], _, _, h, _ => by
      have h' : List.Forall₂ (Covered σ c) [] _ := h
      cases h'
      trivial
  | [], _ :: _, _, _, _, hv => hv.elim
  | _ :: _, [], _, _, _, hv => hv.elim
  | d :: ds, r' :: s', (e, ε), _, h, hv => by
      have h' : List.Forall₂ (Covered σ c)
          ((e, Fintype.card r'.Chal) :: ε.toList.zip (Shape.chalList s')) _ := h
      cases h' with
      | cons h1 ht =>
        rename_i y ys
        refine ⟨?_, countsL_all σ c ds s' ε ys ht hv.2.2⟩
        have hn : (0 : ℚ) < (Fintype.card r'.Chal : ℚ) := by exact_mod_cast hv.1
        have hq : (e : ℚ) / (Fintype.card r'.Chal : ℚ) ≤ (y.round σ c).error.val := by
          have h2 : ((e : ℝ) / (Fintype.card r'.Chal : ℝ)) ≤
              (((y.round σ c).error.val : ℚ) : ℝ) := h1
          exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact h2)
        have he : 0 ≤ (y.round σ c).error.val := le_trans (by positivity) hq
        calc (e : ℚ) ≤ (y.round σ c).error.val * (Fintype.card r'.Chal : ℚ) :=
              (div_le_iff₀ hn).1 hq
          _ ≤ (y.round σ c).error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hv.2.1) he

end OnBytes.Flat.Held

#print axioms OnBytes.Flat.Held.countsL_all
