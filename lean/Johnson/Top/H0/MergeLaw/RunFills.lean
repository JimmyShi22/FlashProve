-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunFills.lean: what the merge's run of claims lays under the slots that it
fills; and a world that fits the entries, written down. Theorems with their proofs.

Main names:
  `run_fills`: where `headMergeClaim` says yes at a ledger whose three arrays have one entry for
  each
    slot: every slot that is filled behind the run and was free in front of it holds the shown value
    0 and the factor -1. With `run_later` (Keeps.lean): what was filled stays as it was.
  `fitWorld`, `fitWorld_fits`: where each claim's slot lies below the first of the sumcheck's own
    slots, the world that gives every slot from that first on its mask entry, and every slot below
    it
    "shown - factor * mask entry" by the typed statement's ledger, has `Fits2`
    (Johnson/Top/H0/K11Caller/AtSlots.lean). So, with `rowForm_same` (OneWorld.lean), "the form is
    worth 0 in some world that fits" and "in every world that fits" are one statement there.

Limits. That a plan's numbers have each claim's slot below the first own slot is not shown.
Identities on ledgers: no random step. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.OneWorld
import Johnson.Top.H0.MergeLaw.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E zeroE oneE subE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading World)
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc (Claim)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open K11Caller (MergeIn Fits2 maskOf)

/-- **What the run lays**: under each slot that it fills: the shown value 0 and the factor -1. -/
theorem run_fills {n : ℕ} {s s' : S} {cls : List Claim} (h : headMergeClaim n s = .ok (cls, s')) :
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧
      (OnBytes.PscRun.Sized a.F → ∀ j, Filled a'.F j → ¬ Filled a.F j →
        a'.F.vp.getD j zeroE = zeroE ∧ a'.F.mf.getD j zeroE = subE zeroE oneE) := by
  obtain ⟨a, wo, G, h1, _, h2, _, h4⟩ := claim_inv h
  refine ⟨a, { a with F := G }, h1, by rw [h2], ?_⟩
  intro hz j hj hn
  obtain ⟨_, _, r3, r4⟩ := OnBytes.PscRun.hideRun_ok a.F G _ _ _ hz h4
  by_cases hin : wo.p.first ≤ j ∧ j < wo.p.first + (Array.replicate wo.p.walk.1.length zeroE).size
  · obtain ⟨_, _, _, q4, q5⟩ := r3 (j - wo.p.first) (by omega)
    have ej : wo.p.first + (j - wo.p.first) = j := by omega
    rw [ej] at q4 q5
    have e0 : (Array.replicate wo.p.walk.1.length zeroE).getD (j - wo.p.first) zeroE = zeroE := by
      by_cases hi : j - wo.p.first < wo.p.walk.1.length <;> simp [Array.getD, hi]
    exact ⟨by show G.vp.getD j zeroE = zeroE; rw [q4, e0], q5⟩
  · exact absurd ((r4 j (by omega)).2.2.1 hj) hn

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- A world that fits the entries, written down. -/
noncomputable def fitWorld (st : MergeIn Pl.n) (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) :
    World GE where
  slot := fun j => if N.first ≤ j then maskOf N m j
    else Reading.gl.val (st.F.vp.getD j zeroE) - Reading.gl.val (st.F.mf.getD j zeroE) * maskOf N m
        j
  entry := fun _ _ _ => 0

theorem fitWorld_fits (st : MergeIn Pl.n) (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE)
    (hlow : ∀ a, N.sv a < N.first) : Fits2 Reading.gl N st m (fitWorld N st m) where
  w1 := fun j h1 _ => by
    show (if N.first ≤ j then _ else _) = _
    rw [if_pos h1]
  w2 := fun a => by
    show (if N.first ≤ N.sv a then _ else _) = _
    rw [if_neg (by have := hlow a; omega)]

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.run_fills
#print axioms VerifiableInference.Desc.First.MergeLaw.fitWorld_fits
