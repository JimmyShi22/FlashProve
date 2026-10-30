-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3KeySizes.lean: the kind "lookup" (K3): WHAT WAS HEARD HAS A KEY POINT OF THE RIGHT
SIZE FOR EACH CALL: call k's point has as many coordinates as the shape's call k says that its keys
have bits. Theorems with their proofs.

Main names:
  `Fo.Tp.lkPad_zk_size`: of the library's flat function lkPad (OnBytes/K/Kc/FlatHear.lean), which
    tests it: after the library's pad_zk_size (OnBytes/Tie/Pv/Lookup/Ends/FoTailSizes.lean), which
    speaks of the routine in a context; over the carried cut (Johnson/Top/H/FlPort/FoPadCut.lean).
  `decide_lkPad`: where K3.block's decide says yes, lkPad returns what decide lays, on a tape that
    it uses up.
  `decide_zk_size`: so what decide leaves as heard has these sizes.

It pays the premise of eq_four_law on the points' sizes, with EqPublic.sizes
(Johnson/Top/H/EqPort/EqPublic.lean).

Limits. A tie: no error term. Nothing where decide refuses.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3DecideHearsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes OnBytes.Model OnBytes.K.Kc

theorem lkPad_zk_size (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) :
    ∀ k, k < g.shape.NC →
      (g.zk.getD k #[]).size = ((g.shape.calls[k]?).map (·.n)).getD 0 := by
  obtain ⟨M, hc⟩ := pad_cut calls pub lid F F' t u g h
  intro k hk
  have e : g.shape = M.h pub := by rw [hc.heard]; rfl
  rw [e] at hk ⊢
  have h1 := List.all_eq_true.1 hc.point k (List.mem_range.2 hk)
  rw [hc.heard]
  exact beq_iff_eq.1 h1

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Tape

/-- **decide's yes is lkPad's yes**, on a tape that it uses up. -/
theorem decide_lkPad {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hdec : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F F' : Fork) (g : Forest.Heard) (t : Tape), seat.fork s = some F ∧ seat.heard s = none ∧
      lkPad p.calls p.pub p.lid F t = some (g, F', []) ∧ s' = seat.put s g F' := by
  obtain ⟨F, x, hF, hn, hx, e⟩ := decide_ok seat piece laid before p guests s s' rs cols hdec
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, _, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      exact ⟨F, x.2, x.1, t, hF, hn,
        messagesCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm, e⟩
    · exact absurd hx (by simp)

/-- **What decide leaves as heard has a key point of the right size for each call.** -/
theorem decide_zk_size {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hr : Desc.K3.SeatReads seat) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hdec : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ g, seat.heard s' = some g ∧ ∀ k, k < g.shape.NC →
      (g.zk.getD k #[]).size = ((g.shape.calls[k]?).map (·.n)).getD 0 := by
  obtain ⟨F, F', g, t, hF, hn, hl, rfl⟩ :=
    decide_lkPad seat piece laid before p guests s s' rs cols hdec
  have hsome : (seat.fork s).isSome = true := by rw [hF]; rfl
  exact ⟨g, hr _ _ _ hsome hn, Fo.Tp.lkPad_zk_size _ _ _ _ _ _ _ _ hl⟩

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.lkPad_zk_size
#print axioms VerifiableInference.OnPublicFiles.decide_lkPad
#print axioms VerifiableInference.OnPublicFiles.decide_zk_size
