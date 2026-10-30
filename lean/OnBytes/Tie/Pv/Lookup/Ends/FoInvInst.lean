-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvInst.lean.
Two properties of a sub-proof's state that every step keeps.

`primLater F0`: to be a later state than F0, with the slots' arrays at their sizes.
`primLS`: the slots' arrays have their sizes, and the one equation has a coefficient for each slot
(LS.size = ns).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvSteps
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsTrees

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem Book.slots5 {F G : Fork} (h : Book F G) : Slots5 F G :=
  ⟨h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem later_step {F0 F G : Fork} (h : Slots5 F G) (hI : Later F0 F ∧ Sized F) :
    Later F0 G ∧ Sized G :=
  ⟨hI.1.trans (h.later hI.2).1, (h.later hI.2).2⟩

instance primLater (F0 : Fork) : Prim (fun F => Later F0 F ∧ Sized F) where
  took := fun F n hI => ⟨hI.1.trans (took_later F n), took_sized n hI.2⟩
  hideRun := fun _ _ _ _ _ h hI =>
    ⟨hI.1.trans (hideRun_later hI.2 h), (hideRun_ok _ _ _ _ _ hI.2 h).2.1⟩
  push := fun _ _ _ _ h hI => later_step (push_slots5 h) hI
  pushRuns := fun _ _ _ _ h hI => later_step (pushRuns_slots5 h) hI
  rootTaken := fun F _ _ hI => later_step (F := F) ⟨rfl, rfl, rfl, rfl, rfl⟩ hI
  fill := fun F _ hI => later_step (F := F) ⟨rfl, rfl, rfl, rfl, rfl⟩ hI
  onRow := fun F _ _ _ hI => later_step (F := F) ⟨rfl, rfl, rfl, rfl, rfl⟩ hI
  book := fun _ _ h hI => later_step h.slots5 hI

theorem pushSlot_size {w : E} {ns : ℕ} {LS LS' : Array E} {x : ℕ × E}
    (h : Fork.pushSlot w ns LS x = some LS') : LS'.size = LS.size := by
  unfold Fork.pushSlot at h
  split at h
  · obtain rfl := Option.some.inj h
    simp
  · exact absurd h (by simp)

theorem pushSlots_size (w : E) (ns : ℕ) : ∀ (l : List (ℕ × E)) (LS LS' : Array E),
    l.foldlM (Fork.pushSlot w ns) LS = some LS' → LS'.size = LS.size
  | [], LS, LS', h => by
    have e : LS = LS' := by simpa using h
    rw [e]
  | x :: l, LS, LS', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, hm, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (pushSlots_size w ns l _ _ h2).trans (pushSlot_size hm)

theorem push_LS {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) :
    G.LS.size = F.LS.size := by
  unfold Fork.push at h
  split at h
  · exact absurd h (by simp)
  · simp only at h
    split at h
    · rename_i t' LS' h1 h2
      obtain rfl := Option.some.inj h
      rw [← Array.foldlM_toList] at h2
      exact pushSlots_size _ _ _ _ _ h2
    · exact absurd h (by simp)

theorem ls_step {F G : Fork} (h : Slots5 F G) (hl : G.LS.size = F.LS.size)
    (hI : Sized F ∧ F.LS.size = F.ns) : Sized G ∧ G.LS.size = G.ns :=
  ⟨(h.later hI.1).2, by rw [hl, hI.2, h.2.1]⟩

instance primLS : Prim (fun F => Sized F ∧ F.LS.size = F.ns) where
  took := fun F n hI => ⟨took_sized n hI.1, hI.2⟩
  hideRun := fun F G _ _ _ h hI => by
    obtain ⟨hs, hz, -, -⟩ := hideRun_ok _ _ _ _ _ hI.1 h
    refine ⟨hz, ?_⟩
    rw [hs]
    exact hI.2
  push := fun _ _ _ _ h hI => ls_step (push_slots5 h) (push_LS h) hI
  pushRuns := fun F G _ _ h hI => by
    refine ls_step (pushRuns_slots5 h) ?_ hI
    unfold Fork.pushRuns at h
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  rootTaken := fun F _ _ hI => ls_step (F := F) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl hI
  fill := fun F _ hI => ls_step (F := F) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl hI
  onRow := fun F _ _ _ hI => ls_step (F := F) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl hI
  book := fun _ _ h hI => ls_step h.slots5 (by rw [h.2.2.2.2.2.1]) hI

end Fo
