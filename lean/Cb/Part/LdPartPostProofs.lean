-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartPostProofs.lean: the proofs of Cb/Part/LdPartPost.lean: the front's last step, for
arbitrary parameters.
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Limits: what the head of Cb/Part/LdPartPost.lean lists as not said is not said here either.
-/
import Cb.Part.LdPartPost
import Cb.Part.LdPartCellsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Blocks Finset Cb.Rng Cb.RngPk

theorem ldPartPost_plus : Spec.ldPartPost_plus := fun _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨fun j => h (.inl j), fun j => h (.inr j)⟩, fun h j => match j with
    | .inl j => h.1 j
    | .inr j => h.2 j⟩

theorem ldPartPost_rows : Spec.ldPartPost_rows := by
  intro p E St J _ _ Rw W st Y e
  refine forall_congr' fun r => ?_
  show (0 : E) + ∑ k, ∑ c, (0 : E) * readsOf (W st) Y k c + ∑ n, Rw.co st r n * e n = Rw.tg st r ↔ _
  simp only [zero_mul, sum_const_zero, zero_add]

theorem ldPartPost : Spec.ldPartPost := by
  intro E _ p O St Jb _ C S Q Kc Wp A f R R' Opn rcO rc c nm hS hSm hrc hOf hT hLaw hX
  have mid : ∀ (s : St) (t : C.Msg × S.Msg),
      Opn s t ↔
      (Q.cl nm).OnCells c.W s (cells p.P (2 * p.D) p.rdx (c.pk t.2)) (c.ent t.2) ∧ Q.Tn s t := by
    intro s t
    rw [hLaw s t, LdPartSrt.cl, ldPartPost_plus, ldPartPost_rows,
      ldPartCells_claims p E St Jb nm Q.K c.W hOf hT, and_assoc]
  refine ⟨fun o y w h => ?_, fun o y h => ?_,
    fun w => (hSm.core _).trans (hS.core _), fun o y w _ h => ?_⟩
  · obtain ⟨hE, hB⟩ := h
    obtain ⟨hR, hO⟩ := (hS.rel o y ((w.2.1.1.1, w.1), w.2.2)).1 hB
    obtain ⟨h1, h2⟩ := (mid _ _).1 hO
    refine ⟨?_, h1, ?_, h2, hSm.fw _ _ _ hR⟩
    · show PackBy p.B p.rdx (c.yz (R'.core ((w.2.1.1.1, w.1), w.2.2))) (c.pk w.1)
      rw [hSm.core]
      exact hX _ _ _ hR
    · show C.Enc (rc (f o)) y w.2.1
      rw [hrc o]
      exact hE
  · refine ⟨?_, hSm.on _ (hS.on o y h.2)⟩
    show ¬ C.coll y (rc (f o)).1
    rw [hrc o]
    exact h.1
  · obtain ⟨hP, h1, U, hU, h2, hR'⟩ := h
    have hR := hSm.bw (f o, y) ((U, w.1), w.2.2) hP hR'
    have hU' : C.dcd y (rc (f o)) = some U := hU
    rw [hrc o] at hU'
    exact ⟨U, hU', (hS.relR o y ((U, w.1), w.2.2)).2 ⟨hR, (mid _ (U, w.1)).2 ⟨h1, h2⟩⟩⟩

end Cb
