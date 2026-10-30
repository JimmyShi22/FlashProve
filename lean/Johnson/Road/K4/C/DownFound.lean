-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/DownFound.lean: CONDITIONAL.

What is here. Wherever the verifier's end of the batched sumcheck returns over a list of panels
(`stackEnd`, OnBytes/Model/LayerPanels.lean), the list holds the panel of the down product: a panel
without the selector whose whole A side is a never-sent vector (`down_found`). The end's last test
asks that the bits which such a panel has written into the state are ll + lPf, which is not 0; no
other panel writes them (`stackEndOf_wD`). The honest side's function for the true end values
searches that panel and refuses where there is none (`StackData.endsAt`,
Johnson/Desc/K4/Honest/Stack.lean). The case analysis follows the library's stackEndOf_in
(Johnson/Road/K4/Reads/PanelsEnts.lean).

  `stackEndOf_wD`   a panel that is not the down product's leaves the state's number of bits as it
      was.
  `down_found`   the panel is found.

Not shown here. That the end returns (h); that ll + lPf is not 0 (h0: the layout has ll at least 1):
hypotheses. Nothing on soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.Reads.PanelsEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Slots (Gives gives_foldlM_inv)

/-- **A panel that is not the down product's leaves the state's number of bits as it was.** -/
theorem stackEndOf_wD (y : Lay) (rs : Array E) (lam : ℕ) (om H1 V : Array E) {s : StackEnd}
    {b : SBlk} {k : ℕ} (hb : (!b.tri && b.virt.isSome) = false) (hs : s.wD = k) :
    Gives (stackEndOf y rs lam om H1 V s b) fun s' => s'.wD = k := by
  have guard : ∀ {α : Type} (f : PUnit → Option α) (Φ : α → Prop),
      Gives ((none : Option PUnit) >>= f) Φ :=
    fun f Φ => Gives.bind (Φ := fun _ => False) Gives.none fun _ h => h.elim
  unfold stackEndOf
  cases ht : b.tri with
  | true =>
    cases hk : b.virt with
    | some k' =>
      simp only [↓reduceIte]
      refine Gives.ite (guard _ _)
        (Gives.skip fun _ => Gives.skip fun v0 => Gives.ite Gives.none (Gives.pure ?_))
      exact hs
    | none =>
      simp only [↓reduceIte]
      refine Gives.ite (guard _ _) (Gives.skip fun _ => Gives.skip fun v0 => Gives.pure ?_)
      exact hs
  | false =>
    cases hk : b.virt with
    | some k' =>
      rw [ht, hk] at hb
      cases hb
    | none =>
      cases hv : b.v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
        refine Gives.skip fun A => ?_
        refine gives_foldlM_inv (P := fun s : StackEnd => s.wD = k) (fun s i hs => ?_) _ _ hs
        refine Gives.bind (Φ := fun s : StackEnd => s.wD = k) ?_ fun s hs => Gives.pure ?_
        · refine gives_foldlM_inv (P := fun s : StackEnd => s.wD = k) (fun s yv hs => ?_) _ _ hs
          refine Gives.skip fun a => Gives.pure ?_
          exact hs
        · exact hs
      | none =>
        cases hBe : b.B with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.skip fun A => ?_
          refine gives_foldlM_inv (P := fun s : StackEnd => s.wD = k) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := fun s : StackEnd => s.wD = k) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := fun s : StackEnd => s.wD = k) (fun s yv hs => ?_) _ _ hs
          exact Gives.skip fun _ => Gives.none
        | some B =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.skip fun A => ?_
          refine gives_foldlM_inv (P := fun s : StackEnd => s.wD = k) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := fun s : StackEnd => s.wD = k) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := fun s : StackEnd => s.wD = k) (fun s yv hs => ?_) _ _ hs
          refine Gives.skip fun a => Gives.skip fun c => Gives.pure ?_
          exact hs

/-- **THE PANEL OF THE DOWN PRODUCT IS FOUND.** CONDITIONAL: on h and h0. -/
theorem down_found {y : Lay} {bl : Array SBlk} {rs : Array E} {lam : ℕ} {om H1 V : Array E}
    {shownA shownB : E} {s : StackEnd}
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s) (h0 : y.h.ll + y.lPf ≠ 0) :
    ∃ dn, (bl.find? fun b => !b.tri && b.virt.isSome) = some dn := by
  cases hf : bl.find? fun b => !b.tri && b.virt.isSome with
  | some dn => exact ⟨dn, rfl⟩
  | none =>
    exfalso
    rw [← Array.find?_toList] at hf
    have hn : ∀ b ∈ bl.toList, (!b.tri && b.virt.isSome) = false := fun b hb => by
      have := List.find?_eq_none.mp hf b hb
      simpa using this
    unfold stackEnd at h
    obtain ⟨s0, hs0, h⟩ := Option.bind_eq_some_iff.mp h
    have hw : s0.wD = 0 := by
      rw [← Array.foldlM_toList] at hs0
      have key : ∀ (l : List SBlk) (a : StackEnd),
          (∀ b ∈ l, (!b.tri && b.virt.isSome) = false) → a.wD = 0 →
          Gives (l.foldlM (stackEndOf y rs lam om H1 V) a) fun s' => s'.wD = 0 := by
        intro l
        induction l with
        | nil => exact fun a _ ha => Gives.pure ha
        | cons b l ih =>
          intro a hl ha
          rw [List.foldlM_cons]
          exact Gives.bind (stackEndOf_wD y rs lam om H1 V (hl b List.mem_cons_self) ha)
            fun c hc => ih c (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) hc
      exact key _ _ hn rfl s0 hs0
    split at h
    · cases h
    · rename_i hc
      rw [hw] at hc
      apply hc
      simp only [bne_iff_ne, ne_eq]
      exact fun e => h0 e.symm

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.stackEndOf_wD
#print axioms OnBytes.Road.K4.C.down_found
