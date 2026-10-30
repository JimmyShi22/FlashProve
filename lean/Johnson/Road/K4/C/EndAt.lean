-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/EndAt.lean: CONDITIONAL.

What is here. The two forms that the verifier's end of the batched sumcheck leaves (`stackEnd`,
OnBytes/Model/LayerPanels.lean: Alin, Blin) have the caller's test T at all the entries that they
name, over any list of panels whose own forms have it (`stackEnd_at`, `stackEndOf_at`). It carries
Johnson/Road/K4/C/EntsAt.lean one step on. THE TWO PROOFS ARE THE LIBRARY's stackEndOf_in AND
stackEnd_ents (Johnson/Road/K4/Reads/PanelsEnts.lean), step for step, with the test in the place of
«in some family of tables».

  `EndTest v T s`   the two forms of the end.
  `stackEndOf_at`   what one panel adds.
  `stackEnd_at`   the end over all panels.

Not shown here. PanAt (that the panels' own forms have T): a hypothesis. That the end returns: each
statement speaks of what is returned, if anything. Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.Road.K4.C.EntsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Reads (EntsIn entsIn_empty entsIn_addMul entsIn_foldl)
open OnBytes.Desc.First.K4.Slots (Gives Side core gives_foldlM_inv)

variable {v : Env} {T : ℕ → Prop}

/-- The two forms of the end have T at the entries that they name. -/
def EndTest (v : Env) (T : ℕ → Prop) (s : StackEnd) : Prop :=
  InTest v T s.Alin ∧ InTest v T s.Blin

/-- **What one panel adds.** -/
theorem stackEndOf_at (y : Lay) (rs : Array E) (lam : ℕ) (om H1 V : Array E) {s : StackEnd}
    {b : SBlk} (hb : CoreTest v T (core b)) (hs : EndTest v T s) :
    Gives (stackEndOf y rs lam om H1 V s b) (EndTest v T) := by
  obtain ⟨hA, hB, hx⟩ := hb
  have guard : ∀ {α : Type} (f : PUnit → Option α) (Φ : α → Prop),
      Gives ((none : Option PUnit) >>= f) Φ :=
    fun f Φ => Gives.bind (Φ := fun _ => False) Gives.none fun _ h => h.elim
  unfold stackEndOf
  cases ht : b.tri with
  | true =>
    cases hk : b.virt with
    | some k =>
      simp only [↓reduceIte]
      refine Gives.ite (guard _ _)
        (Gives.skip fun _ => Gives.skip fun v0 => Gives.ite Gives.none (Gives.pure ?_))
      exact ⟨hs.1, hs.2⟩
    | none =>
      simp only [↓reduceIte]
      refine Gives.ite (guard _ _) (Gives.skip fun _ => Gives.skip fun v0 => Gives.pure ?_)
      exact ⟨entsIn_foldl _ (fun a k2 ha => entsIn_addMul _ ha (hx k2)) _ _ hs.1, hs.2⟩
  | false =>
    cases hk : b.virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine Gives.ite (guard _ _)
        (Gives.skip fun _ => Gives.skip fun v0 => Gives.ite Gives.none (Gives.pure ?_))
      exact ⟨hs.1, hs.2⟩
    | none =>
      cases hv : b.v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
        refine Gives.bind (Φ := fun A => b.A = some A) (fun _ h => h) fun A hAe => ?_
        refine gives_foldlM_inv (P := EndTest v T) (fun s i hs => ?_) _ _ hs
        refine Gives.bind (Φ := EndTest v T) ?_ fun s hs => Gives.pure ?_
        · refine gives_foldlM_inv (P := EndTest v T) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha => Gives.pure ?_
          exact ⟨entsIn_addMul _ hs.1 ha, hs.2⟩
        · exact ⟨hs.1, hs.2⟩
      | none =>
        cases hBe : b.B with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.skip fun A => ?_
          refine gives_foldlM_inv (P := EndTest v T) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndTest v T) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndTest v T) (fun s yv hs => ?_) _ _ hs
          exact Gives.skip fun _ => Gives.none
        | some B =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine Gives.ite (guard _ _) (Gives.skip fun _ => ?_)
          refine Gives.bind (Φ := fun A => b.A = some A) (fun _ h => h) fun A hAe => ?_
          refine gives_foldlM_inv (P := EndTest v T) (fun s i hs => ?_) _ _ hs
          refine Gives.bind (Φ := EndTest v T) ?_ fun s hs => Gives.pure hs
          refine gives_foldlM_inv (P := EndTest v T) (fun s yv hs => ?_) _ _ hs
          refine Gives.bind (hA A hAe i yv) fun a ha =>
            Gives.bind (hB B hBe i yv) fun c hc => Gives.pure ?_
          exact ⟨entsIn_addMul _ hs.1 ha, entsIn_addMul _ hs.2 hc⟩

/-- **The end of the batched sumcheck over all panels.** -/
theorem stackEnd_at {y : Lay} {bl : Array SBlk} {rs : Array E} {lam : ℕ} {om H1 V : Array E}
    {shownA shownB : E} {s : StackEnd} (hbl : PanAt v T bl)
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s) : EndTest v T s := by
  unfold stackEnd at h
  obtain ⟨s0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  have hs0 : EndTest v T s0 := by
    rw [← Array.foldlM_toList] at h0
    have key : ∀ (l : List SBlk) (a : StackEnd), (∀ b ∈ l, CoreTest v T (core b)) → EndTest v T a →
        Gives (l.foldlM (stackEndOf y rs lam om H1 V) a) (EndTest v T) := by
      intro l
      induction l with
      | nil => exact fun a _ ha => Gives.pure ha
      | cons b l ih =>
        intro a hl ha
        rw [List.foldlM_cons]
        exact Gives.bind (stackEndOf_at y rs lam om H1 V (hl b List.mem_cons_self) ha)
          fun c hc => ih c (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) hc
    refine key _ _ (fun b hb => hbl _ ?_) ⟨entsIn_empty, entsIn_empty⟩ s0 h0
    rw [Array.toList_map]
    exact List.mem_map_of_mem hb
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact hs0

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.stackEndOf_at
#print axioms OnBytes.Road.K4.C.stackEnd_at
