-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/EndKeys.lean: CONGRUENCE, FINER THAN End.lean's: THE END OF THE
BATCHED SUMCHECK OF THE SUB-PROTOCOL K4 (stackEndOf, stackEnd: OnBytes/Model/LayerPanels.lean) at
two lists of panels whose forms name the same entries: the two forms that it returns name THE SAME
ENTRIES OF THE READS, in the same order, whatever the coefficients. Statements and proofs.

Limits. NO LAW HERE SAYS THAT stackEnd RETURNS AT ANY PLAN: two calls are compared. Nothing on what
the returned forms or elements are worth; of the forms' slots and constants nothing is said. No
example and no negative test stand here. No property is claimed.

  EndKeys           two states of the end: the bits of the down product's panel; the entries that
                    the two forms name. EndKeys.intro: from the three.
  stackEndOf_keys   one panel's step at two panels in BlkKeys, two lists of challenges of one size
                    and two states in EndKeys. The other arrays and elements are free on both sides.
  **stackEnd_keys** the whole: both calls return or neither does, and what they return is in
                    EndKeys.
-/
import Johnson.Desc.First.K4.Returns.Pub.PanelsKeys
import Johnson.Desc.First.K4.Returns.Pub.End

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)

/-- Two states of the batched sumcheck's end: the bits of the down product's panel, and the entries
that the two forms name. -/
def EndKeys (s s₀ : StackEnd) : Prop :=
  s.wD = s₀.wD ∧ FormKeys s.Alin s₀.Alin ∧ FormKeys s.Blin s₀.Blin

theorem EndKeys.intro {s s₀ : StackEnd} (h1 : s.wD = s₀.wD) (h2 : FormKeys s.Alin s₀.Alin)
    (h3 : FormKeys s.Blin s₀.Blin) : EndKeys s s₀ := And.intro h1 (And.intro h2 h3)

variable {W : Prop}

/-- **One panel's step.** -/
theorem stackEndOf_keys (y : Lay) {rs rs₀ : Array E} (lam : Nat) (om H1 V om₀ H1₀ V₀ : Array E)
    {s s₀ : StackEnd} {b b₀ : SBlk} (hb : BlkKeys W b b₀) (hr : rs.size = rs₀.size)
    (hs : EndKeys s s₀) :
    OptRel EndKeys (stackEndOf y rs lam om H1 V s b) (stackEndOf y rs₀ lam om₀ H1₀ V₀ s₀ b₀) := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  obtain ⟨tri₀, v0₀, claim₀, ec₀, ni₀, ny₀, wy₀, w₀, off₀, A₀, B₀, wt₀, sl₀, xx₀, virt₀⟩ := b₀
  obtain ⟨e1, e2, e9, e3, e4, e5, e6, e7, e8, hA, hB, hx, _, _⟩ := hb
  dsimp only at e1 e2 e9 e3 e4 e5 e6 e7 e8 hA hB hx
  subst e1 e2 e9 e3 e4 e5 e6 e7 e8
  have hI : eqIndexOK (rs.extract w lam) (off / 2 ^ w) =
      eqIndexOK (rs₀.extract w lam) (off / 2 ^ w) := by
    unfold eqIndexOK
    rw [Array.size_extract, Array.size_extract, hr]
  have hw : s.wD = s₀.wD := hs.1
  unfold stackEndOf
  cases tri with
  | true =>
    cases virt with
    | some k =>
      simp only [↓reduceIte]
      exact optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_iteB rfl trivial hs)
    | none =>
      simp only [↓reduceIte]
      exact optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_pure (EndKeys.intro hs.1
          (foldl_rel (R := FormKeys) (fun _ _ k2 r => formKeys_addMul r (hx k2) _ _) _ _ _ hs.2.1)
          hs.2.2))
  | false =>
    cases virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_iteB (by rw [hw]) trivial (optRel_pure (EndKeys.intro rfl hs.2.1 hs.2.2)))
    | none =>
      cases v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
          optRel_bind hA fun f f₀ hf => ?_)
        refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
        refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
        exact optRel_bind (hf i yv) fun _ _ hq =>
          optRel_pure (EndKeys.intro hc.1 (formKeys_addMul hc.2.1 hq _ _) hc.2.2)
      | none =>
        cases B with
        | none =>
          cases B₀ with
          | some _ => exact False.elim hB
          | none =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
              optRel_bind hA fun f f₀ hf => ?_)
            refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
            refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
            exact optRel_bind (hf i yv) fun _ _ _ => trivial
        | some g =>
          cases B₀ with
          | none => exact False.elim hB
          | some g₀ =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
              optRel_bind hA fun f f₀ hf => ?_)
            refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
            refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
            exact optRel_bind (hf i yv) fun _ _ hq =>
              optRel_bind (hB i yv) fun _ _ hq' =>
                optRel_pure (EndKeys.intro hc.1 (formKeys_addMul hc.2.1 hq _ _)
                  (formKeys_addMul hc.2.2 hq' _ _))

/-- **The end over all panels**: both calls return or neither does, and the two forms of the one
name the entries of the two forms of the other. -/
theorem stackEnd_keys (y : Lay) {bl bl₀ : Array SBlk} {rs rs₀ : Array E} (lam : Nat)
    (om H1 V om₀ H1₀ V₀ : Array E) (a b a₀ b₀ : E)
    (hb : All2 (BlkKeys W) bl.toList bl₀.toList) (hr : rs.size = rs₀.size) :
    OptRel EndKeys (stackEnd y bl rs lam om H1 V a b)
      (stackEnd y bl₀ rs₀ lam om₀ H1₀ V₀ a₀ b₀) := by
  have key : OptRel EndKeys (bl.foldlM (stackEndOf y rs lam om H1 V) { As := a, Bs := b })
      (bl₀.foldlM (stackEndOf y rs₀ lam om₀ H1₀ V₀) { As := a₀, Bs := b₀ }) :=
    afoldlM_all2_rel (S := BlkKeys W) (R := EndKeys) (f := stackEndOf y rs lam om H1 V)
      (f' := stackEndOf y rs₀ lam om₀ H1₀ V₀)
      (fun _ _ _ _ hs hx => stackEndOf_keys y lam om H1 V om₀ H1₀ V₀ hx hr hs) hb
      { As := a, Bs := b } { As := a₀, Bs := b₀ } (EndKeys.intro rfl rfl rfl)
  unfold stackEnd
  refine optRel_bind key fun s s₀ hs => ?_
  have hw : s.wD = s₀.wD := hs.1
  exact optRel_iteB (by rw [hw]) trivial hs

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.EndKeys.intro
#print axioms OnBytes.Desc.First.K4.RtPub.stackEndOf_keys
#print axioms OnBytes.Desc.First.K4.RtPub.stackEnd_keys
