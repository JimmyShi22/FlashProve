-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/End.lean: THE END OF THE BATCHED SUMCHECK OF THE SUB-PROTOCOL K4
(stackEndOf, stackEnd: OnBytes/Model/LayerPanels.lean): on what its return hangs. General laws:
nothing is evaluated.

Limits. NO LAW HERE SAYS THAT stackEnd RETURNS AT ANY PLAN: two calls are compared, and one of its
tests is shown to pass at placed panels. Nothing on what the returned forms are worth. The bound of
63 coordinates in placed_index is a premise. No property is claimed.

  optRel_iteB      two tests of one answer, in front of two pairs of values that may be missing.
  stackEndOf_rel   one panel's step at two panels in BlkSkel, two lists of challenges of one size
                   and two states in EndSkel: both results are missing, or neither is and the states
                   that are left are in EndSkel. The other arrays and elements are free on both
                   sides.
  stackEnd_rel     the whole: at two lists of panels in BlkSkel, member by member, and two lists of
                   challenges of one size, both calls return or neither does.
  placed_index     the step's first test (eqIndexOK) passes at every panel that placePanels has
                   placed, where the caller's test on the number of places has passed, there are lam
                   challenges, and no panel has fewer than lam - 63 bits.
-/
import Johnson.Desc.First.K4.Returns.Pub.Kit
import Johnson.Road.FormsKeysEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)

/-- Two tests of one answer, in front of two pairs of values that may be missing. -/
theorem optRel_iteB {α : Type} {R : α → α → Prop} {c c' : Bool} (hc : c = c')
    {x y x' y' : Option α} (h1 : OptRel R x x') (h2 : OptRel R y y') :
    OptRel R (if c = true then x else y) (if c' = true then x' else y') := by
  subst hc
  exact optRel_ite h1 h2

/-- **One panel's step**: its return hangs on the panel's skeleton, the number of challenges and the
bits of the down product's panel so far. -/
theorem stackEndOf_rel (y : Lay) {rs rs₀ : Array E} (lam : Nat) (om H1 V om₀ H1₀ V₀ : Array E)
    {s s₀ : StackEnd} {b b₀ : SBlk} (hb : BlkSkel b b₀) (hr : rs.size = rs₀.size)
    (hs : EndSkel s s₀) :
    OptRel EndSkel (stackEndOf y rs lam om H1 V s b) (stackEndOf y rs₀ lam om₀ H1₀ V₀ s₀ b₀) := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  obtain ⟨tri₀, v0₀, claim₀, ec₀, ni₀, ny₀, wy₀, w₀, off₀, A₀, B₀, wt₀, sl₀, xx₀, virt₀⟩ := b₀
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, hA, hB⟩ := hb
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8 hA hB
  subst e1 e2 e3 e4 e5 e6 e7 e8
  have hI : eqIndexOK (rs.extract w lam) (off / 2 ^ w) =
      eqIndexOK (rs₀.extract w lam) (off / 2 ^ w) := by
    unfold eqIndexOK
    rw [Array.size_extract, Array.size_extract, hr]
  have hw : s.wD = s₀.wD := hs
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
        hs)
  | false =>
    cases virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_iteB (by rw [hw]) trivial rfl)
    | none =>
      cases v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
          optRel_bind hA fun f f₀ hf => ?_)
        refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
        refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
        exact optRel_bind (optRel_of_isSome (hf i yv)) fun _ _ _ => hc
      | none =>
        cases B with
        | none =>
          cases B₀ with
          | some _ => exact hB.elim
          | none =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
              optRel_bind hA fun f f₀ hf => ?_)
            refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
            refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
            exact optRel_bind (optRel_of_isSome (hf i yv)) fun _ _ _ => trivial
        | some g =>
          cases B₀ with
          | none => exact hB.elim
          | some g₀ =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine optRel_iteB (by rw [hI]) trivial (optRel_bind_same fun _ =>
              optRel_bind hA fun f f₀ hf => ?_)
            refine foldlM_opt_rel (fun a a₀ i ha => optRel_bind ?_ fun c c₀ hc => hc) _ _ _ hs
            refine foldlM_opt_rel (fun c c₀ yv hc => ?_) _ _ _ ha
            exact optRel_bind (optRel_of_isSome (hf i yv)) fun _ _ _ =>
              optRel_bind (optRel_of_isSome (hB i yv)) fun _ _ _ => hc

/-- **The end over all panels**: both calls return or neither does. -/
theorem stackEnd_rel (y : Lay) {bl bl₀ : Array SBlk} {rs rs₀ : Array E} (lam : Nat)
    (om H1 V om₀ H1₀ V₀ : Array E) (a b a₀ b₀ : E) (hb : All2 BlkSkel bl.toList bl₀.toList)
    (hr : rs.size = rs₀.size) :
    (stackEnd y bl rs lam om H1 V a b).isSome =
      (stackEnd y bl₀ rs₀ lam om₀ H1₀ V₀ a₀ b₀).isSome := by
  have key : OptRel EndSkel (bl.foldlM (stackEndOf y rs lam om H1 V) { As := a, Bs := b })
      (bl₀.foldlM (stackEndOf y rs₀ lam om₀ H1₀ V₀) { As := a₀, Bs := b₀ }) :=
    afoldlM_all2_rel (S := BlkSkel) (R := EndSkel) (f := stackEndOf y rs lam om H1 V)
      (f' := stackEndOf y rs₀ lam om₀ H1₀ V₀)
      (fun _ _ _ _ hs hx => stackEndOf_rel y lam om H1 V om₀ H1₀ V₀ hx hr hs) hb
      { As := a, Bs := b } { As := a₀, Bs := b₀ } (Eq.refl (0 : Nat))
  refine OptRel.isSome_eq (R := EndSkel) ?_
  unfold stackEnd
  refine optRel_bind key fun s s₀ hs => ?_
  have hw : s.wD = s₀.wD := hs
  exact optRel_iteB (by rw [hw]) trivial hs

/-- **The step's first test passes at placed panels.** -/
theorem placed_index {bl : Array SBlk} {lam : Nat} {rs : Array E}
    (hN : (ceilLog2 (placePanels bl).2 == lam) = true) (hr : rs.size = lam)
    (h63 : ∀ b ∈ bl.toList, lam - b.w ≤ 63) :
    ∀ b ∈ (placePanels bl).1.toList, eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true := by
  intro b hb
  have h1 := ((Road.placed_list bl).2 b hb).1
  have hN' := Road.places_le hN
  obtain ⟨b0, h0, o, rfl⟩ := Road.placed_from bl b hb
  have h63' := h63 b0 h0
  have h1' : o + 2 ^ b0.w ≤ (placePanels bl).2 := h1
  have hp : 0 < 2 ^ b0.w := Nat.pow_pos (by omega)
  have hw : 2 ^ b0.w ≤ 2 ^ lam := by omega
  have hwl : b0.w ≤ lam := (Nat.pow_le_pow_iff_right (by omega)).mp hw
  have hsz : (rs.extract b0.w lam).size = lam - b0.w := by
    rw [Array.size_extract, hr, Nat.min_self]
  show eqIndexOK (rs.extract b0.w lam) (o / 2 ^ b0.w) = true
  unfold eqIndexOK
  rw [hsz, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  refine ⟨h63', ?_⟩
  rw [Nat.div_lt_iff_lt_mul hp, ← Nat.pow_add, Nat.sub_add_cancel hwl]
  omega

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.optRel_iteB
#print axioms OnBytes.Desc.First.K4.RtPub.stackEndOf_rel
#print axioms OnBytes.Desc.First.K4.RtPub.stackEnd_rel
#print axioms OnBytes.Desc.First.K4.RtPub.placed_index
