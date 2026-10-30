-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/ConditionReal.lean (kind K10; the row K10_condition): THE PROVED
SUB-PROTOCOL's CONDITION HOLDS AT EACH OF THE 25 LINKS OF THE FULL SIZE, AND AT EACH OF THE 5 OF THE
SMALL SIZE, AT THE WRITTEN LIST, THE WRITTEN REQUEST's FLAGS AND A GROUP IN FRONT: NO PREMISE ON
NUMBERS IS LEFT. Statements and proofs.

Why. `k10_condition_full_layK` (CornersKept.lean, beside this file) shows the condition of the
proved batching and fold (`BatFoldOKAt`) at the typed group of any written list, whichever members
are kept, from ONE premise: the group in front has the number of row variables that the layout's
formula gives for these flags. ReqKept.lean shows by the kernel, at every link, that a group in
front has that number at the flags which the written request's shape gives (`real_full`,
`RealAt.group`). The two were not joined.
  `full_mem`, `small_mem`: the l-th written list is a member of the written lists.
  `k10_condition_real_full`: at each l < 25: there is a group gs in front with gs.k = `kLay` of the
    l-th list at the flags `kbAt shapeFull l`, AND at every choice of the caller's letters (keep, B,
    Sb, sl, n, num, fx, A₀, w₀, w₁) `BatFoldOKAt` holds of the caller of `groupFullLayK` at that
    list, that group and these flags, the coefficients the powers of one element along num.
  `k10_condition_real_small`: the like at each l < 5.
Limits. THE NUMBERS ARE THE WRITTEN ONES: that the written request's shape is the planner's is held
by a run, not by Lean (Johnson/Desc/ReqLit/); the flags are those that `joinersAt` makes of it,
typed after the program's two rules, tied to the program by no lemma (ReqKept.lean's own limits).
That a verifier's state's group has these members and flags at a closing is not shown here. The
caller's letters stay letters. The last group (the last test's first stage) is not treated. It
rests, through the prices of the fold, on the files under ThirdParty/ (lean/LIMITS.md, L15). Nothing
on soundness of the protocol.

-/
import Johnson.Desc.First.Close.Law.ReqKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb Iop IOR
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.ReqLit

theorem full_mem {l : ℕ} (hl : l < 25) : linksFullLit.getD l [] ∈ linksFullLit := by
  have h : l < linksFullLit.length := lt_of_lt_of_le hl (by decide)
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem small_mem {l : ℕ} (hl : l < 5) : linksSmallLit.getD l [] ∈ linksSmallLit := by
  have h : l < linksSmallLit.length := lt_of_lt_of_le hl (by decide)
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

/-- **THE ROW K10_condition AT THE FULL SIZE's 25 LINKS.** -/
theorem k10_condition_real_full {l : ℕ} (hl : l < 25) :
    ∃ (gs : GroupSize) (hgs : gs ∈ frontFull),
      gs.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) ∧
      ∀ (keep : (sigOf codesFull2 (linksFullLit.getD l [])).O → Prop) [DecidablePred keep]
        {B : Type} [Fintype B] (Sb : B → Type)
        (sl : ∀ b, Slf GE (Sb b) (groupFullLayK (linksFullLit.getD l []) (full_mem hl) gs hgs
          (kbAt shapeFull l (linksFullLit.getD l []))).G.C.J) (n : ℕ)
        (num : (groupFullLayK (linksFullLit.getD l []) (full_mem hl) gs hgs
          (kbAt shapeFull l (linksFullLit.getD l []))).G.Row B ≃ Fin n)
        (fx : Fin (((groupFullLayK (linksFullLit.getD l []) (full_mem hl) gs hgs
          (kbAt shapeFull l (linksFullLit.getD l []))).Sh.fold Sb sl
          (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
        {Kc St₀ Wp : Type} {E₀ : ExtSpec}
        (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 (linksFullLit.getD l [])).sub
          ((groupFullLayK (linksFullLit.getD l []) (full_mem hl) gs hgs
            (kbAt shapeFull l (linksFullLit.getD l []))).sizeB keep Sb sl
            (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
        (w₀ : (sigOf codesFull2 (linksFullLit.getD l [])).Wit × Wp)
        (w₁ : LdBrW (groupFullLayK (linksFullLit.getD l []) (full_mem hl) gs hgs
          (kbAt shapeFull l (linksFullLit.getD l []))).G
          ((groupFullLayK (linksFullLit.getD l []) (full_mem hl) gs hgs
            (kbAt shapeFull l (linksFullLit.getD l []))).sizeB keep Sb sl
            (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp),
        BatFoldOKAt ((groupFullLayK (linksFullLit.getD l []) (full_mem hl) gs hgs
          (kbAt shapeFull l (linksFullLit.getD l []))).foldCaller keep Sb sl
          (Cb.Pv.Bat.powersZ (E := GE) n num) fx A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀
          w₁) := by
  obtain ⟨gs, hgs, hk⟩ := (real_full l hl).group
  exact ⟨gs, hgs, hk, fun keep _ _ _ Sb sl n num fx _ _ _ _ A₀ w₀ w₁ =>
    k10_condition_full_layK _ (full_mem hl) gs hgs _ keep Sb sl n num fx A₀ w₀ w₁ hk⟩

/-- **The like at the small size's 5 links.** -/
theorem k10_condition_real_small {l : ℕ} (hl : l < 5) :
    ∃ (gs : GroupSize) (hgs : gs ∈ frontSmall),
      gs.k = kLay (linksSmallLit.getD l []) (kbAt shapeSmall l (linksSmallLit.getD l [])) ∧
      ∀ (keep : (sigOf codesSmall2 (linksSmallLit.getD l [])).O → Prop) [DecidablePred keep]
        {B : Type} [Fintype B] (Sb : B → Type)
        (sl : ∀ b, Slf GE (Sb b) (groupSmallLayK (linksSmallLit.getD l []) (small_mem hl) gs hgs
          (kbAt shapeSmall l (linksSmallLit.getD l []))).G.C.J) (n : ℕ)
        (num : (groupSmallLayK (linksSmallLit.getD l []) (small_mem hl) gs hgs
          (kbAt shapeSmall l (linksSmallLit.getD l []))).G.Row B ≃ Fin n)
        (fx : Fin (((groupSmallLayK (linksSmallLit.getD l []) (small_mem hl) gs hgs
          (kbAt shapeSmall l (linksSmallLit.getD l []))).Sh.fold Sb sl
          (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
        {Kc St₀ Wp : Type} {E₀ : ExtSpec}
        (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 (linksSmallLit.getD l [])).sub
          ((groupSmallLayK (linksSmallLit.getD l []) (small_mem hl) gs hgs
            (kbAt shapeSmall l (linksSmallLit.getD l []))).sizeB keep Sb sl
            (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
        (w₀ : (sigOf codesSmall2 (linksSmallLit.getD l [])).Wit × Wp)
        (w₁ : LdBrW (groupSmallLayK (linksSmallLit.getD l []) (small_mem hl) gs hgs
          (kbAt shapeSmall l (linksSmallLit.getD l []))).G
          ((groupSmallLayK (linksSmallLit.getD l []) (small_mem hl) gs hgs
            (kbAt shapeSmall l (linksSmallLit.getD l []))).sizeB keep Sb sl
            (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp),
        BatFoldOKAt ((groupSmallLayK (linksSmallLit.getD l []) (small_mem hl) gs hgs
          (kbAt shapeSmall l (linksSmallLit.getD l []))).foldCaller keep Sb sl
          (Cb.Pv.Bat.powersZ (E := GE) n num) fx A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀
          w₁) := by
  obtain ⟨gs, hgs, hk⟩ := (real_small l hl).group
  exact ⟨gs, hgs, hk, fun keep _ _ _ Sb sl n num fx _ _ _ _ A₀ w₀ w₁ =>
    k10_condition_small_layK _ (small_mem hl) gs hgs _ keep Sb sl n num fx A₀ w₀ w₁ hk⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_condition_real_full
#print axioms VerifiableInference.Desc.First.Close.k10_condition_real_small
