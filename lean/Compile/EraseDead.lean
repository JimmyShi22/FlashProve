-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/EraseDead.lean: a token whose string is never used may have any string: the proofs of the
statements of Compile/SpecEraseDead.lean (words of this library: lean/GLOSSARY.md).

The header of Compile/SpecEraseDead.lean says what the statements say and what they do not. Proved
here: lemmas on `StoreRel` (`snoc`: the same string appended to both stores; `snocDead`: two strings
appended to one store: the new index is the dead one), and the eight statements.

Notation (Compile/SpecEraseDead.lean): `D` : `Tok` → Prop: the dead tokens; `StoreRel D vs vs'` :
Prop: two stores of the same length that agree outside the dead tokens; `NoUse D Q c n` : Prop: the
program, started on a store of length n, never uses the string of a token in D; `OAlike R c c'` :
Prop: the same oracle algorithm but for the values at its ends, which are related by R;
`FacDead ag Q R c n` : Prop: after two answers related by ag the program goes on in the same way and
never uses the string of the new token; `ag` : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop; Q, R:
conditions at the ends: see the doc comments there.
-/
import Compile.SpecEraseDead

set_option autoImplicit false

namespace Compile
open Rom

variable {S : OSpec} {sp : Split S} {α β : Type} {D : Tok → Prop}

namespace StoreRel

theorem refl (D : Tok → Prop) (vs : List Bits) : StoreRel D vs vs := ⟨rfl, fun _ _ => rfl⟩

theorem getD' {vs vs' : List Bits} (h : StoreRel D vs vs') {t : Tok} (ht : ¬ D t) :
    vs.getD t [] = vs'.getD t [] := h.2 t ht

theorem map {vs vs' : List Bits} (h : StoreRel D vs vs') {us : List Tok} (hu : ∀ u ∈ us, ¬ D u) :
    (us.map fun u => vs.getD u []) = us.map fun u => vs'.getD u [] :=
  List.map_congr_left fun u hm => h.2 u (hu u hm)

/-- the same string appended to both stores -/
theorem snoc {vs vs' : List Bits} (h : StoreRel D vs vs') (x : Bits) :
    StoreRel D (vs ++ [x]) (vs' ++ [x]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  have h2 := h.2 i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at h2 ⊢
  rw [← h.1]
  by_cases hl : i < vs.length
  · rw [if_pos hl, if_pos hl]
    exact h2
  · rw [if_neg hl, if_neg hl]

/-- two strings appended to one store: the results agree except at the new index -/
theorem snocDead (vs : List Bits) (x y : Bits) :
    StoreRel (fun t => t = vs.length) (vs ++ [x]) (vs ++ [y]) := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases hl : i < vs.length
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl]
    have hi' : i ≠ vs.length := hi
    have h3 : vs.length < i := lt_of_le_of_ne (not_lt.1 hl) (Ne.symm hi')
    obtain ⟨j, hj⟩ : ∃ j, i - vs.length = j + 1 :=
      ⟨i - vs.length - 1, (Nat.sub_add_cancel (Nat.sub_pos_of_lt h3)).symm⟩
    rw [hj]
    rfl

end StoreRel

theorem eraseDead : Spec.eraseDead := by
  intro S sp α D Q c
  induction c with
  | pure a => exact fun vs vs' h hn => .pure ⟨rfl, h, hn⟩
  | sample n k ih => exact fun vs vs' h hn => .sample _ fun r => ih r vs vs' h (hn r)
  | plain o q k ih => exact fun vs vs' h hn => .query _ _ fun r => ih r vs vs' h (hn r)
  | fresh ℓ k ih =>
    intro vs vs' h hn
    show OAlike _ (.sample _ fun r => erase (k vs.length) _)
      (.sample _ fun r => erase (k vs'.length) _)
    rw [← h.1]
    exact .sample _ fun r => ih _ _ _ (h.snoc _) (by rw [List.length_append]; exact hn)
  | marked o t us pt inj k ih =>
    intro vs vs' h hn
    show OAlike _
      (.query o (pt (vs.getD t []) (us.map fun u => vs.getD u [])) fun r => erase (k _ vs.length) _)
      (.query o (pt (vs'.getD t []) (us.map fun u => vs'.getD u [])) fun r =>
        erase (k _ vs'.length) _)
    rw [← h.1, ← h.getD' hn.1, ← h.map hn.2.1]
    exact .query _ _ fun r => ih _ _ _ _ (h.snoc _) (by rw [List.length_append]; exact hn.2.2 _)
  | reveal ts k ih =>
    intro vs vs' h hn
    show OAlike _ (erase (k (ts.map fun u => vs.getD u [])) vs)
      (erase (k (ts.map fun u => vs'.getD u [])) vs')
    rw [← hn.1 (fun u => vs.getD u []) (fun u => vs'.getD u []) h.2]
    exact ih _ vs vs' h (hn.2 _)

theorem alikeBind : Spec.alikeBind := by
  intro S α β R c c' g g' h hg
  induction h with
  | pure h => exact hg _ _ h
  | sample n _ ih => exact congrArg (OComp.sample n) (funext ih)
  | query o q _ ih => exact congrArg (OComp.query o q) (funext ih)

theorem OAlike.refl {R : α → α → Prop} (hR : ∀ a, R a a) : ∀ c : OComp S α, OAlike R c c
  | .pure a => .pure (hR a)
  | .sample n k => .sample n fun r => OAlike.refl hR (k r)
  | .query o q k => .query o q fun r => OAlike.refl hR (k r)

theorem OAlike.mono {R R' : α → α → Prop} (hR : ∀ a a', R a a' → R' a a')
    {c c' : OComp S α} (h : OAlike R c c') : OAlike R' c c' := by
  induction h with
  | pure h => exact .pure (hR _ _ h)
  | sample n _ ih => exact .sample n ih
  | query o q _ ih => exact .query o q ih

theorem noUseBind : Spec.noUseBind := by
  intro S sp α β D Q Q' c g
  induction c with
  | pure a => exact fun n h hg => hg a n h
  | sample m k ih => exact fun n h hg r => ih r n (h r) hg
  | plain o q k ih => exact fun n h hg r => ih r n (h r) hg
  | fresh ℓ k ih => exact fun n h hg => ih n (n + 1) h hg
  | marked o t us pt inj k ih =>
    exact fun n h hg => ⟨h.1, h.2.1, fun v => ih v n (n + 1) (h.2.2 v) hg⟩
  | reveal ts k ih =>
    exact fun n h hg =>
      ⟨fun f f' hf => congrArg (fun c => Step.bind c g) (h.1 f f' hf), fun w => ih w n (h.2 w) hg⟩

theorem noUseMono : Spec.noUseMono := by
  intro S sp α D D' Q Q' c n hD hQ
  induction c generalizing n with
  | pure a => exact fun h => hQ a n h
  | sample m k ih => exact fun h r => ih r n (h r)
  | plain o q k ih => exact fun h r => ih r n (h r)
  | fresh ℓ k ih => exact fun h => ih n (n + 1) h
  | marked o t us pt inj k ih =>
    exact fun h =>
      ⟨fun d => h.1 (hD _ d), fun u hu d => h.2.1 u hu (hD _ d), fun v => ih v n (n + 1) (h.2.2 v)⟩
  | reveal ts k ih =>
    exact fun h =>
      ⟨fun f f' hf => h.1 f f' fun u hu => hf u fun d => hu (hD _ d), fun w => ih w n (h.2 w)⟩

theorem deadTail : Spec.deadTail := by
  intro S sp α Q o k vs r r' hk hn
  rw [← hk]
  exact eraseDead S sp α _ Q _ _ _ (StoreRel.snocDead vs _ _) (by rw [List.length_append]; exact hn)

theorem facDeadBind : Spec.facDeadBind := by
  intro S sp α β ag Q Q' R R' c g
  induction c with
  | pure a => exact fun n h _ hg => hg a n h
  | sample m k ih => exact fun n h hu hg r => ih r n (h r) hu hg
  | plain o q k ih =>
    exact fun n h hu hg =>
      ⟨fun r r' e => congrArg (fun c => Step.bind c g) (h.1 r r' e), fun r => ih r n (h.2 r) hu hg⟩
  | fresh ℓ k ih => exact fun n h hu hg => ih n (n + 1) h hu hg
  | marked o t us pt inj k ih =>
    exact fun n h hu hg =>
      ⟨fun v ws r r' e =>
          ⟨congrArg (fun c => Step.bind c g) (h.1 v ws r r' e).1,
            noUseBind S sp α β _ (Q n) (Q' n) _ g (n + 1)
              (h.1 v ws r r' e).2 fun a m hq => hu n a m hq⟩,
        fun v => ih v n (n + 1) (h.2 v) hu hg⟩
  | reveal ts k ih => exact fun n h hu hg w => ih w n (h w) hu hg

theorem facDeadMono : Spec.facDeadMono := by
  intro S sp α ag Q Q' R R' c n hQ hR
  induction c generalizing n with
  | pure a => exact fun h => hR a n h
  | sample m k ih => exact fun h r => ih r n (h r)
  | plain o q k ih => exact fun h => ⟨h.1, fun r => ih r n (h.2 r)⟩
  | fresh ℓ k ih => exact fun h => ih n (n + 1) h
  | marked o t us pt inj k ih =>
    exact fun h =>
      ⟨fun v ws r r' e =>
          ⟨(h.1 v ws r r' e).1,
            noUseMono S sp α _ _ (Q n) (Q' n) _ (n + 1) (fun _ h => h) (hQ n) (h.1 v ws r r' e).2⟩,
        fun v => ih v n (n + 1) (h.2 v)⟩
  | reveal ts k ih => exact fun h w => ih w n (h w)

theorem facDeadErase : Spec.facDeadErase := by
  intro S sp α β ag Q R c
  induction c with
  | pure a => exact fun vs g h _ hf => hf a vs h
  | sample m k ih => exact fun vs g h hg hf r => ih r vs g (h r) hg hf
  | plain o q k ih =>
    exact fun vs g h hg hf => ⟨fun r r' e => by
      show (erase (k r) vs).bind g = (erase (k r') vs).bind g
      rw [h.1 r r' e], fun r => ih r vs g (h.2 r) hg hf⟩
  | fresh ℓ k ih => exact fun vs g h hg hf r => ih _ _ g (by rw [List.length_append]; exact h) hg hf
  | marked o t us pt inj k ih =>
    intro vs g h hg hf
    refine ⟨fun r r' e => ?_, fun r => ih _ _ _ g (by rw [List.length_append]; exact h.2 _) hg hf⟩
    obtain ⟨e1, e2⟩ := h.1 _ _ r r' e
    exact alikeBind S _ β _ _ _ g g
        (deadTail S sp α (Q vs.length) o k vs r r' e1 e2) fun x y hxy => by
      obtain ⟨a, st⟩ := x
      obtain ⟨a', st'⟩ := y
      obtain ⟨ea, hs, hq⟩ := hxy
      have ea' : a = a' := ea
      subst ea'
      exact hg vs.length a st st' hs hq
  | reveal ts k ih => exact fun vs g h hg hf => ih _ vs g (h _) hg hf



end Compile
