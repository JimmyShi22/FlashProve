-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegCarryJoin.lean: wide facts in the closure under joining: the join of two wide facts at
one reading is a wide fact; a wide fact can be brought to any smaller reading that still holds its
own entries.

Statements (Cb.Spec.wideJ_*) and proofs.
Cb/Req1/LdSegFreshS.lean closes a set X of facts under: join at one reading, a coarser reading,
another type for the same masks (`MaskFact.JCl X`); Cb/Req1/LdReqS.lean lets a request's masked
blocks take their facts from the closed sets.

Why: a block whose own masks were drawn by two sendings (a sumcheck of a later segment that
reveals a map (`PscPar.A`, `PscOur.A`, Cb/Ld/LdPsc.lean: by type finite types, which index the maps
`PscPar.G`, `PscOur.F`) linear in the index: its hiding coefficients go out with the closing before
it, its inner masks with the request's first sending).
Each part has a wide fact (`LdStage.wideFact`, Cb/Req1/LdSegCarry.lean) of its own. Here the two are
put together in the parameters of wide facts, so that the rules for wide facts go on applying to the
pair.

Main names (the types of masks Mk, M₁, M₂ are finite and non-empty, as `wideFact` needs):
  `Spec.wideJ_sub`: JCl X (wide fact at Rd, Rr) → JCl X (the same at Rd', Rr'), if Rd' ⊆ Rd,
    Rr' ⊆ Rr and own ⊆ Rd'.
  `Spec.wideJ_join`: JCl X (wide fact at Rd, Rr, own₁, M₁, v₁) → JCl X (wide fact at the same Rd,
    Rr, own₂, M₂, v₂) → JCl X (wide fact at Rd, Rr; own: own₁ or own₂; masks: M₁ × M₂; value at an
    entry: v₁ where own₁, else v₂). No disjointness is asked.
  `Spec.wideJ_pair`: both in one: two wide facts at readings (Rd₁, Rr₁), (Rd₂, Rr₂) give the pair's
    wide fact at every reading within both that holds all own entries.

Limits: this file does not say that two given parts have wide facts (the rules of
Cb/Req1/LdSegCarry*.lean, Cb/Ld/LdSendStdVis.lean, Cb/Ld/LdGroupNewRideWFresh.lean). No instance in
this file.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFreshS
import Cb.Req1.LdSegCarry

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

namespace Spec
section
variable (E Kc : Type) [Field E]

def wideJ_sub : Prop :=
  ∀ (a : LdStage E Kc) (X : MaskFact a.J.W → Prop) (Rd Rd' : a.S.Ent → Prop) (Rr Rr' : a.S.O → Prop)
      (own : a.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E),
    (∀ n, Rd' n → Rd n) → (∀ o, Rr' o → Rr o) → (∀ n, own n → Rd' n) →
    MaskFact.JCl X (a.wideFact Rd Rr own Mk val) → MaskFact.JCl X (a.wideFact Rd' Rr' own Mk val)

open Classical in
def wideJ_join : Prop :=
  ∀ (a : LdStage E Kc) (X : MaskFact a.J.W → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
      (own₁ own₂ : a.S.Ent → Prop) (M₁ M₂ : Type) [Fintype M₁] [Nonempty M₁] [Fintype M₂]
      [Nonempty M₂] (v₁ : M₁ → a.S.Ent → E) (v₂ : M₂ → a.S.Ent → E),
    MaskFact.JCl X (a.wideFact Rd Rr own₁ M₁ v₁) → MaskFact.JCl X (a.wideFact Rd Rr own₂ M₂ v₂) →
    MaskFact.JCl X
      (a.wideFact Rd Rr (fun n => own₁ n ∨ own₂ n) (M₁ × M₂) fun M n =>
        if own₁ n then v₁ M.1 n else v₂ M.2 n)

open Classical in
def wideJ_pair : Prop :=
  ∀ (a : LdStage E Kc) (X : MaskFact a.J.W → Prop) (Rd₁ Rd₂ Rd : a.S.Ent → Prop)
      (Rr₁ Rr₂ Rr : a.S.O → Prop) (own₁ own₂ : a.S.Ent → Prop) (M₁ M₂ : Type) [Fintype M₁]
      [Nonempty M₁] [Fintype M₂] [Nonempty M₂] (v₁ : M₁ → a.S.Ent → E) (v₂ : M₂ → a.S.Ent → E),
    (∀ n, Rd n → Rd₁ n ∧ Rd₂ n) → (∀ o, Rr o → Rr₁ o ∧ Rr₂ o) → (∀ n, own₁ n ∨ own₂ n → Rd n) →
    MaskFact.JCl X (a.wideFact Rd₁ Rr₁ own₁ M₁ v₁) →
    MaskFact.JCl X (a.wideFact Rd₂ Rr₂ own₂ M₂ v₂) →
    MaskFact.JCl X
      (a.wideFact Rd Rr (fun n => own₁ n ∨ own₂ n) (M₁ × M₂) fun M n =>
        if own₁ n then v₁ M.1 n else v₂ M.2 n)

end
end Spec

section
variable {E Kc : Type} [Field E]

theorem wideJ_sub : Spec.wideJ_sub E Kc := by
  classical
  intro a X Rd Rd' Rr Rr' own Mk _ _ val h1 h2 h3 hf
  have h := MaskFact.JCl.conseq
    (a.wideFact Rd Rr own Mk val) (a.S.Msg × (∀ o, Option (a.S.om o).Rnd) × a.Wp)
    (fun k => (a.S.cut Rd' k.1, (fun o => if Rr' o then k.2.1 o else none), k.2.2))
    (fun M k => (a.S.ow own (val M) k.1, k.2)) (fun M k => by
      refine Prod.ext (funext fun o => funext fun j => ?_) rfl
      show (if Rd' ⟨o, j⟩ then (if own ⟨o, j⟩ then val M ⟨o, j⟩ else k.1 o j) else 0) =
        if own ⟨o, j⟩ then val M ⟨o, j⟩ else (if Rd' ⟨o, j⟩ then k.1 o j else 0)
      by_cases ho : own ⟨o, j⟩
      · rw [if_pos (h3 _ ho), if_pos ho, if_pos ho]
      · rw [if_neg ho, if_neg ho]) hf
  have e : (fun w : a.J.W =>
        ((a.S.cut Rd' ((a.wideFact Rd Rr own Mk val).kc w).1,
          (fun o => if Rr' o then ((a.wideFact Rd Rr own Mk val).kc w).2.1 o else none),
          ((a.wideFact Rd Rr own Mk val).kc w).2.2) :
          a.S.Msg × (∀ o, Option (a.S.om o).Rnd) × a.Wp)) =
      a.S.wide a.Wp Rd' Rr' := by
    funext w
    refine Prod.ext (funext fun o => funext fun j => ?_) (Prod.ext (funext fun o => ?_) rfl)
    · show (if Rd' ⟨o, j⟩ then (if Rd ⟨o, j⟩ then a.S.msgs w.1 o j else 0) else 0) =
        if Rd' ⟨o, j⟩ then a.S.msgs w.1 o j else 0
      by_cases hr : Rd' ⟨o, j⟩
      · rw [if_pos hr, if_pos hr, if_pos (h1 _ hr)]
      · rw [if_neg hr, if_neg hr]
    · show (if Rr' o then (if Rr o then some (w.1 o).2 else none) else none) =
        if Rr' o then some (w.1 o).2 else none
      by_cases hr : Rr' o
      · rw [if_pos hr, if_pos hr, if_pos (h2 _ hr)]
      · rw [if_neg hr, if_neg hr]
  rw [e] at h
  exact h

theorem wideJ_join : Spec.wideJ_join E Kc := by
  classical
  intro a X Rd Rr own₁ own₂ M₁ M₂ _ _ _ _ v₁ v₂ h1 h2
  have h := MaskFact.JCl.join (X := X) (a.S.Msg × (∀ o, Option (a.S.om o).Rnd) × a.Wp)
    (a.S.wide a.Wp Rd Rr) M₁ M₂ (fun M k => (a.S.ow own₁ (v₁ M) k.1, k.2))
    (fun M k => (a.S.ow own₂ (v₂ M) k.1, k.2)) h1 h2
  have e : (fun (M : M₁ × M₂) (k : a.S.Msg × (∀ o, Option (a.S.om o).Rnd) × a.Wp) =>
        ((a.S.ow own₁ (v₁ M.1) (a.S.ow own₂ (v₂ M.2) k.1, k.2).1,
          (a.S.ow own₂ (v₂ M.2) k.1, k.2).2) : a.S.Msg × (∀ o, Option (a.S.om o).Rnd) × a.Wp)) =
      fun M k =>
        (a.S.ow (fun n => own₁ n ∨ own₂ n) (fun n => if own₁ n then v₁ M.1 n else v₂ M.2 n) k.1,
          k.2) := by
    funext M k
    refine Prod.ext (funext fun o => funext fun j => ?_) rfl
    by_cases a1 : own₁ ⟨o, j⟩ <;> by_cases a2 : own₂ ⟨o, j⟩ <;> simp [Sig.ow, a1, a2]
  rw [e] at h
  exact h

theorem wideJ_pair : Spec.wideJ_pair E Kc := by
  intro a X Rd₁ Rd₂ Rd Rr₁ Rr₂ Rr own₁ own₂ M₁ M₂ _ _ _ _ v₁ v₂ hd hr ho h1 h2
  exact wideJ_join a X Rd Rr own₁ own₂ M₁ M₂ v₁ v₂
    (wideJ_sub a X Rd₁ Rd Rr₁ Rr own₁ M₁ v₁ (fun n h => (hd n h).1) (fun o h => (hr o h).1)
      (fun n h => ho n (Or.inl h)) h1)
    (wideJ_sub a X Rd₂ Rd Rr₂ Rr own₂ M₂ v₂ (fun n h => (hd n h).2) (fun o h => (hr o h).2)
      (fun n h => ho n (Or.inr h)) h2)

end
end Cb
