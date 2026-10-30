-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelRowsE.lean: rows cost nothing, for every code with the laws (`C.Laws`, Cb/Ld/LdRel.lean),
read under a transformation: the count of exceptional values for two words is a count for tables of
any number of rows. At every radius. No extension field.

A code read under a transformation (`LdCode`, Cb/Ld/LdRel.lean) has native words; its transformation
`C.T` makes long words of them. `C.MCAat e bad` (same file), mutual correlated agreement on lines at
the radius e, as a count: for all native words f₀, f₁ at most `bad` values θ of the field E are
exceptional, that is: on some set S of all but at most e long positions C.T f₀ + θ • C.T f₁ agrees
with the transform of a codeword, while C.T f₀ and C.T f₁ do not both agree on S with transforms of
codewords. `C.MCArows e bad` (Cb/Ld/LdRelRows.lean): (C.il R).MCAat e bad for every finite set R of
rows; `C.il R` is the interleaving: rows named by R under one code, so its words are tables. The
laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
`C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native words
to long words, are linear over E; the encoder sends only the zero message with zero randomness to
zero; and, for every long position x, any two native words that agree at the native positions
`C.src x` have the same long symbol at x. Here they are a premise of the statement.

One statement (`Cb.Spec.ld_rows_free`) and its proof: an application of Cb/Ld/LdRelRowsEAbs.lean
(`Spec.rows_free_abs`); before it a definition (`LdCode.onSub`) and a lemma (`onCode_il`) that the
proof uses. Generic: any finite field, any code with the laws. Nothing assumed beyond the hypotheses
of the statements and whatever the arguments hold as proofs.

Main names:
  `Spec.ld_rows_free`: C.Laws → C.MCAat e bad → C.MCArows e bad.
  With `Cb.ld_rows_self` (the converse: one row; Cb/Ld/LdRelRowsProofs.lean) the two notions are the
    same for a code with the laws. No distance, no list, no structure of the code enters; of the
    laws only "the encoder is linear" and "the transformation is linear" are used.

Where it comes from. This protocol's technical report (lean/CREDITS.md) proves, for every linear
code with symbols in E, every number of rows and every radius, that the agreement error on lines of
the interleaving equals the code's. The proof's idea is the description's (credit: lean/CREDITS.md):
combine the rows with one vector of coefficients that lies in none of the at most |E| proper
subspaces "both combinations agree with codewords on the set fixed for θ". That it holds for symbols
with several coordinates and under a transformation is ours, not the description's.

What it is good for. The statement on codes (Cb/Gen/CodeListRS.lean) speaks of
two words. The step to tables went through an extension field (Cb/Gen/CodeListRSF.lean:
rows_cost_nothingF), so the hypothesis had to speak of all finite extensions of the base field. With
this lemma's core it can be cut down to one field: Cb/Gen/CodeListRSAt.lean.

Limits: this file does not say that any code has MCAat with a useful count beyond a third of the
distance (below a third: `Spec.ld_mca_third`, Cb/Ld/LdBaseCode.lean). It says nothing on other
generators than the line (1, θ).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelRowsProofs
import Cb.Ld.LdRelRowsEAbsProofs

set_option autoImplicit false

namespace Cb
open Prob

/-- States that rows cost nothing: for a code C with the laws, `C.MCAat e bad` gives
`C.MCArows e bad`. -/
def Spec.ld_rows_free : Prop :=
  ∀ (E P : Type) [Field E] [Finite E] [Fintype P] (C : LdCode E P) (e bad : ℕ),
    C.Laws → C.MCAat e bad → C.MCArows e bad

/-- The long words that agree on S with the transform of a codeword: a subspace, by the laws
`hL`. -/
def LdCode.onSub {E P : Type} [Field E] (C : LdCode E P) (hL : C.Laws) (S : Finset P) :
    Submodule E (P → C.Aa → E) where
  carrier := {g | C.OnCode g S}
  zero_mem' := ⟨0, 0, fun x _ => by
    have h1 : C.enc 0 0 = 0 := hL.encLin.map_zero
    have h2 : C.T 0 = 0 := hL.tLin.map_zero
    rw [h1, h2]⟩
  add_mem' := fun {a b} ha hb => by
    have := onCode_line hL 1 1 ha hb
    rwa [one_smul, one_smul] at this
  smul_mem' := fun c a ha => by
    have := onCode_line hL c 0 ha ha
    rwa [zero_smul, add_zero] at this

/-- A long word of the interleaved code agrees with the transform of a codeword on S if and only if
each of its rows does. -/
theorem onCode_il {E P : Type} [Field E] (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R]
    (G : P → (C.il R).Aa → E) (S : Finset P) :
    (C.il R).OnCode G S ↔ ∀ i, C.OnCode (fun x α => G x (i, α)) S := by
  constructor
  · rintro ⟨m, r, h⟩ i
    exact ⟨fun j => m (i, j),
      fun q => r (i, q),
      fun x hx => funext fun α => congrFun (h x hx) (i, α)⟩
  · intro h
    choose m r hmr using h
    exact ⟨fun n => m n.1 n.2,
      fun n => r n.1 n.2,
      fun x hx => funext fun α => congrFun (hmr α.1 x hx) α.2⟩

theorem ld_rows_free : Spec.ld_rows_free := by
  intro E P _ _ _ C e bad hL h R _ _ f₀ f₁
  obtain ⟨w, hw⟩ := rows_free_abs E R (P → C.Aa → E) (Finset P)
    (fun S => Fintype.card P ≤ S.card + e) (C.onSub hL)
    (fun i => C.T (C.rowW f₀ i)) (fun i => C.T (C.rowW f₁ i))
  have hT : ∀ f : (C.il R).Word, C.T (∑ i, w i • C.rowW f i) = ∑ i, w i • C.T (C.rowW f i) := by
    intro f
    have e1 : C.T (∑ i, w i • C.rowW f i) = hL.tLin.mk' C.T (∑ i, w i • C.rowW f i) := rfl
    rw [e1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  refine le_trans (cnt_mono fun θ hθ => ?_) (h (∑ i, w i • C.rowW f₀ i) (∑ i, w i • C.rowW f₁ i))
  obtain ⟨S, hS, h1, h2⟩ := hθ
  obtain ⟨S', hS', h3, h4⟩ :=
    hw θ ⟨S, hS,
        fun i => ((onCode_il C R _ S).1 h1 i),
        fun hc => h2 ⟨(onCode_il C R _ S).2 hc.1, (onCode_il C R _ S).2 hc.2⟩⟩
  refine ⟨S', hS', ?_, ?_⟩
  · rw [hT, hT]
    exact h3
  · rw [hT, hT]
    exact h4

end Cb
