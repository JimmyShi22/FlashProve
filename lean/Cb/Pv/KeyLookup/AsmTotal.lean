-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/AsmTotal.lean: the assembled lookup's verifier never rejects, if no stretch's does.

Why it is wanted. Knowledge soundness holds idly of a reduction that rejects every transcript. This
file says of the lookup with parts that its verifier puts out
a new statement at every state, every oracle string and every transcript: what it has to say against
a false claim it says in the rows and claims that it puts out.

It imports Cb/Pv/KeyLookup/Asm.lean and the library (`IOR.seq_out`); no file of the port.

  `Total R`       for all x y τ there is an x' with R.out x y τ = some x'.
  `Total.seq`, `Total.post`, `Total.pre`, `Total.draw`   the rules: reductions in a row; a total map
                    behind or before a reduction; a draw.
  `B.Totals`      what is asked of the letters: each of the eight blocks is `Total`.
  `lam1_total`    B.Totals ⇒ B.lam1.R is `Total`.
Not claimed: that blocks with `Totals` exist (files of their own); anything on what is put out.

-/
import Cb.Pv.KeyLookup.Asm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

/-- The verifier never rejects. -/
def Total {X₁ X₂ : Type} {E₁ E₂ : ExtSpec} (R : IOR X₁ E₁ X₂ E₂) : Prop :=
  ∀ x y τ, ∃ x', R.out x y τ = some x'

theorem Total.seq {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃
    E₃}
    (h₁ : Total R₁) (h₂ : Total R₂) : Total (R₁.seq R₂) := by
  intro x y τ
  obtain ⟨x₂, hx⟩ := h₁ x y (Tr.fst τ)
  obtain ⟨x₃, hx'⟩ := h₂ x₂ (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ)
  exact ⟨x₃, by rw [seq_out, hx]; exact hx'⟩

theorem Total.post {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R : IOR X₁ E₁ X₂ E₂} (h : Total R)
    (φ : X₂ → X₃) (g : ExtMap E₂ E₃) : Total (R.post (fun x => some (φ x)) g) := by
  intro x y τ
  obtain ⟨x₂, hx⟩ := h x y τ
  exact ⟨φ x₂, by
    show (R.out x y τ).bind (fun x => some (φ x)) = some (φ x₂)
    rw [hx]
    rfl⟩

theorem Total.pre {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R : IOR X₂ E₂ X₃ E₃} (h : Total R)
    (φ : X₁ → X₂) (g : ExtMap E₁ E₂) : Total (R.pre (fun x => some (φ x)) g) := by
  intro x y τ
  obtain ⟨x₃, hx⟩ := h (φ x) (g.map y) τ
  exact ⟨x₃, hx⟩

theorem Total.draw {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec)
    :
    Total (IOR.draw D nx E) := fun _ _ _ => ⟨_, rfl⟩

section
variable {X₁ X₂ X₃ : Type} {Ex : ExtSpec}

theorem total_seq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} (ha : Total a.R) (hb : Total b.R) :
    Total (a.seq b).R := ha.seq hb

theorem total_postM {b : BkK X₁ X₂ Ex} (φ : X₂ → X₃) (h : Total b.R) : Total (b.postM φ).R :=
  h.post φ (ExtMap.id Ex)

theorem total_preM {b : BkK X₂ X₃ Ex} (φ : X₁ → X₂) (h : Total b.R) : Total (b.preM φ).R :=
  h.pre φ (ExtMap.id Ex)

theorem total_drawK {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (err : ℕ) :
    Total (drawK D nx Ex err).R := Total.draw D nx Ex

theorem total_chain (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (h : ∀ l, Total (b l).R) :
    ∀ n, Total (BkK.chain X b n).R
  | 0 => h 0
  | n + 1 => total_seq (total_chain X b h n) (h (n + 1))

end

namespace Bks
variable {E : Type} [Field E] [Fintype E] {A : Dat E} {Ex : ExtSpec} (B : Bks A Ex)

/-- What is asked of the letters. -/
structure Totals : Prop where
  head  : Total B.head.R
  parts : Total B.parts.R
  join  : Total B.join.R
  keys  : Total B.keys.R
  table : Total B.table.R
  clo   : Total B.clo.R
  zero  : Total B.zero.R
  bits  : Total B.bits.R

/-- The lookup's verifier never rejects. -/
theorem lam1_total (h : B.Totals) : Total B.lam1.R :=
  total_postM A.rd (total_seq (total_seq (total_seq (total_seq (total_seq (total_seq (total_seq
      h.head
    h.parts) h.join) h.keys) h.table) h.clo) h.zero) h.bits)

end Bks
end Lk6
