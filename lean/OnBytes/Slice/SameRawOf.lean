-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SameRawOf.lean: two of the three parts of the join whose readings go by leaves, and
whose implementations agree on bit strings, read one raw string under every root.

OnBytes/Slice/PartO.lean joins three checkers over one random oracle. It asks of two parts that they
read one raw string under every root, off every log in which no two strings have one answer
(`SameRaw`). There a part is a record over the one oracle alone (`PartO`); a part with an interface,
a wiring and an implementation of the typed oracles (`Part`, OnBytes/Slice/JoinThree.lean) gives one
(`Part.toO`). This file gives `SameRaw` of two such from what OnBytes/Slice/SameAt.lean proves place
by place. A raw string (OnBytes/Slice/Raw.lean) is a function on the natural numbers, so that the
strings of two interfaces, which have two types, can be compared.

Main theorems.
 `sameRaw_of`        `SameRaw s₁.toO s₂.toO`, if both readings go by leaves (`Reading.ByLeaves`),
                     both implementations have one block for a leaf's and a vertex's answer
                     (`OneBlock`), they agree on bit strings as to what the two `keep` make of leaf
                     queries (`SameRead`), the two wirings have one depth, the two ways of building
                     a string agree where their inputs do, and the two strings have one length.
 `sameRaw_of_build`  the same for two readings that build their strings as their wirings do
                     (`build`), with the hypothesis on the two `build` in the form of `extEnc_same`
                     (OnBytes/Slice/SameStored.lean).

What is not claimed. That any two parts meet the six hypotheses: all are hypotheses here.
Of a `PartO` that does not come from a `Part` nothing is
said. No probability: the log is fixed in `SameRaw`, and that no two of its strings have one answer
stands there as a condition. Nothing on any protocol, language, checker or hash function.

-/
import OnBytes.Slice.JoinThree
import OnBytes.Slice.SameAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

variable {lam : ℕ} {γ γ' Sg : Type}

/-- **Two parts read one raw string under every root**, off every log in which no two strings have
one answer. The symbols of the first part are matched with those of the second through the shared
type of symbols: `s₁.u` and then `s₂.u` backwards. Asked: `OneBlock` of both implementations; both
readings go by leaves; `SameRead` at what the two `keep` make of leaf queries, the first matched;
one depth of the two wirings; `hg`: the two ways of building a string agree at equal places where
their inputs agree at all places; `hn`: the two strings have one length. All six are hypotheses. No
probability. -/
theorem sameRaw_of (s₁ : Part lam γ Sg) (s₂ : Part lam γ' Sg)
    (h₁ : OneBlock s₁.m) (h₂ : OneBlock s₂.m)
    {keep₁ : ℕ → LeafIn s₁.L → Option s₁.L.Symbol} {keep₂ : ℕ → LeafIn s₂.L → Option s₂.L.Symbol}
    {g₁ : (ℕ → Option s₁.L.Symbol) → Fin s₁.L.wordLength → s₁.L.Symbol}
    {g₂ : (ℕ → Option s₂.L.Symbol) → Fin s₂.L.wordLength → s₂.L.Symbol}
    (B₁ : s₁.J.R.ByLeaves keep₁ g₁) (B₂ : s₂.J.R.ByLeaves keep₂ g₂)
    (h : SameRead (fun j q => (keep₁ j q).map (s₁.u.trans s₂.u.symm)) keep₂ s₁.m s₂.m)
    (hd : s₁.W.depth = s₂.W.depth)
    (hg : ∀ (φ₁ : ℕ → Option s₁.L.Symbol) (φ₂ : ℕ → Option s₂.L.Symbol),
      (∀ j, (φ₁ j).map (s₁.u.trans s₂.u.symm) = φ₂ j) →
      ∀ q₁ q₂, q₁.val = q₂.val → (s₁.u.trans s₂.u.symm) (g₁ φ₁ q₁) = g₂ φ₂ q₂)
    (hn : s₁.L.wordLength = s₂.L.wordLength) : SameRaw s₁.toO s₂.toO := by
  intro σ hσ cm
  show rawOf s₁.u (s₁.str σ cm) = rawOf s₂.u (s₂.str σ cm)
  refine rawOf_congr hn s₁.u s₂.u _ _ fun q₁ q₂ hq => ?_
  have e := Reading.at_same_of s₁.W s₂.W h₁ h₂ s₁.J.R s₂.J.R B₁ B₂ h σ hσ cm hd hg q₁ q₂ hq
  show s₁.u (s₁.J.R.at s₁.W (singleTr s₁.m σ) cm q₁) =
    s₂.u (s₂.J.R.at s₂.W (singleTr s₂.m σ) cm q₂)
  rw [← e, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- `sameRaw_of` for two readings that build their strings as their wirings do. In the place of `hg`
stands `hb`, in the form of `extEnc_same`: the two fillings (`build`) agree at equal places where
their inputs agree at equal places. All six are hypotheses. No probability. -/
theorem sameRaw_of_build (s₁ : Part lam γ Sg) (s₂ : Part lam γ' Sg)
    (h₁ : OneBlock s₁.m) (h₂ : OneBlock s₂.m)
    {keep₁ : ℕ → LeafIn s₁.L → Option s₁.L.Symbol} {keep₂ : ℕ → LeafIn s₂.L → Option s₂.L.Symbol}
    (B₁ : s₁.J.R.ByLeaves keep₁ fun φ => s₁.W.B.ext.build fun q => φ q.val)
    (B₂ : s₂.J.R.ByLeaves keep₂ fun φ => s₂.W.B.ext.build fun q => φ q.val)
    (h : SameRead (fun j q => (keep₁ j q).map (s₁.u.trans s₂.u.symm)) keep₂ s₁.m s₂.m)
    (hd : s₁.W.depth = s₂.W.depth)
    (hb : ∀ (f₁ : Fin s₁.L.wordLength → Option s₁.L.Symbol) (f₂ : Fin s₂.L.wordLength → Option s₂.L.Symbol),
      (∀ q₁ q₂, q₁.val = q₂.val → (f₁ q₁).map (s₁.u.trans s₂.u.symm) = f₂ q₂) →
      ∀ q₁ q₂, q₁.val = q₂.val →
        (s₁.u.trans s₂.u.symm) (s₁.W.B.ext.build f₁ q₁) = s₂.W.B.ext.build f₂ q₂)
    (hn : s₁.L.wordLength = s₂.L.wordLength) : SameRaw s₁.toO s₂.toO :=
  sameRaw_of s₁ s₂ h₁ h₂ B₁ B₂ h hd
    (fun φ₁ φ₂ hφ => hb _ _ fun p₁ p₂ hp => by rw [hφ p₁.val, hp]) hn

end OnBytes.Slice
