-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/AsmErr.lean: the assembled lookup's errors and numbers of values, read by the
library's own readers, are the
list Λ, if each stretch's are its share.

It imports Cb/Pv/KeyLookup/Asm.lean, Cb/Pv/KeyLookup/Lam.lean and the library's readers
(`Iop.Err.toList`, `Iop.Shape.chalList`: Ior/KnowCollRulesChainErr.lean); no file of the port.

  `BkK.IsL b l`   the block's errors are the counts c of the rows l, and the numbers of values of
                  its verifier's messages are
                  their n, both in order.
  `isL_seq`, `isL_postM`, `isL_preM`   the rules: blocks in a row; steps without rounds.
  `B.Lists q`     what is asked of the letters: each block `IsL` its share of Λ.
  `lam1_isL`      B.Lists q ⇒ B.lam1 `IsL` (Lam q A.toPub).
  `plainList s` defined in this file: round by round the number of values of the prover's message in
                  the clear (`Nat.card r.Plain`).
  `IsS q b l`     that list is q ^ sent, row by row: in each round the prover's message in the clear
                  has as many values as `sent` scalars have.
  `B.Sents q`, `lam1_isS`   the like of `Lists`, `lam1_isL` for that column.
Not claimed: that blocks with `Lists` or `Sents` exist; anything on the column «kind» (a name: no
shape has it).

-/
import Cb.Pv.KeyLookup.Asm
import Cb.Pv.KeyLookup.Lam
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

/-- The block's errors and numbers of values are those of the rows. -/
def IsL {X₁ X₂ : Type} {Ex : ExtSpec} (b : BkK X₁ X₂ Ex) (l : List LRow) : Prop :=
  b.e.toList = l.map (·.c) ∧ b.R.shape.chalList = l.map (·.n)

/-- The numbers of values of the prover's messages in the clear, in order. -/
noncomputable def plainList (s : Shape) : List ℕ := s.map fun r => Nat.card r.Plain

/-- In each round the prover's message in the clear has as many values as `sent` scalars have. -/
def IsS {X₁ X₂ : Type} {Ex : ExtSpec} (q : ℕ) (b : BkK X₁ X₂ Ex) (l : List LRow) : Prop :=
  plainList b.R.shape = l.map fun r => q ^ r.sent

section
variable {X₁ X₂ X₃ : Type} {Ex : ExtSpec}

theorem isL_seq {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {l l' : List LRow} (ha : IsL a l) (hb : IsL b
    l') :
    IsL (a.seq b) (l ++ l') :=
  ⟨(Err.toList_app a.e b.e).trans (by rw [ha.1, hb.1, List.map_append]),
    (Shape.chalList_append a.R.shape b.R.shape).trans (by rw [ha.2, hb.2, List.map_append])⟩

theorem isL_postM {b : BkK X₁ X₂ Ex} {l : List LRow} (φ : X₂ → X₃) (h : IsL b l) : IsL (b.postM φ) l
    := h

theorem isL_preM {b : BkK X₂ X₃ Ex} {l : List LRow} (φ : X₁ → X₂) (h : IsL b l) : IsL (b.preM φ) l
    := h

theorem isS_seq {q : ℕ} {a : BkK X₁ X₂ Ex} {b : BkK X₂ X₃ Ex} {l l' : List LRow} (ha : IsS q a l)
    (hb : IsS q b l') : IsS q (a.seq b) (l ++ l') := by
  show plainList (a.R.shape ++ b.R.shape) = _
  unfold plainList
  rw [List.map_append, List.map_append]
  exact congrArg₂ (· ++ ·) ha hb

theorem isS_postM {q : ℕ} {b : BkK X₁ X₂ Ex} {l : List LRow} (φ : X₂ → X₃) (h : IsS q b l) :
    IsS q (b.postM φ) l := h

theorem isS_preM {q : ℕ} {b : BkK X₂ X₃ Ex} {l : List LRow} (φ : X₁ → X₂) (h : IsS q b l) :
    IsS q (b.preM φ) l := h

end

namespace Bks
variable {E : Type} [Field E] [Fintype E] {A : Dat E} {Ex : ExtSpec} (B : Bks A Ex)

/-- What is asked of the letters. -/
structure Lists (q : ℕ) : Prop where
  head  : IsL B.head (lamHead q A.toPub)
  parts : IsL B.parts (lamParts q A.toPub)
  join  : IsL B.join (lamJoin q A.toPub)
  keys  : IsL B.keys (lamKeys q A.toPub)
  table : IsL B.table (lamTable q A.toPub)
  clo   : IsL B.clo (lamClo q A.toPub)
  zero  : IsL B.zero (lamZero q A.toPub)
  bits  : IsL B.bits (lamBits q A.toPub)

/-- The lookup's errors and numbers of values are the list. -/
theorem lam1_isL (q : ℕ) (h : B.Lists q) : IsL B.lam1 (Lam q A.toPub) :=
  isL_postM A.rd (isL_seq (isL_seq (isL_seq (isL_seq (isL_seq (isL_seq (isL_seq h.head h.parts)
      h.join)
    h.keys) h.table) h.clo) h.zero) h.bits)

/-- What is asked of the letters, for the column «sent»; f: the form in which a row is read (the
identity, or `LRow.short`). -/
structure Sents (q : ℕ) (f : LRow → LRow) : Prop where
  head  : IsS q B.head ((lamHead q A.toPub).map f)
  parts : IsS q B.parts ((lamParts q A.toPub).map f)
  join  : IsS q B.join ((lamJoin q A.toPub).map f)
  keys  : IsS q B.keys ((lamKeys q A.toPub).map f)
  table : IsS q B.table ((lamTable q A.toPub).map f)
  clo   : IsS q B.clo ((lamClo q A.toPub).map f)
  zero  : IsS q B.zero ((lamZero q A.toPub).map f)
  bits  : IsS q B.bits ((lamBits q A.toPub).map f)

/-- The lookup's messages in the clear are the list's column «sent». -/
theorem lam1_isS (q : ℕ) (f : LRow → LRow) (h : B.Sents q f) : IsS q B.lam1 ((Lam q A.toPub).map f)
    := by
  have := isS_postM A.rd (isS_seq (isS_seq (isS_seq (isS_seq (isS_seq (isS_seq (isS_seq h.head
      h.parts)
    h.join) h.keys) h.table) h.clo) h.zero) h.bits)
  simpa [Lam, List.map_append] using this

end Bks
end Lk6

#print axioms Lk6.Bks.lam1_isL
#print axioms Lk6.Bks.lam1_isS
