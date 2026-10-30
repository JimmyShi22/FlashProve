-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbFin.lean: bookkeeping for countability of message types: a condition on codes
(each symbol has finitely many coordinates: `LdCode.FinNS`, Cb/Obj/LdObjectCtb.lean) is kept by the
ways of building a code: rows interleaved; two codes side by side; a family of codes; a code with
encoder (`Code.Enc`); a reading (`Reading`, Cb/Gen/CodeRep.lean) with its rows.

Five theorems. The first three carry `FinNS` from the parts to the whole; the last two have no
hypothesis beside their instance arguments and, in `finNS_reading`, the instance field
`finP : Fintype P` of `T : Reading C`. Generic: all codes.

Why a file of its own: generic files use them, and so does the file on toys
Cb/Obj/LdObjectCtbToy.lean: here they import no toy.

Limits: this file says nothing on a particular code.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtbPre
import Cb.Ld.LdRelRep

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

section Codes
variable {E P : Type}

theorem finNS_il (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R] (h : C.FinNS) :
    (C.il R).FinNS := fun p => by
  haveI := h p
  exact inferInstanceAs (Finite (R × C.NS p))

theorem finNS_pair (C₁ C₂ : LdCode E P) (h₁ : C₁.FinNS) (h₂ : C₂.FinNS) :
    (C₁.pair C₂).FinNS := fun p => match p with
  | .inl p => h₁ p
  | .inr p => h₂ p

theorem finNS_fam {A : Type} [Fintype A] [DecidableEq A]
    (C : A → LdCode E P) (h : ∀ a, (C a).FinNS) : (LdCode.fam C).FinNS :=
  fun p => h p.1 p.2

theorem finNS_ofEnc {F : Type} [Field F] [Field E] [Algebra F E]
    (C₀ : Code.Enc F) (pos : P → Fin C₀.n) :
    (LdCode.ofEnc (E := E) C₀ pos).FinNS :=
  fun _ => inferInstanceAs (Finite Unit)

/-- a family of codes with rows, under a reading -/
theorem finNS_reading {F A : Type} [Field F] [Fintype A] [DecidableEq A]
    {C : A → Code.Enc F} (T : Reading C) [Field E] [Algebra F E] (R : A → Type)
    [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)] : (T.ld E R).FinNS :=
  finNS_fam _ fun _ => finNS_il _ _ (finNS_ofEnc _ _)

end Codes

end Cb
