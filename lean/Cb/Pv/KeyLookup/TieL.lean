-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/TieL.lean: at the library's own sumcheck the errors and the sizes of the challenge
sets of the draw and the fused tie (Cb/Pv/KeyLookup/TieM.lean), read by the library's `Err.toList`
and `Shape.chalList`, are the columns c and n of the rows `lamHead` of the list of rounds
(Cb/Pv/KeyLookup/Lam.lean). The draw and the tie together are called the head.

It imports no file of the program (OnBytes/Iop, OnBytes/Params, ...). Terms: lean/GLOSSARY.md.

Main names:
  `flat_succ`: a list repeated k + 1 times is the list, then k times the list.
  `head_isL`: n + 2 = pl ⇒ `IsL (A.headK L (PscLtK.lib E Ex) n) (lamHead q A.toPub)`, q the number
  of elements of the field.
Limits: the one condition is n + 2 = pl, a public number. Not said: the column kind; the scalars
sent (Cb/Pv/KeyLookup/TieSent.lean); anything on the program.

-/
import Cb.Pv.KeyLookup.TieM
import Cb.Pv.KeyLookup.AsmErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

theorem flat_succ (c : List ℕ) (k : ℕ) :
    (List.range (k + 1)).flatMap (fun _ => c) = c ++ (List.range k).flatMap fun _ => c := by
  rw [flat_rep, flat_rep, List.replicate_succ, List.flatten_cons]

/-- The head's errors and numbers of values are its share of the list. -/
theorem head_isL {E : Type} [Field E] [Fintype E] (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec)
    (n : ℕ) (hn : n + 2 = A.pl) :
    IsL (A.headK L (PscLtK.lib E Ex) n) (lamHead (Fintype.card E) A.toPub) := by
  obtain ⟨h1, h2⟩ := head_ll A L Ex n
  have hp : A.pl - 2 = n := by omega
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · unfold lamHead
    rw [hp, flat_succ]
    simp [psc, List.map_flatMap]
  · unfold lamHead
    rw [hp, flat_succ]
    simp [psc, List.map_flatMap]

end Lk6

#print axioms Lk6.head_isL
