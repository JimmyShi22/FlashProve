-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Front.lean: what the proved chain of attention's own rounds claims at its
first
joint, at the library's letters, in the letters of Johnson/Road/Rows/AttStartBase.lean
(att_rel_base,
att_ord_base: premises own1, own2).

The chain's knowledge soundness (Cb/Pv/Att/OwnAt.lean: ownAt_knowAt) goes from "Dn and Todo" to
"Last Dn":
the extracted witness has Todo. Its two last clauses are families that vanish on cubes
(Cb/Pv/Att/Mean/Turned.lean: scoreIdnG, bitIdnT).

Main names:
  `own2_of_todo`: Todo gives the identities at2 at every valid place: own2, at D := P.D, t := P.tOf
    m.
  `own1_of_todo`: Todo and P.D.lT ≤ 2 ^ P.kap give the identities at1: own1. (At kap = 4: a position
    has
    at most 16 bits.)

The proofs are the library's (Cb/Pv/Att/End/Seam.lean: att_todo, at2_of_cubeG): the two statements
here give them the letters
of AttStartBase.lean, own2 without the premise on the bits.
Not here: the identities at3 (the denominator is the row's sum at every head and position): Todo has
them
at one point alone, the lookup's · the keys' clause: the lookup's own · how the cells are read off
the
committed symbols: P.rd and P.msg are parameters here.
Sources: Cb/Pv/Att/End/Seam.lean (att_todo); Cb/Pv/Att/OwnAt.lean (theMeans, ownAt_todo);
Mean/Turned.lean; Inst/Model/Att/Trace.lean (Idn,
Idn.Valid, idnVal); Index.lean (Dim, T_eq).
Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.End.Seam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Cb.Pv.Att Inst.Model Inst.Model.AttSeg

variable {K M X : Type} [Field K] [Fintype K]

/-- **own2**: the identities at2 vanish at every valid place. -/
theorem own2_of_todo (P : OwnPar K M X) (x : X) (m : M) (h : (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m)
    (b g i : ℕ) (hv : (Idn.at2 b g i).Valid P.D) : idnVal P.D (P.tOf m) (.at2 b g i) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h1, _⟩ := (ownAt_todo P x m).1 h
  exact at2_of_cubeG P.D (P.tOf m) (fun b hb Y hY => h1 ⟨b, hb⟩ Y hY) b g i hv

/-- **own1**: the identities at1 vanish at every valid place, where kap variables number all bits of
a position. -/
theorem own1_of_todo (P : OwnPar K M X) (hk : P.D.lT ≤ 2 ^ P.kap) (x : X) (m : M)
    (h : (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m) (k b g i : ℕ) (hv : (Idn.at1 k b g i).Valid P.D) :
    idnVal P.D (P.tOf m) (.at1 k b g i) = 0 :=
  (Cb.Pv.Att.End.att_todo P hk x m h).1 k b g i hv

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.own2_of_todo
#print axioms VerifiableInference.Desc.First.Att.P.own1_of_todo
