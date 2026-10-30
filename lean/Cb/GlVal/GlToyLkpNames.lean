-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyLkpNames.lean: abbreviations: a small test instance of the lookup sub-protocol, which
is defined for any finite field, taken at the cubic extension E of the field with
p = 2^64 - 2^32 + 1 elements.

Abbreviations and restatements; nothing new is proved.
Cb/Ld/LdLkpToyE.lean and Cb/Ld/LdLkpToyMaskE.lean have the toy lookup and its masked item for any
finite field, with the field as an explicit argument (namespace `Cb.LkpToyE`). Toy files over
`ZMod 101` cite Cb/Ld/LdLkpToy.lean, Cb/Ld/LdLkpToyMask.lean (namespace `Cb.LkpToy`: no argument).
Here: namespace `Cb.Gl.LkpToy`: the same names, no argument, at E = F[x] / (x^3 - 2), so that a toy
file that cites these names can be stated over this field under the same names.
What each name of this file is: Cb/Ld/LdLkpToyE.lean, Cb/Ld/LdLkpToyMaskE.lean.

Main names:
  `w57`, `w55`, `w56`: the keys (5, 7), each entry of the table once; the keys (5, 5), the first
    entry twice; the keys (5, 6); the table (`toyA.tab`) is (5, 7).
  `in57`, `in55`, `out56`: `toyA.lk.inP toyA.ValidMu ()` of the first two; not `toyA.lk.inR ()` of
    the third.
  `adm`: `toyA.H.lkb.Adm pK` (there for every number above 6; `pK`, the characteristic p:
    Cb/GlVal/GlToyNum.lean).

Limits: not here, among others: the oracle message of Cb/Ld/LdLkpToy.lean (`nuR`, `padR`, `toyM`,
`Sg`, `toyMsg`) and what is stated of it (`errs`, `chals`, `small`, `rounds`, `nrows`): over any
field these take a signature and a reading as arguments. `valid_of` is not here either.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpToyMaskE
import Cb.GlVal.GlToyNum

set_option autoImplicit false

namespace Cb.Gl
namespace LkpToy
open Iop Prob Hiop Cb.LdLkp

noncomputable section

abbrev Mk : Type := LkpToyE.Mk E
abbrev J0 : Type := LkpToyE.J0 E
abbrev Rw : Type := LkpToyE.Rw E
abbrev Nm : Type := LkpToyE.Nm E
abbrev kAt (b : Bool) : Rw := LkpToyE.kAt b
abbrev bitAt (u j : Bool) : Rw := LkpToyE.bitAt u j
abbrev mAt (i : Mk) : Rw := LkpToyE.mAt i
abbrev idle : Rw := LkpToyE.idle
abbrev toyA : LkAsm2 E := LkpToyE.toyA E
abbrev plAt : (Bool ⊕ (Bool × Bool)) ⊕ Mk → toyA.J := LkpToyE.plAt E
abbrev iN : Nm → toyA.J := LkpToyE.iN E
abbrev wit (k : Bool → E) (b : Bool × Bool → E) : toyA.J → E := LkpToyE.wit E k b
abbrev w57 : toyA.J → E := LkpToyE.w57 E
abbrev w55 : toyA.J → E := LkpToyE.w55 E
abbrev w56 : toyA.J → E := LkpToyE.w56 E

theorem adm : toyA.H.lkb.Adm pK := LkpToyE.adm E pK (lt_pK (by norm_num))
theorem plAt_eq (x : (Bool ⊕ (Bool × Bool)) ⊕ Mk) : plAt x = Sum.inl (Sum.map id Sum.inl x) :=
  LkpToyE.plAt_eq E x
theorem plAt_inj : Function.Injective plAt := LkpToyE.plAt_inj E
theorem plAt_ne (x : (Bool ⊕ (Bool × Bool)) ⊕ Mk) : plAt x ≠ idle ∧ plAt x ≠ .inr () :=
  LkpToyE.plAt_ne E x
theorem iN_inj : Function.Injective iN := LkpToyE.iN_inj E
theorem places : toyA.PlacesIn (fun j => j ∈ Set.range iN) := LkpToyE.places E
theorem in57 : toyA.lk.inP toyA.ValidMu () w57 := LkpToyE.in57 E
theorem in55 : toyA.lk.inP toyA.ValidMu () w55 := LkpToyE.in55 E
theorem out56 : ¬ toyA.lk.inR () w56 := LkpToyE.out56 E

abbrev mkDt : toyA.J → Prop := LkpToyE.mkDt E
abbrev mkRd : toyA.J → Prop := LkpToyE.mkRd E
abbrev mkC : toyA.St → (toyA.J → E) → Prop := LkpToyE.mkC E
abbrev mkCode : toyA.Nm → Mk := LkpToyE.mkCode E
abbrev mkDecode : Mk → toyA.Nm := LkpToyE.mkDecode E
theorem mkDecode_code : ∀ x, mkDecode (mkCode x) = x := LkpToyE.mkDecode_code E
theorem plN_eq : ∀ x, toyA.plN x = mAt (mkCode x) := LkpToyE.plN_eq E
theorem mAt_inj : Function.Injective mAt := LkpToyE.mAt_inj E
theorem mkPlacesOK : toyA.PlacesOK mkDt := LkpToyE.mkPlacesOK E
theorem mkRd_keeps (j : toyA.J) (h : toyA.srAll mkDt j) : mkRd j := LkpToyE.mkRd_keeps E j h

end
end LkpToy
end Cb.Gl
