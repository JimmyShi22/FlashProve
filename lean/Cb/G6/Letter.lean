-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Letter.lean: a sumcheck block with short messages as a letter: any reduction between the
sumcheck's own two joints that has the short rounds, the long block's error numbers and `KnowAt`. A
letter is a record that stands for any reduction with these properties, so that a theorem can be
stated for all of them.

Definitions and two small theorems. No protocol occurs here. The records are over the library's own
parameters `PscPar` (Cb/Ld/LdPsc.lean). The sumcheck's joints `Y.baseIn`, `Y.baseOut` do not speak
of the format of a round, so they serve a block whose rounds send one coefficient less.

Main names:
  `shapeSC Y`: the short rounds without the round of values: round 0 and one round for each
    variable. (With the round of values: `shapeS Y`, Cb/G6/Johnson/Layers/Short.lean.)
  `ShortK Y Ex`: the half on the verifier. R: a reduction between the sumcheck's own statements.
    `shape`: its rounds are round 0 (a scalar, then a draw), one round for each variable with n_j
    scalars, and the round of values. The errors ε, with `nums`: the long block's numbers: 1, then
    n_j for each variable, then 0. `know`: `KnowAt` at the sumcheck's own joints, for every joint A0
    that rides along (Cb/Ld/LdPsc.lean) and every reading msg of the messages; the extractor hands
    the further witness back.
  `ShortH K`: the half on the honest prover, over K: for every reading an honest side, numbers whose
    errors are K's, and `HonAt`.
  `ShortH.good`: the two halves give the library's `GoodAt`.
  `ShortKC`, `ShortHC`, `ShortHC.good`: the same for round 0 and the rounds of the variables alone,
    to `Y.Mid`.

The library's premises stand inside the fields: `Y.VarsOK`, `Y.DegOK`, `Y.ValInj` in `know`;
`Y.VarsOK`, `Y.DegOK` in `hon`. R, `shape`, ε and `nums` take none.
Limits: `ShortK` lays no law on what R puts out: a verifier that rejects everything fills it
(`rejectK`, Cb/G6/Control.lean). A theorem for every `ShortK` is the stronger for that; it shows
nothing on what is accepted or handed on.

-/
import Cb.G6.Cut
import Cb.Ld.LdPscSig
import Cb.G6.Johnson.Layers.Short

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E]

/-- The short rounds without the round of values: round 0 and one round for each variable. -/
abbrev shapeSC (Y : PscPar E) : Shape := pRound0 E :: sRounds Y.fmt

/-- The half on the verifier. R, its shape and its errors take no premise; the library's three stand
inside the field `know`. -/
structure ShortK (Y : PscPar E) (Ex : ExtSpec) where
  R     : IOR (E × Y.St) Ex Y.Out Ex
  shape : R.shape = shapeS Y
  ε     : Err R.shape
  nums  : errList ε = 1 :: (Y.fmt.map PFmt.n ++ [0])
  know  : Y.VarsOK → Y.DegOK → Y.ValInj →
    ∀ (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    KnowAt R (Y.baseIn A0 fun w => msg w.1) (Y.baseOut A0 fun w => msg w.1) (fun _ _ _ wp => wp) ε

/-- The half on the honest prover. -/
structure ShortH {Y : PscPar E} {Ex : ExtSpec} (K : ShortK Y Ex) where
  H   : ∀ {M Wp : Type}, (M → Y.J → E) → K.R.Honest (M × Wp) (M × Wp)
  P   : ∀ Kc : Type, IOR.Nums Kc K.R
  err : ∀ Kc, (P Kc).err = K.ε
  hon : Y.VarsOK → Y.DegOK →
    ∀ (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    HonAt K.R (H (Wp := Wp) msg) (Y.baseIn A0 fun w => msg w.1) (Y.baseOut A0 fun w => msg w.1)
      (P Kc)

/-- The two halves give the library's `GoodAt`. -/
theorem ShortH.good {Y : PscPar E} {Ex : ExtSpec} {K : ShortK Y Ex} (Hh : ShortH K)
    (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    GoodAt K.R (Hh.H (Wp := Wp) msg) (Y.baseIn A0 fun w => msg w.1)
      (Y.baseOut A0 fun w => msg w.1) (fun _ _ _ wp => wp) (Hh.P Kc) :=
  (goodAt_iff _ _ _ _ _ _).2
    ⟨by rw [Hh.err Kc]; exact K.know hV hD hI M Wp Kc A0 msg, Hh.hon hV hD M Wp Kc A0 msg⟩

/-- The half on the verifier for round 0 and the rounds of the variables alone, to `Y.Mid`. -/
structure ShortKC (Y : PscPar E) (Ex : ExtSpec) where
  R     : IOR (E × Y.St) Ex Y.Mid Ex
  shape : R.shape = shapeSC Y
  ε     : Err R.shape
  nums  : errList ε = 1 :: Y.fmt.map PFmt.n
  know  : Y.VarsOK → Y.DegOK → Y.ValInj →
    ∀ (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    KnowAt R (Y.baseIn A0 fun w => msg w.1) (Y.baseMid A0 fun w => msg w.1) (fun _ _ _ wp => wp) ε

/-- The half on the honest prover, for the same. -/
structure ShortHC {Y : PscPar E} {Ex : ExtSpec} (K : ShortKC Y Ex) where
  H   : ∀ {M Wp : Type}, (M → Y.J → E) → K.R.Honest (M × Wp) (M × Wp)
  P   : ∀ Kc : Type, IOR.Nums Kc K.R
  err : ∀ Kc, (P Kc).err = K.ε
  hon : Y.VarsOK → Y.DegOK →
    ∀ (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    HonAt K.R (H (Wp := Wp) msg) (Y.baseIn A0 fun w => msg w.1) (Y.baseMid A0 fun w => msg w.1)
      (P Kc)

/-- The two halves give the library's `GoodAt`. -/
theorem ShortHC.good {Y : PscPar E} {Ex : ExtSpec} {K : ShortKC Y Ex} (Hh : ShortHC K)
    (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (M Wp Kc : Type) (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E) :
    GoodAt K.R (Hh.H (Wp := Wp) msg) (Y.baseIn A0 fun w => msg w.1)
      (Y.baseMid A0 fun w => msg w.1) (fun _ _ _ wp => wp) (Hh.P Kc) :=
  (goodAt_iff _ _ _ _ _ _).2
    ⟨by rw [Hh.err Kc]; exact K.know hV hD hI M Wp Kc A0 msg, Hh.hon hV hD M Wp Kc A0 msg⟩

end TWhole
