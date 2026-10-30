--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/HonestColl.lean: at a stored table that is the code's words of rows, no seed
has a collision, for every radius below the code's distance.

  honest_notColl   at the typed index ixOf2 (Johnson/Desc/K14/Law/PointKey2.lean) and tabF of a
  table.

The library holds this fact already, at a decoder with a record: not_coll_words
(OnBytes/K/Oracle/Decodes.lean). This file says nothing more: it is the same fact at the letters
that this kind's laws name, by the same two theorems (DecodesTo.row_unique, decodesTo_mulVec).

What is not claimed. That any stored table is of that form. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K14.Law.HonestTab
import Cb.Gen.OodDecMinProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Cb Prob Blocks Cb.Ood

/-- **At a stored table that IS the code's words of rows M, no seed has a collision**, for every
radius below the code's distance: within that radius the list holds M's table alone. -/
theorem honest_notColl (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64)
    (M : (Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE)
    (ha : p.S.fold.index.code.logN ≤ 32)
    (hk : p.S.fold.index.code.r + p.S.fold.index.code.ell ≤ 2 ^ p.S.fold.index.code.logN)
    (he : eM < 2 ^ p.S.fold.index.code.logN -
      (p.S.fold.index.code.r + p.S.fold.index.code.ell) + 1)
    (htab : tabF OnBytes.Model.Reading.gl p.S.fold.index tab =
      fun r => (genOf (codeOf p.S.fold.index.code)).mulVec (M r))
    (sd : (ixOf2 p.S.fold err eM rank).Z.D) :
    ¬ (ixOf2 p.S.fold err eM rank).Coll (tabF OnBytes.Model.Reading.gl p.S.fold.index tab) sd := by
  have hd := hasDist_genOf (codeOf p.S.fold.index.code) ha hk
  rw [htab]
  have hall : ∀ u, InList (ixOf2 p.S.fold err eM rank).G eM (ixOf2 p.S.fold err eM rank).view
      (fun r => (genOf (codeOf p.S.fold.index.code)).mulVec (M r)) u →
      u = (ixOf2 p.S.fold err eM rank).view M := by
    rintro u ⟨M', h1, rfl⟩
    exact congrArg _ (funext fun _ => DecodesTo.row_unique hd (by
      show eM + 0 < _
      exact he) h1 (decodesTo_mulVec _ 0 M) rfl)
  rintro ⟨u, u', hu, hu', hne, _⟩
  exact hne ((hall u hu).trans (hall u' hu').symm)

end Desc.K14.Law
