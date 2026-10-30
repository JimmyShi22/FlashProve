-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BaseValuedAt.lean: what the law of "LIN point" calls the decoded table (TabX2,
at the encoded index's typed data with the library's own matrix: ixOf2:
Johnson/Desc/K14/Law/PointKey2.lean) is base-valued: by dec_overF
(Johnson/Desc/K14/Law/BaseValued.lean: a corollary of Cb.ldFc_overF) at the stored table
as that law reads it (tabF: PointKey.lean).

  tabF_lift    the stored table of machine words, as the law reads it, is the up-cast of a table of
               base words.
  tabX2_base   **every entry of TabX2 is the up-cast of a base element**, where the radius eM is
               below the code's distance 2 ^ logN - (r + ell) + 1.
What is not claimed. Nothing at a radius from the distance on. That a reader of a witness's cells
returns these base words. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.BaseValued
import Johnson.Desc.K14.Law.PointKey2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (GE GF toF codeOf)

/-- The stored table, as the law reads it, is the up-cast of a table of base words. -/
theorem tabF_lift (s : IndexShape) (tab : Nat → List UInt64) :
    tabF OnBytes.Model.Reading.gl s tab = fun r => Code.liftWord GE
      (fun x : Fin (2 ^ s.code.logN) => toF ((tab x.val).toArray.getD (numOf s.v r) 0)) := by
  funext r x
  show Slice.toE (ofF ((tab x.val).toArray.getD (numOf s.v r) 0)).triple = _
  rw [ofF_triple, Slice.toE_ofF]
  rfl

/-- **What the stored table decodes to is base-valued.** -/
theorem tabX2_base (p : Par) (ha : p.S.fold.index.code.logN ≤ 32)
    (hk : p.S.fold.index.code.r + p.S.fold.index.code.ell ≤ 2 ^ p.S.fold.index.code.logN)
    (err eM : Nat)
    (he : eM < 2 ^ p.S.fold.index.code.logN -
      (p.S.fold.index.code.r + p.S.fold.index.code.ell) + 1)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64) (key : TableKey) (r k : Nat) :
    ∃ b : GF, TabX2 p err eM rank tab key r k = algebraMap GF GE b := by
  unfold TabX2
  split
  · rename_i U hU
    split
    · rw [tabF_lift] at hU
      exact dec_overF (codeOf p.S.fold.index.code) ha hk (ixOf2 p.S.fold err eM rank) rfl he _ _ U
        hU _
    · exact ⟨0, (map_zero _).symm⟩
  · exact ⟨0, (map_zero _).symm⟩

end Desc.K14.Law
