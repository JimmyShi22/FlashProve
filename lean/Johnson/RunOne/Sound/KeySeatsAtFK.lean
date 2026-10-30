-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeySeatsAtFK.lean: A fact on the
maker's list of all trees.

What is said. `allOf_nodup`: no two trees of the maker's list of all trees have one number.

Limits. A fact on the maker.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyEndsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open VerifiableInference.Desc.Key (descriptionFromSource Source)
open _root_.Run (ckP)
open _root_.Iop (Err)

theorem allOf_nodup (D : WholeD) : ((allOf D).map (·.no)).Nodup := by
  have e : (allOf D).map (·.no) = List.range (nAll D) := by
    unfold allOf
    rw [List.map_map]
    exact List.map_id _
  rw [e]
  exact List.nodup_range

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.allOf_nodup
