-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CxPropsApply.lean: the three theorems that take `Cx.Props`, applied at the complex of
Cb/Gen/CxProps.lean: its encoding has the laws, its budget hides, and where decoding with samples
answers one message the plain decoder gives that message, with some randomness.
-/
import Cb.Gen.CxProps
import Cb.Gen.CodeProofsComp
import Cb.Gen.OodDecCxProofs

set_option autoImplicit false

namespace Cb.Cx
open Cb.Ood

local instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- `Cb.cx_laws` at the closed complex. -/
theorem laws_closed : (closed.enc (ZMod 101)).Laws := Cb.cx_laws _ _ closed props_closed

/-- `Cb.cx_hides` at the closed complex. -/
theorem hides_closed : (closed.enc (ZMod 101)).Hides (closed.bud (ZMod 101)) :=
  Cb.cx_hides _ _ closed props_closed

/-- `Cb.ood_cx_guard` at the closed complex: at the codes' own radii, decoding with samples never
answers `several`, and where it answers one message the plain decoder gives that message, with
some randomness. -/
theorem ood_closed (Z : Sample (ZMod 101) closed.Ent) (y : (closed.ext (ZMod 101)).Str) (ρ : Z.D)
    (v : Z.S → ZMod 101) :
    closed.decS (ZMod 101) (fun a => (closed.comp a).code.e) Z y ρ v ≠ .several ∧
    ∀ m, closed.decS (ZMod 101) (fun a => (closed.comp a).code.e) Z y ρ v = .one m →
      ∃ r, (closed.enc (ZMod 101)).dec y = some (m, r) :=
  Cb.ood_cx_guard (ZMod 101) (ZMod 101) closed Z y ρ v props_closed

end Cb.Cx

#print axioms Cb.Cx.laws_closed
#print axioms Cb.Cx.hides_closed
#print axioms Cb.Cx.ood_closed
