-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/RelGuards.lean: there is a `Table`.

Main names:
  `table_ref`: there is a `Table`: the reference table `ppRef` (whose policy is (2^8, 2^8, 0)).

Limits: what the head of Cm/RelTrue.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cm.RelProofs
import Cm.RelTrue

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Inst.Model.ScalesSanity
  Inst.Model.ProgramRGuards Inst.Model.SanityRef

theorem table_ref : Table ppRef := ⟨lawful_ref, by decide⟩

end Cm
