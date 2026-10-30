-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Rel2Proofs.lean: lemmas on Cm/Rel2.lean: lawful tables and the bound.

Main names (s is a table of scales, `Scales`):
  `Scales.Lawful.toPP`, `lawful_iff`, `Scales.Lawful.lawfulK`: a table of scales is lawful if and
    only if, with the policy (2^8, 2^8, 0) beside it, it is lawful in the sense of
    Inst/Model/Scales.lean (`Inst.Model.Lawful`, whose clause on the policy holds of these three
    numbers); so it is lawful in the form that the proofs on the layers take (`LawfulK`, with
    `tbRef` in every group).
  `Below2.mono`: the bound `Below2 B T` (Cm/Rel2.lean) for B gives it for every B' ≥ B.

Limits: what the head of Cm/Rel2.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cm.Rel2

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-! ## Lawful tables -/

theorem Scales.Lawful.toPP {s : Scales} (h : s.Lawful) : Inst.Model.Lawful ⟨s.w, s.nf, AcceptancePolicy.exact⟩ :=
  ⟨⟨h.ff, h.sh, h.one, h.nf,
      (by decide : AcceptancePolicy.exact.C < 2 ^ 32 ∧ AcceptancePolicy.exact.theta ≤ AcceptancePolicy.exact.C ∧ AcceptancePolicy.exact.cap ≤ 1024)⟩,
    h.km⟩

theorem lawful_iff (s : Scales) : s.Lawful ↔ Inst.Model.Lawful ⟨s.w, s.nf, AcceptancePolicy.exact⟩ :=
  ⟨fun h => h.toPP, fun h => ⟨h.ff, h.sh, h.one, h.nf, h.km⟩⟩

theorem Scales.Lawful.lawfulK {s : Scales} (h : s.Lawful) : LawfulK s.kap s.nf fun _ => tbRef :=
  lawfulK_of h.toPP

/-! ## The bound -/

theorem Below2.mono {B B' : ℤ} (h : B ≤ B') {T : Trace} (b : Below2 B T) : Below2 B' T :=
  ⟨b.toBelowL.mono h,
    fun i hi φ hφ => lt_of_lt_of_le (b.hf i hi φ hφ) h,
    fun i hi φ hφ => lt_of_lt_of_le (b.hd i hi φ hφ) h,
    fun i hi φ hφ => lt_of_lt_of_le (b.hr i hi φ hφ) h⟩

end Cm
