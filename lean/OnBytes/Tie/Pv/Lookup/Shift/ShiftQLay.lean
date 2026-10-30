-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Shift/ShiftQLay.lean.
The record of the whole lookup at the shifted vectors, and the padding and the in-joint at a forest
of calls.

Definitions, and one statement with its proof.
Main names:
  `ShiftQ.asmH A0 P`: the record `A0` of one lookup with the state St × E, and with keys and table
    shifted by theta times the tag of their call (`shKeyQ`, `shTabQ`); all other fields are A0's.
  `Port.pads h`: the public padding of a forest of calls `h` (`OnBytes.Model.Forest.Shape`), call by
    call: the padding's row in the joint numbering, and how many keys are padding.
  `Port.jIn h T K msg R0`: the joint "R0, and each call's keys lie in that call's table", written
    out.
  `port_jIn`: under `Port.OK h` the shift's own in-joint at the maps of `h` is `Port.jIn`.
Limits: nothing is said here of a reduction, of an honest prover, or of whether `A0` belongs to `h`.

-/
import OnBytes.Tie.Pv.Lookup.Port.ShiftQPort
import Cb.Pv.Lookup.Asm.AsmH

set_option autoImplicit false

namespace Cb.LdLkp
open Finset Cb.Lkp Iop IOR

namespace ShiftQ
variable {E St : Type} [Field E] [Fintype E]

/-- The assembled lookup at the shifted vectors. -/
def asmH (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E)) : LkAsmH E :=
  { A0 with
    St := St × E, key := fun x m => shKeyQ P.fK (P.key x.1 m) P.tag x.2,
    tab := fun x => shTabQ P.fT (P.tab x.1) P.tag x.2 }

end ShiftQ

namespace Port

/-- The public padding by call: row t0 of call c, in the joint numbering; the padding keys of c's
trees, and for call 0 those of the trees of padding alone. -/
def pads (h : Sh) : List (ℕ × ℕ) :=
  (List.range h.NC).map fun c =>
    (c + 2 ^ h.cK * t0Of h c,
      (((List.range h.NT).filter fun y => co h y = c).map fun y => h.pub.getD y 0).sum +
        if c = 0 then h.emptyKeys else 0)

end Port

/-- The in-joint at a forest of calls, written out. -/
def Port.jIn {E St J M Kc Wp : Type} [Field E] {Ex : ExtSpec} (h : Port.Sh) (T : St → ℕ → ℕ → E)
    (K : St → (J → E) → ℕ → ℕ → E) (msg : M → J → E) (R0 : Rels Kc St Ex (M × Wp)) :
    Rels Kc St Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x y w ∧
      ∀ c < h.NC, InTable (Port.nOf h c) (Port.kOf h c) (K x (msg w.1) c) (T x c),
    fun a w => R0.relR a w ∧
      ∀ c < h.NC, InTable (Port.nOf h c) (Port.kOf h c) (K a.1 (msg w.1) c) (T a.1 c),
    R0.on, R0.core⟩

end Cb.LdLkp

namespace Cb.Spec
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

section
variable (E : Type) [Field E] [Fintype E]

/-- The shift's in-joint at the maps of a forest of calls is the joint written out. -/
def port_jIn : Prop :=
  ∀ (St J M Kc Wp : Type) (Ex : ExtSpec) (h : Port.Sh) (T : St → ℕ → ℕ → E)
      (K : St → (J → E) → ℕ → ℕ → E) (msg : M → J → E) (R0 : Rels Kc St Ex (M × Wp)),
    Port.OK h → ((Port.Q h T K).on msg).jIn R0 = Port.jIn h T K msg R0

end
end Cb.Spec

namespace Cb
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

section
variable (E : Type) [Field E] [Fintype E]

omit [Fintype E] in
theorem port_jIn : Spec.port_jIn E := by
  intro St J M Kc Wp Ex h T K msg R0 hOK
  have i : ∀ x (m : M), ((Port.Q h T K).on msg).inC x m =
      ∀ c < h.NC, InTable (Port.nOf h c) (Port.kOf h c) (K x (msg m) c) (T x c) := fun x m =>
    propext (port_in_iff E h (T x) (K x (msg m)) hOK)
  unfold ShiftQ.jIn Port.jIn
  simp only [i]

end
end Cb

#print axioms Cb.port_jIn
