-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/ReadsNextO.lean: kind K5: the state behind the step that makes an
attention segment's tables and closes the list, whole, for the third text of the step: readsAtSO
(Johnson/Desc/First/Att/ReadsO.lean: over Johnson/Desc/First/K8/Order.lean's close and front).

Main names:
  `reads_next_o`: readsAtSO A s = .ok s' → NextIsH A s s' (Claims/ReadsNext.lean): the next state is
    { s with here := .att { a with t := some ‹the tables›, tl := ‹the closed record› } }: every other
    field unturned.
  `next_slot_o`: so a'.F = a.F.
  `plantAtSO`, `plant_fails_o`: readsAtSO's own text with one name turned (the record is laid as it
    came, unclosed) fails the law wherever it returns.
By Att/ReadsOAgrees.lean's atS_ok_iff and Claims/ReadsNext.lean's reads_next_h.
Not claimed: anything on later steps.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.ReadsNext
import Johnson.Desc.First.Att.ReadsOAgrees

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc (named)

theorem reads_next_o (A : Plan) (s s' : S) (h : readsAtSO A s = .ok s') : NextIsH A s s' :=
  reads_next_h A s s' ((atS_ok_iff A s s').1 h)

theorem next_slot_o {A : Plan} {s s' : S} (h : readsAtSO A s = .ok s') :
    ∃ a a', s.here = .att a ∧ s'.here = .att a' ∧ a'.F = a.F :=
  next_slot_h (reads_next_o A s s' h)

/-! ### on the kind's own road: a step that lays the record as it came, unclosed, fails that law -/

/-- readsAtSO's text (Johnson/Desc/First/Att/ReadsO.lean) with one name turned: the record laid is
the one that came in, not the closed one. -/
def plantAtSO (A : Plan) (s : S) : Except String S :=
  let c := P.parCOf A
  match s.here with
  | .att a => do
    let h ← named "A.reads.heard" s.heard5?
    let g ← named "A.reads.look" a.g
    let r ← readsStepO c g.zk (P.lookOfO c.geo.lmb g) h a.tl a.L s.st a.F
    pure { s with here := .att { a with t := some r.1, tl := a.tl } }
  | _ => .error "A.reads.here"

theorem plant_fails_o (A : Plan) (s s' : S) (h : plantAtSO A s = .ok s') : ¬ NextIsH A s s' := by
  rintro ⟨a2, _, _, _, _, c2, h2, _, _, _, _, hc2, e2⟩
  unfold plantAtSO at h
  simp only [h2] at h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  obtain ⟨r, _, h⟩ := except_bind_ok h
  have e1 : (match s'.here with | .att a => a.tl.funClosed | _ => false) = a2.tl.funClosed := by
    cases h; rfl
  have e3 : (match s'.here with | .att a => a.tl.funClosed | _ => false) = c2.tl.funClosed := by
    rw [e2]
  have k := closeStep_closed hc2
  rw [e3, k.1] at e1
  exact Bool.noConfusion (e1.trans k.2)

end K5Law

