-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsCut/Wants.lean: of the stretches of the written book two are spent at the kind's place,
its two entries. One closed fact by evaluation in Lean's kernel, on the entries' six fields.

  fieldsOf             an entry as a tuple, on which equality can be decided
  k11_wants_fields     the evaluation
  k11_wants            the stretches at the kind's place are its two entries
-/
import AtFullSide.K11.LendsCut.Small

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open ProofFile.Honest
open AtFullSide.K14 (rawWantsW)

/-- An entry's six fields. -/
def fieldsOf (e : Ahead) : String × Addr × Due × Due × Addr × Bool :=
  (e.name, e.owner, e.start, e.count, e.spender, e.once)

/-- An entry is its six fields. -/
theorem fieldsOf_injective : Function.Injective fieldsOf := by
  intro a b h
  have g : (⟨(fieldsOf a).1, (fieldsOf a).2.1, (fieldsOf a).2.2.1, (fieldsOf a).2.2.2.1,
      (fieldsOf a).2.2.2.2.1, (fieldsOf a).2.2.2.2.2⟩ : Ahead) =
      ⟨(fieldsOf b).1, (fieldsOf b).2.1, (fieldsOf b).2.2.1, (fieldsOf b).2.2.2.1,
        (fieldsOf b).2.2.2.2.1, (fieldsOf b).2.2.2.2.2⟩ := by rw [h]
  cases a
  cases b
  exact g

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1024 in
/-- The evaluation, on the six fields. -/
theorem k11_wants_fields :
    (((rawWantsW.map (·.entry)).filter fun e => e.spender.place == IM.k11Place).map fieldsOf) =
      [fieldsOf k11Sum, fieldsOf k11Ends] := by
  decide +kernel

/-- **The stretches spent at the kind's place are its two entries.** -/
theorem k11_wants :
    ((rawWantsW.map (·.entry)).filter fun e => e.spender.place == IM.k11Place) =
      [k11Sum, k11Ends] :=
  List.map_injective_iff.2 fieldsOf_injective k11_wants_fields

end AtFullSide.K11

#print axioms AtFullSide.K11.fieldsOf
#print axioms AtFullSide.K11.fieldsOf_injective
#print axioms AtFullSide.K11.k11_wants_fields
#print axioms AtFullSide.K11.k11_wants
