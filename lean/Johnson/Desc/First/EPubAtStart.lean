--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/EPubAtStart.lean: THE COMPOSED PUBLIC TESTS (pubAll,
Johnson/Desc/First/PubAll.lean) AT THE FIRST CHAIN's FIRST STATE: the two public items that the
table holds open from the start ("no reply has been heard", "no oracle message has been sent") are
accepted there, the second
JUST WHERE the plan's number of segment 0's group is 0. Theorems with their proofs; two of them are
negative tests.

  start?_first        where S.start? answers, its value is S.firstRecord
  unheard_first       pubAll D base .unheard accepts at the first state, the request's words laid
  noneSent_first_eq   pubAll D base .noneSent there IS the test "D.N.groupAt 0 is 0"
  noneSent_first      so it accepts where D.N.groupAt 0 = 0
  noneSent_first_no   A NEGATIVE TEST: it refuses where D.N.groupAt 0 is not 0
  indexThere_first    A NEGATIVE TEST: "the index masks' message is there" is refused at that state

Limits. On the verifier's state alone: no oracle, no witness. That D.N.groupAt 0 = 0 at the numbers
that are meant is not shown here. Nothing on soundness.

-/
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes
open VerifiableInference.Desc.K13 (noneSentC indexThereC)

/-- Where the first state is made, it is the written one. -/
theorem start?_first {Pp : Par} {codes : Codes} {shape : Params.ReqShape}
    {layout : Params.ReqLayout} {s₀ : S} (h : S.start? Pp codes shape layout = some s₀) :
    s₀ = S.firstRecord codes shape layout := by
  unfold S.start? S.startP at h
  split at h
  · exact (Option.some.inj h).symm
  · exact nomatch h

section
variable {P : Type} (D : PubData) (base : Pub → P × S → Bool) (z : P) (codes : Codes)
  (shape : Params.ReqShape) (layout : Params.ReqLayout) (req : Array UInt32)

/-- **"No reply has been heard" at the first state.** -/
theorem unheard_first :
    pubAll D base .unheard (z, (S.firstRecord codes shape layout).withReq req) = true := rfl

/-- **"No oracle message has been sent" at the first state is a test on one number of the plan.** -/
theorem noneSent_first_eq :
    pubAll D base .noneSent (z, (S.firstRecord codes shape layout).withReq req) =
      (0 == D.N.groupAt 0) := by
  rw [pubAll_noneSent]
  show ((true && true) && (0 == D.N.groupAt 0) && true) = _
  simp

theorem noneSent_first (hG : D.N.groupAt 0 = 0) :
    pubAll D base .noneSent (z, (S.firstRecord codes shape layout).withReq req) = true := by
  rw [noneSent_first_eq, hG]
  rfl

/-- A negative test: the premise bites. -/
theorem noneSent_first_no (hG : D.N.groupAt 0 ≠ 0) :
    pubAll D base .noneSent (z, (S.firstRecord codes shape layout).withReq req) = false := by
  rw [noneSent_first_eq]
  exact beq_eq_false_iff_ne.2 (Ne.symm hG)

/-- A negative test: an item that the first state does not meet. -/
theorem indexThere_first :
    pubAll D base .indexThere (z, (S.firstRecord codes shape layout).withReq req) = false := rfl

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.start?_first
#print axioms VerifiableInference.Desc.First.unheard_first
#print axioms VerifiableInference.Desc.First.noneSent_first_eq
#print axioms VerifiableInference.Desc.First.noneSent_first
#print axioms VerifiableInference.Desc.First.noneSent_first_no
#print axioms VerifiableInference.Desc.First.indexThere_first
