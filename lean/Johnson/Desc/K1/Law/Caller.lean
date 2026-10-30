-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Caller.lean: from a place of the kind to the library's closed caller of the kind
SEND (Johnson/Pack/SendSize.lean): the list of the place's sampled messages' shapes with their
radii; under the kind's one Boolean the library's test on numbers holds of that list, and so the
caller's conditions.

Main names: sampledList; sig_om (a member of the library's signature of a list is the oracle message
of its shape and radius, of which the files Port1.lean to Port8.lean speak); cond_allMeet;
cond_sendOK.

What is not claimed. The joint in front of the sending and the way back are arguments of the
library's caller and stay so. That the library's joint seeds are the place's is not said here. A
prover's message that also holds an oracle message without answers is not of the library's kind.
Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Iop IOR VerifiableInference.OnPublicFiles

/-- The place's sampled messages' shapes, in the order of sending, each with its radius. -/
def sampledList (P : Par) (rad : Nat → Nat) : List (OracleShape × Nat) :=
  ((List.finRange (shapesOf P).length).filter fun k => decide (sampledAt P k)).map fun k =>
    (shapeAt P k, rad k.val)

/-- A member of the library's signature is the oracle message of its shape and radius. -/
theorem sig_om (cs : Codes) (l : List (OracleShape × Nat)) (i : Fin l.length) :
    (sigOf cs l).om i = portOmZ cs (l.get i).1 (l.get i).2 := rfl

/-- **Under the kind's one Boolean the library's test on numbers holds of the place's list.** -/
theorem cond_allMeet (P : Par) (rad : Nat → Nat) (h : condPort P rad = true) :
    allMeet P.codes (sampledList P rad) = true := by
  unfold allMeet sampledList
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact (cond_parts P rad h).2.2 k (of_decide_eq_true (List.mem_filter.1 hk).2)

/-- **And so the conditions of the library's closed caller.** -/
theorem cond_sendOK (P : Par) (rad : Nat → Nat) (h : condPort P rad = true)
    {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W)
    (back : (sigOf P.codes (sampledList P rad)).Msg → W' → W) :
    SendOK [sendCaller P.codes (sampledList P rad) A back] :=
  sendCaller_ok P.codes (sampledList P rad) (cond_allMeet P rad h) A back

end VerifiableInference.Desc.K1
