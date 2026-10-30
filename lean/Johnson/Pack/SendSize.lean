-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/SendSize.lean: what is public of a sending (`Cb.Pv.Send.Size`, Cb/Pv/Send.lean), as a
function of the codes and of the list of the sampled messages' shapes with their radii; its
conditions from a test on numbers.

The kind SEND (Johnson/Top/H/Send.lean) asks of a caller the record `Cb.Pv.Send.Size` and its
conditions `Size.OK`: the codes' laws, fair seeds, bounded lists, evading samples. Johnson/Pack/
has each part as a function of public data, and Johnson/Pack/Buys.lean has the four conditions
from the test `allMeet`. Here they are laid into the kind's record. One definition, statements and
proofs; nothing is proved anew.

Main names:
  `sendSize cs l`: the family `sigOf cs l`, the joint seeds `seedsOf cs l`, and for member i the
    bound `lOf cs` at its shape and radius.
  `sendSize_ok`: `allMeet cs l = true → (sendSize cs l).OK`.
  `sendCaller cs l A back`: a caller of the kind at that size, at any joint before the sending.
  `sendCaller_ok`: under the test, `SendOK` of the list that holds this caller alone.

Limits: those of Johnson/Pack/Buys.lean. The list l holds the sampled messages alone: a prover's
message that also holds an oracle message without answers is not of this kind
(Johnson/Top/H/Send.lean, Limits). No list is written here.
-/
import Johnson.Pack.Buys
import Johnson.Top.H.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Iop IOR OnBytes.Slice VerifiableInference.OnPublicFiles

/-- What is public of the sending of the sampled messages l under the codes cs. -/
noncomputable def sendSize (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) :
    Cb.Pv.Send.Size GE :=
  ⟨sigOf cs l, seedsOf cs l, fun i => lOf cs (l.get i).1 (l.get i).2⟩

/-- Its conditions, from the test on numbers. -/
theorem sendSize_ok (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (h : allMeet cs l = true) : (sendSize cs l).OK :=
  have B := allMeet_buys cs l h
  ⟨B.laws, B.fair, B.list, B.evades⟩

/-- A caller of the kind SEND at that size. -/
noncomputable def sendCaller (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W)
    (back : (sigOf cs l).Msg → W' → W) : SendCaller GE :=
  ⟨sendSize cs l, Kc, X, W, W', E₀, A, back⟩

theorem sendCaller_ok (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (h : allMeet cs l = true) {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W)
    (back : (sigOf cs l).Msg → W' → W) : SendOK [sendCaller cs l A back] := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact sendSize_ok cs l h

end Johnson.Pack

#print axioms Johnson.Pack.sendSize_ok
#print axioms Johnson.Pack.sendCaller_ok
