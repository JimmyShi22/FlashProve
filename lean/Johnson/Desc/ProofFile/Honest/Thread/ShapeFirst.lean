-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ShapeFirst.lean: for the proof file's first chain, the record
`Shape` (Shape.lean, in this folder) filled in as far as that can be done without the text of any
single block of the chain. The shape of the chain's state is `chainSh`
(Johnson/Desc/First/Shape/Chain.lean); the form is "one Bool and one update for each block"
(`Shape.meet`, ShapeMeet.lean). The blocks' guards, updates and tests on values are parameters. One
definition, four theorems; nothing is evaluated.

Main names.
* `firstShape guard upd vals` := Shape.meet chainSh guard upd vals.
* `rest_plain`: `Plain` (Shape.lean) holds of the product Bool × Nat × Option LedSh × Option Nat ×
  Bool × Nat, which the statement writes out. Plain admits Nat, Bool, String, Unit, lists, options
  and pairs alone: so no field element occurs in that type. By Chain.lean's text these six factors
  are the types of six of ChainSh's nineteen components: marked, here, led, rowsOwed, reply,
  indexMasks (the places 1, 2, 4, 6, 8, 9). THE STATEMENT NAMES NEITHER ChainSh NOR A READER OF IT:
  see the Limits.
* `blind_request`: the shape is the same before and after S.withReq lays a request's words
  (`Shape.Blind`). It is Chain.lean's `chainSh_withReq`, said through Shape.Blind; ChainSh has no
  component for the request.
* **`start_shape`**: where the request passes S.reqOk, chainSh (ProofFile.startS Z p) = chainSh Z.s₀: the
  right side does not mention p.
* `start_blank`: where the request does not pass S.reqOk, (chainSh (ProofFile.startS Z p)).marked = true.

Limits. rest_plain IS A FACT ON A TYPE THAT STANDS ALONE. No line of Lean ties its six factors to
the shape's components: that tie is a reading of Chain.lean's text. If a component's type changed,
the theorem would still compile and the words above would be false. A statement that names the
components is lacking. `Shape.Typed (firstShape …)` is Plain ChainSh; THAT CANNOT BE DERIVED FROM
Plain's CONSTRUCTORS: the other thirteen components hold structures that the library declares
itself, and no constructor yields such a type (Chain.lean's opening comment, under "THE TYPES",
names them with the files that list their fields' types, but for OracleNotice,
OnBytes/Iop/Ground.lean, which stands inside the type of atEnd). Nothing here says whether the shape
of Z.s₀ bears the mark, and nothing ties ProofFile.startS to the states at which Shape.lean's theorems let
a chain begin: so whether all these states have one shape is not settled here. No guard, update or
test on values of any block is given here, so nothing here says that a run on shapes succeeds
anywhere. None of the statements is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ShapeMeet
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Shape (ChainSh chainSh chainSh_withReq)

/-- `Plain` of a product of six types, written out. By Chain.lean's text they are the types of six
of ChainSh's nineteen components; the statement does not name these. -/
theorem rest_plain :
    Plain (Bool × Nat × Option VerifiableInference.Desc.First.Shape.LedSh × Option Nat × Bool ×
      Nat) := by
  repeat' first
    | exact Plain.nat
    | exact Plain.bool
    | exact Plain.str
    | exact Plain.unit
    | apply Plain.list
    | apply Plain.opt
    | apply Plain.prod

/-- **The first chain's `Shape`**, with the blocks' guards, updates and tests on values as
parameters. -/
def firstShape (guard : Nat → ChainSh → Bool) (upd : Nat → ChainSh → ChainSh)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) : Shape S :=
  Shape.meet chainSh guard upd vals

variable (guard : Nat → ChainSh → Bool) (upd : Nat → ChainSh → ChainSh)
  (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)

/-- The shape does not change when a request's words are laid: Chain.lean's `chainSh_withReq`, said
through Shape.Blind. -/
theorem blind_request (req : Array UInt32) :
    (firstShape guard upd vals).Blind fun s => s.withReq req := fun s => chainSh_withReq s req

/-- **Where the request passes, the first state's shape is the shape of Z.s₀**: p does not occur in
it. -/
theorem start_shape (Z : ProofFile.Pub) (p : ProofFile.InstPub)
    (h : (Z.s₀.withReq (OnBytes.Model.Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) :
    chainSh (ProofFile.startS Z p) = chainSh Z.s₀ := by
  unfold ProofFile.startS
  simp only [h, if_true]
  exact chainSh_withReq _ _

/-- Where it does not pass, the first state's shape bears the mark. -/
theorem start_blank (Z : ProofFile.Pub) (p : ProofFile.InstPub)
    (h : (Z.s₀.withReq (OnBytes.Model.Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V =
      false) : (chainSh (ProofFile.startS Z p)).marked = true := by
  unfold ProofFile.startS
  simp only [h]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.rest_plain
#print axioms ProofFile.Honest.blind_request
#print axioms ProofFile.Honest.start_shape
#print axioms ProofFile.Honest.start_blank
