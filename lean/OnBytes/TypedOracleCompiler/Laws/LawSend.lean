-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawSend.lean: the two laws at a first routine, the block SEND
(OnBytes/Iop/Send.lean): `Send.admit`, `Send.verify`, `sendVerify`.

Main names. `same_admit`, `same_verify`, `same_sendVerify`: each routine carries `Alike G d`, for
every G and d, with equal values. `law2_send` and `law1_send`: the two laws at `Send.verify`,
written out.

Not claimed. `Send.verify` has no argument that holds a value (its arguments are numbers of oracle
messages and a flag), so law 1 compares one text with itself here, from two contexts that are alike:
it says that the notes do not hang on given sources. That two texts with different values note the
same rounds is tried on other routines (OnBytes/TypedOracleCompiler/Laws/LawDry.lean).

-/
import OnBytes.TypedOracleCompiler.Laws.LawGround
import OnBytes.Iop.Send

namespace OnBytes.TwoLaws

open OnBytes

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

instance same_admit (o : Nat) (rows : Array Row) : Same (Alike G d) (Send.admit o rows) := by
  unfold Send.admit; walk

instance same_verify (ids : Array Nat) (own : Bool) : Same (Alike G d) (Send.verify ids own) := by
  unfold Send.verify; walk

instance same_sendVerify (n : Array OracleNotice) (own : Bool) :
    Same (Alike G d) (sendVerify n own) := by
  unfold sendVerify; walk

/-- Law 2 at SEND. Two runs of Send.verify from contexts that are equal but for the digests drawn
and for root and start of the trees that the book holds as given: both fail, under one name, or both
succeed and leave contexts that are again equal but for these. -/
theorem law2_send (ids : Array Nat) (own : Bool) :
    Carries (Alike AnyGiven false) Eq (Send.verify ids own) (Send.verify ids own) :=
  (same_verify ids own).out

/-- Law 1 at SEND. Two dry runs of Send.verify from contexts whose given sources go together under
G: both fail, under one name, or both succeed, and what they have noted is equal but for given
sources, which go together under G. -/
theorem law1_send (ids : Array Nat) (own : Bool) :
    Carries (Alike G true) Eq (Send.verify ids own) (Send.verify ids own) :=
  (same_verify ids own).out

#print axioms law2_send
#print axioms law1_send

end OnBytes.TwoLaws
