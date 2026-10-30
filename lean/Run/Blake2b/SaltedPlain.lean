-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.Salted
import Run.Blake2b.WordsThm
/-!
# BLAKE2b with a salt and a personalization, read with natural-number indices only

The functions of Salted.lean read bytes through load64, whose fast branch is guarded by a test on
machine words that Lean's kernel cannot evaluate. This file has the same functions with load64Plain
in its place. Lean's kernel can compute them, so known answers can be theorems; compiled code should
call the functions of Salted.lean. blake2bSaltedPlain_eq: the two agree for all arguments.

The four definitions are MessageBlock.ofBytes of Hash.lean and firstStateSalted, stateSalted and
blake2bSalted of Salted.lean with load64Plain for load64, and have the sources of these.
Source. So the four follow, at one remove, what Hash.lean and Salted.lean name as their source.
Hash.lean's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
-/
namespace Run.Blake2b

/-- `MessageBlock.ofBytes a off` with `load64Plain` for `load64`: the 128 bytes at offset `off` of `a` as
sixteen words; a byte at or beyond the end of `a` reads as 0. -/
def MessageBlock.ofBytesPlain (a : ByteArray) (off : Nat) : MessageBlock :=
  { m0 := load64Plain a (off + 8 * 0),
    m1 := load64Plain a (off + 8 * 1),
    m2 := load64Plain a (off + 8 * 2),
    m3 := load64Plain a (off + 8 * 3),
    m4 := load64Plain a (off + 8 * 4),
    m5 := load64Plain a (off + 8 * 5),
    m6 := load64Plain a (off + 8 * 6),
    m7 := load64Plain a (off + 8 * 7),
    m8 := load64Plain a (off + 8 * 8),
    m9 := load64Plain a (off + 8 * 9),
    m10 := load64Plain a (off + 8 * 10),
    m11 := load64Plain a (off + 8 * 11),
    m12 := load64Plain a (off + 8 * 12),
    m13 := load64Plain a (off + 8 * 13),
    m14 := load64Plain a (off + 8 * 14),
    m15 := load64Plain a (off + 8 * 15) }

/-- `firstStateSalted outlen salt personal` with `load64Plain` for `load64`. -/
def firstStateSaltedPlain (outlen : Nat) (salt personal : ByteArray) : State :=
  initParam (parameterBlockFirstWord 0 outlen) 0 0 0
    (load64Plain salt 0) (load64Plain salt 8) (load64Plain personal 0) (load64Plain personal 8)

/-- `stateSalted salt personal data outlen` with `load64Plain` for `load64`. -/
def stateSaltedPlain (salt personal data : ByteArray) (outlen : Nat) : State :=
  message (fun j => MessageBlock.ofBytesPlain data (128 * j)) data.size
    (firstStateSaltedPlain outlen salt personal)

/-- `blake2bSalted salt personal data outlen` with `load64Plain` for `load64`: BLAKE2b of `data`
with a salt and a personalization and no key, in the form that Lean's kernel can compute. -/
def blake2bSaltedPlain (salt personal data : ByteArray) (outlen : Nat) : ByteArray :=
  if outlen = 0 ∨ outlen > 64 then ByteArray.empty
  else (stateSaltedPlain salt personal data outlen).h.bytes outlen

/-- The two forms of a block agree. -/
theorem ofBytesPlain_eq (a : ByteArray) (off : Nat) :
    MessageBlock.ofBytesPlain a off = MessageBlock.ofBytes a off := by
  unfold MessageBlock.ofBytesPlain MessageBlock.ofBytes
  simp only [load64_eq_plain]

/-- The two forms of the hash agree, for all arguments. -/
theorem blake2bSaltedPlain_eq (salt personal data : ByteArray) (outlen : Nat) :
    blake2bSaltedPlain salt personal data outlen = blake2bSalted salt personal data outlen := by
  unfold blake2bSaltedPlain blake2bSalted stateSaltedPlain stateSalted firstStateSaltedPlain
    firstStateSalted
  simp only [ofBytesPlain_eq, load64_eq_plain]

end Run.Blake2b

#print axioms Run.Blake2b.ofBytesPlain_eq
#print axioms Run.Blake2b.blake2bSaltedPlain_eq
