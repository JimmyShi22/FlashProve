-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyOfRecInj.lean: the program's key of a stored table, written of a record over the
field, holds the whole record: two records with one key are one.

`keyOf` (OnBytes/Slice/KeyOfRec.lean) writes a record over the field (a seed: for each of s answers
a point and a factor; and the answers of every row) as the program's `TableKey`. A description of a
key file's verifier takes the key as its instance's public part. Whoever reads the instance back out
of that public part wants the writing to lose nothing.

Main theorem: `keyOf_injective`: where the reading `val` of a factor is injective, `keyOf val` is
injective. By `keyOf_record` and `keyOf_seeds`: read back in the field, the key's record and seeds
are the pair's.

Not claimed. That a key which a reader has read is `keyOf` of some pair. Nothing on any decoder or
on soundness.

-/
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false

namespace OnBytes.Slice
open Cb

/-- **The program's key of a table, written of a record over the field, is injective** where the
reading of a factor is: the key holds the whole record. -/
theorem keyOf_injective {B : Type} (val : B → GE) (hval : Function.Injective val)
    {v lg s : ℕ} :
    Function.Injective (keyOf val : RecP B v lg s → TableKey) := by
  intro r r' h
  have h2 : r.2 = r'.2 := funext fun x => by
    obtain ⟨x, i⟩ := x
    rw [← keyOf_record val r x i, h, keyOf_record]
  have hs := keyOf_seeds val r
  rw [h, keyOf_seeds val r'] at hs
  have hf := List.ofFn_injective hs
  have h1 : r.1 = r'.1 := funext fun i => by
    have hi := congrFun hf i
    exact (Prod.ext (List.ofFn_injective (Prod.ext_iff.1 hi).1) (hval (Prod.ext_iff.1 hi).2)).symm
  exact Prod.ext h1 h2

end OnBytes.Slice

#print axioms OnBytes.Slice.keyOf_injective
