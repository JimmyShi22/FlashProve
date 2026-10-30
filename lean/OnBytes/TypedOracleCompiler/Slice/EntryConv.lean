-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryConv.lean: the converter, as code that runs.

Untrusted by design. `convE` is the port's own `Entry.read` and `recordSeeds`, at the port's fast
hash: no theorem on soundness leans on it.

With: `seedOfC`, a twin of `seedOf` that Lean compiles (`seedOf1`'s one "if" is decided classically;
equality in GE has code), and `seedOfC = seedOf`: so the instance that runs is the instance of
`asmE` (OnBytes/TypedOracleCompiler/Slice/EntryTypE.lean). Nothing in this file is marked noncomputable.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryTypE
import OnBytes.TypedOracleCompiler.Run.LenientFill

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

open OnBytes.Slice (GE NZ readE seedOf seedOf1)
open OnBytes.Tie (AskedE seedsUnder)

/-- `seedOf1`, with the test on the factor decided by code. -/
def seedOf1C (lg : ℕ) (x : List OnBytes.E × OnBytes.E) : (Fin lg → GE) × NZ :=
  (fun c => readE (x.1.getD c.val OnBytes.zeroE),
    if h : readE x.2 = 0 then ⟨1, one_ne_zero⟩ else ⟨readE x.2, h⟩)

theorem seedOf1C_eq (lg : ℕ) (x : List OnBytes.E × OnBytes.E) : seedOf1C lg x = seedOf1 lg x := by
  unfold seedOf1C seedOf1
  by_cases h : readE x.2 = 0
  · simp [h]
  · simp [h]

/-- `seedOf`, as code. -/
def seedOfC (lg s : ℕ) (l : List (List OnBytes.E × OnBytes.E)) : Fin s → (Fin lg → GE) × NZ :=
  fun i => seedOf1C lg (l.getD i.val ([], OnBytes.oneE))

/-- It is `seedOf`. -/
theorem seedOfC_eq (lg s : ℕ) (l : List (List OnBytes.E × OnBytes.E)) : seedOfC lg s l = seedOf lg s l :=
  funext fun _ => seedOf1C_eq lg _

/-- The instance, as code. -/
def xOfAskedC (lg s : ℕ) (a : AskedE) : XE AnsT lg s :=
  ((a.first.answers.map OnBytes.E.triple, a.further.answers.map OnBytes.E.triple),
    (seedOfC lg s a.l0, seedOfC lg s a.l1))

/-- It is the instance of `asmE`. -/
theorem xOfAskedC_eq (lg s : ℕ) (a : AskedE) : xOfAskedC lg s a = xOfAsked lg s a := by
  unfold xOfAskedC xOfAsked
  rw [seedOfC_eq, seedOfC_eq]

/-- THE CONVERTER's FIRST HALF: the port's own reading of the entry file under parameters q
against the first table, and the port's own seeds at both tables' names. No decision is taken. -/
def convE (q : OnBytes.Params.Link) (first : OnBytes.Params.TableName) (ent : ByteArray) : Option AskedE :=
  match OnBytes.Entry.read q first ent with
  | .error _ => none
  | .ok r =>
    (seedsUnder OnBytes.recordSeeds q first).bind fun a =>
      (seedsUnder OnBytes.recordSeeds q r.further).map fun b => ⟨first, r.further, a, b, r.chain.out⟩

/-- A LENIENT CONVERTER (so that damaged FILES reach the verifier): the port's text up to the
chain (head, the copy's table, both keys, the description: `Tie.entryPlaceR`), THEN `lenientX` (the
library's `cutChainX`: it cuts the file and recomputes the chain; it tests NO work, walks NO path,
compares NO root; every opening's record is filled by hashing) in the strict reader's place; bytes
left over are refused here. As untrusted as `convE`. -/
def convLax (q : OnBytes.Params.Link) (first : OnBytes.Params.TableName) (ent : ByteArray) : Option AskedE :=
  (OnBytes.Tie.entryPlaceR OnBytes.recordSeeds q first ent).bind fun P =>
    (TypedOracleCompiler.Run.lenientX OnBytes.formatHashFastForm P.spec ent P.byte).bind fun z =>
      if z.2 = ent.size then
        (seedsUnder OnBytes.recordSeeds q first).bind fun a =>
          (seedsUnder OnBytes.recordSeeds q P.further).map fun b => ⟨first, P.further, a, b, z.1⟩
      else none

end TypedOracleCompiler.Slice
