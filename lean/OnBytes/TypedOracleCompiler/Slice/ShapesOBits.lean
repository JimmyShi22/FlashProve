-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesOBits.lean: a key's record under the oracle on bit strings that is made from
the format's hash: its seeds are the seeds that the program's `recordSeeds` draws.

Why. `Three.Accepts` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) tests each checker's record against the key's
record under the oracle (`recUAt`, OnBytes/TypedOracleCompiler/Slice/ShapesAt.lean). The tie "where the program
returns 0, the verifier on bytes says yes" owes these tests at one oracle: `patch Run.oBits f`.
There `Run.oBits` is the library's oracle on bit strings that is made from the format's oracle, and
f speaks at the strings of requests alone. What the program computes is `recordSeeds`. This file
joins the two.

Main theorems.
 `hashAt_oBits`        the hash that `Run.oBits` induces is the hash that the format's oracle
                       induces.
 `seedUnder_oBits`     the seeds of a key's table under `Run.oBits` are the program's
                       `recordSeeds` on the table's name, read in the extension field, for a root
                       and a configuration digest of 32 bytes.
 `recUAt_oBits`, `recUAt_oBits_some`, `recUAt_oBits_patch`, `recUAt_oBits_patch_some`   so a key's
                       record there; under that oracle patched by a function that is silent at the
                       strings of the seeds' chain; and as a value, where the program's draw and the
                       key's answers are given.
 `oB_patch_call`, `hashAt_patch`   the format's hash over the patched oracle is the format's, at
                       every number but 177.
 `hDom_ne177`, `hashAt_patch_dom`   so on the whole domain of the format's hash.

What is not claimed. For one file alone, at `Run.oBits` itself: `recUAt_oBits_some`; what is said at
the patch is for a verifier of several files with a second hash. Nothing on what the hash is:
`Fmt.oracle`, `Run.oBits` and their laws are taken from the library by name, and nothing here
unfolds them. The field is the second, and the numbers of coordinates and answers are z's: that the
program calls `recordSeeds` with these is not said here. Nor that the root in a key that the program
hands on has 32 bytes; nor that the record in a checker's value is `seedOf` of the program's list
with the key's answers. No probability: one fixed oracle. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesPatch
import OnBytes.Slice.SeedsAtOracle
import Run.ParserHashProofs

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open _root_.Iop Rom _root_.Run
open OnBytes.Tie (IdKey)

/-- The hash that `Run.oB (Run.oBits ())` induces is the hash that `Fmt.oracle` induces: the two
functions agree at the strings of the hash's calls (`Run.ph_oStr`). -/
theorem hashAt_oBits : Fmt.HO (oB (oBits ())) = Fmt.HO Fmt.oracle := by
  funext n t i st bs
  unfold Fmt.HO
  rw [ph_oStr 0 n t i st bs (Or.inl rfl), ph_oStr 1 n t i st bs (Or.inr rfl)]

/-- THE SEEDS OF A KEY'S TABLE UNDER THE ORACLE MADE FROM THE FORMAT'S HASH ARE THE PROGRAM'S:
`recordSeeds` at the second field on the table's name, read in the extension field. For a root and a
configuration digest of 32 bytes; the numbers of coordinates and of seeds are free. -/
theorem seedUnder_oBits (lg s : ℕ) (k : IdKey) (hr : k.2.2.root.size = 32)
    (hc : k.2.1.size = 32) :
    seedUnder lg s k oBits =
      (recordSeeds .two (Key.nameOf k.1 k.2.1 k.2.2) lg s).map (seedOf lg s) := by
  unfold seedUnder Key.nameOf
  rw [hashAt_oBits, recordSeedsW_oracle_table .two k.2.2.root k.2.1 hr hc]

/-- So a key's record under that oracle: the program's seeds, and the answers in the key. -/
theorem recUAt_oBits (z : Size) (k : IdKey) (hr : k.2.2.root.size = 32) (hc : k.2.1.size = 32) :
    recUAt z oBits k =
      ((recordSeeds .two (Key.nameOf k.1 k.2.1 k.2.2) z.lg z.s).map (seedOf z.lg z.s)).bind
        fun ρ => (recAns z.v z.s k).map fun a => (ρ, a) := by
  unfold recUAt
  rw [seedUnder_oBits z.lg z.s k hr hc]

/-- That record as a value: where the program's `recordSeeds` on the table's name returns the
list l, and the key holds the answers a. -/
theorem recUAt_oBits_some (z : Size) (k : IdKey) (hr : k.2.2.root.size = 32)
    (hc : k.2.1.size = 32) (l : List (List E × E)) (a : (Fin z.v → Bool) × Fin z.s → GE)
    (hl : recordSeeds .two (Key.nameOf k.1 k.2.1 k.2.2) z.lg z.s = some l)
    (ha : recAns z.v z.s k = some a) : recUAt z oBits k = some (seedOf z.lg z.s l, a) := by
  rw [recUAt_oBits z k hr hc, hl, ha]
  rfl

/-- And under that oracle patched by a function that is silent at the strings of the seeds'
chain. -/
theorem recUAt_oBits_patch (z : Size) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, IsSeedStr s → f s = none) (k : IdKey) (hr : k.2.2.root.size = 32)
    (hc : k.2.1.size = 32) :
    recUAt z (patch oBits f) k =
      ((recordSeeds .two (Key.nameOf k.1 k.2.1 k.2.2) z.lg z.s).map (seedOf z.lg z.s)).bind
        fun ρ => (recAns z.v z.s k).map fun a => (ρ, a) :=
  (recUAt_patch z oBits f hf k).trans (recUAt_oBits z k hr hc)

/-- The record as a value: where the program's `recordSeeds` on the table's name returns the
list l, and the key holds the answers a. -/
theorem recUAt_oBits_patch_some (z : Size) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, IsSeedStr s → f s = none) (k : IdKey) (hr : k.2.2.root.size = 32)
    (hc : k.2.1.size = 32) (l : List (List E × E)) (a : (Fin z.v → Bool) × Fin z.s → GE)
    (hl : recordSeeds .two (Key.nameOf k.1 k.2.1 k.2.2) z.lg z.s = some l)
    (ha : recAns z.v z.s k = some a) :
    recUAt z (patch oBits f) k = some (seedOf z.lg z.s l, a) := by
  rw [recUAt_oBits_patch z f hf k hr hc, hl, ha]
  rfl

/-! ## The format's hash over the patched oracle -/

/-- Any oracle, patched by a function that speaks at the strings of requests alone, has its own
values at the string of every call under a number that is not 177 modulo 65536. AT THE NUMBER 177
THAT IS FALSE: a request's string is the spelling of a call under 177. -/
theorem oB_patch_call (O : Fam (rom 256)) (m : ℕ) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, f s ≠ none → ∃ w, s = codeOld m w) {n : ℕ} (hn : n % 65536 ≠ 177) (half : UInt8)
    (t i : ℕ) (st bs : ByteArray) :
    oB (patch O f ()) (Fmt.oStr half n t i st bs) = oB (O ()) (Fmt.oStr half n t i st bs) := by
  unfold oB
  rw [patch_none O f _ (quiet_call m f hf hn half t i st bs)]

/-- THE FORMAT'S HASH OVER THE PATCHED ORACLE IS THE FORMAT'S, AT EVERY NUMBER BUT 177. As
functions of the number the two hashes differ: whoever carries a text from the one to the other
must know that the text calls no hash under 177. -/
theorem hashAt_patch (m : ℕ) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, f s ≠ none → ∃ w, s = codeOld m w) {n : ℕ} (hn : n % 65536 ≠ 177) (t i : ℕ)
    (st bs : ByteArray) :
    Fmt.HO (oB (patch oBits f ())) n t i st bs = Fmt.HO Fmt.oracle n t i st bs := by
  have e : Fmt.HO (oB (patch oBits f ())) n t i st bs = Fmt.HO (oB (oBits ())) n t i st bs := by
    unfold Fmt.HO
    rw [oB_patch_call oBits m f hf hn 0, oB_patch_call oBits m f hf hn 1]
  rw [e, hashAt_oBits]

/-- No call in the domain of the format's hash has the number 177 modulo 65536. -/
theorem hDom_ne177 (n t i : ℕ) (st bs : ByteArray) (hd : Fmt.hDom n t i st bs = true) :
    n % 65536 ≠ 177 := by
  unfold Fmt.hDom at hd
  simp only [Bool.and_eq_true] at hd
  have hn : Fmt.isNumber n = true := hd.1.1.1.1.1.1.1
  unfold Fmt.isNumber Fmt.numbers at hn
  simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- ON THE DOMAIN OF THE FORMAT'S HASH, THE HASH OVER THE PATCHED ORACLE IS THE FORMAT'S OWN
HASH. In the form in which a congruence "two hashes that agree on the domain" takes it. -/
theorem hashAt_patch_dom (m : ℕ) (f : List Bool → Option (Dig 256))
    (hf : ∀ s, f s ≠ none → ∃ w, s = codeOld m w) (n t i : ℕ) (st bs : ByteArray)
    (hd : Fmt.hDom n t i st bs = true) :
    Fmt.HO (oB (patch oBits f ())) n t i st bs = Fmt.formatHash n t i st bs :=
  (hashAt_patch m f hf (hDom_ne177 n t i st bs hd) t i st bs).trans
    (Fmt.HO_oracle n t i st bs hd)

end OnBytes.Slice.Shapes
