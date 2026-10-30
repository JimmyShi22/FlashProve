-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/KeysHonest.lean: THE TWO KEYS THAT ARE WRITTEN OF A PAIR OF TYPED OOD SAMPLES
(keyOf, OnBytes/Slice/KeyOfRec.lean; the second with the item 1: as keysOfX lays them,
OnBytes/TypedOracleCompiler/Slice/KeysOfX.lean) PASS THE LINK's TEST ON THE INSTANCE (okKey,
Johnson/Desc/Link/LinkDesc.lean: the words of seeds and answers below the prime; the item) AND HOLD
THESE SAMPLES (KeyHasR, OnBytes/Slice/BlkRecRow.lean). For all such samples.

Main names (namespace Johnson.Prover.Link).
  elemOk_writeE, seedsOk_keyOf, recordOk_keyOf   a written element's words are below the prime.
  okKeys_written   the test on the instance returns true.
  keyHas_written   KeyHasR at both keys, at shapes with the samples' three numbers: two calls of
    keyHasR_keyOf.

By: okE_writeE (OnBytes/Slice/KeyOfRecBack.lean): the description's test on an element is the
program's by unfolding · keyHasR_keyOf.

Limits. Nothing on what the samples hold: any typed pair. Nothing here says that a verifier accepts.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Link.LinkDesc
import OnBytes.Slice.BlkRecRow
import OnBytes.Slice.KeyOfRecBack

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb.Ood
open VerifiableInference.Desc.Own (elemOk seedsOk recordOk)

/-- a written element passes the description's test on words -/
theorem elemOk_writeE (x : GE) : elemOk (writeE x) = true := okE_writeE x

variable {v lg s : ℕ} (rec : RecP NZ v lg s)

theorem seedsOk_keyOf : seedsOk (keyOf (fun β : NZ => β.val) rec) = true := by
  refine List.all_eq_true.2 fun sd hsd => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hsd
  rw [Bool.and_eq_true]
  refine ⟨elemOk_writeE _, List.all_eq_true.2 fun z hz => ?_⟩
  obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hz
  exact elemOk_writeE _

theorem recordOk_keyOf : recordOk (keyOf (fun β : NZ => β.val) rec) = true := by
  refine Array.all_eq_true'.2 fun a ha => ?_
  obtain ⟨n, rfl⟩ := Array.mem_ofFn.1 ha
  exact elemOk_writeE _

/-- **The link's test on the instance returns true at the written keys.** -/
theorem okKeys_written (rec' : RecP NZ v lg s) :
    (_root_.Desc.K15.okKey 0 (keyOf (fun β : NZ => β.val) rec) &&
      _root_.Desc.K15.okKey 1 { keyOf (fun β : NZ => β.val) rec' with item := 1 }) = true := by
  unfold _root_.Desc.K15.okKey
  have a := seedsOk_keyOf rec
  have b := recordOk_keyOf rec
  have a' : seedsOk { keyOf (fun β : NZ => β.val) rec' with item := 1 } = true := seedsOk_keyOf rec'
  have b' : recordOk { keyOf (fun β : NZ => β.val) rec' with item := 1 } = true :=
    recordOk_keyOf rec'
  rw [a, b, a', b']
  rfl

/-- **The written keys hold their OOD samples**, at shapes with the samples' three numbers. -/
theorem keyHas_written (rec' : RecP NZ v lg s) (sh sh' : Params.IndexShape)
    (hv : sh.v = v) (hs : sh.answers = s) (hl : sh.cubeBits = lg)
    (hv' : sh'.v = v) (hs' : sh'.answers = s) (hl' : sh'.cubeBits = lg) :
    KeyHasR v lg s sh (keyOf (fun β : NZ => β.val) rec) rec ∧
      KeyHasR v lg s sh' { keyOf (fun β : NZ => β.val) rec' with item := 1 } rec' :=
  ⟨keyHasR_keyOf rec sh hv hs hl 0, keyHasR_keyOf rec' sh' hv' hs' hl' 1⟩

end Johnson.Prover.Link
