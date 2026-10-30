-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawNamesKeys.lean: THE NAMES OF THE RAW BOOK's 13,116 ENTRIES, AS THE FRAME's MAKERS
LAY THEM, ARE THE NAMES OF THE KEYS rawKeysW (AtFullSide/K14/RawKeyDefs.lean) AT THE TWO TABLES
(rawNames_keys). BY LEAN's KERNEL: ONE COMPARISON OF TWO LISTS OF TERMS (kernel_rfl,
Johnson/Unfolds/KernelRfl.lean). A WORKING FILE. One statement with its proof; no definition.

  rawNames_keys   **rawAheadW.map (·.name) = rawKeysW.map (NameKey.name ownersW usesW)**: the
                  premise hK of clause11_of_keys (Honest/BookLinear/NameKeys.lean) at rawAheadW

How it goes, by the authors' reading: at each entry both sides are runName, or carriedName, at three
arguments; the kernel compares argument by argument; the strings come down to literals. A wrong tag
makes the kernel reject the declaration: so it was seen once, on a loose sheet, at the stretches'
7,940 entries with the fourth tag bent.

maxRecDepth and maxHeartbeats are lifted in front of the fact. Its proof first unfolds rawKeysW,
rawAheadW, rawSegW, segmentCarries and linkOf and rewrites by Johnson.Unfolds.splitOn_eq and
slice_toNat?_eq. IF THE FRAME's segmentCarries TURNS, THE PROOF RIDES ANEW, OVER TAGS WRITTEN ANEW.

Limits. A FACT ON WRITTEN VALUES: at the proof file's IOP as written in Lean at the full size
(P2Law.ProofPlan.WP), the written sendings (Johnson.G.proofSendsFull) and the merges that
mergesByName lays ("a guess", in the frame's own word): rawAheadW
(AtFullSide/K14/RawAheadWritten.lean) is made at these. rawSegW STANDS OVER THE FRAME's
segmentCarries AS IT IS TODAY. No negative test stands in this file: a false equation cannot be
stated as a theorem here without opening the strings. Nothing on what an evaluation costs. Nothing
on any property.
-/
import AtFullSide.K14.RawKeyDefs
import Johnson.Unfolds.KernelRfl
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **THE ENTRIES' NAMES ARE THE KEYS' NAMES.** -/
theorem rawNames_keys : rawAheadW.map (·.name) = rawKeysW.map (NameKey.name ownersW usesW) := by
  unfold rawKeysW rawAheadW rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  kernel_rfl

end AtFullSide.K14

#print axioms AtFullSide.K14.rawNames_keys
