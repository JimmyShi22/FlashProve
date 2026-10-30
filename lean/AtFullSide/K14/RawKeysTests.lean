-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawKeysTests.lean: EVERY ONE OF THE RAW BOOK's 13,116 KEYS rawKeysW
(AtFullSide/K14/RawKeyDefs.lean) LIES IN THE TWO TABLES (rawKeys_in), AND NO TWO HAVE ONE CODE, BY
nodupN AT 20 ROUNDS OF THE SORT (rawKeys_nodup). BY ONE EVALUATION IN LEAN's KERNEL (decide
+kernel). A WORKING FILE. Statements with their proofs; no definition.

  rawKeys_both    the two together: one evaluation
  rawKeys_in      rawKeysW.all (NameKey.inTables ownersW.length usesW.length) = true
  rawKeys_nodup   nodupN 20 (rawKeysW.map NameKey.code) = true

What it is for: with rawTables_ok and rawNames_keys (AtFullSide/K14/RawNamesKeys.lean) they are the
four premises of clause11_of_keys (Honest/BookLinear/NameKeys.lean) at rawAheadW. That step is not
drawn here.

maxRecDepth and maxHeartbeats are lifted in front of rawKeys_both. Its proof first unfolds rawKeysW,
rawAheadW, rawSegW, segmentCarries and linkOf and rewrites by Johnson.Unfolds.splitOn_eq and
slice_toNat?_eq. IF THE FRAME's segmentCarries TURNS, THE PROOF RIDES ANEW, OVER TAGS WRITTEN ANEW.

Limits. A FACT ON WRITTEN VALUES: at the proof file's IOP as written in Lean at the full size
(P2Law.ProofPlan.WP), the written sendings (Johnson.G.proofSendsFull) and the merges that
mergesByName lays ("a guess", in the frame's own word): rawAheadW
(AtFullSide/K14/RawAheadWritten.lean) is made at these. rawSegW STANDS OVER THE FRAME's
segmentCarries AS IT IS TODAY. Nothing here says that a key is an entry's. No negative test at this
size. Nothing on what an evaluation costs. Nothing on any property.
-/
import AtFullSide.K14.RawKeyDefs
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The keys' two tests, in one evaluation. -/
theorem rawKeys_both : rawKeysW.all (NameKey.inTables ownersW.length usesW.length) = true ∧
    nodupN 20 (rawKeysW.map NameKey.code) = true := by
  unfold rawKeysW rawAheadW rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- Every key lies in the tables. -/
theorem rawKeys_in : rawKeysW.all (NameKey.inTables ownersW.length usesW.length) = true :=
  rawKeys_both.1

/-- No two keys have one code. -/
theorem rawKeys_nodup : nodupN 20 (rawKeysW.map NameKey.code) = true := rawKeys_both.2

end AtFullSide.K14

#print axioms AtFullSide.K14.rawKeys_both
#print axioms AtFullSide.K14.rawKeys_in
#print axioms AtFullSide.K14.rawKeys_nodup
