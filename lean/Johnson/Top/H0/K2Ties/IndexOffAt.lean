-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/IndexOffAt.lean: code switching, the fifth tie: THE FIELD indexOff OF K2Owes
(Johnson/Top/H0/K2Ties/T5.lean) AT THE CONSTANT's NUMBERS: THE SWITCH DOES NOT LAY THE INDEX MASKS'
PAD: where the constant's parameters are the written values. NO SUB-PROTOCOL IMPORTS THIS FILE.
  index_off_written   THE CLOSED FACT: at the written numbers the index masks' tenant is among no
                      segment's kept ones: by Lean's kernel, at all 25
  kept_some           so that the fact is not idle: the 25 lists of kept tenants are not all empty
  kept_is_seen        a negative test: the same sentence at a tenant that is kept fails
  indexOff_at         THE STATEMENT, at the constant's letters
CALLED: AtWritten (K2Ties/WrittenAt.lean: its fields keptOf and index) · laysPads_switch
(K2Ties/KeptOff.lean).
LIMITS. The full size alone. AtWritten stands under the first pinned test's accept. The road without
it (index_off_switch, from the test numbersFit) wants that test at the constant's letters, which
nobody holds. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.Top.H0.K2Ties.KeptOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (laysPads)
open P5J (TS)

/-- **The closed fact.** -/
theorem index_off_written : ∀ m, m < 25 → P5T.N0Full.index ∉ P5T.N0Full.keptOf m := by
  decide +kernel

theorem kept_some : 0 < ((List.range 25).map fun m => (P5T.N0Full.keptOf m).length).sum := by
  decide +kernel

/-- A negative test: the same sentence at a tenant that IS kept (the first of segment 0's) fails. -/
theorem kept_is_seen :
    ¬ ∀ m, m < 25 → (P5T.N0Full.keptOf 0).headD (0, 0) ∉ P5T.N0Full.keptOf m :=
  fun h => h 0 (by decide) (by decide +kernel)

/-- **The switch does not lay the index masks' pad**, at the constant's numbers. -/
theorem indexOff_at {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) (pl : Place)
    (hk : pl.kind = KindName.K2) (hm : pl.link.getD P5J.At.links.length - 1 < 25) :
    (P5J.At.N Zp cF).index ∉ laysPads (P5J.At.N Zp cF) P5J.At.links pl := by
  rcases laysPads_switch (P5J.At.N Zp cF) P5J.At.links pl hk with e | e
  · rw [e, A.keptOf, A.index]
    exact index_off_written _ hm
  · rw [e]
    exact List.not_mem_nil

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.index_off_written
#print axioms VerifiableInference.Desc.First.K2Ties.kept_some
#print axioms VerifiableInference.Desc.First.K2Ties.kept_is_seen
#print axioms VerifiableInference.Desc.First.K2Ties.indexOff_at
