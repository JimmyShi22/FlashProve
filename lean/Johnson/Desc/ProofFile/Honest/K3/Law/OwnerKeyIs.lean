-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/OwnerKeyIs.lean: the honest side of the kind "lookup" (K3). The
owner's key of Honest/BorrowedOne.lean is the key at which the lookup's seated filling reads a
matrix. Theorems.

Terms. Honest/K3/GLOSSARY.md ("owner, borrowed matrix", "seated filling"). In this file:
Honest/BorrowedOne.lean defines the owner's key once, off the public parameters: `ownerKey X l M` is
a segment, a name and a first column. The seated filling reads an entry M of link l's list at
`ownerOf X l M`, a segment and a name, from column `M.ttOff` on (Honest/K3/WitOwner.lean: `atOwn`
for the keys on the calls, `matsOwn` for the digits). An entry M is borrowed if `M.kind = 1`.

What is shown.
  `tlAt_tlOf`: the entries of a link's list by the library's reader of the link's state (`tlAt`,
    Johnson/Desc/First/Look/Laid.lean) are those of `tlOf` (Honest/K3/WitPlan.lean).
  `ownerKey_seg`, `ownerKey_name`: the segment and the name are those of `ownerOf`. Neither has a
    hypothesis.
  `ownerKey_col`: the first column is `M.ttOff`. Conditional on `M.kind = 1` or `M.ttOff = 0`.
  `ownerKey_is`: the three together, conditional on the same.
  `matsOwn_is`: the digits' list of where the matrices are read is the list of the owner's keys.
    Conditional on that hypothesis at every entry of the link's list.
  `atOwn_is`: a key's reading at a matrix's number is the reader's cell at the owner's key.
    Conditional on the same at that entry.

Hypotheses that remain.
  `h`: the entry is borrowed or begins at column 0. Where the two definitions part: at an entry that
    is not borrowed `ownerKey` gives the first column 0, while `atOwn` and `matsOwn` give `M.ttOff`
    in both cases. The test `markFitsB` (Honest/K3/WitFits.lean) asks `ttOff = 0` of such an entry.
  `hM`: (in `atOwn_is`) the link's list has the entry M at that number.

Imported. Honest/BorrowedOne.lean.

Limits. Nothing is said on `BorrowedOne` itself: that a reader answers alike at both keys is shown
of no reader here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.BorrowedOne
import Johnson.Desc.ProofFile.Honest.K3.WitOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (TMat)

/-- The entries of a link's list by the library's reader of the link's state are those of `tlOf`. -/
theorem tlAt_tlOf (X : OnBytes.Model.Verify.Public) (l a : ℕ) :
    (VerifiableInference.Desc.First.Look.tlAt X l).bind (·.mats[a]?) =
      (ProofFile.Honest.K3.tlOf X l).mats[a]? := by
  unfold VerifiableInference.Desc.First.Look.tlAt ProofFile.Honest.K3.tlOf ProofFile.Honest.K3.linkH
    ProofFile.Honest.K3.stepOf
  dsimp only
  generalize (if X.p4 = true then 2 else 1 : ℕ) = st
  by_cases h1 : (l == st * X.NGr) = true
  · simp [h1]
  · by_cases h2 : (l % st == 0) = true
    · cases X.G[l / st]? <;> simp [h1, h2]
    · cases X.A[l / st]? <;> simp [h1, h2]

/-- **The segment is that of `ownerOf`.** -/
theorem ownerKey_seg (X : OnBytes.Model.Verify.Public) (l : ℕ) (M : TMat) :
    (ownerKey X l M).1 = (ownerOf X l M).1 := by
  unfold ownerKey ownerKeyBy ownerOf ProofFile.Honest.K3.linkG ProofFile.Honest.K3.stepOf
  by_cases h : (M.kind == 1) = true <;> simp [h]

/-- **The name is that of `ownerOf`.** -/
theorem ownerKey_name (X : OnBytes.Model.Verify.Public) (l : ℕ) (M : TMat) :
    (ownerKey X l M).2.1 = (ownerOf X l M).2 := by
  unfold ownerKey ownerKeyBy ownerOf
  by_cases h : (M.kind == 1) = true
  · simp only [h, if_true]
    rw [tlAt_tlOf]
    rfl
  · simp [h]

/-- **The first column is the entry's.** Conditional on: the entry is borrowed, or it begins at
column 0. -/
theorem ownerKey_col (X : OnBytes.Model.Verify.Public) (l : ℕ) (M : TMat)
    (h : M.kind = 1 ∨ M.ttOff = 0) : (ownerKey X l M).2.2 = M.ttOff := by
  unfold ownerKey ownerKeyBy
  by_cases hk : (M.kind == 1) = true
  · simp [hk]
  · rcases h with h | h
    · exact absurd (by simp [h]) hk
    · simp [hk, h]

/-- The three together. Conditional on the same. -/
theorem ownerKey_is (X : OnBytes.Model.Verify.Public) (l : ℕ) (M : TMat)
    (h : M.kind = 1 ∨ M.ttOff = 0) :
    ownerKey X l M = ((ownerOf X l M).1, (ownerOf X l M).2, M.ttOff) := by
  rw [← ownerKey_seg, ← ownerKey_name, ← ownerKey_col X l M h]

/-- **The digits' list of where the matrices are read is the list of the owner's keys.** Conditional
on: every entry of the link's list is borrowed or begins at column 0. -/
theorem matsOwn_is (X : OnBytes.Model.Verify.Public) (l : ℕ)
    (h : ∀ M ∈ (tlOf X l).mats.toList, M.kind = 1 ∨ M.ttOff = 0) :
    matsOwn X l = (tlOf X l).mats.toList.map (ownerKey X l) := by
  unfold matsOwn
  exact List.map_congr_left fun M hM => (ownerKey_is X l M (h M hM)).symm

/-- **A key's reading at a matrix's number is the reader's cell at the owner's key.** Conditional
on: the list has the entry M at that number; M is borrowed or begins at column 0. -/
theorem atOwn_is (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (l a r c : ℕ) (M : TMat) (hM : (tlOf X l).mats[a]? = some M)
    (h : M.kind = 1 ∨ M.ttOff = 0) :
    atOwn X cell l a r c = algebraMap Cb.Gl.F Cb.Gl.E
      (cell (ownerKey X l M).1 (ownerKey X l M).2.1 r ((ownerKey X l M).2.2 + c)) := by
  unfold atOwn
  rw [hM, ownerKey_seg, ownerKey_name, ownerKey_col X l M h]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.tlAt_tlOf
#print axioms ProofFile.Honest.K3.ownerKey_seg
#print axioms ProofFile.Honest.K3.ownerKey_name
#print axioms ProofFile.Honest.K3.ownerKey_col
#print axioms ProofFile.Honest.K3.ownerKey_is
#print axioms ProofFile.Honest.K3.matsOwn_is
#print axioms ProofFile.Honest.K3.atOwn_is
