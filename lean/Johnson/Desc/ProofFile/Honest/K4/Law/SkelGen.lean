-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelGen.lean: CONDITIONAL: on `LookSkel`, on lengths and, in
the first group, on whether a token reaches the vocabulary's size.

What is here. CONGRUENCES: THE SUMMANDS' MAKERS OF THE FEED-FORWARD LAYERS' ROUNDS AT TWO INPUTS AND
TWO LISTS OF THE SUB-PROTOCOL's OWN SAMPLED VALUES OF THE SAME LENGTHS: those makers for which
Law/SkelJobs.lean takes the own values as equal, or which it does not treat
(Johnson/Desc/K4/Honest/Norms.lean, Johnson/Desc/K4/Honest/Gated.lean,
Johnson/Desc/K4/Honest/Merge.lean). No definition; thirteen statements with their proofs.

  `len_two`, `foldl_keeps`, `downFrom_skel`, `layerTab_size`   small laws on lengths.
  `wSums_len`, `jobSquares_skel`   the sums of limb products; the squares' layer.
  `jobRows_gen`   the row products' sumcheck over the tokens.
  `jobGated_gen`, `gatedTabs2_rel`, `jobGated2_skel`   the two gated products.
  `embClaim_gen`, `mergeClaimsAt_gen`, `jobMerge_gen`   the merge, at two lists of tokens that, in
      the first group, are as many and pass the verifier's test together.

Debts and ends. The file defines no relation. `JobSkel` (Law/SkelJobs.lean) IS AN END: see there:
five statements here end in it: `jobSquares_skel`, `jobRows_gen`, `jobGated_gen`, `jobGated2_skel`,
`jobMerge_gen`. `LookSkel` IS A DEBT: see Law/LookSkel.lean: it is the hypothesis S of five
statements here: `jobRows_gen`, `jobGated_gen`, `embClaim_gen`, `mergeClaimsAt_gen`, `jobMerge_gen`.
The two hypotheses hs and ha on the tokens are the two fields of `InSkel` (Law/MakersAt.lean: a
debt: see there), written out. THE TWO INPUTS w AND w₀ ARE FREE LETTERS but for these two; of the
own sampled values LENGTHS ALONE are asked: of rhoI, PV, rs, rhoM, rt, ZE and tkh: each a field of
`PtsFull` (Law/MakersAt.lean) or of its first field `PtsSkel` (Law/SkelEnv.lean): debts: see there
for their payers.

Not shown here. NO MAKER IS SHOWN TO RETURN ANYWHERE: a statement on a maker compares two calls.
`LookSkel` on what the lookup has sampled is a premise of the five statements named above; who makes
`look` is to show it. Nothing on what a table, a sum or an end value is worth.

Kin. `foldl_keeps`: two more theorems of the library bear that name and are the general law: a
property that each step keeps holds behind the fold (Johnson/Road/K4/WalkV0.lean,
Johnson/Desc/K8/Honest/ReadAgainVal.lean); here each step YIELDS n members, whatever came in;
`foldl_size` (Law/SkelLists.lean) is its sister: the step keeps the size. `downFrom_skel` follows
from `downFrom_size` (Johnson/Desc/First/K4/Returns/Gated.lean: the size is the smaller of n and the
array's), which is not called. `wSums_len` calls `length_flatMap_every` (Law/SkelReads.lean).
`jobRows_gen`, `jobGated_gen`, `embClaim_gen`, `mergeClaimsAt_gen` and `jobMerge_gen` are
Law/SkelJobs.lean's five with lengths in the stead of equal values. `wSums_length`
(Law/W/FitNorms.lean) is the stronger law: the list has ledNS xl times NI members at every input and
all sampled values; `wSums_len` would follow from it; `foldl_size_const` there is `foldl_keeps` at
arrays of elements. `gatedTabs2_size` (Law/SumLevels.lean) has, from one return, the number of
entries of the two tables that `gatedTabs2_rel` compares. No twin in the library is known to its
writers.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Forest.Heard WsClaim)
open OnBytes.Model.Layer (downFrom)
open OnBytes.Flat (All2 OptRel ClaimAlike optRel_bind optRel_bind_same optRel_map')
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw (fits_sizes valuesAt_size)
open OnBytes.Desc.First.K4.RtPub

/-- Two lists of two members. Stated of variables, so that the members are not compared. -/
theorem len_two {α : Type} (a b c d : α) : [a, b].length = [c, d].length := rfl

/-- A fold each of whose steps yields an array of n members. -/
theorem foldl_keeps {α β : Type} {n : Nat} {f : Array β → α → Array β}
    (h : ∀ t x, (f t x).size = n) : ∀ (l : List α) (t : Array β), t.size = n →
      (l.foldl f t).size = n
  | [], _, ht => ht
  | x :: l, t, _ => by
    rw [List.foldl_cons]
    exact foldl_keeps h l _ (h t x)

/-- `downFrom` at two arrays of one size: of one size. -/
theorem downFrom_skel {rs rs₀ : Array E} (h : rs.size = rs₀.size) (n : Nat) :
    (downFrom rs n).size = (downFrom rs₀ n).size := by
  unfold downFrom
  rw [Array.size_reverse, Array.size_reverse, Array.size_extract, Array.size_extract, h]

/-- A layer's table has 2 ^ mu entries. -/
theorem layerTab_size (y : OnBytes.Model.Layer.Lay) (cell : Nat → Nat → Nat → F)
    (X : OnBytes.Model.Layer.Ten) (mu stride width : Nat) (lamOf : Nat → Nat) (first : Nat) :
    (layerTab y cell X mu stride width lamOf first).size = 2 ^ mu := by
  unfold layerTab
  exact Array.size_ofFn

variable (Q : K4Pub) (w w₀ : K4In) {p p₀ : Pts}

/-! ## The sums of limb products, and their squares' layer -/

/-- The sums of limb products: as many, at any two inputs and any two lists of sampled values. -/
theorem wSums_len : (wSums Q w p).length = (wSums Q w₀ p₀).length := by
  unfold wSums
  dsimp only
  rw [length_flatMap_every _ (OnBytes.Model.ledNS Q.P.y.h.xl) (fun i => ?_),
    length_flatMap_every _ (OnBytes.Model.ledNS Q.P.y.h.xl) (fun i => ?_)]
  · rw [Array.length_toList]
    exact foldl_keeps (fun _ _ => by rw [Array.size_map, Array.size_range]) _ _
      Array.size_replicate
  · rw [Array.length_toList]
    exact foldl_keeps (fun _ _ => by rw [Array.size_map, Array.size_range]) _ _
      Array.size_replicate

/-- The squares' layer's job, where rhoI and PV have the same sizes. -/
theorem jobSquares_skel (hr : p.rhoI.size = p₀.rhoI.size) (hP : p.PV.size = p₀.PV.size) :
    OptRel JobSkel (jobSquares Q w p) (jobSquares Q w₀ p₀) := by
  unfold jobSquares
  dsimp only
  have hz : (squaresTab Q w p.gp).size = (squaresTab Q w₀ p₀.gp).size := by
    simp [squaresTab]
  have hw : (OnBytes.Model.Layer.normsStart Q.P.y 0 p.gp p.rhoI p.PV).2.size =
      (OnBytes.Model.Layer.normsStart Q.P.y 0 p₀.gp p₀.rhoI p₀.PV).2.size := by
    show (p.rhoI ++ Array.replicate Q.P.y.lPd _ ++ p.PV).size =
      (p₀.rhoI ++ Array.replicate Q.P.y.lPd _ ++ p₀.PV).size
    rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append, hr, hP]
  refine optRel_iteB
    (fits_sizes _ _ (by rfl) (by rfl) (by
      show #[_].map Array.size = #[_].map Array.size
      simp [hz]) (by rfl) (by exact congrArg some hw))
    (OptRel.some (jobSkel_of
      (fits_sizes _ _ (by rfl) (by rfl) (by
        show #[_].map Array.size = #[_].map Array.size
        simp [hz]) (by rfl) (by exact congrArg some hw)) (by rfl) (by rfl) (by rfl) (by rfl)
      fun _ => len_two _ _ _ _))
    (by trivial)

/-! ## The row products' sumcheck over the tokens -/

/-- The row products' sumcheck over the tokens, where PV has the same size. -/
theorem jobRows_gen (S : LookSkel p.fo p₀.fo) (hPV : p.PV.size = p₀.PV.size) :
    OptRel JobSkel (jobRows Q w p) (jobRows Q w₀ p₀) := by
  unfold jobRows
  refine optRel_bind (rowMaps_rel Q w w₀ S) fun ms ms₀ hm => ?_
  dsimp only
  refine optRel_iteB
    (fits_sizes _ _ (by rfl) (by rfl) hm (by
      dsimp only
      rw [List.map_flatMap, List.map_flatMap]
      simp only [List.map_map]
      rfl) (by exact congrArg some hPV))
    (optRel_pure (jobSkel_of
      (fits_sizes _ _ (by rfl) (by rfl) hm (by
        dsimp only
        rw [List.map_flatMap, List.map_flatMap]
        simp only [List.map_map]
        rfl) (by exact congrArg some hPV)) (by rfl)
      (len_one _ _) (by rfl) (by rfl) fun rs => ?_))
    (by trivial)
  show (Cube.valuesAt _ rs).toList.length = (Cube.valuesAt _ rs).toList.length
  rw [Array.length_toList, Array.length_toList, valuesAt_size, valuesAt_size]
  have e := congrArg Array.size hm
  rw [Array.size_map, Array.size_map] at e
  exact e

/-! ## The two gated products -/

/-- The first gated product's job, where rs has the same size. -/
theorem jobGated_gen (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size) :
    OptRel JobSkel (jobGated Q w p) (jobGated Q w₀ p₀) := by
  unfold jobGated
  refine optRel_map' (gatedTabs_rel Q w w₀) fun t t₀ h => levelJob_skel _ _ ?_ h.1 h.2
  rw [Array.size_append, Array.size_append, ztOf_skel Q S, downFrom_skel hrs]

/-- The second gated product's two tables: made together, of the same sizes. -/
theorem gatedTabs2_rel :
    OptRel (fun t t₀ : Tab × Tab => t.1.size = t₀.1.size ∧ t.2.size = t₀.2.size) (gatedTabs2 Q w)
      (gatedTabs2 Q w₀) := by
  unfold gatedTabs2
  dsimp only
  refine optRel_bind_same fun ts => optRel_bind_same fun tu => optRel_pure ⟨?_, ?_⟩
  · rw [layerTab_size, layerTab_size]
  · rw [layerTab_size, layerTab_size]

/-- The second gated product's job, where rhoM, rs and rt have the same sizes. -/
theorem jobGated2_skel (hm : p.rhoM.size = p₀.rhoM.size) (hrs : p.rs.size = p₀.rs.size)
    (hrt : p.rt.size = p₀.rt.size) : OptRel JobSkel (jobGated2 Q w p) (jobGated2 Q w₀ p₀) := by
  unfold jobGated2
  refine optRel_map' (gatedTabs2_rel Q w w₀) fun t t₀ h => levelJob_skel _ _ ?_ h.1 h.2
  rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append, hm, hrt,
    downFrom_skel hrs]

/-! ## The merge -/

/-- CONDITIONAL: on S, hrs, hZ, hk, hs and ha. The embedding's claim at two inputs and two lists of
sampled values: both are there or neither, and they are alike. -/
theorem embClaim_gen (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size)
    (hZ : p.ZE.size = p₀.ZE.size) (hk : p.tkh.size = p₀.tkh.size)
    (hs : (Q.g == 0) = true → w.tokv.size = w₀.tokv.size)
    (ha : (Q.g == 0) = true → w.tokv.any (· ≥ Q.P.V) = w₀.tokv.any (· ≥ Q.P.V)) :
    OptRel ClaimAlike (embClaim Q w p) (embClaim Q w₀ p₀) := by
  unfold embClaim
  by_cases hg : (Q.g == 0) = true
  · rw [if_pos hg, if_pos hg]
    exact optRel_bind (claimEnvOf_rel Q S hrs) fun c c₀ k => claimE_rel k hZ hk _ (hs hg) (ha hg)
  · rw [if_neg hg, if_neg hg]
    trivial

/-- CONDITIONAL: on S, hrs, hZ, hk, hs and ha. The merge's list of claims likewise, claim by
claim. -/
theorem mergeClaimsAt_gen (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size)
    (hZ : p.ZE.size = p₀.ZE.size) (hk : p.tkh.size = p₀.tkh.size)
    (hs : (Q.g == 0) = true → w.tokv.size = w₀.tokv.size)
    (ha : (Q.g == 0) = true → w.tokv.any (· ≥ Q.P.V) = w₀.tokv.any (· ≥ Q.P.V)) :
    OptRel (All2 ClaimAlike) (mergeClaimsAt Q w p) (mergeClaimsAt Q w₀ p₀) := by
  unfold mergeClaimsAt panelClaims
  refine optRel_bind (S := All2 ClaimAlike)
    (optRel_bind (claimEnvOf_rel Q S hrs) fun c c₀ k =>
      optRel_bind_same fun TS => weightClaims_rel k TS)
    fun cp cp₀ hcp => ?_
  dsimp only
  exact optRel_ite
    (optRel_bind (S := All2 ClaimAlike)
      (optRel_map' (embClaim_gen Q w w₀ S hrs hZ hk hs ha) fun _ _ h => .cons h .nil)
      fun ce ce₀ hce => optRel_pure (hcp.append hce))
    (optRel_bind (S := All2 ClaimAlike) (OptRel.some .nil)
      fun ce ce₀ hce => optRel_pure (hcp.append hce))

/-- CONDITIONAL: on S, hrs, hZ, hk, hs and ha. The merge's job likewise: both makers return or
neither, and the public test on a job's shape gives one answer at every call (`JobSkel`). -/
theorem jobMerge_gen (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size)
    (hZ : p.ZE.size = p₀.ZE.size) (hk : p.tkh.size = p₀.tkh.size)
    (hs : (Q.g == 0) = true → w.tokv.size = w₀.tokv.size)
    (ha : (Q.g == 0) = true → w.tokv.any (· ≥ Q.P.V) = w₀.tokv.any (· ≥ Q.P.V)) :
    OptRel JobSkel (jobMerge Q w p) (jobMerge Q w₀ p₀) := by
  unfold jobMerge
  exact optRel_map' (mergeClaimsAt_gen Q w w₀ S hrs hZ hk hs ha) fun _ _ h =>
    mergeJob_skel _ _ _ h.length _ _

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.len_two
#print axioms ProofFile.Honest.K4.foldl_keeps
#print axioms ProofFile.Honest.K4.downFrom_skel
#print axioms ProofFile.Honest.K4.layerTab_size
#print axioms ProofFile.Honest.K4.wSums_len
#print axioms ProofFile.Honest.K4.jobSquares_skel
#print axioms ProofFile.Honest.K4.jobRows_gen
#print axioms ProofFile.Honest.K4.jobGated_gen
#print axioms ProofFile.Honest.K4.gatedTabs2_rel
#print axioms ProofFile.Honest.K4.jobGated2_skel
#print axioms ProofFile.Honest.K4.embClaim_gen
#print axioms ProofFile.Honest.K4.mergeClaimsAt_gen
#print axioms ProofFile.Honest.K4.jobMerge_gen
