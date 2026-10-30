-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LikeOfCut.lean: **"THE STRETCH's DATA ARE LIKE THE WRITTEN ROUNDS", APART**:
the first half of `atPlace_of_cut`'s proof (AtDesc.lean) as a lemma of its own.
Statements and proofs.
`atPlace_of_cut` takes `bears` (the errors bear the chain's counts) and gives `AtPlace`, in which
`like` lies. Whoever wants to SHOW `bears` at a file's own stretch (`bears_errJ`, GameJ.lean, asks
`like`) needs `like` first. This half spends neither `bears` nor the wants, nor the codes' facts.
  `like_of_cut`: general in the chain: from the parting of the chain's declared rounds (pre ++ (mid
    ++ post), mid the block's own), "the data are the rounds as written" (`RoundAsG`), the trees'
    and the openings' places in the list of all trees, the numbering of the chain's own trees, and
    "the place's count of trees in front is pre's roots":
    ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ Forall₂ Like (dB :: dt) (w0 :: l).
  `numOwn_of_cut`: beside it: the numbering's equation at the stretch's base.
  `batTrees_of_cut`: and: the batching's round sends no tree.
AtDesc.lean is not turned: its proof keeps its own lines.
Limits: those of AtDesc.lean. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (writtenOf WR)
open Johnson.G.OfPlan (rootsOf)

section
variable (π : P12) (num : Fmt.TreeSource → ℕ) (ds : List RDT) (pre mid post : List Fmt.DeclaredRound)
  (base₀ : ℕ)

/-- The numbering's equation at the stretch's base. -/
theorem numOwn_of_cut (hAs : List.Forall₂ RoundAsG ds (pre ++ (mid ++ post)))
    (hnum0 : ∀ m, num (.own m) = base₀ + m) (hfree : π.nums.free = rootsOf pre) :
    ∀ n, num (.own (π.nums.free + n)) = base₀ + nTrees (ds.take pre.length) + n := by
  have hpre : nTrees (ds.take pre.length) = rootsOf pre := by
    have h1 := List.forall₂_take pre.length hAs
    rw [List.take_left] at h1
    exact nTrees_roots h1
  intro n
  rw [hnum0, hfree, hpre, Nat.add_assoc]

/-- The stretch's data are the block's rounds as written: no stored table is opened. -/
theorem roundAs_of_cut (dB : RDT) (dt : List RDT)
    (hcons : dB :: dt = (ds.drop pre.length).take mid.length)
    (hAs : List.Forall₂ RoundAsG ds (pre ++ (mid ++ post)))
    (hrs : H2U.roundsOfNums π.nums = some mid) : List.Forall₂ RoundAs (dB :: dt) mid := by
  have hst := H2K.Sw.roundsOfNums_stored π.nums mid hrs
  rw [hcons]
  exact forall₂_imp_mem (forall₂_cut pre mid post hAs) fun d r hr h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans (hst r hr)⟩

/-- **`like`, apart.** -/
theorem like_of_cut (allTs : List Fmt.Shape) (dB : RDT) (dt : List RDT)
    (hcons : dB :: dt = (ds.drop pre.length).take mid.length)
    (hAs : List.Forall₂ RoundAsG ds (pre ++ (mid ++ post)))
    (hmid : mid = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hchain : ∀ n x, (ds.flatMap (·.trees))[n]? = some x → allTs[base₀ + n]? = some x)
    (hopen : ∀ r ∈ mid, ∀ o ∈ r.opens, allTs[num o.2]? = some o.1)
    (hnum0 : ∀ m, num (.own m) = base₀ + m) (hfree : π.nums.free = rootsOf pre)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (w0 : WR) (l : List WR)
    (hw : writtenOf π.nums = some (w0 :: l)) :
    ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l) := by
  have hrs : H2U.roundsOfNums π.nums = some mid := by
    rw [hmid]
    exact VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π planOk
  have hE := roundAs_of_cut π ds pre mid post dB dt hcons hAs hrs
  have hcut : ∀ n x, ((dB :: dt).flatMap (·.trees))[n]? = some x →
      allTs[base₀ + nTrees (ds.take pre.length) + n]? = some x := by
    intro n x h
    rw [hcons] at h
    rw [Nat.add_assoc]
    exact hchain _ x (cutTrees ds pre.length mid.length n x h)
  have hopen' : ∀ o ∈ mid.flatMap (·.opens), allTs[num o.2]? = some o.1 := by
    intro o ho'
    obtain ⟨r, hr, hor⟩ := List.mem_flatMap.1 ho'
    exact hopen r hr o hor
  exact like_of_data π mid hrs w0 l hw (dB :: dt) hE num _ allTs hcut hopen'
    (numOwn_of_cut π num ds pre mid post base₀ hAs hnum0 hfree)

/-- The batching's round sends no tree. -/
theorem batTrees_of_cut (dB : RDT) (dt : List RDT)
    (hcons : dB :: dt = (ds.drop pre.length).take mid.length)
    (hAs : List.Forall₂ RoundAsG ds (pre ++ (mid ++ post)))
    (hmid : mid = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) : dB.trees = [] := by
  have hrs : H2U.roundsOfNums π.nums = some mid := by
    rw [hmid]
    exact VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π planOk
  have hE := roundAs_of_cut π ds pre mid post dB dt hcons hAs hrs
  obtain ⟨_, _, _, R, _, _, hR⟩ := H2K.Made.rounds_top π.nums mid hrs
  rw [hR] at hE
  cases hE with
  | cons h _ => exact List.eq_nil_of_length_eq_zero h.2.2.2.1

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.numOwn_of_cut
#print axioms VerifiableInference.Desc.K12.Coin.like_of_cut
#print axioms VerifiableInference.Desc.K12.Coin.batTrees_of_cut
