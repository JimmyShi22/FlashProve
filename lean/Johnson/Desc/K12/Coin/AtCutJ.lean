-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/AtCutJ.lean: **`AtPlace` AT A CUT OF A CHAIN's DATA, AT THE PLACE's OWN
ERRORS**: `atPlace_of_cut` (AtDesc.lean) with its two premises `bears` and `codes` paid: the first
by `like_of_cut` (LikeOfCut.lean) and `bears_errJ` (GameJ.lean), the second by the test `johOk`
(`codes_of_johOk`). One statement with its proof: so that the road "like, apart ⇒ bears at the
place's own errors ⇒ AtPlace" is one term through Lean, not a reading.
  `atPlace_cutJ`: `atPlace_of_cut`'s other premises, to the letter, and `johOk π r = true`: THEN
    `AtPlace` at the Johnson letters, the radii r and the errors `errJ π r dt`.
First arm. Limits: those of AtDesc.lean and GameJ.lean. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.LikeOfCut
import Johnson.Desc.K12.Coin.GameJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (writtenOf WR spendOk johOk codes_of_johOk)
open Johnson.G.OfPlan (rootsOf)

/-- **At a cut, at the place's own errors.** -/
theorem atPlace_cutJ (Fr : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (r : Fmt.M1.Stage → ℕ)
    (ds : List RDT) (pre mid post : List Fmt.DeclaredRound) (base₀ : ℕ) (allTs : List Fmt.Shape)
    (dB : RDT) (dt : List RDT) (hcons : dB :: dt = (ds.drop pre.length).take mid.length)
    (hAs : List.Forall₂ RoundAsG ds (pre ++ (mid ++ post)))
    (hmid : mid = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hwants : ∀ Rs, wantsOf Fr.a (stg Fr (base₀ + nTrees (ds.take pre.length))
        ((ds.drop pre.length).take mid.length)).depth ((ds.drop pre.length).take mid.length) Rs =
      wantsDecl num mid Rs)
    (hchain : ∀ n x, (ds.flatMap (·.trees))[n]? = some x → allTs[base₀ + n]? = some x)
    (hopen : ∀ r ∈ mid, ∀ o ∈ r.opens, allTs[num o.2]? = some o.1)
    (hnum0 : ∀ m, num (.own m) = base₀ + m) (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (hj : johOk π r = true) (ho : π.nums.ownMask = false) (w0 : WR) (l : List WR)
    (hw : writtenOf π.nums = some (w0 :: l)) :
    AtPlace Fr π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st)
      (base₀ + nTrees (ds.take pre.length)) dB dt (errJ π r dt) :=
  atPlace_of_cut Fr π num _ _ _ _ _ ds pre mid post base₀ allTs dB dt (errJ π r dt) hcons hAs hmid
    hwants hchain hopen hnum0 hfree early answers planOk spend (codes_of_johOk r π hj) ho w0 l hw
    (bears_errJ π r dB dt
      (like_of_cut π num ds pre mid post base₀ allTs dB dt hcons hAs hmid hchain hopen hnum0 hfree
        planOk w0 l hw))

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlace_cutJ
