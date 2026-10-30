-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/AtDescJ.lean: **`AtPlace` AT A DESCRIPTION's THREE CHAINS, AT THE PLACE's OWN
ERRORS**: `atPlace_first` | `atPlace_shared` | `atPlace_last` (AtDesc.lean) with their premises
`codes` and `bears` gone and the test `johOk π r = true` in their place: `atPlace_cutJ`
(AtCutJ.lean) at a description's data. Statements and proofs; each proof is AtDesc.lean's own glue,
with `atPlace_cutJ` called where `atPlace_of_cut` was.
  `atPlace_firstJ`, `atPlace_sharedJ`, `atPlace_lastJ`: from F.data file = .ok D, the parting of the
    chain's declared rounds at the test's, the cut of the chain's data, "the place's count of trees
    in front is the roots that the rounds in front declare", and the plan's tests: `AtPlace` at the
    frame of the data over all trees, the numbering `numAt F.t₁ F.t₂ ‹chain›`, the Johnson letters,
    the radii r and the errors `errJ π r dt`.
First arm. Limits: those of AtDesc.lean and GameJ.lean. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.AtCutJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (writtenOf WR spendOk johOk)
open Johnson.G.OfPlan (rootsOf)

/-- **At the first chain: the stretch ends in front of the sealing round.** -/
theorem atPlace_firstJ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (pre post : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.1 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (post ++ [r₀])))
    (dB : RDT) (dt : List RDT)
    (hcons : dB :: dt =
      (D.ds₁.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (hj : johOk π r = true) (ho : π.nums.ownMask = false) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l)) :
    AtPlace (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 0) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (fun s => r s.st) (0 + nTrees (D.ds₁.take pre.length)) dB dt (errJ π r dt) := by
  obtain ⟨hS, k₁, k₂⟩ := opensShaped F file D h
  have hA := roundsOfData F file D h
  refine atPlace_cutJ _ π _ r D.ds₁ pre _ post (0) (allT D) dB dt
    hcons ?_ rfl (wants_first h pre _ post r₀ e key ft)
    (fun n x hx => (by rw [Nat.zero_add]; exact ((chainTrees D n x).1 hx))) ?_ ?_ hfree early
    answers planOk spend hj ho w0 l hw
  · have ed : F.roundsDeclaredByBlocks.1.dropLast = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post) := by
      rw [e]
      simp only [← List.append_assoc, List.dropLast_concat]
    rw [← ed]
    exact hA.1
  · intro r' hr o ho'
    exact hS.1 r' (by rw [e]; simp [hr]) o ho'
  · intro m
    simp [numAt]

/-- **At the shared chain.** -/
theorem atPlace_sharedJ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (pre post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.1 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post))
    (dB : RDT) (dt : List RDT)
    (hcons : dB :: dt =
      (D.ds₂.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (hj : johOk π r = true) (ho : π.nums.ownMask = false) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l)) :
    AtPlace (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 1) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (fun s => r s.st) (D.t₁ + nTrees (D.ds₂.take pre.length)) dB dt (errJ π r dt) := by
  obtain ⟨hS, k₁, k₂⟩ := opensShaped F file D h
  have hA := roundsOfData F file D h
  refine atPlace_cutJ _ π _ r D.ds₂ pre _ post (D.t₁) (allT D) dB dt
    hcons ?_ rfl (wants_shared h pre _ post e key ft)
    (fun n x hx => (chainTrees D n x).2.1 hx) ?_ ?_ hfree early
    answers planOk spend hj ho w0 l hw
  · rw [← e]
    exact hA.2.1
  · intro r' hr o ho'
    exact hS.2.1 r' (by rw [e]; simp [hr]) o ho'
  · intro m
    simp [numAt, k₁]

/-- **At the last chain.** -/
theorem atPlace_lastJ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (pre post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.2 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post))
    (dB : RDT) (dt : List RDT)
    (hcons : dB :: dt =
      (D.ds₃.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (hj : johOk π r = true) (ho : π.nums.ownMask = false) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l)) :
    AtPlace (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 2) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (fun s => r s.st) (D.t₁ + D.t₂ + nTrees (D.ds₃.take pre.length)) dB dt (errJ π r dt) := by
  obtain ⟨hS, k₁, k₂⟩ := opensShaped F file D h
  have hA := roundsOfData F file D h
  refine atPlace_cutJ _ π _ r D.ds₃ pre _ post (D.t₁ + D.t₂) (allT D) dB dt
    hcons ?_ rfl (wants_last h pre _ post e key ft)
    (fun n x hx => (chainTrees D n x).2.2 hx) ?_ ?_ hfree early
    answers planOk spend hj ho w0 l hw
  · rw [← e]
    exact hA.2.2
  · intro r' hr o ho'
    exact hS.2.2 r' (by rw [e]; simp [hr]) o ho'
  · intro m
    simp [numAt, k₁, k₂]

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlace_firstJ
#print axioms VerifiableInference.Desc.K12.Coin.atPlace_sharedJ
#print axioms VerifiableInference.Desc.K12.Coin.atPlace_lastJ
