-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12AtPlaceRowJ.lean: THE PUBLIC PREMISES OF THE PROXIMITY TEST's LAW (`AtPlace`) AT THE MAKER's OWN PIECE OF A DESCRIPTION's FIRST CHAIN, AT THE LIBRARY's JOHNSON LETTERS AND THE PLACE's OWN ERRORS: atPlace_row₁ (Johnson/RunOne/Law/K12AtPlaceRow.lean) again, with its two premises on numbers, the facts on codes and "the errors bear the chain's", PAID BY ONE TEST ON THE PLAN. One statement with its proof.
OBJECT. As K12AtPlaceRow.lean's. USER. Whoever pays a field of the key file's tables at the first chain's proximity test.
LETTERS. F D c₁ k₁ n π: free. r: the radius of each stage. Premises: atPlace_row₁'s, LESS the five letters of the facts on codes, εt, codes, bears; WITH johOk π r = true.

  atPlace_row₁J: the statement: AtPlace at Sg.lstJ Sg.flC Sg.flZ Sg.flZ, the radii r, and the errors errJ π r dt.
BY: ONE CALL of atPlace_firstJ (Johnson/Desc/K12/Coin/AtDescJ.lean: atPlace_first, AtDesc.lean beside it, with codes paid by codes_of_johOk, Johnson/Desc/K12/Law/CodesJoh.lean, and bears by bears_errJ, Johnson/Desc/K12/Coin/GameJ.lean, over like_of_cut); and K12AtPlaceRow.lean's before_held over cutDs_inner | cutBase_eq (Johnson/Top/Fire/Code/RowCut.lean).
Limits. errJ π r dt is AN εt that bears: that it is the least is shown by nobody. The facts on codes come from johOk through the theorem on codes (Cb/Bridge/GlCodesProved.lean's head says on what that rests). "free" above all is still shown of no test. The first arm and the first chain alone. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12AtPlaceRow
import Johnson.Desc.K12.Coin.AtDescJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12AtPlaceRow
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin
open H2K.Pub (writtenOf WR spendOk johOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Law.RoundsInFront
open LPFD (before cutBase cutDs cutDs_inner cutBase_eq)

/-- **`AtPlace` at the maker's n-th piece of the first chain, from `johOk`.** -/
theorem atPlace_row₁J {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl))
    (hf : F.first.blocksInOrder = c₁ :: k₁) (n : ℕ) (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b)
    (hn : n < k₁.length) (π : P12) (hr : b.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (post : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hpost : ((c₁ :: k₁).drop (n + 1)).flatMap (·.rounds) = post ++ [r₀])
    (r : Fmt.M1.Stage → ℕ) (dB : RDT) (dt : List RDT)
    (hcons : cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n = dB :: dt)
    (hfree : π.nums.free = rootsOf (((c₁ :: k₁).take n).flatMap (·.rounds)))
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (hj : johOk π r = true) (ho : π.nums.ownMask = false) (w0 : WR) (l : List WR)
    (hw : writtenOf π.nums = some (w0 :: l)) :
    AtPlace (frameAt D (allOf D) D.key₁ 0) π (numAt F.t₁ F.t₂ 0) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st)
      (cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) dB dt (errJ π r dt) := by
  have e : F.roundsDeclaredByBlocks.1 = ((c₁ :: k₁).take n).flatMap (·.rounds) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (post ++ [r₀])) := by
    show F.first.blocksInOrder.flatMap (·.rounds) = _
    rw [hf, rounds_part (c₁ :: k₁) n b hb, hr, hpost]
  have hb' : ((held c₁ : Block (F.XiPub × F.S₁) F.Cl) :: k₁.map held)[n]? = some (held b) := by
    have : ((c₁ :: k₁).map (held (P := F.XiPub)))[n]? = some (held b) := by
      rw [List.getElem?_map, hb]; rfl
    exact this
  have hn' : n < (k₁.map (held (P := F.XiPub))).length := by rw [List.length_map]; exact hn
  have ed := cutDs_inner (k₁.map (held (P := F.XiPub))) n D.ds₁ (held c₁) (held b) hn' hb'
  have eb := cutBase_eq (k₁.map (held (P := F.XiPub))) n 0 D.ds₁ (held c₁) (Nat.le_of_lt hn')
  rw [before_held] at ed eb
  rw [eb]
  have hc : dB :: dt = (D.ds₁.drop (((c₁ :: k₁).take n).flatMap (·.rounds)).length).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length := by
    rw [← hcons, ed, ← hr]
    rfl
  exact atPlace_firstJ F file D h D.key₁ 0 π r _ post r₀ e dB dt hc hfree early answers planOk spend
    hj ho w0 l hw

end Johnson.RunOne.Law.K12AtPlaceRow

#print axioms Johnson.RunOne.Law.K12AtPlaceRow.atPlace_row₁J
