-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.GameAtField
import Johnson.Goal.Numbers.PlanWrittenDescScope
import Johnson.Flat.Dec.FitAtWritten
/-
Johnson/Desc/K12/Coin/GameAtFieldScope.lean: gameK_at_field (Johnson/Desc/K12/Coin/GameAtField.lean) IN SCOPE: AT THE LETTERS THAT STAND IN THE RULE's CALLERS: the data writtenPFull.at frS.P.T.a. The two premises on the data (F.data's yes; a = F.tableDepth) are paid by two theorems: seat_in_scope (Johnson/Goal/Numbers/PlanWrittenDescScope.lean: in scope a description that passes the pinned seat's test has tableDepth = 32 and F.data "proof file" = .ok writtenPFull) and fr_a (Johnson/Flat/Dec/FitAtWritten.lean: frS.P.T.a = 32). A CARRIAGE: IT PAYS NO LAW. NO SOUNDNESS AND NO LEVEL IS CLAIMED. NOTHING ON HIDING.
  depth_in_scope        VerifierAndGoals.InScope Z = true · seatPinnedProof Z.pol F = true ⇒ frS.P.T.a = F.tableDepth ∧ F.data "proof file" = .ok writtenPFull
  gameK_at_field_scope  these two · gameK_at_tile₂_cap's own premises at D := writtenPFull.at frS.P.T.a ⇒ OF gameK_at_field's conclusion there: the row's entry number pre.length is p · p.b = held B · THE LAW FOR A BATCH (LeadsBN at every number N of slots) at p's own errors: what the rule's clause on the shared chain's row asks; the law with the key, the law of keys and p.base are gameK_at_field's to give
THAT THE SEATED DESCRIPTION PASSES seatPinnedProof IS A PREMISE HERE. NEIGHBOURS: Johnson/Flat/Dec/DataAtWritten.lean: writtenPFull_at · data_at_written: the same carriage at the closed terms.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.PlanWritten (seat_in_scope seatPinnedProof)
open Johnson.G (fr_a writtenPFull)
open OnBytes.Flat
open H2K.Pub (johOk batV0 batPriceOk)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

theorem depth_in_scope {Xi : Type} (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles)
    (hZ : VerifierAndGoals.InScope Z = true) (hpin : seatPinnedProof Z.pol F = true) :
    frS.P.T.a = F.tableDepth ∧ F.data "proof file" = .ok writtenPFull := by
  obtain ⟨_, hd, hdata⟩ := seat_in_scope Xi F Z hZ hpin
  exact ⟨fr_a.trans hd.symm, hdata⟩


theorem gameK_at_field_scope {Xi W : Type} (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles)
    (hZ : VerifierAndGoals.InScope Z = true) (hpin : seatPinnedProof Z.pol F = true)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a))
        (writtenPFull.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a))
        (writtenPFull.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a))
        (writtenPFull.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (rd : ℕ → ℕ) (hcap : AtCap rest₂)
    (N : ℕ) :
    ∃ p,
      ((atDesc F (piecesAt (ckP .two) F (writtenPFull.at frS.P.T.a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd)).p₂ ::
        (atDesc F (piecesAt (ckP .two) F (writtenPFull.at frS.P.T.a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd)).l₂)[pre.length]? = some p ∧
      p.b = held B ∧
      p.ior.red.LeadsBN
        (actAt (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a))
          (writtenPFull.at frS.P.T.a).key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂)
          (writtenPFull.at frS.P.T.a).t₁ p.base).2 (fun _ => True)
        (fun x y => (QV (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a))
            (writtenPFull.at frS.P.T.a).key₂ 0) π (nlAt π (writtenPFull.at frS.P.T.a).t₁) r rd enter
            leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a))
            (writtenPFull.at frS.P.T.a).key₂ 0) p.base x y) N p.err := by
  obtain ⟨ha, hdata⟩ := depth_in_scope F Z hZ hpin
  obtain ⟨p, h1, h2, _, _, h5, _⟩ := gameK_at_field F "proof file" writtenPFull hdata frS.P.T.a ha b₁
    l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r enter leave pre B b' post hfl hcut hal hfree hp hC hj
    hbat ho hlb hf rd hcap N
  exact ⟨p, h1, h2, h5⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.depth_in_scope
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_field_scope
