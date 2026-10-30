-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.ReadsKey
import Johnson.Desc.K12.Coin.TileIsField
/-
Johnson/Desc/K12/Coin/GameAtField.lean: THE GAME OF THE PROXIMITY TEST WITH A KEY (first arm; every piece's errors the cap: gameK_at_tile₂_cap, Johnson/Desc/K12/Coin/ReadsKey.lean) AT THE OWN LETTERS OF THE RULE THAT TAKES A DESCRIPTION's PIECES TO THE PROOF FILE's GOAL (proofSound_at_descB, Johnson/Desc/Plain/BothAtDesc.lean): the row (atDesc F T).p₂ :: (atDesc F T).l₂ · the data DP.at a · the window's lower end (DP.at a).t₁. A CARRIAGE: IT PAYS NO LAW. NO SOUNDNESS AND NO LEVEL IS CLAIMED. NOTHING ON HIDING.
  gameK_at_field   F.data file = .ok DP · a = F.tableDepth · gameK_at_tile₂_cap's own premises at D := DP.at a ⇒ its conclusion with the row written through atDesc and F.t₁ written (DP.at a).t₁
THE ONE PREMISE THAT IS NEW: a = F.tableDepth: NOT BY TYPE (Johnson/Desc/K12/Coin/TileIsField.lean: data_at; at_not shows that it is spent).
All that stands first at the head of ReadsKey.lean stands here.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pub (johOk batV0 batPriceOk)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal


theorem gameK_at_field {Xi W : Type} (F : FileDescription Xi) (file : String) (DP : WholeD)
    (h : F.data file = .ok DP) (a : ℕ) (ha : a = F.tableDepth)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
        ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
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
      ((atDesc F (piecesAt (ckP .two) F (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc F (piecesAt (ckP .two) F (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).l₂)[pre.length]? = some p ∧
      p.b = held B ∧
      p.base = (DP.at a).t₁ + nTrees ((DP.at a).ds₂.take (pre.flatMap (·.rounds)).length) ∧
      p.ior.red.LeadsK
        (actAt (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (DP.at a).t₁ p.base).2 (fun _ => True)
        (fun x y => (QV (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) π
            (nlAt π (DP.at a).t₁) r rd enter leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) p.base x y) p.err ∧
      p.ior.red.LeadsBN
        (actAt (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (DP.at a).t₁ p.base).2 (fun _ => True)
        (fun x y => (QV (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) π
            (nlAt π (DP.at a).t₁) r rd enter leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) p.base x y) N p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (DP.at a).t₁ p.base).2
        (actAt (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (DP.at a).t₁ (p.base + p.trees)).2 := by
  have e : F.t₁ = (DP.at a).t₁ := lo_is_field F file DP h a
  have g := gameK_at_tile₂_cap F file (DP.at a) (data_at F file DP h a ha) b₁ l₁ b₂ l₂ b₃ l₃ rest₁
    rest₂ rest₃ d wEnd π r enter leave pre B b' post hfl hcut hal hfree hp hC hj hbat ho hlb hf rd
    hcap N
  rw [e] at g
  exact g

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_field
