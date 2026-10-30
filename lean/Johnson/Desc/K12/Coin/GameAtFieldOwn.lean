-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.ReadsKeyOwn
import Johnson.Desc.K12.Coin.GameAtFieldScope
/-
Johnson/Desc/K12/Coin/GameAtFieldOwn.lean: THE SECOND ARM (the place's first fold sends its own mask: the test on G_omega): THE GAME WITH A KEY (every piece's errors the cap: gameK_at_tile₂O_cap, Johnson/Desc/K12/Coin/ReadsKeyOwn.lean) AT THE OWN LETTERS OF THE RULE THAT TAKES A DESCRIPTION's PIECES TO THE PROOF FILE's GOAL (proofSound_at_descB, Johnson/Desc/Plain/BothAtDesc.lean); AND IN SCOPE. After the first arm's GameAtField.lean | GameAtFieldScope.lean; made by program off these two. A CARRIAGE: IT PAYS NO LAW. NO SOUNDNESS AND NO LEVEL IS CLAIMED. NOTHING ON HIDING.
  t₂_is_field            F.data file = .ok D ⇒ F.t₂ = (D.at a).t₂ (opensShaped's third clause; the second arm's relation reads F.t₂ too)
  gameK_at_fieldO        F.data file = .ok DP · a = F.tableDepth · gameK_at_tile₂O_cap's own premises at D := DP.at a ⇒ its conclusion with the row written through atDesc, F.t₁ written (DP.at a).t₁ and F.t₂ written (DP.at a).t₂
  gameK_at_fieldO_scope  VerifierAndGoals.InScope Z = true · seatPinnedProof Z.pol F = true · the same premises at D := writtenPFull.at frS.P.T.a ⇒ THE WHOLE CONCLUSION there (the row's entry · p.b · p.base · LeadsK · LeadsBN · KeyLaw)
All that stands first at the heads of ReadsKeyOwn.lean, GameAtField.lean and GameAtFieldScope.lean stands here.
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

theorem t₂_is_field {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (a : ℕ) : F.t₂ = (D.at a).t₂ :=
  (opensShaped F file D h).2.2.symm


theorem gameK_at_fieldO {Xi W : Type} (F : FileDescription Xi) (file : String) (DP : WholeD)
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
    (hbat : batPriceOk π r 128 = true) (hown : π.nums.ownMask = true)
    (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free) (rd : ℕ → ℕ)
    (hcap : AtCap rest₂)
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
        (fun x y => (QVO (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) π
            (DP.at a).t₁ (DP.at a).t₂ 1 r rd enter leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) p.base x y) p.err ∧
      p.ior.red.LeadsBN
        (actAt (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (DP.at a).t₁ p.base).2 (fun _ => True)
        (fun x y => (QVO (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) π
            (DP.at a).t₁ (DP.at a).t₂ 1 r rd enter leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0) p.base x y) N p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (DP.at a).t₁ p.base).2
        (actAt (frameAt (DP.at a) (Sound.allOf (DP.at a)) (DP.at a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (DP.at a).t₁ (p.base + p.trees)).2 := by
  have e : F.t₁ = (DP.at a).t₁ := lo_is_field F file DP h a
  have e2 : F.t₂ = (DP.at a).t₂ := t₂_is_field F file DP h a
  have g := gameK_at_tile₂O_cap F file (DP.at a) (data_at F file DP h a ha) b₁ l₁ b₂ l₂ b₃ l₃ rest₁
    rest₂ rest₃ d wEnd π r enter leave pre B b' post hfl hcut hal hfree hp hC hj hbat hown hPl hne hfr
    rd hcap N
  rw [e, e2] at g
  exact g


theorem gameK_at_fieldO_scope {Xi W : Type} (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles)
    (hZ : VerifierAndGoals.InScope Z = true) (hpin : seatPinnedProof Z.pol F = true)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0)
        ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (hown : π.nums.ownMask = true)
    (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free) (rd : ℕ → ℕ)
    (hcap : AtCap rest₂)
    (N : ℕ) :
    ∃ p,
      ((atDesc F (piecesAt (ckP .two) F (writtenPFull.at frS.P.T.a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc F (piecesAt (ckP .two) F (writtenPFull.at frS.P.T.a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).l₂)[pre.length]? = some p ∧
      p.b = held B ∧
      p.base = (writtenPFull.at frS.P.T.a).t₁ + nTrees ((writtenPFull.at frS.P.T.a).ds₂.take (pre.flatMap (·.rounds)).length) ∧
      p.ior.red.LeadsK
        (actAt (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (writtenPFull.at frS.P.T.a).t₁ p.base).2 (fun _ => True)
        (fun x y => (QVO (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0) π
            (writtenPFull.at frS.P.T.a).t₁ (writtenPFull.at frS.P.T.a).t₂ 1 r rd enter leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0) p.base x y) p.err ∧
      p.ior.red.LeadsBN
        (actAt (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (writtenPFull.at frS.P.T.a).t₁ p.base).2 (fun _ => True)
        (fun x y => (QVO (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0) π
            (writtenPFull.at frS.P.T.a).t₁ (writtenPFull.at frS.P.T.a).t₂ 1 r rd enter leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0) p.base x y) N p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (writtenPFull.at frS.P.T.a).t₁ p.base).2
        (actAt (frameAt (writtenPFull.at frS.P.T.a) (Sound.allOf (writtenPFull.at frS.P.T.a)) (writtenPFull.at frS.P.T.a).key₂ 0)
          (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) (writtenPFull.at frS.P.T.a).t₁ (p.base + p.trees)).2 := by
  obtain ⟨ha, hdata⟩ := depth_in_scope F Z hZ hpin
  exact gameK_at_fieldO F "proof file" writtenPFull hdata frS.P.T.a ha b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
    rest₃ d wEnd π r enter leave pre B b' post hfl hcut hal hfree hp hC hj hbat hown hPl hne hfr rd hcap
    N

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.t₂_is_field
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_fieldO
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_fieldO_scope
