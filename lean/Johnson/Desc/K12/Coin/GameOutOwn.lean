-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameOutOwn.lean: GameOut.lean's like at the second arm (the first fold sends
its own mask): the test's own decision's yes laid into the game's relation. One definition, two
statements with proofs; made of GameOut.lean's text by program.

What it is not, first: all that stands first at the heads of GameOut.lean and ReadsKeyOwn.lean.
Main names.
  `QWO`, `qwo_of_yes`: `QVO` (ReadsKeyOwn.lean) with the record that the way out takes pinned: it is
    what the test's decision left. `QWO.outAll`: the readable face (`OutAll`, GameOut.lean).
  `gameK_at_tile₂O_out`: `gameK_at_tile₂O_cap` (ReadsKeyOwn.lean) with `QWO` in the place of `QVO`.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.GameOut
import Johnson.Desc.K12.Coin.ReadsKeyOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pub (johOk batV0 batPriceOk)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

/-- The second arm's relation; the record that the way out takes to the record behind is what the
test's yes left. -/
def QWO {P S : Type} (F : Frame) (π : P12) (t₁ t₂ ch : ℕ) (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × F.E.Str) : Prop :=
  ∃ t tE, enter a.1.2 = .ok t ∧ leave a.1.2 tE = .ok b.1.2 ∧
    QO F π t₁ t₂ ch (fun s => r s.st) rd (t, a.2) ∧
    ∃ rs gs, (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE

/-- The readable face: what that yes leaves. -/
theorem QWO.outAll {P S : Type} {F : Frame} {π : P12} {t₁ t₂ ch : ℕ} {r : Fmt.M1.Stage → ℕ}
    {rd : ℕ → ℕ} {enter : S → Except String T12} {leave : S → T12 → Except String S}
    {a b : (P × S) × F.E.Str} (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (h : QWO F π t₁ t₂ ch r rd enter leave a b) :
    ∃ t tE, enter a.1.2 = .ok t ∧ leave a.1.2 tE = .ok b.1.2 ∧ OutAll π t tE := by
  obtain ⟨t, tE, h1, h2, _, rs, gs, h3⟩ := h
  exact ⟨t, tE, h1, h2, outAll_of_yes π hp t tE rs gs h3⟩

theorem qwo_of_yes {P S Cl' W : Type} {F : Frame} (π : P12) (t₁ t₂ ch : ℕ)
    (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (p : Piece (ckP .two) F (P × S) Cl' W) (B : Block S Cl')
    (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (a b : (P × S) × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) p.ds)) (h : p.ior.red.out a τ = some b)
    (hq : QVO F π t₁ t₂ ch r rd enter leave a b) : QWO F π t₁ t₂ ch r rd enter leave a b := by
  obtain ⟨t, tE, gs, h1, h2, h3⟩ := held_yes p B hb (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave
    hal a b τ h
  obtain ⟨t', _, h1', _, hN⟩ := hq
  obtain rfl : t = t' := Except.ok.inj (h1.symm.trans h1')
  exact ⟨t, tE, h1, h3, hN, _, gs, h2⟩

/-- **`gameK_at_tile₂O_cap` (ReadsKeyOwn.lean) with `QWO` in the place of `QVO`.** -/
theorem gameK_at_tile₂O_out {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
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
    (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true) (hfr : 0 < π.nums.free)
    (rd : ℕ → ℕ) (hcap : AtCap rest₂)
    (N : ℕ) :
    ∃ p,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧
      p.ior.red.LeadsK
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QWO (frameAt D (allOf D) D.key₂ 0) π F.t₁ F.t₂ 1 r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (frameAt D (allOf D) D.key₂ 0) p.base a b) p.err ∧
      p.ior.red.LeadsBN
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QWO (frameAt D (allOf D) D.key₂ 0) π F.t₁ F.t₂ 1 r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (frameAt D (allOf D) D.key₂ 0) p.base a b) N p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, hrow, hpb, hpbase, hK, hBN, hLaw⟩ :=
    gameK_at_tile₂O_cap F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r enter leave pre
      B b' post hfl hcut hal hfree hp hC hj hbat hown hPl hne hfr rd hcap N
  exact ⟨p, hrow, hpb, hpbase,
    hK.conseq (fun _ x => x) fun a τ b _ hout hq =>
      ⟨⟨qwo_of_yes π _ _ _ r rd enter leave p B hpb hal a b τ hout hq.1.1, hq.1.2⟩, hq.2⟩,
    hBN.conseq (fun _ x => x) fun a τ b _ hout hq =>
      ⟨⟨qwo_of_yes π _ _ _ r rd enter leave p B hpb hal a b τ hout hq.1.1, hq.1.2⟩, hq.2⟩,
    hLaw⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.QWO.outAll
#print axioms VerifiableInference.Desc.K12.Coin.qwo_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂O_out
