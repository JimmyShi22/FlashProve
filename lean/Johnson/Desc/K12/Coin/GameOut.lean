-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameOut.lean: what a yes of the proximity test's piece (the kind K12) hands on
of the record behind, for certain, laid into the game's relation. Definitions, statements and
proofs; each proof is a row of calls.

Why. In the game's relation `QV` (ReadsKey.lean) the record t' that the way out takes to the record
behind is under «there is» and tied by nothing else. A yes says more: t' is what the test's own
decision left. `QW` lays that decision's yes itself into the relation (its rounds and columns under
«there is»: a relation has no transcript): so whatever a yes of the decision gives is a corollary.
Of it stand: `k12_out`, `k12_out2`, `k12_out3`
(Johnson/Desc/K12/Law/OutK.lean, OutK2.lean, OutK3.lean), `k12_guards` (TopH.lean): gathered in
`OutAll`. t' stays under «there is»: at the seat's own doors (Johnson/Desc/K12/Seat.lean) the record
behind is the record in front with the statement, the book and the roots of t': these three are
fixed by the record behind; of the rest of t' `OutAll` speaks.
Whose is what. Called: `piece_yes` (Johnson/Desc/K14/Law/Bridge.lean: a piece's yes is its block's
decision's yes at the piece's own rounds); `decide_below_lift`
(Johnson/Desc/Sound/FenceK14AtDesc.lean: a yes of the block with the test in front, lifted, is a yes
of the block); `inside_ok` (Johnson/Desc/K12/SeatLaws.lean); `Alike` (Alike.lean); `LeadsK.conseq`,
`LeadsBN.conseq` (Johnson/Desc/Plain/Keyed.lean, KeyAlone.lean), whose step on relations has the yes
in hand.
What it is not, first.
  (1) `QW` is no function of the keys and need not be: it is laid behind the law with the key.
  (2) It pays no clause of the rule's premise: it is what the payer of «the relation gives the next
    piece's promise» gets of the record behind. Which of it the next condition wants is the rule's
    table's to say.
  (3) Of the strings behind nothing is said beyond `Rides`.
  (4) All that stands first at the head of ReadsKey.lean stands here.
Main names.
  `held_yes`: general in the block K: a yes of a piece that holds an entry alike to K inside two
    doors: the door lets in, K's decision says yes at the piece's own rounds, the way out gives the
    record behind.
  `OutAll π t0 tE`, `outAll_of_yes`: what a yes of the test's decision leaves, gathered.
  `QW`, `qw_of_yes`: the game's relation with the test's own yes laid in: t' is what that decision
    left. `QW.outAll`: the readable face.
  `gameK_at_tile₂_out`: `gameK_at_tile₂_cap` with `QW` in the place of `QV`.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.ReadsKey
import Johnson.Desc.K14.Law.Bridge
import Johnson.Desc.Sound.FenceK14AtDesc
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Law.TopH
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pub (johOk batV0 batPriceOk)
open H2K.Pin (NTuple)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

/-! ## A yes of the piece is a yes of the block inside its doors -/

/-- **General in the block K.** -/
theorem held_yes {P S T Cl Cl' W : Type} {C : PQ.CK} {F : Frame} (p : Piece C F (P × S) Cl' W)
    (B : Block S Cl') (hb : p.b = held B) (K : Block T Cl) (enter : S → Except String T)
    (leave : S → T → Except String S) (hal : Alike (K.inside enter leave) B)
    (a b : (P × S) × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some b) :
    ∃ t tE gs, enter a.1.2 = .ok t ∧
      K.decide t ((OnBytes.Maker.rvT C p.ds τ ++ p.back).map noDigest) gs = .ok tE ∧
      leave a.1.2 tE = .ok b.1.2 := by
  obtain ⟨_, gs, hd⟩ := _root_.Desc.K14.Law.piece_yes p a τ b h
  rw [hb] at hd
  obtain ⟨hB, _⟩ := _root_.Desc.K14.Law.Fence.decide_below_lift B a.1 b.1 _ gs hd
  rw [hal.decide] at hB
  obtain ⟨t, tE, h1, h2, h3⟩ :=
    (VerifiableInference.Desc.K12.Seat.inside_ok enter K leave a.1.2 b.1.2 _ gs).1 hB
  exact ⟨t, tE, gs, h1, h2, h3⟩

/-! ## What a yes of the test's decision leaves -/

/-- What a yes of the test's decision leaves, gathered. -/
structure OutAll (π : P12) (t0 tE : T12) : Prop where
  out : H2K.Out.OutK t0 tE
  out2 : ∃ G, H2K.Out.OutK2 t0 tE (π.nums.stages.length - 1) G
  out3 : H2K.Out.OutK3 t0 tE
  free : π.nums.free = t0.roots
  pub : H2K.Pub.pubOk π t0.st.codes = true

theorem outAll_of_yes (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t0 rs gs = .ok tE) : OutAll π t0 tE := by
  have he := H2K.JointK.early_of_planOk π hp
  have ha := H2K.JointK.answers_of_planOk π hp
  obtain ⟨g1, g2, _⟩ := H2K.JointK.k12_guards π he t0 tE rs gs hp h
  exact ⟨H2K.Out.k12_out π he ha t0 tE rs gs h, H2K.Out.k12_out2 π he ha t0 tE rs gs h,
    H2K.Out.k12_out3 π he ha t0 tE rs gs h, g1, g2⟩

/-! ## The game's relation with t' pinned -/

/-- The game's relation; the record that the way out takes to the record behind is what the test's
yes left. -/
def QW {P S : Type} (F : Frame) (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × F.E.Str) : Prop :=
  ∃ t tE, enter a.1.2 = .ok t ∧ leave a.1.2 tE = .ok b.1.2 ∧
    QN π (NTuple F π (nuOf π nl t) (fun s => r s.st) rd) (t, a.2) ∧
    ∃ rs gs, (proximityTestKind guardedProximityTestParts π : Block T12 Unit).decide t rs gs = .ok tE

/-- The readable face: what that yes leaves. -/
theorem QW.outAll {P S : Type} {F : Frame} {π : P12} {nl : ℕ → ℕ} {r : Fmt.M1.Stage → ℕ}
    {rd : ℕ → ℕ} {enter : S → Except String T12} {leave : S → T12 → Except String S}
    {a b : (P × S) × F.E.Str} (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (h : QW F π nl r rd enter leave a b) :
    ∃ t tE, enter a.1.2 = .ok t ∧ leave a.1.2 tE = .ok b.1.2 ∧ OutAll π t tE := by
  obtain ⟨t, tE, h1, h2, _, rs, gs, h3⟩ := h
  exact ⟨t, tE, h1, h2, outAll_of_yes π hp t tE rs gs h3⟩

theorem qw_of_yes {P S Cl' W : Type} {F : Frame} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (rd : ℕ → ℕ) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (p : Piece (ckP .two) F (P × S) Cl' W) (B : Block S Cl') (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (a b : (P × S) × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) p.ds)) (h : p.ior.red.out a τ = some b)
    (hq : QV F π nl r rd enter leave a b) : QW F π nl r rd enter leave a b := by
  obtain ⟨t, tE, gs, h1, h2, h3⟩ := held_yes p B hb (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave
    hal a b τ h
  obtain ⟨t', _, h1', _, hN⟩ := hq
  obtain rfl : t = t' := Except.ok.inj (h1.symm.trans h1')
  exact ⟨t, tE, h1, h3, hN, _, gs, h2⟩

/-! ## At the letters of record -/

/-- **`gameK_at_tile₂_cap` (ReadsKey.lean) with `QW` in the place of `QV`.** -/
theorem gameK_at_tile₂_out {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (rd : ℕ → ℕ) (hcap : AtCap rest₂)
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
        (fun a b => (QW (frameAt D (allOf D) D.key₂ 0) π (nlAt π F.t₁) r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (frameAt D (allOf D) D.key₂ 0) p.base a b) p.err ∧
      p.ior.red.LeadsBN
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QW (frameAt D (allOf D) D.key₂ 0) π (nlAt π F.t₁) r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (frameAt D (allOf D) D.key₂ 0) p.base a b) N p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, hrow, hpb, hpbase, hK, hBN, hLaw⟩ :=
    gameK_at_tile₂_cap F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r enter leave pre B
      b' post hfl hcut hal hfree hp hC hj hbat ho hlb hf rd hcap N
  exact ⟨p, hrow, hpb, hpbase,
    hK.conseq (fun _ x => x) fun a τ b _ hout hq =>
      ⟨⟨qw_of_yes π _ r rd enter leave p B hpb hal a b τ hout hq.1.1, hq.1.2⟩, hq.2⟩,
    hBN.conseq (fun _ x => x) fun a τ b _ hout hq =>
      ⟨⟨qw_of_yes π _ r rd enter leave p B hpb hal a b τ hout hq.1.1, hq.1.2⟩, hq.2⟩,
    hLaw⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.held_yes
#print axioms VerifiableInference.Desc.K12.Coin.outAll_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.QW.outAll
#print axioms VerifiableInference.Desc.K12.Coin.qw_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂_out
