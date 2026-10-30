-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.GameKAtGu
import Johnson.Desc.K12.Coin.GameAtFieldScope
/-
Johnson/Loose/H2K12/GameKAtGuField.lean: THE JOIN: THE KEY's-SIDE LAW AT G_u's SEAT OF THE PROOF
FILE's SEATED DESCRIPTION, AT THE RULE's OWN LETTERS: the row is read through atDesc, the
data are writtenPFull.at frS.P.T.a, the chain's first tree's number is that data's t₁: as
Johnson/Desc/Plain/BothAtDesc.lean's rule asks its e₂. ONE CALL of Coin/GameAtFieldScope.lean's
gameK_at_field_scope (general in the description; its premises on the seat left free), paid at
descN's shared cut by the same facts as GameKAtGu.lean's (gathered here under one name:
gu_facts). NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO
NEW MATHEMATICS.
  dField · frField     the rule's data and the shared chain's frame at them.
  gu_facts             what the law's callers ask of the place pGu N, in scope: eight facts in one.
  GameKGuField         the conclusion under a name.
  gameK_at_Gu_field · gameK_at_Gu_field_laid     from the five · from InScope and proofDataAndDecisionOfPublicFiles's
      yes.
WHAT IT IS NOT: the first and the third of the rule's three clauses at this one index (LeadsK |
LeadsBN · KeyLaw), at one p: not the second (what our
relation hands to the next piece's condition), not the other pieces of the row · AtCap rest₂ is the
letters of record's own word: a premise on the filling · G_u's seat alone.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes.Maker (RDT WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (QV nlAt Rides)
open H2K.Member (rUFull)
open Johnson.G (writtenPFull)
open scoped ENNReal

/-- The rule's data: the written data at the table's depth of record. -/
abbrev dField : WholeD := writtenPFull.at OnBytes.Slice.frS.P.T.a

/-- The shared chain's frame at them. -/
abbrev frField : Frame := frameAt dField (Sound.allOf dField) dField.key₂ 0

/-- What the law's callers ask of the place pGu N, in scope. -/
theorem gu_facts (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    (pGu N).nums.free = Johnson.G.OfPlan.rootsOf
        ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)) ∧
      Coin.ClosedL (pGu N) rUFull 1 0 0 Coin.At.TUFull ∧ (pGu N).nums.ownMask = false ∧
      Coin.ownLabelsFreeB (pGu N) = true ∧ 0 < (pGu N).nums.free := by
  obtain ⟨hW, _, _⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hC := (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hC.plan
  have e1 : (pGu N).nums.free = H2K.Member.piUFull.nums.free :=
    (congrArg (·.free) hn).trans (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW)
  refine ⟨(congrArg (·.free) hn).trans (plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).1.2, hC,
    ownMask_in_scope_U hS Z hZ mk N c hN hp,
    H2K.Sizes.labels_U_of_full A hN _ hC.plan
      (rounds_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW), ?_⟩
  rw [e1]
  decide

/-- The first and the third clause of the rule's e₂ at G_u's index, at the rule's own letters. -/
def GameKGuField {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (f : Xi' → ProofFile.Inst) : Prop :=
  ∀ (b₁ : Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl)
    (l₁ : List (Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl))
    (b₂ : Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl)
    (l₂ : List (Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl))
    (b₃ : Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl)
    (l₃ : List (Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt dField (Sound.allOf dField) dField.key₁ 0)
        ((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) frField
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) ×
          (seatedAt o mk Z N c f).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two)
        (frameAt dField (Sound.allOf dField) dField.key₃ (seatedAt o mk Z N c f).lastChainFirstTreeNumber)
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁ × (seatedAt o mk Z N c f).S₂) ×
          (seatedAt o mk Z N c f).S₃) W ds)
    (d wEnd : W) (_ : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) (rd : ℕ → ℕ)
    (_ : AtCap rest₂) (n : ℕ),
    ∃ p,
      ((atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length]? = some p ∧
      p.b = held (guEntry ProofFile.Cl N) ∧
      p.base = dField.t₁ + nTrees (dField.ds₂.take 8) ∧
      p.ior.red.LeadsK (actAt frField Prod.snd dField.t₁ p.base).2 (fun _ => True)
        (fun x y => (QV frField (pGu N) (nlAt (pGu N) dField.t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField p.base x y) p.err ∧
      p.ior.red.LeadsBN (actAt frField Prod.snd dField.t₁ p.base).2 (fun _ => True)
        (fun x y => (QV frField (pGu N) (nlAt (pGu N) dField.t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField p.base x y) n p.err ∧
      p.ior.red.KeyLaw (actAt frField Prod.snd dField.t₁ p.base).2
        (actAt frField Prod.snd dField.t₁ (p.base + p.trees)).2

/-- From the five. -/
theorem gameK_at_Gu_field {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : GameKGuField W o mk Z N c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap n
  obtain ⟨hfree, hC, ho, hlb, hf⟩ := gu_facts o S hS Z hZ mk N c hN hp hpin
  obtain ⟨b', post', e⟩ := shared_behind ProofFile.Cl (p14N Z N) N
  have hcut : b₂ :: l₂ = sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++
      guEntry ProofFile.Cl N :: b' :: post' := by
    rw [← e]
    exact hfl.symm.trans (descN_shared o mk guardedProximityTestParts Z N c)
  obtain ⟨ha, hD⟩ := Coin.depth_in_scope (seatedAt o mk Z N c f) S hS hpin
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  have hl := (stretch_at_U o S.pol S.lay S.KL Z hZ mk N c hN hp _ hW 8
    H2K.Member.bat_UFull).2.2.1
  obtain ⟨p, h1, h2, h3, h4, h5, h6⟩ := Coin.gameK_at_field (seatedAt o mk Z N c f) "proof file"
    writtenPFull hD OnBytes.Slice.frS.P.T.a ha b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd (pGu N)
    rUFull (Seat.enter (·.gU) (·.firstMask)) Seat.leave
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N) b' post' hfl hcut
    (guEntry_alike ProofFile.Cl N) hfree hC.plan hC.chain hC.joh hC.bat ho hlb hf rd hcap n
  exact ⟨p, h1, h2, h3.trans (congrArg (fun m => dField.t₁ + nTrees (dField.ds₂.take m)) hl), h4,
    h5, h6⟩

/-- Of the value that is laid. -/
theorem gameK_at_Gu_field_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧ dField = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      GameKGuField W o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨ha, hD'⟩ := Coin.depth_in_scope _ S hS hpin
  exact ⟨Z, N, c, hZ, hN, hF, Except.ok.inj (hD.symm.trans hD'),
    Coin.at_of_depth _ _ (ha.trans (Coin.data_depth _ _ _ hD').symm), hr,
    gameK_at_Gu_field W o S hS Z hZ _ N c hN hp hpin _⟩

end H2K.JointK

#print axioms H2K.JointK.gu_facts
#print axioms H2K.JointK.gameK_at_Gu_field
#print axioms H2K.JointK.gameK_at_Gu_field_laid
