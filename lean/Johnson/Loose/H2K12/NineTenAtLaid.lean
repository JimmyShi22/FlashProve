-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.GameKAtGomegaField
import Johnson.Desc.K12.Coin.NineTenFacts
import Johnson.Desc.K12.Law.FirstTreeOfMade
/-
Johnson/Loose/H2K12/NineTenAtLaid.lean: «THE JOIN OF THE TWO ROADS», OUR HALF, AT THE PROOF FILE: WHAT
THE SHARED CHAIN's LEDGER ASKS OF THE PLAN AND OF THE PIECE AT ITS BLOCKS 9 AND 10 (the proximity tests
on G_u and G_omega), AS FACTS AT LPFD.Full.proofDataAndDecisionOfPublicFiles's RETURN, IN SCOPE. The general half
(ownLabelsB_of_free · pins_at_tile₂ · NineFacts | TenFacts · nine_ | ten_facts_tile₂) stands in
Johnson/Desc/K12/Coin/NineTenFacts.lean; here stand the seated and the
laid forms, and ten's three premises on "BAT"'s round.
FACTS ON VALUES: IT PAYS NO LAW. NO SOUNDNESS AND NO LEVEL IS
CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  NineAtGu | TenAtGomega · nine_facts_at_Gu | ten_facts_at_Gomega   at the seated description, in
      scope, at the rule's own data dField := writtenPFull.at frS.P.T.a, AT EVERY FILLING OF piecesAt's
      LETTERS (no AtCap: nothing here reads the pieces' errors)
  nine_facts_laid | ten_facts_laid     VerifierAndGoals.InScope S · LPFD.Full.proofDataAndDecisionOfPublicFiles … = .ok (D, r) ⇒
      ∃ Z N c (nO), the returns ∧ …
  TenFacts.pays     ten_paid's | ten_at_K's hPay · h1 · hlog OFF TenFacts: PayPub π (fun s =>
      r s.st) dB.entry.rows (batV0 π r) ∧ Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] ∧
      dB.entry.logN ≤ 64: one call of pays_at_tile (Johnson/Desc/K12/Coin/LawAtTileOwn.lean) at
      ⟨place, small⟩ and joh
WHAT IS NOT HERE, FLATLY: herr (the askers' ε is a free letter, met by choice: not x.err) · hr | hle
(rfl | le_refl at our letters) · hsU | hsO | hms | Say and every premise on the table, the seam, the
members · hft's right side (P.par.toGPar.firstTree: 0 by its text: the caller's rfl) · THE CALL OF
nine_paid | ten_paid | nine_at_K | ten_at_K ITSELF: the fit is by reading until it is typed · "BAT"
stands in front of the chain: its number is priced in «small»; the law that this number bounds the
round's bad verifier messages is the game's.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes.Maker (RDT WholeD uLT)
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Member (rUFull rOFull)
open H2K.Pub (johOk batV0 batPriceOk PayPub)
open Johnson.G (writtenPFull)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

/-- The three premises that the second arm's game asks on "BAT"'s round, off TenFacts. -/
theorem TenFacts.pays {P₁ S Cl W : Type} {Fr : Frame} {π : P12} {r : Fmt.M1.Stage → ℕ} {t₁ t₂ : ℕ}
    {K : Block S Unit} {x : Piece (ckP .two) Fr (P₁ × S) Cl W} {dB : RDT} {dt : List RDT}
    (T : TenFacts Fr π r t₁ t₂ K x dB dt) :
    PayPub π (fun s => r s.st) dB.entry.rows (batV0 π r) ∧
      Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] ∧ dB.entry.logN ≤ 64 :=
  Coin.pays_at_tile ⟨T.place, T.small⟩ T.joh

/-- NineFacts at G_u's seat of the seated description, at the rule's own data, at every filling of
piecesAt's letters. -/
def NineAtGu {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
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
    (d wEnd : W) (_ : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂),
    ∃ x dB dt,
      ((piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length]? = some x ∧
      NineFacts frField (pGu N) rUFull (seatedAt o mk Z N c f).t₁ (seatedAt o mk Z N c f).t₂
        (Seat.onGu (proximityTestKind guardedProximityTestParts (pGu N) : Block T12 Unit)) x dB dt

/-- TenFacts at G_omega's seat. -/
def TenAtGomega {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (nO : H2U.PlaceNums) (c : Chain First.S ProofFile.Cl) (f : Xi' → ProofFile.Inst) : Prop :=
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
    (d wEnd : W) (_ : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂),
    ∃ x dB dt,
      ((piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length]? =
        some x ∧
      TenFacts frField (pGomega nO) rOFull (seatedAt o mk Z N c f).t₁ (seatedAt o mk Z N c f).t₂
        (Seat.onGomega (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit)) x dB dt


theorem nine_facts_at_Gu {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : NineAtGu W o mk Z N c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl
  obtain ⟨hfree, hC, ho, hlb, _⟩ := gu_facts o S hS Z hZ mk N c hN hp hpin
  obtain ⟨b', post', e⟩ := shared_behind ProofFile.Cl (p14N Z N) N
  have hcut : b₂ :: l₂ = sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++
      guEntry ProofFile.Cl N :: b' :: post' := by
    rw [← e]
    exact hfl.symm.trans (descN_shared o mk guardedProximityTestParts Z N c)
  obtain ⟨ha, hD⟩ := Coin.depth_in_scope (seatedAt o mk Z N c f) S hS hpin
  have hft : (pGu N).nums.firstTree = 0 :=
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hC.plan)).trans
      (H2K.Made.places_firstTree Z.made N hN).2.1
  exact nine_facts_tile₂ (seatedAt o mk Z N c f) "proof file" dField
    (Coin.data_at _ _ _ hD _ ha) hp b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd (pGu N) rUFull
    (Seat.enter (·.gU) (·.firstMask)) Seat.leave (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N)
    (guEntry ProofFile.Cl N) b' post' hfl hcut (guEntry_alike ProofFile.Cl N)
    ((guEntry_keeps ProofFile.Cl N).1.trans (H2K.Made.k12_before guardedProximityTestParts (pGu N) hC.plan)) hfree hC.plan
    hC.chain hC.joh hC.bat ho (ownLabelsB_of_free _ hlb) hft


theorem ten_facts_at_Gomega {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : TenAtGomega W o mk Z N nO c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl
  obtain ⟨hfree, hC, ho, hPl, _, _⟩ := gomega_facts o S hS Z hZ mk N nO hO c hN hp hpin
  have hcut : b₂ :: l₂ = (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) ++
      omegaEntry ProofFile.Cl nO :: sharedEnd ProofFile.Cl (p14N Z N) N :: [] :=
    hfl.symm.trans (shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO)
  obtain ⟨ha, hD⟩ := Coin.depth_in_scope (seatedAt o mk Z N c f) S hS hpin
  have hft : (pGomega nO).nums.firstTree = 0 :=
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hC.plan)).trans
      ((H2K.Made.places_firstTree Z.made N hN).2.2.1 nO hO)
  exact ten_facts_tile₂ (seatedAt o mk Z N c f) "proof file" dField
    (Coin.data_at _ _ _ hD _ ha) hp b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd (pGomega nO) rOFull
    (Seat.enter (·.gOmega) fun _ => none) Seat.leave
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) (omegaEntry ProofFile.Cl nO)
    (sharedEnd ProofFile.Cl (p14N Z N) N) [] hfl hcut (omegaEntry_alike ProofFile.Cl nO)
    ((omegaEntry_keeps ProofFile.Cl nO).1.trans (H2K.Made.k12_before guardedProximityTestParts (pGomega nO) hC.plan)) hfree
    hC.plan hC.chain hC.joh hC.bat ho hPl hft

/-- Of the value that is laid. -/
theorem nine_facts_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧ dField = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      NineAtGu W o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨ha, hD'⟩ := Coin.depth_in_scope _ S hS hpin
  exact ⟨Z, N, c, hZ, hN, hF, Except.ok.inj (hD.symm.trans hD'),
    Coin.at_of_depth _ _ (ha.trans (Coin.data_depth _ _ _ hD').symm), hr,
    nine_facts_at_Gu W o S hS Z hZ _ N c hN hp hpin _⟩

/-- Of the value that is laid. -/
theorem ten_facts_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧ dField = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      TenAtGomega W o ProofFile.pureRoad.links Z N nO c LPFD.Full.instanceAsPlainRecord := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  obtain ⟨ha, hD'⟩ := Coin.depth_in_scope _ S hS hpin
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, Except.ok.inj (hD.symm.trans hD'),
    Coin.at_of_depth _ _ (ha.trans (Coin.data_depth _ _ _ hD').symm), hr,
    ten_facts_at_Gomega W o S hS Z hZ _ N nO hO c hN hp hpin _⟩

end H2K.JointK

#print axioms H2K.JointK.TenFacts.pays
#print axioms H2K.JointK.nine_facts_at_Gu
#print axioms H2K.JointK.ten_facts_at_Gomega
#print axioms H2K.JointK.nine_facts_laid
#print axioms H2K.JointK.ten_facts_laid
