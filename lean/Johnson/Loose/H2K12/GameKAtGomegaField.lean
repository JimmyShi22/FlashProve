-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.GameKAtGuField
import Johnson.Loose.H2K12.GameKAtGomega
import Johnson.Desc.K12.Coin.GameAtFieldOwn
import Johnson.Desc.K12.Law.PieceEnd
/-
Johnson/Loose/H2K12/GameKAtGomegaField.lean: THE JOIN: THE KEY's-SIDE LAW AT G_omega's SEAT (⟨2, none, 10, .K12⟩; the second arm) OF THE PROOF FILE's SEATED DESCRIPTION, AT THE RULE's OWN LETTERS: the row is read through atDesc, the data are writtenPFull.at frS.P.T.a, the chain's first tree's number is that data's t₁: as Johnson/Desc/Plain/BothAtDesc.lean's rule asks its e₂. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
AFTER H2K12/GameKAtGuField.lean (the first seat): its statements' texts again, made by a program that turns the seat's letters (its dField | frField are called); ONE CALL of Coin/GameAtFieldOwn.lean's gameK_at_fieldO (general in the description), paid at descN's shared cut by the same facts as H2K12/GameKAtGomega.lean's, gathered here under one name: gomega_facts.
  gomega_facts · GameKGomegaField · gameK_at_Gomega_field (from the five and hO) · gameK_at_Gomega_field_laid (from InScope and proofDataAndDecisionOfPublicFiles's yes; «N.O = some nO» under its ∃).
  TwoSeatsKField · twoSeatsK_field · next_at_Gomega_field · twoSeatsK_field_laid: BOTH SEATS AT ONCE IN THE RULE's OWN LETTERS BY FORM, U's law of keys ending at the key at which O's laws begin, O's at the key in front of the chain's end: over piece_next₂ (Law/PieceEnd.lean: of the maker's text alone).
WHAT IT IS NOT: NO TERM OF EachLeadsK | EachLeadsBN IS BUILT: «at the rule's own letters» means: in these letters BY FORM · the first and the third of the rule's three clauses at this one index (LeadsK | LeadsBN · KeyLaw), at one p: not the second toward the next piece, not the other pieces of the row · AtCap rest₂ is the letters of record's own word: a premise on the filling · QVO says nothing of the own mask's word · this seat alone · no sum · no member.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes.Maker (RDT WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (QV QVO nlAt Rides)
open H2K.Member (rUFull rOFull)
open Johnson.G (writtenPFull)
open scoped ENNReal

/-- What the law's callers ask of the place pGomega nO, in scope: eight facts in one. -/
theorem gomega_facts (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (mk : ProofFile.LinksBy)
    (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    (pGomega nO).nums.free = Johnson.G.OfPlan.rootsOf
        ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds)) ∧
      Coin.ClosedL (pGomega nO) rOFull 1 0 0 Coin.At.TOFull ∧ (pGomega nO).nums.ownMask = true ∧
      Coin.ownLabelsB (pGomega nO) = true ∧ H2K.Made.firstNe (pGomega nO) = true ∧
      0 < (pGomega nO).nums.free := by
  have hC := (closedL_in_scope_O hS Z hZ mk N nO hO c hN hp hpin).1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hC.plan
  obtain ⟨hPl, hne, hfr⟩ := tests_in_scope_O hS Z hZ mk N nO hO c hN hp hpin
  exact ⟨(congrArg (·.free) hn).trans
      ((plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).2.1 nO hO).2, hC,
    ownMask_in_scope_O hS Z hZ mk N nO hO c hN hp, hPl, hne, hfr⟩

/-- The first and the third clause of the rule's e₂ at G_omega's index, at the rule's own letters. -/
def GameKGomegaField {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
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
    (d wEnd : W) (_ : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) (rd : ℕ → ℕ)
    (_ : AtCap rest₂) (n : ℕ),
    ∃ p,
      ((atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length]? = some p ∧
      p.b = held (omegaEntry ProofFile.Cl nO) ∧
      p.base = dField.t₁ + nTrees (dField.ds₂.take 43) ∧
      p.ior.red.LeadsK (actAt frField Prod.snd dField.t₁ p.base).2 (fun _ => True)
        (fun x y => (QVO frField (pGomega nO) dField.t₁ dField.t₂ 1 rOFull rd
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField p.base x y) p.err ∧
      p.ior.red.LeadsBN (actAt frField Prod.snd dField.t₁ p.base).2 (fun _ => True)
        (fun x y => (QVO frField (pGomega nO) dField.t₁ dField.t₂ 1 rOFull rd
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField p.base x y) n p.err ∧
      p.ior.red.KeyLaw (actAt frField Prod.snd dField.t₁ p.base).2
        (actAt frField Prod.snd dField.t₁ (p.base + p.trees)).2

/-- From the five. -/
theorem gameK_at_Gomega_field {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : GameKGomegaField W o mk Z N nO c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap n
  obtain ⟨hfree, hC, hown, hPl, hne, hfr⟩ := gomega_facts o S hS Z hZ mk N nO hO c hN hp hpin
  have hcut : b₂ :: l₂ = (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) ++
      omegaEntry ProofFile.Cl nO :: sharedEnd ProofFile.Cl (p14N Z N) N :: [] :=
    hfl.symm.trans (shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO)
  obtain ⟨ha, hD⟩ := Coin.depth_in_scope (seatedAt o mk Z N c f) S hS hpin
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1
  have hl := (stretch_at_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp _ hW 43
    H2K.Member.bat_OFull).2.2.1
  obtain ⟨p, h1, h2, h3, h4, h5, h6⟩ := Coin.gameK_at_fieldO (seatedAt o mk Z N c f) "proof file"
    writtenPFull hD OnBytes.Slice.frS.P.T.a ha b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    (pGomega nO) rOFull (Seat.enter (·.gOmega) fun _ => none) Seat.leave
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) (omegaEntry ProofFile.Cl nO)
    (sharedEnd ProofFile.Cl (p14N Z N) N) [] hfl hcut (omegaEntry_alike ProofFile.Cl nO) hfree hC.plan hC.chain
    hC.joh hC.bat hown hPl hne hfr rd hcap n
  exact ⟨p, h1, h2, h3.trans (congrArg (fun m => dField.t₁ + nTrees (dField.ds₂.take m)) hl), h4,
    h5, h6⟩

/-- Of the value that is laid. -/
theorem gameK_at_Gomega_field_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧ dField = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      GameKGomegaField W o ProofFile.pureRoad.links Z N nO c LPFD.Full.instanceAsPlainRecord := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  obtain ⟨ha, hD'⟩ := Coin.depth_in_scope _ S hS hpin
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, Except.ok.inj (hD.symm.trans hD'),
    Coin.at_of_depth _ _ (ha.trans (Coin.data_depth _ _ _ hD').symm), hr,
    gameK_at_Gomega_field W o S hS Z hZ _ N nO hO c hN hp hpin _⟩

/-! ## The two seats, and the chain's end, at the rule's own letters -/

/-- TwoSeatsK (H2K12/GameKAtGomega.lean) again, IN THE RULE's OWN LETTERS BY FORM: the row through
atDesc, the data dField, lo := dField.t₁; with the law for a batch at every number of slots beside
the law with a key: the pieces number i and i + 1, i := (sharedPre …).length: EachLeadsK's |
EachLeadsBN's first and third clauses at both, U's law of keys ENDING AT THE VERY KEY AT WHICH O's
LAWS BEGIN. The second clause between the two is not written: at on (i + 1) := fun _ => True it is
idle (it cannot fail): A CHOSEN TABLE's; what spends that choice is the rule's own premise on the
table's end, which nobody holds at the seated letters. NO TERM OF EachLeadsK | EachLeadsBN IS BUILT
HERE: the row's other pieces lack. -/
def TwoSeatsKField {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
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
    (d wEnd : W) (_ : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) (rd : ℕ → ℕ)
    (_ : AtCap rest₂) (n : ℕ),
    ∃ pU pO,
      ((atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length]? = some pU ∧
      ((atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length + 1]? = some pO ∧
      pU.base + pU.trees = pO.base ∧
      pU.ior.red.LeadsK (actAt frField Prod.snd dField.t₁ pU.base).2 (fun _ => True)
        (fun x y => (QV frField (pGu N) (nlAt (pGu N) dField.t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField pU.base x y) pU.err ∧
      pU.ior.red.LeadsBN (actAt frField Prod.snd dField.t₁ pU.base).2 (fun _ => True)
        (fun x y => (QV frField (pGu N) (nlAt (pGu N) dField.t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField pU.base x y) n pU.err ∧
      pU.ior.red.KeyLaw (actAt frField Prod.snd dField.t₁ pU.base).2 (actAt frField Prod.snd dField.t₁ pO.base).2 ∧
      pO.ior.red.LeadsK (actAt frField Prod.snd dField.t₁ pO.base).2 (fun _ => True)
        (fun x y => (QVO frField (pGomega nO) dField.t₁ dField.t₂ 1 rOFull rd
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField pO.base x y) pO.err ∧
      pO.ior.red.LeadsBN (actAt frField Prod.snd dField.t₁ pO.base).2 (fun _ => True)
        (fun x y => (QVO frField (pGomega nO) dField.t₁ dField.t₂ 1 rOFull rd
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave x y ∧ y.1 = (x.1.1, y.1.2)) ∧
          Rides frField pO.base x y) n pO.err ∧
      pO.ior.red.KeyLaw (actAt frField Prod.snd dField.t₁ pO.base).2
        (actAt frField Prod.snd dField.t₁ (pO.base + pO.trees)).2

/-- From the five and hO. -/
theorem twoSeatsK_field {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : TwoSeatsKField W o mk Z N nO c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap n
  obtain ⟨pU, u1, _, _, u4, u5, u6⟩ := gameK_at_Gu_field W o S hS Z hZ mk N c hN hp hpin f b₁ l₁ b₂
    l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap n
  obtain ⟨pO, o1, _, _, o4, o5, o6⟩ := gameK_at_Gomega_field W o S hS Z hZ mk N nO hO c hN hp hpin f
    b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap n
  have o1' : ((atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length + 1]? = some pO := by
    rw [List.length_append, List.length_singleton] at o1
    exact o1
  obtain ⟨b', post', e⟩ := shared_behind ProofFile.Cl (p14N Z N) N
  have hcut : b₂ :: l₂ = sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++
      guEntry ProofFile.Cl N :: b' :: post' := by
    rw [← e]
    exact hfl.symm.trans (descN_shared o mk guardedProximityTestParts Z N c)
  have hm : pU.base + pU.trees = pO.base :=
    (H2K.Tile.piece_next₂ (seatedAt o mk Z N c f) dField b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
      (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N) b' post' hcut pU pO u1 o1').2.symm
  exact ⟨pU, pO, u1, o1', hm, u4, u5, hm ▸ u6, o4, o5, o6⟩

/-- The piece next behind the second seat's holds the chain's end, and begins where the second
seat's ends: so the second seat's law of keys ends at the key in front of the chain's end. -/
theorem next_at_Gomega_field {Xi' W : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO) (c : Chain First.S ProofFile.Cl)
    (f : Xi' → ProofFile.Inst)
    (b₁ : Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl)
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
    (d wEnd : W) (hfl : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) :
    ∀ p q, ((atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length]? = some p →
      ((atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc (seatedAt o mk Z N c f) (piecesAt (ckP .two) (seatedAt o mk Z N c f) dField b₁ l₁
          b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length + 1]? = some q →
      q.b = held (sharedEnd ProofFile.Cl (p14N Z N) N) ∧ q.base = p.base + p.trees :=
  H2K.Tile.piece_next₂ (seatedAt o mk Z N c f) dField b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) (omegaEntry ProofFile.Cl nO)
    (sharedEnd ProofFile.Cl (p14N Z N) N) []
    (hfl.symm.trans (shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO))

/-- Of the value that is laid: both seats at once. -/
theorem twoSeatsK_field_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧ dField = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      TwoSeatsKField W o ProofFile.pureRoad.links Z N nO c LPFD.Full.instanceAsPlainRecord := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  obtain ⟨ha, hD'⟩ := Coin.depth_in_scope _ S hS hpin
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, Except.ok.inj (hD.symm.trans hD'),
    Coin.at_of_depth _ _ (ha.trans (Coin.data_depth _ _ _ hD').symm), hr,
    twoSeatsK_field W o S hS Z hZ _ N nO hO c hN hp hpin _⟩

end H2K.JointK

#print axioms H2K.JointK.gomega_facts
#print axioms H2K.JointK.gameK_at_Gomega_field
#print axioms H2K.JointK.gameK_at_Gomega_field_laid
#print axioms H2K.JointK.twoSeatsK_field
#print axioms H2K.JointK.next_at_Gomega_field
#print axioms H2K.JointK.twoSeatsK_field_laid
