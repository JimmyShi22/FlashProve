-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.GameKAtGu
import Johnson.Desc.K12.Coin.ReadsKeyOwn
import Johnson.Loose.H2K12.OmegaIsSome
/-
Johnson/Loose/H2K12/GameKAtGomega.lean: THE KEY's-SIDE LAW AT THE FILE's OWN PIECE AT G_omega's SEAT (⟨2, none, 10, .K12⟩; THE SECOND ARM: the first fold sends its own mask) OF THE PROOF FILE's SEATED DESCRIPTION, IN SCOPE. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
AFTER H2K12/GameKAtGu.lean (the first seat): ITS STATEMENTS' TEXTS AGAIN, MADE BY A PROGRAM THAT TURNS THE SEAT's LETTERS (its frShared | seatedAt are called): π := pGomega nO · r := rOFull · pre := sharedPre … ++ [guEntry ProofFile.Cl N] · B := omegaEntry ProofFile.Cl nO · the block behind := sharedEnd … · 43 rounds in front · the doors Seat.enter (·.gOmega) (fun _ => none) | Seat.leave · QVO (Coin/ReadsKeyOwn.lean) in QV's place. The proofs: calls.
  gameK_at_Gomega: over gameK_at_tile₂O_le: LeadsK ∧ KeyLaw at the piece number (sharedPre … ++ [guEntry …]).length of piecesAt's second row, at whatever errors the family lays there that are at least this law's own.
  GameKGomega · gameK_at_Gomega_cap: AT THE LETTERS OF RECORD (AtCap rest₂): no premise on the errors; LeadsK, LeadsBN at every number of slots, the strings ride, KeyLaw.
  gameK_at_Gomega_laid: VerifierAndGoals.InScope S · LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r) ⇒ ∃ Z N nO c, the returns ∧ N.O = some nO ∧ D = writtenPFull ∧ r = the seated description's run behind instanceAsPlainRecord ∧ GameKGomega …: TWO PREMISES.
  end_at_Gu | end_at_Gomega: THE TWO SEATS' KEYS MEET: the first seat's piece's base and trees are writtenPFull.t₁ + nTrees (… .take 43): the second's base to the letter (over tile_end₂ | tile_endOwn₂: Coin/LawAtTile.lean | LawAtTileOwn.lean).
  TwoSeatsK · twoSeatsK_in_scope: THE THREE CLAUSES THAT EachLeadsK ASKS AT THE FIRST SEAT's INDEX, and the second seat's first and third. THE SECOND CLAUSE IS MET AT A CHOSEN TABLE (on (i + 1) := fun _ => True; Q i := this file's own relation): the rule's table is a free letter of the rule: WHAT SPENDS THE CHOICE IS THE RULE's OWN PREMISE ON THE TABLE's END (that the relations, chained, give what the file's goal wants), WHICH NOBODY HOLDS AT THE SEATED LETTERS. gameK_at_Gomega_laid hands TwoSeatsK on too.
WHO PAYS: the cut: shared_cut_omega · the entry alike to the seat: omegaEntry_alike · 43 rounds | free: stretch_at_O | plain_free · ClosedL (pGomega nO) rOFull 1 0 0 TOFull · ownMask = true · the three tests on the plan (ownLabelsB · firstNe · 0 < free): closedL_ | ownMask_ | tests_in_scope_O · that the plan HAS a place for this test in scope: omega_some_in_scope.
WHAT IT IS NOT: as the first seat's: the SECOND clause of EachLeadsK toward the NEXT piece (what QVO hands to the chain's end's condition) is not here (toward THIS piece nothing is asked: fun _ => True) · QVO says nothing of the own mask's word · this seat alone · no sum · no member.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes.Maker (RDT WholeD uLT)
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (QV QVO nlAt errJ Rides)
open H2K.Member (rUFull rOFull)
open H2K.Pub (batV0)
open Johnson.G (writtenPFull)
open scoped ENNReal

/-- LeadsK AND KeyLaw AT THE FILE's OWN PIECE AT G_omega's SEAT, IN SCOPE. -/
theorem gameK_at_Gomega {Xi' W : Type} (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst)
    (b₁ : Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl)
    (l₁ : List (Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl))
    (b₂ : Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl)
    (l₂ : List (Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl))
    (b₃ : Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl)
    (l₃ : List (Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₁ 0)
        ((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) frShared
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) ×
          (seatedAt o mk Z N c f).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two)
        (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₃
          (seatedAt o mk Z N c f).lastChainFirstTreeNumber)
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁ × (seatedAt o mk Z N c f).S₂) ×
          (seatedAt o mk Z N c f).S₃) W ds)
    (d wEnd : W) (hfl : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (writtenPFull.ds₂.drop 43).take
        (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 (pGomega nO) rOFull * (bsRound .two dB.entry dB.kind).w, errJ (pGomega nO) rOFull dt)
        (rest₂ (0 + (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length]? = some p ∧
      p.b = held (omegaEntry ProofFile.Cl nO) ∧
      p.base = writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take 43) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₂ (0 + (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 (pGomega nO) rOFull * (bsRound .two dB.entry dB.kind).w, errJ (pGomega nO) rOFull dt)
        ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      p.ior.red.LeadsK (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (fun _ => True)
        (fun a b => QVO frShared (pGomega nO) (seatedAt o mk Z N c f).t₁ (seatedAt o mk Z N c f).t₂ 1 rOFull rd
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ (p.base + p.trees)).2 := by
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have hC := (closedL_in_scope_O hS Z hZ mk N nO hO c hN hp hpin).1
  have hl := (stretch_at_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp _ hW 43
    H2K.Member.bat_OFull).2.2.1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hC.plan
  have hfree : (pGomega nO).nums.free = Johnson.G.OfPlan.rootsOf
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds)) :=
    (congrArg (·.free) hn).trans ((plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).2.1 nO hO).2
  obtain ⟨hPl, hne, hfr⟩ := tests_in_scope_O hS Z hZ mk N nO hO c hN hp hpin
  have hcut : b₂ :: l₂ = (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) ++
      omegaEntry ProofFile.Cl nO :: sharedEnd ProofFile.Cl (p14N Z N) N :: [] :=
    hfl.symm.trans (shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO)
  have h := Coin.gameK_at_tile₂O_le (seatedAt o mk Z N c f) "proof file" writtenPFull hD b₁ l₁ b₂
    l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd (pGomega nO) rOFull 128 (Seat.enter (·.gOmega) fun _ => none)
    Seat.leave (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N])
    (omegaEntry ProofFile.Cl nO) (sharedEnd ProofFile.Cl (p14N Z N) N) [] hfl hcut (omegaEntry_alike ProofFile.Cl nO)
    hfree hC.plan hC.chain hC.joh hC.bat (ownMask_in_scope_O hS Z hZ mk N nO hO c hN hp) hPl hne hfr
    rd (fun dB dt hx => herr dB dt ((congrArg (fun n => (writtenPFull.ds₂.drop n).take
      (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).rounds.length) hl).symm.trans hx))
  obtain ⟨p, dB, dt, h1, h2, h3, h4⟩ := h
  exact ⟨p, dB, dt, h1, h2,
    h3.trans (congrArg (fun n => writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take n)) hl), h4⟩

/-- WHAT THE KEY's SIDE SAYS OF THE FILE's OWN PIECE AT G_omega's SEAT, AT THE LETTERS OF RECORD: at
every
filling of piecesAt's letters whose second row's errors are the cap's (AtCap rest₂) and at every
number
of slots n: the piece number (sharedPre … ++ [guEntry …]).length of the second row is there · its block is the held
entry · its base is the written data's at 43 rounds · LeadsK and LeadsBN at the acting part in front,
nothing promised, of «QVO ∧ the held part stays ∧ the strings ride», AT THE PIECE's OWN ERRORS ·
KeyLaw ·
and the two names of the chain's first tree's number are one. -/
def GameKGomega {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (nO : H2U.PlaceNums) (c : Chain First.S ProofFile.Cl) (f : Xi' → ProofFile.Inst) : Prop :=
  ∀ (b₁ : Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl)
    (l₁ : List (Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl))
    (b₂ : Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl)
    (l₂ : List (Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl))
    (b₃ : Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl)
    (l₃ : List (Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₁ 0)
        ((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) frShared
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) ×
          (seatedAt o mk Z N c f).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two)
        (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₃
          (seatedAt o mk Z N c f).lastChainFirstTreeNumber)
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁ × (seatedAt o mk Z N c f).S₂) ×
          (seatedAt o mk Z N c f).S₃) W ds)
    (d wEnd : W) (_ : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) (rd : ℕ → ℕ)
    (_ : AtCap rest₂) (n : ℕ),
    ∃ p,
      ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length]? = some p ∧
      p.b = held (omegaEntry ProofFile.Cl nO) ∧
      p.base = writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take 43) ∧
      writtenPFull.t₁ = (seatedAt o mk Z N c f).t₁ ∧
      p.ior.red.LeadsK (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (fun _ => True)
        (fun a b => (QVO frShared (pGomega nO) (seatedAt o mk Z N c f).t₁ (seatedAt o mk Z N c f).t₂ 1 rOFull rd
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) ∧
          Rides frShared p.base a b) p.err ∧
      p.ior.red.LeadsBN (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (fun _ => True)
        (fun a b => (QVO frShared (pGomega nO) (seatedAt o mk Z N c f).t₁ (seatedAt o mk Z N c f).t₂ 1 rOFull rd
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) ∧
          Rides frShared p.base a b) n p.err ∧
      p.ior.red.KeyLaw (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ (p.base + p.trees)).2

/-- AT THE LETTERS OF RECORD: NO PREMISE ON THE ERRORS. -/
theorem gameK_at_Gomega_cap {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : GameKGomega W o mk Z N nO c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap n
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have hC := (closedL_in_scope_O hS Z hZ mk N nO hO c hN hp hpin).1
  have hl := (stretch_at_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp _ hW 43
    H2K.Member.bat_OFull).2.2.1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hC.plan
  have hfree : (pGomega nO).nums.free = Johnson.G.OfPlan.rootsOf
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds)) :=
    (congrArg (·.free) hn).trans ((plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).2.1 nO hO).2
  obtain ⟨hPl, hne, hfr⟩ := tests_in_scope_O hS Z hZ mk N nO hO c hN hp hpin
  have hcut : b₂ :: l₂ = (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) ++
      omegaEntry ProofFile.Cl nO :: sharedEnd ProofFile.Cl (p14N Z N) N :: [] :=
    hfl.symm.trans (shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO)
  have h := Coin.gameK_at_tile₂O_cap (seatedAt o mk Z N c f) "proof file" writtenPFull hD b₁ l₁ b₂
    l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd (pGomega nO) rOFull (Seat.enter (·.gOmega) fun _ => none)
    Seat.leave (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N])
    (omegaEntry ProofFile.Cl nO) (sharedEnd ProofFile.Cl (p14N Z N) N) [] hfl hcut (omegaEntry_alike ProofFile.Cl nO)
    hfree hC.plan hC.chain hC.joh hC.bat (ownMask_in_scope_O hS Z hZ mk N nO hO c hN hp) hPl hne hfr
    rd hcap n
  obtain ⟨p, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨p, h1, h2,
    h3.trans (congrArg (fun n => writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take n)) hl),
    (opensShaped (seatedAt o mk Z N c f) "proof file" writtenPFull hD).2.1, h4, h5, h6⟩

/-! ## The two seats' keys meet -/

/-- The rounds in front of a block and its own are the rounds in front of the next. -/
theorem flat_len_snoc {S Cl : Type} (pre : List (Block S Cl)) (B : Block S Cl)
    (R : List Fmt.DeclaredRound) (n : Nat) (hB : B.rounds = R)
    (h : ((pre ++ [B]).flatMap (·.rounds)).length = n) :
    (pre.flatMap (·.rounds)).length + R.length = n := by
  subst hB
  rw [List.flatMap_append, List.length_append] at h
  simpa using h

/-- **The first seat's piece ends where the second's begins**: 8 rounds in front and the test's own
are the 43 rounds in front of the second seat. (nO and hO stand among the premises of this lemma on
the FIRST seat because the literal 43 is read off the second seat's stretch: stretch_at_O.) -/
theorem end_at_Gu {Xi' W : Type} (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst)
    (b₁ : Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl)
    (l₁ : List (Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl))
    (b₂ : Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl)
    (l₂ : List (Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl))
    (b₃ : Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl)
    (l₃ : List (Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₁ 0)
        ((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) frShared
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) ×
          (seatedAt o mk Z N c f).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two)
        (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₃
          (seatedAt o mk Z N c f).lastChainFirstTreeNumber)
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁ × (seatedAt o mk Z N c f).S₂) ×
          (seatedAt o mk Z N c f).S₃) W ds)
    (d wEnd : W) (hfl : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) :
    ∀ p, ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length]? = some p →
      p.base + p.trees = writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take 43) := by
  intro p hrow
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have hC := (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hC.plan
  have hfree : (pGu N).nums.free = Johnson.G.OfPlan.rootsOf
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)) :=
    (congrArg (·.free) hn).trans (plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).1.2
  obtain ⟨b', post', e⟩ := shared_behind ProofFile.Cl (p14N Z N) N
  have hcut : b₂ :: l₂ = sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++
      guEntry ProofFile.Cl N :: b' :: post' := by
    rw [← e]
    exact hfl.symm.trans (descN_shared o mk guardedProximityTestParts Z N c)
  have h := Coin.tile_end₂ (seatedAt o mk Z N c f) "proof file" writtenPFull hD b₁ l₁ b₂ l₂ b₃ l₃
    rest₁ rest₂ rest₃ d wEnd (pGu N) rUFull 128 (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N)
    (guEntry ProofFile.Cl N) b' post' hfl hcut (guEntry_alike ProofFile.Cl N).rounds hfree hC.plan hC.chain
    hC.joh hC.bat (ownMask_in_scope_U hS Z hZ mk N c hN hp) p hrow
  have hl := (stretch_at_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp _ hW 43
    H2K.Member.bat_OFull).2.2.1
  exact h.trans (congrArg (fun n => writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take n))
    (flat_len_snoc _ _ _ 43 (guEntry_alike ProofFile.Cl N).rounds hl))

/-- The second seat's piece ends behind its own rounds. -/
theorem end_at_Gomega {Xi' W : Type} (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst)
    (b₁ : Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl)
    (l₁ : List (Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl))
    (b₂ : Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl)
    (l₂ : List (Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl))
    (b₃ : Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl)
    (l₃ : List (Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₁ 0)
        ((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) frShared
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) ×
          (seatedAt o mk Z N c f).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two)
        (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₃
          (seatedAt o mk Z N c f).lastChainFirstTreeNumber)
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁ × (seatedAt o mk Z N c f).S₂) ×
          (seatedAt o mk Z N c f).S₃) W ds)
    (d wEnd : W) (hfl : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) :
    ∀ p, ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).length]? = some p →
      p.base + p.trees = writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take
        (43 + (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).rounds.length)) := by
  intro p hrow
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have hC := (closedL_in_scope_O hS Z hZ mk N nO hO c hN hp hpin).1
  have hl := (stretch_at_O o S.pol S.lay S.KL Z hZ mk N nO hO c hN hp _ hW 43
    H2K.Member.bat_OFull).2.2.1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hC.plan
  have hfree : (pGomega nO).nums.free = Johnson.G.OfPlan.rootsOf
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds)) :=
    (congrArg (·.free) hn).trans ((plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).2.1 nO hO).2
  obtain ⟨hPl, hne, hfr⟩ := tests_in_scope_O hS Z hZ mk N nO hO c hN hp hpin
  have hcut : b₂ :: l₂ = (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) ++
      omegaEntry ProofFile.Cl nO :: sharedEnd ProofFile.Cl (p14N Z N) N :: [] :=
    hfl.symm.trans (shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO)
  have h := Coin.tile_endOwn₂ (seatedAt o mk Z N c f) "proof file" writtenPFull hD b₁ l₁ b₂ l₂ b₃
    l₃ rest₁ rest₂ rest₃ d wEnd (pGomega nO) rOFull 128
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]) (omegaEntry ProofFile.Cl nO)
    (sharedEnd ProofFile.Cl (p14N Z N) N) [] hfl hcut (omegaEntry_alike ProofFile.Cl nO).rounds hfree hC.plan
    hC.chain hC.joh hC.bat (ownMask_in_scope_O hS Z hZ mk N nO hO c hN hp) p hrow
  exact h.trans (congrArg (fun n => writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take
    (n + (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).rounds.length))) hl)

/-- WHAT THE KEY's SIDE SAYS OF THE TWO NEIGHBOURS, AT THE LETTERS OF RECORD: the pieces number i and
i + 1 of the second row, i := (sharedPre …).length: THE THREE CLAUSES THAT EachLeadsK
(Johnson/Desc/Plain/FoldChainK.lean) ASKS AT THE INDEX i, AT A CHOSEN TABLE: key j := the acting part
up to the j-th piece's base · on := fun _ => True · Q := the relations here: (1) LeadsK at the first
seat · (2) what its relation hands on is what the second seat's law asks in front: NOTHING: SO THE
FIFTH CONJUNCT BELOW IS IDLE: IT CANNOT FAIL: it is the chosen table's, and all the weight goes to
what these relations SAY, which the rule's own premise on the table's end must spend · (3) the
law of keys, ENDING AT THE VERY KEY AT WHICH THE SECOND SEAT's LeadsK BEGINS; and the second seat's
own (1) and (3). Shaped for EachLeadsK; for the rule at a batch (EachLeadsBN) a caller takes the
lemma LeadsK.bothN. -/
def TwoSeatsK {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (nO : H2U.PlaceNums) (c : Chain First.S ProofFile.Cl) (f : Xi' → ProofFile.Inst) : Prop :=
  ∀ (b₁ : Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl)
    (l₁ : List (Block (seatedAt o mk Z N c f).S₁ (seatedAt o mk Z N c f).Cl))
    (b₂ : Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl)
    (l₂ : List (Block (seatedAt o mk Z N c f).S₂ (seatedAt o mk Z N c f).Cl))
    (b₃ : Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl)
    (l₃ : List (Block (seatedAt o mk Z N c f).S₃ (seatedAt o mk Z N c f).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₁ 0)
        ((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) frShared
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) ×
          (seatedAt o mk Z N c f).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two)
        (frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₃
          (seatedAt o mk Z N c f).lastChainFirstTreeNumber)
        (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁ × (seatedAt o mk Z N c f).S₂) ×
          (seatedAt o mk Z N c f).S₃) W ds)
    (d wEnd : W) (_ : (seatedAt o mk Z N c f).shared.blocksInOrder = b₂ :: l₂) (rd : ℕ → ℕ)
    (_ : AtCap rest₂),
    ∃ pU pO,
      ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length]? = some pU ∧
      ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length + 1]? = some pO ∧
      pU.base + pU.trees = pO.base ∧
      pU.ior.red.LeadsK (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ pU.base).2 (fun _ => True)
        (fun a b => (QV frShared (pGu N) (nlAt (pGu N) (seatedAt o mk Z N c f).t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) ∧
          Rides frShared pU.base a b) pU.err ∧
      (∀ a b : (((seatedAt o mk Z N c f).XiPub × (seatedAt o mk Z N c f).S₁) ×
          (seatedAt o mk Z N c f).S₂) × frShared.E.Str, True → (fun a b => (QV frShared (pGu N) (nlAt (pGu N) (seatedAt o mk Z N c f).t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) ∧
          Rides frShared pU.base a b) a b → True) ∧
      pU.ior.red.KeyLaw (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ pU.base).2 (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ pO.base).2 ∧
      pO.ior.red.LeadsK (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ pO.base).2 (fun _ => True)
        (fun a b => (QVO frShared (pGomega nO) (seatedAt o mk Z N c f).t₁
            (seatedAt o mk Z N c f).t₂ 1 rOFull rd (Seat.enter (·.gOmega) fun _ => none)
            Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) ∧ Rides frShared pO.base a b) pO.err ∧
      pO.ior.red.KeyLaw (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ pO.base).2
        (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ (pO.base + pO.trees)).2

/-- e₂'s THREE CLAUSES AT THE FIRST SEAT's INDEX, IN SCOPE. -/
theorem twoSeatsK_in_scope {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO)
    (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : TwoSeatsK W o mk Z N nO c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap
  obtain ⟨pU, u1, _, _, _, u5, _, u7⟩ := gameK_at_Gu_cap W o S hS Z hZ mk N c hN hp hpin f b₁ l₁ b₂
    l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap 0
  obtain ⟨pO, o1, _, o3, _, o5, _, o7⟩ := gameK_at_Gomega_cap W o S hS Z hZ mk N nO hO c hN hp hpin f
    b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap 0
  have hm : pU.base + pU.trees = pO.base :=
    (end_at_Gu o S hS Z hZ mk N nO hO c hN hp hpin f b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl
      pU u1).trans o3.symm
  have o1' : ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length + 1]? = some pO := by
    rw [List.length_append, List.length_singleton] at o1
    exact o1
  exact ⟨pU, pO, u1, o1', hm, u5, fun _ _ _ _ => trivial, hm ▸ u7, o5, o7⟩

/-- OF THE VALUE THAT IS LAID: TWO PREMISES: the files are in scope · the proof file's value is
laid. D: its rounds' data; r: its decision. -/
theorem gameK_at_Gomega_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      GameKGomega W o ProofFile.pureRoad.links Z N nO c LPFD.Full.instanceAsPlainRecord ∧
      TwoSeatsK W o ProofFile.pureRoad.links Z N nO c LPFD.Full.instanceAsPlainRecord := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  have hD' := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).2.2
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, Except.ok.inj (hD.symm.trans hD'), hr,
    gameK_at_Gomega_cap W o S hS Z hZ _ N nO hO c hN hp hpin _,
    twoSeatsK_in_scope W o S hS Z hZ _ N nO hO c hN hp hpin _⟩

end H2K.JointK

#print axioms H2K.JointK.gameK_at_Gomega
#print axioms H2K.JointK.gameK_at_Gomega_cap
#print axioms H2K.JointK.flat_len_snoc
#print axioms H2K.JointK.end_at_Gu
#print axioms H2K.JointK.end_at_Gomega
#print axioms H2K.JointK.twoSeatsK_in_scope
#print axioms H2K.JointK.gameK_at_Gomega_laid
