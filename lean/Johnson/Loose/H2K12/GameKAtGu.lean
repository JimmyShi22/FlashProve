-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.TileAtGu
import Johnson.Desc.K12.Coin.ReadsKey
import Johnson.Desc.Laid.ProofFullScope
/-
Johnson/Loose/H2K12/GameKAtGu.lean: THE KEY's-SIDE LAW AT THE FILE's OWN PIECE AT G_u's SEAT (⟨2,
none, 9, .K12⟩) OF THE PROOF FILE's SEATED DESCRIPTION, IN SCOPE: ONE CALL of Coin/ReadsKey.lean's
gameK_at_tile₂ (general in the description) at the description seatedAt o mk Z N c f := (descN o mk
guardedProximityTestParts Z N c).pull f (f: any map of instances: the seated value's is LPFD.Full.instanceAsPlainRecord), D :=
writtenPFull, π := pGu N, r := rUFull, k := 128, pre := sharedPre …, B := guEntry ProofFile.Cl N, enter |
leave := the seat's own doors. WHAT IT GIVES: the piece number (sharedPre …).length of piecesAt's
second row: its block is the held entry · its base and data are the written data's at 8 rounds · its
whole error is below 2⁻¹ ^ 128 round by round · LeadsK at the acting part (the chain's own record,
the stored strings, the chain's own trees in front), nothing promised in front, of the relation QV …
∧ «the held part stays» · KeyLaw: the first and the third of the three clauses that the shared
chain's rule (Johnson/Desc/Plain/FoldChainK.lean: EachLeadsK) asks of each piece. WHO PAYS: as in
TileAtGu.lean; beside: the entry is alike to the seat (guEntry_alike) · a block stands behind
(shared_behind) · the labels' test (Law/Sizes/ClosedAtScope.lean's labels_U_of_full) · 0 < free
(free_at_seat_U). NO SOUNDNESS IS CLAIMED. NOTHING ON
HIDING. NO NEW MATHEMATICS.
ALSO HERE: GameKGu (the conclusion at the letters of record, under a name) · gameK_at_Gu_cap
(over gameK_at_tile₂_cap: (AtCap rest₂): NO PREMISE ON THE ERRORS; LeadsBN at every number of slots;
the strings ride) · gameK_at_Gu_laid: VerifierAndGoals.InScope S · LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL =
.ok (D, r) ⇒ ∃ Z N c, the returns ∧ D = writtenPFull ∧ r = the seated description's run behind
instanceAsPlainRecord ∧ GameKGu …: TWO PREMISES: IT NAMES THE VALUE THAT IS LAID.
WHAT IT IS NOT: herr IS A PREMISE: the errors that the file's piece bears are whatever the filler of
piecesAt's letter rest₂ lays there: it is asked only that they be AT LEAST ours (Err.le), round by
round: every such rest₂ is served; that THEY are small is then the filler's to show: what is shown
small here is our own pair · hp (planOk) and hpin (the pin) are premises: what the seated value's
door asks · the SECOND clause of EachLeadsK (what our relation hands to the next piece's condition)
is not here · G_u's seat alone.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes.Maker (RDT WholeD uLT)
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (QV nlAt errJ Rides)
open H2K.Member (rUFull)
open H2K.Pub (batV0)
open Johnson.G (writtenPFull)
open scoped ENNReal

/-- The shared chain's frame at the written data: as piecesAt lays it. -/
abbrev frShared : Frame := frameAt writtenPFull (allOf writtenPFull) writtenPFull.key₂ 0

/-- The seated description behind a map of instances. -/
abbrev seatedAt {Xi' : Type} (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (f : Xi' → ProofFile.Inst) : FileDescription Xi' :=
  (descN o mk guardedProximityTestParts Z N c).pull f

/-- LeadsK AND KeyLaw AT THE FILE's OWN PIECE AT G_u's SEAT, IN SCOPE. -/
theorem gameK_at_Gu {Xi' W : Type} (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
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
    (herr : ∀ dB dt, (writtenPFull.ds₂.drop 8).take
        (proximityTestKind guardedProximityTestParts (pGu N) : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 (pGu N) rUFull * (bsRound .two dB.entry dB.kind).w, errJ (pGu N) rUFull dt)
        (rest₂ (0 + (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) (seatedAt o mk Z N c f) writtenPFull b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length]? = some p ∧
      p.b = held (guEntry ProofFile.Cl N) ∧
      p.base = writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take 8) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₂ (0 + (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 (pGu N) rUFull * (bsRound .two dB.entry dB.kind).w, errJ (pGu N) rUFull dt)
        ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      p.ior.red.LeadsK (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (fun _ => True)
        (fun a b => QV frShared (pGu N) (nlAt (pGu N) (seatedAt o mk Z N c f).t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ (p.base + p.trees)).2 := by
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hC := (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1
  have hl := (stretch_at_U o S.pol S.lay S.KL Z hZ mk N c hN hp _ hW 8
    H2K.Member.bat_UFull).2.2.1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hC.plan
  have hfree : (pGu N).nums.free = Johnson.G.OfPlan.rootsOf
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)) :=
    (congrArg (·.free) hn).trans (plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).1.2
  have e1 : (pGu N).nums.free = H2K.Member.piUFull.nums.free :=
    (congrArg (·.free) hn).trans (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW)
  have hf : 0 < (pGu N).nums.free := by
    rw [e1]
    decide
  obtain ⟨b', post', e⟩ := shared_behind ProofFile.Cl (p14N Z N) N
  have hcut : b₂ :: l₂ = sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++
      guEntry ProofFile.Cl N :: b' :: post' := by
    rw [← e]
    exact hfl.symm.trans (descN_shared o mk guardedProximityTestParts Z N c)
  have h := Coin.gameK_at_tile₂_le (seatedAt o mk Z N c f) "proof file" writtenPFull hD b₁ l₁ b₂ l₂
    b₃ l₃ rest₁ rest₂ rest₃ d wEnd (pGu N) rUFull 128 (Seat.enter (·.gU) (·.firstMask)) Seat.leave
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N) b' post' hfl hcut
    (guEntry_alike ProofFile.Cl N) hfree hC.plan hC.chain hC.joh hC.bat
    (ownMask_in_scope_U hS Z hZ mk N c hN hp)
    (H2K.Sizes.labels_U_of_full A hN _ hC.plan
      (rounds_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW)) hf rd
    (fun dB dt hx => herr dB dt ((congrArg (fun n => (writtenPFull.ds₂.drop n).take
      (proximityTestKind guardedProximityTestParts (pGu N) : Block T12 Unit).rounds.length) hl).symm.trans hx))
  obtain ⟨p, dB, dt, h1, h2, h3, h4⟩ := h
  exact ⟨p, dB, dt, h1, h2,
    h3.trans (congrArg (fun n => writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take n)) hl), h4⟩

/-- WHAT THE KEY's SIDE SAYS OF THE FILE's OWN PIECE AT G_u's SEAT, AT THE LETTERS OF RECORD: at
every
filling of piecesAt's letters whose second row's errors are the cap's (AtCap rest₂) and at every
number
of slots n: the piece number (sharedPre …).length of the second row is there · its block is the held
entry · its base is the written data's at 8 rounds · LeadsK and LeadsBN at the acting part in front,
nothing promised, of «QV ∧ the held part stays ∧ the strings ride», AT THE PIECE's OWN ERRORS ·
KeyLaw ·
and the two names of the chain's first tree's number are one. -/
def GameKGu {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (f : Xi' → ProofFile.Inst) : Prop :=
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
          rest₃ d wEnd).l₂)[(sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length]? = some p ∧
      p.b = held (guEntry ProofFile.Cl N) ∧
      p.base = writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take 8) ∧
      writtenPFull.t₁ = (seatedAt o mk Z N c f).t₁ ∧
      p.ior.red.LeadsK (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (fun _ => True)
        (fun a b => (QV frShared (pGu N) (nlAt (pGu N) (seatedAt o mk Z N c f).t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) ∧
          Rides frShared p.base a b) p.err ∧
      p.ior.red.LeadsBN (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (fun _ => True)
        (fun a b => (QV frShared (pGu N) (nlAt (pGu N) (seatedAt o mk Z N c f).t₁) rUFull rd
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave a b ∧ b.1 = (a.1.1, b.1.2)) ∧
          Rides frShared p.base a b) n p.err ∧
      p.ior.red.KeyLaw (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ p.base).2
        (actAt frShared Prod.snd (seatedAt o mk Z N c f).t₁ (p.base + p.trees)).2

/-- AT THE LETTERS OF RECORD: NO PREMISE ON THE ERRORS. -/
theorem gameK_at_Gu_cap {Xi' : Type} (W : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true)
    (f : Xi' → ProofFile.Inst) : GameKGu W o mk Z N c f := by
  intro b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd hfl rd hcap n
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hC := (closedL_in_scope_U hS Z hZ mk N c hN hp hpin).1
  have hl := (stretch_at_U o S.pol S.lay S.KL Z hZ mk N c hN hp _ hW 8
    H2K.Member.bat_UFull).2.2.1
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U hC.plan
  have hfree : (pGu N).nums.free = Johnson.G.OfPlan.rootsOf
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)) :=
    (congrArg (·.free) hn).trans (plain_free o S.pol S.lay S.KL Z hZ mk N c hN hp).1.2
  have e1 : (pGu N).nums.free = H2K.Member.piUFull.nums.free :=
    (congrArg (·.free) hn).trans (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW)
  have hf : 0 < (pGu N).nums.free := by
    rw [e1]
    decide
  obtain ⟨b', post', e⟩ := shared_behind ProofFile.Cl (p14N Z N) N
  have hcut : b₂ :: l₂ = sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++
      guEntry ProofFile.Cl N :: b' :: post' := by
    rw [← e]
    exact hfl.symm.trans (descN_shared o mk guardedProximityTestParts Z N c)
  have h := Coin.gameK_at_tile₂_cap (seatedAt o mk Z N c f) "proof file" writtenPFull hD b₁ l₁ b₂ l₂
    b₃ l₃ rest₁ rest₂ rest₃ d wEnd (pGu N) rUFull (Seat.enter (·.gU) (·.firstMask)) Seat.leave
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N) b' post' hfl hcut
    (guEntry_alike ProofFile.Cl N) hfree hC.plan hC.chain hC.joh hC.bat
    (ownMask_in_scope_U hS Z hZ mk N c hN hp)
    (H2K.Sizes.labels_U_of_full A hN _ hC.plan
      (rounds_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp A hW)
      (free_at_seat_U o S.pol S.lay S.KL Z hZ mk N c hN hp hW)) hf rd hcap n
  obtain ⟨p, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨p, h1, h2,
    h3.trans (congrArg (fun n => writtenPFull.t₁ + nTrees (writtenPFull.ds₂.take n)) hl),
    (opensShaped (seatedAt o mk Z N c f) "proof file" writtenPFull hD).2.1, h4, h5, h6⟩

/-- OF THE VALUE THAT IS LAID: TWO PREMISES: the files are in scope · the proof file's value is
laid. D: its rounds' data; r: its decision. -/
theorem gameK_at_Gu_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      GameKGu W o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  have hD' := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).2.2
  exact ⟨Z, N, c, hZ, hN, hF, Except.ok.inj (hD.symm.trans hD'), hr,
    gameK_at_Gu_cap W o S hS Z hZ _ N c hN hp hpin _⟩

end H2K.JointK

#print axioms H2K.JointK.gameK_at_Gu
#print axioms H2K.JointK.gameK_at_Gu_cap
#print axioms H2K.JointK.gameK_at_Gu_laid
