-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.ChainAtLast
import Johnson.Desc.K12.Coin.LawAtTileFirst
/-
Johnson/Loose/H2K12/TileAtLast.lean: THE GAME
OF THE PROXIMITY TEST (the kind K12) AT THE FILE's OWN PIECE ON THE FIRST CHAIN, at the seat
⟨1, none, 2, .K12⟩ of the proof file's seated description, in the goals' scope, in the form `Leads`:
the form that the rule `proofSound_at_desc` (Johnson/Desc/Plain/AtDesc.lean) asks of the first
chain's row (`EachLeads`). An assembly.
Who pays what. The game, general in the description: `game_at_tile₁VY_le`, `game_at_tile₁VY_cap`
(Johnson/Desc/K12/Coin/LawAtTileFirst.lean). That the entry of the flat list sits on the kind's
sub-protocol, behind its guards, with nothing joined behind it: `firstJ_sits`
(H2K12/FirstSeatForm.lean). The public premises at the seat: `PublicAtLast`
(ChainAtLast.lean).
`FirstOut`: J is the kind's sub-protocol as laid and the way out is `outCore`
at the guard's test. That the description has data, and which: `seat_in_scope`
(Johnson/Goal/Numbers/PlanWrittenDescScope.lean). That the seat is not the chain's last block, and
that a declared round stands behind it: by counting: the written list has 48,293 rounds; 48,237
stand in front; the test has 33.
THE NAMED PREMISE `LastIsTyped o S` (ChainAtLast.lean) stands bare in front of the seated and the
laid form. Neither of its two payers is whole: the test with code on what the planner sized is not
asked by the laid value; the closed sentence on the layout file is proved nowhere.
Main names:
  `GameFirstAt F D π r k n enter leave i B`: at every filling of `piecesAt`'s letters whose family
    of errors lays, at the number i of the first row, AT LEAST "BAT"'s count times the sampler's
    number and the place's own errors, round by round: the piece number i of the first row holds B;
    its base is the number of trees in the first n rounds of D's first chain; its data are some
    dB :: dt UNDER "THERE IS": the end ties them to no stretch of D's first chain (the premise on
    the family speaks of the stretch behind n rounds; the end does not say that the piece's data
    are that stretch); it bears the family's errors at these data; the pair is at most 2^-k of its
    rounds' verifier messages; and the piece's reduction leads, with nothing promised, at the
    piece's own errors, to the game's conclusion behind the two doors, with the step's own accept
    (`StepYes`, Johnson/Desc/K12/Coin/SitsYes.lean).
  `GameFirstCap F D π r n enter leave i B`: where the family's errors are the cap (`AtCap rest₁`,
    Johnson/Desc/Sound/BoundsAtCap.lean): NO PREMISE ON THE ERRORS, AND FEWER CLAUSES: the piece
    number i holds B, has that base, and its reduction leads at p.err. THAT p.err IS THE CAP IS NOT
    AMONG THE END's CLAUSES (the data and "p.err is the family's" are dropped): it is a reading.
  `gameFirstAt_of`: both, general in the description.
  `behind_L`: at the seat: l is b' :: post, and its declared rounds end in a round.
  `game_at_descN_L`: at the description pulled along any f (`FileDescription.pull`), under
    CondAtLast.lean's premises: at f := the laid value's own it is the laid value's description.
  `game_at_Last`, `game_at_Last_laid`: from `onlineDescription`'s return with the two tests; from `proofDataAndDecisionOfPublicFiles`'s
    return, with "D is the written data" and "r is the pulled description's run".
What it is not, first. NO TERM OF `EachLeads` IS BUILT: one of its two conjuncts, at one index, at
on := "nothing promised" and at K12's files' own relation Q: what that Q is worth to the rule's
table and to what glues the rows is not said. (1) That the conclusion gives the next piece's promise
is not said here. (2) The row is `piecesAt`'s: not read through `atDesc`; the data are the
written data: not at the stored table's depth. (3) The conclusion's numbering is read off the
record by the trees' labels. (4) One round's share each, no sum; 20 of the 128 bits are work at "CS"
and "BASE"; "BAT": its number is priced; its list's law is not shown. (5) 48,237 is a fact of the
written list, which is what a print showed. (6) No member: nothing shows that `onlineDescription` or
`proofDataAndDecisionOfPublicFiles` returns at any files in scope.
No soundness of a verifier is claimed. Nothing on hiding.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Slice OnBytes.Maker
open Iop _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (ownLabelsFreeB ChainAt QN nuOf nlAt)
open H2K.Member (piLFull rLFull dsOf xsFirst)
open H2K.Pub (johOk batV0 batPriceOk)
open H2K.Pin (NTuple)
open Johnson.G (dryProofFull writtenPFull)
open scoped ENNReal

/-- **The game at the piece number i of the first row of `piecesAt`**, with the step's own accept in
the conclusion, at every filling of its letters whose family of errors lays there at least the pair,
round by round. n: the rounds in front. The piece's data dB :: dt stand under "there is" in the end,
tied to no stretch of D's first chain. -/
def GameFirstAt {Xi : Type} (F : FileDescription Xi) (D : WholeD) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (k n : ℕ) (enter : F.S₁ → Except String T12) (leave : F.S₁ → T12 → Except String F.S₁)
    (i : ℕ) (B : Block F.S₁ F.Cl) : Prop :=
  ∀ (W : Type) (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (rd : ℕ → ℕ), F.first.blocksInOrder = b₁ :: l₁ →
    (∀ dB dt, (D.ds₁.drop n).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, Coin.errJ π r dt)
        (rest₁ (0 + i) (dB :: dt)).err) →
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[i]? = some p ∧
      p.b = held B ∧ p.base = 0 + nTrees (D.ds₁.take n) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₁ (0 + i) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, Coin.errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.Leads (fun _ => True)
        (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
            QN π (NTuple (frameAt D (allOf D) D.key₁ 0) π
              (nuOf π (nlAt π (numAt F.t₁ F.t₂ 0 (.own 0))) t) (fun s => r s.st) rd) (t, a.2)) ∧
          Coin.StepYes (frameAt D (allOf D) D.key₁ 0).ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter
            leave a.1.2 b.1.2) ∧
          b.1 = (a.1.1, b.1.2))
        p.err

/-- **Where the family's errors are the cap** (`AtCap rest₁`): no premise on the errors. The end
keeps the piece, what it holds, its base, and `Leads` at p.err; that p.err is the cap is not among
its clauses. -/
def GameFirstCap {Xi : Type} (F : FileDescription Xi) (D : WholeD) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (n : ℕ) (enter : F.S₁ → Except String T12) (leave : F.S₁ → T12 → Except String F.S₁)
    (i : ℕ) (B : Block F.S₁ F.Cl) : Prop :=
  ∀ (W : Type) (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (rd : ℕ → ℕ), F.first.blocksInOrder = b₁ :: l₁ → AtCap rest₁ →
    ∃ p,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[i]? = some p ∧
      p.b = held B ∧ p.base = 0 + nTrees (D.ds₁.take n) ∧
      p.ior.red.Leads (fun _ => True)
        (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
            QN π (NTuple (frameAt D (allOf D) D.key₁ 0) π
              (nuOf π (nlAt π (numAt F.t₁ F.t₂ 0 (.own 0))) t) (fun s => r s.st) rd) (t, a.2)) ∧
          Coin.StepYes (frameAt D (allOf D) D.key₁ 0).ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter
            leave a.1.2 b.1.2) ∧
          b.1 = (a.1.1, b.1.2))
        p.err

/-- **General in the description.** -/
theorem gameFirstAt_of {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₁ → Except String T12) (leave : F.S₁ → T12 → Except String F.S₁)
    (pre : List (Block F.S₁ F.Cl)) (B b' : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (postR : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hcut : F.first.blocksInOrder = pre ++ B :: b' :: post)
    (hend : (b' :: post).flatMap (·.rounds) = postR ++ [r₀])
    (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave)
    (hfree : π.nums.free = Johnson.G.OfPlan.rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (n : ℕ) (hn : (pre.flatMap (·.rounds)).length = n) :
    GameFirstAt F D π r 128 n enter leave pre.length B ∧
      GameFirstCap F D π r n enter leave pre.length B := by
  subst hn
  refine ⟨?_, ?_⟩
  · intro W b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd rd hfl herr
    exact Coin.game_at_tile₁VY_le F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r 128
      enter leave pre B b' post postR r₀ hfl (hfl.symm.trans hcut) hend hS hfree hp hC hj hbat ho
      hlb rd herr
  · intro W b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd rd hfl hcap
    exact Coin.game_at_tile₁VY_cap F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r
      enter leave pre B b' post postR r₀ hfl (hfl.symm.trans hcut) hend hS hfree hp hC hj hbat ho
      hlb rd hcap

section
variable (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
  (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
  (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
  (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
  (A : H2K.Sizes.AtFull Z.made.p.chains.made)
  (hL : Z.made.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull)
  (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
    .ok dryProofFull)
  (same : First.S → First.S → Bool) (pre l : List (Block First.S ProofFile.Cl))
  (J : Block First.S ProofFile.Cl)
  (hb : c.blocksInOrder = pre ++ firstEntry same J :: l) (hJ : FirstJ (pL N) J)
include hZ hN hp A hL hW hb hJ

/-- The seat is not the first chain's last block, and a declared round stands behind it: of the
written list's 48,293 rounds 48,237 stand in front and 33 are the test's. -/
theorem behind_L : ∃ b' post postR r₀, l = b' :: post ∧
    (b' :: post).flatMap (·.rounds) = postR ++ [r₀] := by
  obtain ⟨hx, hr0, hl, _⟩ :=
    stretch_at_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  have hR := rounds_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  have hds : (proximityTestKind guardedProximityTestParts (pL N) : Blk').rounds = dsOf piLFull :=
    Option.some.inj (hr0.symm.trans (hR.trans H2K.Member.rounds_LFull))
  have h33 : (dsOf piLFull).length = 33 := by
    have := H2K.Member.namesL_length
    unfold H2K.Member.namesL at this
    rwa [List.length_map] at this
  have hT : xsFirst.length = 48293 := by
    unfold H2K.Member.xsFirst
    rw [List.length_map]
    exact congrArg Prod.fst Johnson.G.dryProofFull_length
  have hlen := congrArg List.length (entries_of_rounds hx)
  rw [List.length_map, List.length_map, List.length_append, List.length_append, hT, hl, hds,
    h33] at hlen
  have hne : l.flatMap (·.rounds) ≠ [] := List.ne_nil_of_length_pos (by omega)
  cases l with
  | nil => exact absurd rfl hne
  | cons b' post =>
    exact ⟨b', post, _, _, rfl, (List.dropLast_concat_getLast hne).symm⟩

/-- **The game at the file's own piece at the first chain's seat**, at the description pulled along
any f. -/
theorem game_at_descN_L {Xi' : Type} (f : Xi' → ProofFile.Inst) (D : WholeD)
    (hD : (descN o mk guardedProximityTestParts Z N c).data "proof file" = .ok D) :
    ∃ leave, FirstOut same (pL N) J leave ∧
      GameFirstAt ((descN o mk guardedProximityTestParts Z N c).pull f) D (pL N) rLFull 128 48237 enterFinish leave
        pre.length (firstEntry same J) ∧
      GameFirstCap ((descN o mk guardedProximityTestParts Z N c).pull f) D (pL N) rLFull 48237 enterFinish leave
        pre.length (firstEntry same J) := by
  obtain ⟨hl, C, _, ho, hfree, hlb, _⟩ :=
    public_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  obtain ⟨b', post, postR, r₀, rfl, hend⟩ :=
    behind_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  obtain ⟨leave, hout, hS⟩ := firstJ_sits same (pL N) J hJ
  exact ⟨leave, hout, gameFirstAt_of ((descN o mk guardedProximityTestParts Z N c).pull f) "proof file" D hD (pL N)
    rLFull enterFinish leave pre (firstEntry same J) b' post postR r₀ hb hend hS hfree C.plan
    C.chain C.joh C.bat ho hlb 48237 hl⟩

end

/-- **At the seated description, in scope**: the named premise stands bare in front. -/
theorem game_at_Last {Xi' : Type} (f : Xi' → ProofFile.Inst) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles)
    (hS : VerifierAndGoals.InScope S = true) (hT : LastIsTyped o S) (F : FileDescription ProofFile.Inst)
    (hF : ProofFile.onlineDescription o S.pol S.lay S.KL = .ok F) (hp : F.planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol F = true) :
    ∃ Z N c pre l J leave, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧ F = descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c ∧
      c.blocksInOrder = pre ++ firstEntry ProofFile.sameReply J :: l ∧ PublicAtLast Z N pre ∧
      FirstOut ProofFile.sameReply (pL N) J leave ∧
      GameFirstAt ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pull f) writtenPFull (pL N) rLFull
        128 48237 enterFinish leave pre.length (firstEntry ProofFile.sameReply J) ∧
      GameFirstCap ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pull f) writtenPFull (pL N) rLFull
        48237 enterFinish leave pre.length (firstEntry ProofFile.sameReply J) := by
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _, pre, l, J, hb, _, hJ⟩ := k12_sits o S.pol S.lay S.KL F hF
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hLs := hT Z hZ
  obtain ⟨hW, _, hD⟩ := VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin
  obtain ⟨leave, hout, hg⟩ := game_at_descN_L o S.pol S.lay S.KL Z hZ _ N c hN hp A hLs hW
    ProofFile.sameReply pre l J hb hJ f writtenPFull hD
  exact ⟨Z, N, c, pre, l, J, leave, hZ, hN, rfl, hb,
    public_at_seat_L o S.pol S.lay S.KL Z hZ _ N c hN hp A hLs hW ProofFile.sameReply pre l J hb hJ,
    hout, hg⟩

/-- **Of the value that is laid**: D is the written data; r is the run of the very description of
whose piece the game speaks. -/
theorem game_at_Last_laid (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true) (o : ProofFile.SecondHashFunctionArgument)
    (hT : LastIsTyped o S) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c pre l J leave, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧
      r = ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pull LPFD.Full.instanceAsPlainRecord).run ∧
      c.blocksInOrder = pre ++ firstEntry ProofFile.sameReply J :: l ∧ PublicAtLast Z N pre ∧
      FirstOut ProofFile.sameReply (pL N) J leave ∧
      GameFirstAt ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pull LPFD.Full.instanceAsPlainRecord) writtenPFull
        (pL N) rLFull 128 48237 enterFinish leave pre.length (firstEntry ProofFile.sameReply J) ∧
      GameFirstCap ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pull LPFD.Full.instanceAsPlainRecord) writtenPFull
        (pL N) rLFull 48237 enterFinish leave pre.length (firstEntry ProofFile.sameReply J) := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  have hD' := (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).2.2
  obtain ⟨Z, N, c, pre, l, J, leave, hZ, hN, rfl, hb, hP, hout, hg⟩ :=
    game_at_Last LPFD.Full.instanceAsPlainRecord o S hS hT F hF hp hpin
  exact ⟨Z, N, c, pre, l, J, leave, hZ, hN, hF, Except.ok.inj (hD.symm.trans hD'), hr, hb, hP,
    hout, hg⟩

end H2K.JointK

#print axioms H2K.JointK.gameFirstAt_of
#print axioms H2K.JointK.behind_L
#print axioms H2K.JointK.game_at_descN_L
#print axioms H2K.JointK.game_at_Last
#print axioms H2K.JointK.game_at_Last_laid
