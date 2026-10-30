-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the rows' sentence at the test on G_omega, at a run, at the maker's return.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/SaysAtOPaid.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN
MEMBER: nothing shows that ready or runC returns at the maker's return, or that the part is called
at any coin: where it is never called the end is asked of nothing.

What is here. The sentence on values `SaysAt` (AsksWhole.lean: the rows that the test takes in say
true things of the words that the job's own rows make) AT THE CALLED SECOND PART OF THE TEST ON
G_omega, at the maker's return at the wide filling and that return's own book, at the walk's own
stand and at the blocks that the book hands as carried at the run's own coins: WITH NO PREMISE ON
VALUES. `saysAt_run_O` (Sim2/SaysAtRunO.lean) has it from two premises on what was shown and the tie
of the words; here all three are paid. No definition; three statements.

  `seat_at_O`   the seat: the side, its place, the second member's stand behind the first ten.
  `split_half_at_return`   the eighth sub-protocol's half is what the search finds at the return.
  `saysAt_O_paid`   the statement.

THE PREMISES, SORTED. PUBLIC: h · hO · hb. THE MAKER: hAr (the wide filling; at the matrices and
the base's values it is the base filling). THE RUN: hρ (not read by the proof; kept for the caller's
binder order) · hR · hrun · hc. NO PREMISE ON VALUES, ON A BOOK, ON THE FILLING's HALVES OR AT A
STAND. No premise on the instance's key: the limit on the committer's randomness that binds the like
top at the test on G_u does not bear here: the rows on G_omega are two sample rows and one open row,
and neither the key's answers nor the stored columns enter them.

How each is paid. `ShownO`: `shownO_at_run`; `ShownMu`: `shownMu_at_run` with `rows_held` and
`coin_head` (Sim/ShownAtRun.lean, HeldAtCommitter.lean, AtFullSide/K12/CutsAtHead.lean): the first
two are general in the stand and ask of it only that six, or eight, rounds lie in front. The tie:
`tie_at_run_O` (Sim2/TieAtRunO.lean), its test on the book by `bookCutsOmega_head`
(SimO/BookO.lean). The book, the key's reader, the test's half and the sending's: `four_at_return`
(Sim2/ListOAtReturn.lean). What is held: `heldAt` of the input that ready lays and of the coins that
the book lends the sending of o_omega and o_sp; the first sender's coins enter nowhere: the empty
array stands there.

Every letter under "there are" in the end: m is tied by the walk's own equation; ca stands under ∀,
bound by carriedAt at the run's own k.

The label. Files beneath bear "NOT IN FRONT OF A LAW OVER COINS" for statements behind a thread's
stand (K12/AtFile/OSays.lean, OWords.lean). What is called of them has no thread and no coin among
its binders, and no premise of that kind is left here.

Limits. At the maker's return at the wide filling, not at the online maker's: no crossing is typed
here. Of the walk (runC), not of play. It is the clause on values alone: not On, not `Good`. No
later law may take it as a hypothesis on a run and then speak of the random values as sampled anew.
Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SaysAtRunO
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TieAtRunO
import Johnson.Desc.ProofFile.Honest.K12.HeldAtCommitter
import Johnson.Desc.ProofFile.Honest.K14.PaidAt
import Johnson.Desc.ProofFile.Honest.K14.PartsPlay
import AtFullSide.K12.CutsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open OnBytes (TableKey E)
open VerifiableInference.Desc (Block Chain K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks)
open H2K.Member (piOFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K14 (sendPlace liftSend sendingPart jobOmega)
open AtFullSide.K12 (coin_head)

/-- CONDITIONAL: on the head, hO, the eight, ready's return and the test's half. **The seat of the
test on G_omega at a run**: there is the side that the row of the test seats; it stands at the
test's place; its guarded second member stands behind the shared chain's first ten, after the first
part's rounds. The proof's text is the first half of the proof of `onOmega_at_side`
(SimO/OnAtSide.lean), which holds these facts and does not hand them out. -/
theorem seat_at_O {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {W₀ Tr Y : Type} {pO : P12} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y} {w₀ : W₀}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y}
    (wt : W₀ → Weights)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hg₀ : (P.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : Placed Empty _
          _).needsField) :
    ∃ (σ : Side St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
      (pre t : List (Block St ProofFile.Cl)), σ.block.place = pO.place ∧
      pO.place = ⟨2, none, 10, .K12⟩ ∧
      StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ
        (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
            (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5,
            b6, b7, b8]) : Member Empty _ _ _).guarded pre t
        (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages) ∧
      pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10 := by
  obtain ⟨b, hf, -, -, -⟩ := find_gomega h hO
  obtain ⟨σ, hσ⟩ : ∃ σ : Side St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey,
      Side.seated (P5J.F0T o Zp Np cF).shared.blocksInOrder pO.place
        (omegaRow (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega
            Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8])) [] =
            some σ := by
    unfold Side.seated
    rw [hf]
    exact ⟨_, rfl⟩
  have hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : Placed Empty _
          _).needsField := by
    have e := (side_omega h hO _ _ _ none (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf
        Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) rfl rfl [] σ hσ).2.2.2.2.1
    rw [e]
    exact hg₀
  obtain ⟨hfit, hmem, hrow, hblk, hpl, hr, hor⟩ := side_omega h hO _ _ _ none (simulatorJobAtOmega
      Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) rfl rfl [] σ hσ
  have hk := planOk_head_O h hO
  have hlaid : σ.block.rounds.zip σ.block.oracles = (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6,
      b7, b8] wt pO).laid := by
    rw [hr, hor]
    exact zip_laid pO hk
  have hsh := planOk_shaped h.laid.planOk σ.block hblk
  unfold VerifiableInference.Desc.Block.shaped at hsh
  rw [Bool.and_eq_true] at hsh
  have hlen : σ.block.rounds.length ≤ σ.block.oracles.length := Nat.le_of_eq (beq_iff_eq.1
      hsh.1).symm
  have hn := nums_head_O h hO
  obtain ⟨s, next, rest, hlit⟩ : ∃ s next rest, piOFull.nums.stages = s :: next :: rest := ⟨_, _,
      _, rfl⟩
  have hst : (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages = s :: next
      :: rest := by
    show pO.nums.stages = _
    rw [hn, hlit]
  have l1 : (firstPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) :
      ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).moves.length =
      firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages :=
    (congrArg List.length (first_moves (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt
        pO))).trans (len_movesFrom (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) _ _
        _)
  have l2 : (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part
      Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).moves.length =
      restLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages :=
    (congrArg List.length (rest_moves (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) s
        next rest hst)).trans (len_movesFrom (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]
        wt pO) _ _ _)
  have hpos : ((restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
      (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7,
      b8]) : Member Empty _ _ _).guarded).part.moves.length ≠ 0 := by
    show ((restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part
        Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).moves.map _).length ≠ 0
    rw [List.length_map, l2]
    intro h0
    have Q : PublicTiesOwn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
        (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6,
        b7, b8]) H2K.Member.codesFull 3 := publicTiesOwn_head h hO _ _ _ none _ rfl rfl
    have q' := Q.rounds
    omega
  have hu : (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
      (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7,
      b8]) : Member Empty _ _ _).guarded ∈ σ.members := by
    rw [hmem]
    exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)
  obtain ⟨pre, t, S⟩ := stands_member h.laid.planOk hR σ hblk hfit _ hu hpos _ hg
    (by rw [hrow]; rfl)
  have e : ((σ.row.take ((restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
      (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7,
      b8]) : Member Empty _ _ _).guarded).number).map (·.1.moves.length)).sum =
      firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages := by
    rw [hrow]
    have q : ((firstPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) :
        ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField).moves.length =
        firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages := by
      show (List.map _ _).length = _
      rw [List.length_map]
      exact l1
    exact (Nat.add_zero _).trans q
  rw [e] at S
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  have hnd := (ProofFile.Honest.places_nodup (((P5J.F0T o Zp Np cF).planOk_ok).1
            h.laid.planOk).places).2.1
  have h10 := pre_at_omega (o := o) (Zp := Zp) (Np := Np) (cF := cF)
    b1 b2 b3 b4 b5 b6 b7 b8 hb hnd nO h1 pre t σ.block S.cut
    (hpl.trans (H2K.JointK.place_of_p12At _ _))
  exact ⟨σ, pre, t, hpl, H2K.JointK.place_of_p12At _ _, S, h10⟩

/-- CONDITIONAL: on the head, the eight and the maker's return. **The eighth sub-protocol's half is
what the search finds in the shared list of the prover that the maker returns at the wide
filling.** -/
theorem split_half_at_return {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar) :
    (Ar.H.shared.find? fun g => g.place == b8.place) = some ⟨b8.place,
      [(K14.liftK14 ⟨(K1.qAt Zp Np).S, 0, 6⟩ (I.weights Zp)
        (K14.splitPart ⟨(K1.qAt Zp Np).S, 0, 6⟩) :
        Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit)]⟩ := by
  have eZ : Ar.Z = Zp := (atPure_at_laid h.laid hAr).1
  have h1 : nowSharedBy (I.weights Zp) Zp =
      .ok (K14.proverSidesOfSharedRounds ⟨(K1.qAt Zp Np).S, 0, 6⟩ (I.weights Zp) ++
        K14.proverSidesOfSharedSendings { P := K1.qAt Zp Np, atPoint := 0 } (I.weights Zp)
          (K14.randNow (K1.qAt Zp Np))) := K14.sixBody_at_head h _
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hAr
  have hs' : Ar.H.shared = sharedWithUO I Ar.Z := hs
  rw [eZ] at hs'
  have e0 : sharedWithUO I Zp =
      K14.proverSidesOfSharedRounds ⟨(K1.qAt Zp Np).S, 0, 6⟩ (I.weights Zp) ++
        K14.proverSidesOfSharedSendings { P := K1.qAt Zp Np, atPoint := 0 } (I.weights Zp)
          (K14.randNow (K1.qAt Zp Np)) ++
        halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp ++
        halfO (I.weights Zp) Zp := by
    show (match nowSharedBy (I.weights Zp) Zp with
      | .ok six =>
        six ++ halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp ++
          halfO (I.weights Zp) Zp
      | .error _ => []) = _
    rw [h1]
  have hH : (K14.proverSidesOfSharedRounds ⟨(K1.qAt Zp Np).S, 0, 6⟩ (I.weights Zp) :
      List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)).find?
        (fun g => g.place == K14.place 8) = some ⟨K14.place 8,
      [K14.liftK14 ⟨(K1.qAt Zp Np).S, 0, 6⟩ (I.weights Zp)
        (K14.splitPart ⟨(K1.qAt Zp Np).S, 0, 6⟩)]⟩ := by
    rw [K14.halves_eq, if_pos (facts_at_head h.toAtMg).1]
    rfl
  rw [hs', e0, (K14.places4 _ b1 b2 b3 b4 b5 b6 b7 b8 hb).2.2.2, List.find?_append,
    List.find?_append, List.find?_append, hH]
  rfl

/-- CONDITIONAL: see the head. **`SaysAt` AT A CALLED SECOND PART OF THE TEST ON G_omega AT THE
MAKER's RETURN, AT THE CARRIED COINS**: no premise on values. The door's own fold returned at this
same m (`door_of_called_at_O`, Sim2/ListO.lean), so this is no sentence on the fall-back. -/
theorem saysAt_O_paid {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {pO : P12}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar)
    {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (_hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B Ar.H w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B Ar.H w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨pO.place, 1⟩ = true) :
    ∃ m : Mid (Common W₀ IndexCommitterCoins TableKey) Unit,
      midSharedAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B Ar.H w₀ rc x k ρ ⟨pO.place, 1⟩ =
        .ok (some m) ∧
      ∀ ca : CsAll (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp)
          pO) :
          Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField.carries,
        carriedAt Ar.B k 1 ⟨pO.place, 1⟩
          (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO) :
            Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField = .ok ca →
        SaysAt (jobManyO (X₀ := Unit) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] pO
            (fun w => I.weights Zp w.w₀) (fun w => randAt (K1.qAt Zp Np) w.rc))
          m.st.input
          (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO) m)
          (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO)
            (stretches _ ca)) := by
  obtain ⟨hB, hα, hg, hgO⟩ := four_at_return h hO b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hR
  have hgS := split_half_at_return h b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr
  obtain ⟨σ, pre, t, hpl, hp10, S, h10⟩ := seat_at_O h.toAtMg hO b1 b2 b3 b4 b5 b6 b7 b8 hb
    (I.weights Zp) hR hg
  have hc' : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hpl]
    exact hc
  obtain ⟨m, d8, d9, rest, rest₉, more, more₉, W, D8, hm, hf8, -, hW, -, -, hst, hent, hall⟩ :=
    saysAt_run_O h.toAtMg hO b1 b2 b3 b4 b5 b6 b7 b8 hb hα (fun w => I.weights Zp w.w₀)
      (fun w => randAt (K1.qAt Zp Np) w.rc) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf
          Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) hR σ pre t S h10 hrun hc'
  refine ⟨m, by rw [← hpl]; exact hm, fun ca hca => ?_⟩
  have h8 := rounds_in_front_O h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb pre h10
  -- what was shown, by what the run has played
  obtain ⟨cO, lO, sO⟩ := shownO_at_run h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb hR hrun σ _ pre t _ S hc'
    (Nat.le_trans (by decide : 6 ≤ 8) (Nat.le_trans h8 (Nat.le_add_right _ _)))
    (sendShapes_head h.toAtMg)
    (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w : Common W₀ IndexCommitterCoins TableKey => I.weights Zp w.w₀)
      (fun w => randAt (K1.qAt Zp Np) w.rc)) hgO W D8 rest hW hst
  obtain ⟨cS, lS, sM⟩ := shownMu_at_run h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb hR hrun σ _ pre t _ S
      hc'
    (Nat.le_trans h8 (Nat.le_add_right _ _)) ⟨(K1.qAt Zp Np).S, 0, 6⟩ (I.weights Zp) rfl rfl rfl
        hgS W D8 rest hW hst
  refine hall (heldAt (K1.qAt Zp Np)
    (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w : Common W₀ IndexCommitterCoins TableKey => I.weights Zp w.w₀)
      (fun w => randAt (K1.qAt Zp Np) w.rc) R.common) #[] (coinsE cO.1.1).toArray) _ (sO #[])
    (sM _ (fun r' _ j hj => rows_held (K1.qAt Zp Np) ⟨(K1.qAt Zp Np).S, 0, 6⟩ rfl (I.weights Zp)
        (K14.randNow (K1.qAt Zp Np)) R.common _ _ r' j hj)
      (coin_head h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb hB ⟨(K1.qAt Zp Np).S, 0, 6⟩ (I.weights Zp) _
          lS lO _ _)) ?_
  exact tie_at_run_O h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb _ (fun w => I.weights Zp w.w₀)
    (fun w => randAt (K1.qAt Zp Np) w.rc) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf
        Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) hR σ pre t S h10 hrun hc' hpl
    (bookCutsOmega_head h.toAtMg hB pO hp10) W d8 d9 rest more #[] cO hf8 hW lO m ca hm
    (by rw [hpl]; exact hca) (shape_head_OmegaF h.toAtMg _ hb _ _ _ _) hent

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.seat_at_O
#print axioms ProofFile.Honest.K12.Sim2.split_half_at_return
#print axioms ProofFile.Honest.K12.Sim2.saysAt_O_paid
