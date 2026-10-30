-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/AtHandAtFinish.lean

The way into the first chain's proximity test (`enterFinish`, Johnson/Desc/K12/AtFinish.lean)
returns at the state that the description's own fold reaches in front of the test; so the state on
entry of DoorL.lean in this folder is at hand at every called part of the test's side, and its
default is not taken there. Seven theorems; no definition.

  `enters_of_finishPlace`: behind the place of the last code switch the way in returns, where no
      mark of failure is left.
  `enters_behind_finish`: the same at the seat: at an opening, where the step of the first block
      behind the links returns. No premise on scope.
  `enters_of_fold`: in scope: where the fold over the blocks in front of the test returns, at any
      start, rounds and columns.
  `atHandL_at_head`: under the head `P5J.AtMg` at the older hash: `doorL_at_head`
      (KeepsAtFinish.lean) with its last hypothesis gone: `atHandL` is true, `doorTryL` returns,
      `doorL` agrees with what the way in returns but for targets, whatever its default.
  `testSide_place`, `placeL_of_four`: the side that `testSide` seats stands at the job's place; the
      planner's record for this test bears the test's place.
  `atHandL_at_seat`: `atHandL_at_head` at the seated side.

Why it holds. `enterFinish` reads three things of the state: that the chain stands at its finish,
that no count of claims waits, that no test is marked as failed. The state in front of the test is
what the block in front, the last code switch's place as it is seated, has returned. That place's
quiet step behind lays the finish (`finishBehindQ_iff`, Johnson/Top/H0/Tw/K2C/Asks.lean); the
switch's own decision leaves no count owed (`decideWith_yes`, Johnson/Top/H0/Tw/K2C/Laws.lean); the
seat's guard refuses where a mark is left (`IM.yes_alone`, Johnson/IMR/SeatForm.lean). No accept of
the test itself is asked.

Beside it in the library: from the verifier's yes to all three views the same is had by
`H2K.JointK.descN_atL` (Johnson/Loose/H2K12/FirstSeatForm.lean), whose conclusion `AtCut` holds the
clause that the way in returns (Johnson/Desc/K12/Law/Sits.lean), and by `H2K.JointK.course_atFinish`
(Johnson/Desc/K12/Law/AccKAtFinish.lean).

Over what it stands. Files of the kind K10's authors, rows of the sealed library
(Johnson/Desc/ProofFile/Honest/K10/: AskWipe, BatWipe, RoundsStretch, StAtZero, WipeFold, WipeS,
ZeroTie, Wipe/), and this folder's Wipe.lean, Fold.lean, Readers.lean, Top.lean, DoorL.lean and
KeepsAtFinish.lean.

Limits.
- In the goals' scope and at the library's older hash, but for the first two and the two small ones.
- The premises that are left in `atHandL_at_seat`: on the filling and the book (hR, St, hσ, hp), on
  the run (hrun, hc); and inside the conclusion that start is the description's own at the run's
  input, and that the front shows just the rounds of the blocks in front.
- The head shows no test to accept (Johnson/P5J/AtMg.lean's own limit); at the older hash it has
  members at the goals' two named sets of public files (`headMember_named`,
  AtFullSide/Top/HeadMemberAtGap.lean); these files do not show that the premises on the filling,
  the book and the run hold with it. Nothing on whether `ready` or `runC` returns or a part is
  called.
- Of the walk (`runC`) and of `midAtW`'s stand, as `called_at_first` is.
- `doorL`'s value is not the record T: it agrees with T but for the rows' targets. How it may be
  spoken of: DoorL.lean's head.
- The stand is the state that `midAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- No property of a prover or a protocol: nothing on completeness, soundness, binding or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.KeepsAtFinish
import Johnson.Loose.H2K12.GroupAt354
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open VerifiableInference.Desc (Block Chain Place OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest

/-- **Behind the place of the last code switch the way into the test returns**, where no mark of
failure is left. All three things that `enterFinish` reads are facts on what that place's decision
returns: the quiet step behind lays `.fin`; the switch's own decision leaves no count of claims
owed; the mark is the premise. -/
theorem enters_of_finishPlace (p : VerifiableInference.Desc.First.K2.P2) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (VerifiableInference.Desc.First.K2.finishPlace p : Block S Unit).decide s rs gs = .ok s')
    (hf : s'.failed = none) : ∃ T, enterFinish s' = .ok T := by
  obtain ⟨t, t', rs', gs', -, h2, h3, -⟩ := H2K12.finishPlace_cut p h
  obtain ⟨a, m, -, -, e⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' s').1 h3
  have ow := (VerifiableInference.Desc.First.K2.decideWith_yes h2).owes
  have h1 : s'.here = .fin { a with mask := some m } := by rw [e]
  have h4 : s'.rowsOwed = none := by rw [e]; exact ow
  have h5 : s'.noneWaits = true := by
    unfold S.noneWaits
    rw [h4]
  have key : enterFinish s' = .ok
      { st := s'.st, book := s'.book, roots := s'.roots, g := a.fr.group, pass := .nothing,
        mask := some m } := by
    unfold enterFinish
    rw [h1]
    dsimp only
    rw [h5, hf]
    rfl
  exact ⟨_, key⟩

/-- **The same at the seat.** At an opening of the proof file's description: where the step of the
first block behind the links (c.back[0], "F:1"), as `Chain.blocksInOrder` lays it, returns s', the way into
the test returns at s'. The seat's own guard on the mark pays the premise on the mark. No premise on
scope. -/
theorem enters_behind_finish {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : c.back[0]? = some b) {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : ℕ}
    (h : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl).step 0 s rs cols =
      .ok (s', k)) : ∃ T, enterFinish s' = .ok T := by
  obtain ⟨-, -, hd, -⟩ := VerifiableInference.Desc.Block.step_ok.1 h
  obtain ⟨b0, x, e0, -, -, hla, hx⟩ := IM.k2_finish_of O
  have eb : b0 = b := Option.some.inj (e0.symm.trans hb)
  subst eb
  have hd' : b0.decide s (rs.map VerifiableInference.Desc.noDigest)
      (VerifiableInference.Desc.regroup
        ((VerifiableInference.Desc.groupsOf 0 b0.rounds (rs.map (·.drawn))).map (·.length))
        (cols.take k)) = .ok s' := hd
  obtain ⟨y1, y2, -⟩ := (IM.yes_alone hla (by decide) s s' _ _).1 hd'
  rcases hx with ⟨-, hm⟩ | ⟨P, n, -, -, ex⟩
  · obtain ⟨e, he⟩ := hm s (rs.map VerifiableInference.Desc.noDigest)
      (VerifiableInference.Desc.regroup
        ((VerifiableInference.Desc.groupsOf 0 b0.rounds (rs.map (·.drawn))).map (·.length))
        (cols.take k))
    have y1' : x.decide s _ _ = .ok s' := y1
    rw [he] at y1'
    cases y1'
  · have y1' : x.decide s _ _ = .ok s' := y1
    rw [ex] at y1'
    exact enters_of_finishPlace _ y1' y2

/-- **Where the description's own fold over the blocks in front of the test returns, the way into
the test returns at its state.** In the goals' scope, at an opening at the library's older hash. At
any start, rounds and columns. It begs no accept of the test. -/
theorem enters_of_fold {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s₀ : S}
    {rs : List Fmt.RoundView} {cs : List OpenedColumn} {r : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.takeWhile (·.place != AtProof.placeL)) s₀ rs cs = .ok r) :
    ∃ T, enterFinish r.1 = .ok T := by
  rw [front_is_take_L hS hR O] at h
  obtain ⟨b0, -, e0, -⟩ := IM.k2_finish_of O
  have h353 : c.blocksInOrder[353]? = some { b0 with planOk := b0.planOk && b0.hasNoClaimsAndNothingAfter } :=
    (IM.back_numbers hS hR O).1 0 b0 e0
  rw [show (354 : ℕ) = 353 + 1 from rfl, List.take_add_one, h353] at h
  obtain ⟨s₁, rs₁, cs₁, -, h2⟩ :=
    (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 h
  have h2' : foldBlocks 0 [({ b0 with planOk := b0.planOk && b0.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl)] s₁ rs₁
      cs₁ = .ok r := h2
  obtain ⟨-, s', k, h3, h4⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h2'
  have e : r = (s', _, _) := (Except.ok.inj h4).symm
  rw [e]
  exact enters_behind_finish O e0 h3

/-- **Under the head the state on entry is at hand at every called part of the test's side.**
`doorL_at_head` (KeepsAtFinish.lean) with its last hypothesis gone: the way in returns at s, by
`enters_of_fold`. So, with all eight clauses of `called_at_first` on m, s and cs: there is a record
T that the way in returns at s; `atHandL` is true; `doorTryL` returns T wiped; and `doorL`, whatever
its default, agrees with T but for targets: the default is not taken. What is left as premises: on
the filling and the book (hR, St), on the run (hrun, hc), that the side stands at the test's place
(hσ); and inside the conclusion that start is the description's own and what the front shows. At the
older hash alone. The head shows no test to accept; at the older hash it has members at the goals'
two named sets of public files (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean); these
files do not show that the premises on the filling, the book and the run hold with it. -/
theorem atHandL_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hσ : σ.block.place = AtProof.placeL) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs more : List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∃ T : T12, enterFinish s = .ok T ∧
      ∀ (start : Local W₀ Rc ProofFile.Inst Tr → S) (fr : Front Y),
        start m.st.input =
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x) →
        fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        atHandL cF.blocksInOrder start σ.block.place m.st.input fr = true ∧
        doorTryL cF.blocksInOrder start σ.block.place m.st.input fr = .ok (wipeT T) ∧
        ∀ fall : T12, Agree (doorL cF.blocksInOrder start σ.block.place fall m.st.input fr) T := by
  obtain ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, b7⟩ :=
    doorL_at_head h hR σ u pre t i St hrun hc hσ
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hn := (places_nodup (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1 h.laid.planOk).places).1
  have hcut : cF.blocksInOrder = pre ++ σ.block :: t := St.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : cF.blocksInOrder.takeWhile (·.place != AtProof.placeL) = pre := by
    rw [← hσ, hcut]
    exact takeWhile_cut pre t σ.block (apart_of_nodup hn')
  obtain ⟨T, hT⟩ := enters_of_fold h.scope h.reads O (hpre ▸ a7)
  refine ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, T, hT,
    fun start fr hs hf => ?_⟩
  obtain ⟨c1, c2, c3⟩ := b7 start fr hs hf
  refine ⟨?_, ?_, fun fall => c3 T fall hT⟩
  · rw [c2, hT]
    rfl
  · rw [c1, hT]
    rfl

/-- The side that `testSide` seats stands at the job's place. -/
theorem testSide_place {σ₀ Cl V W X Pb : Type} {bs : List (Block σ₀ Cl)} {J : TestJob W X}
    {Js : SimJob Pb} {fs : List (Fall σ₀)} {σ : Side σ₀ Cl V W X Pb}
    (h : testSide bs J Js fs = some σ) : σ.block.place = J.p.place := by
  unfold testSide Side.seated at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have e := List.find?_some hb
  exact eq_of_beq e

/-- The planner's record for the first chain's test bears the test's place. -/
theorem placeL_of_four (N : H2U.Places4) : (AtProof.fourOf N).L.place = AtProof.placeL :=
  AtProof.p12At_place _ _

/-- **The same at the seated side**: for the side that `testSide` seats in the chain's own list for
a job at the planner's record for the first chain's test: that it stands at the test's place is no
premise any more. -/
theorem atHandL_at_seat {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (Js : SimJob Pb) (fs : List (Fall S))
    (hσ : testSide cF.blocksInOrder J Js fs = some σ) (hp : J.p = (AtProof.fourOf Np).L) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs more : List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∃ T : T12, enterFinish s = .ok T ∧
      ∀ (start : Local W₀ Rc ProofFile.Inst Tr → S) (fr : Front Y),
        start m.st.input =
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x) →
        fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        atHandL cF.blocksInOrder start σ.block.place m.st.input fr = true ∧
        doorTryL cF.blocksInOrder start σ.block.place m.st.input fr = .ok (wipeT T) ∧
        ∀ fall : T12, Agree (doorL cF.blocksInOrder start σ.block.place fall m.st.input fr) T :=
  atHandL_at_head h hR σ u pre t i St hrun hc
    ((testSide_place hσ).trans (hp ▸ placeL_of_four Np))

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.enters_of_finishPlace
#print axioms ProofFile.Honest.K12.Blind.enters_behind_finish
#print axioms ProofFile.Honest.K12.Blind.enters_of_fold
#print axioms ProofFile.Honest.K12.Blind.atHandL_at_head
#print axioms ProofFile.Honest.K12.Blind.testSide_place
#print axioms ProofFile.Honest.K12.Blind.placeL_of_four
#print axioms ProofFile.Honest.K12.Blind.atHandL_at_seat
