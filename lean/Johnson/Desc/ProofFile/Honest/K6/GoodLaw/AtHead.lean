-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/AtHead.lean: THE INVARIANT `K6GoodAt`
(Honest/K6/GoodLaw/Runs.lean) OF THE SUB-PROTOCOL "THE OUTPUT HEAD's OWN ROUNDS" (K6) STANDS BEHIND
ITS MEMBER's ACCEPTING STEP: AT THE MEMBER AS THE IOP AS WRITTEN IN LEAN SEATS IT, AND, FROM THE
SILENCE OF THE MARK `goodK6Mark` (Honest/K6/GoodMark.lean), AT THE FIRST CHAIN's THREAD AT THE
LIBRARY's OWN LETTERS (`lettersHead`, Honest/Thread/FirstHead.lean). CONDITIONAL. Three lemmas, by
calls. None of the library's goals. Whose: part 4's.

WHAT IT IS NOT. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, as h. (The library has a member
of that hypothesis, `P5J.AtMgA`, under four premises on the three public files:
`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) That the
thread holds at any run is shown nowhere. hLook IS A PREMISE: every slot that the form in which the
lookup's key side ended names lies below the ledger's next slot in front of the member: the lookup's
side's debt. THE INVARIANT IS SHOWN AT THE STATE RIGHT BEHIND THE MEMBER, AND AT NO LATER STATE:
five members stand between it and the gathering of the claims. NO MEASURE STANDS IN THIS FILE: how
often the mark speaks is not said here. NOTHING OF Said IS SPENT.

  `good_at_member`  `k6_border_good` with the seat's tests and the makers' guards around the
                    sub-protocol: no frame, no thread
  `good_bare`       the two tests on the samples read sampled elements alone: striking the sealed
                    digests turns neither
  `good_at_head`    **where the mark is silent at the member's own challenges, the invariant holds
                    behind the member's step, wherever the thread stands at border 341**: under the
                    one hypothesis h and one premise on the state behind (hLook)

WHO PAYS WHAT. The member's form and number: `k6_member_at_mg`
(Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean); its step taken apart: `K6MemberIs.step_iff`, `.bare`,
`.rounds` (Law/K6WayUp.lean); `k6On_of_start` (Law/K6OrdLeft.lean) with `alone_planOk`
(Johnson/IMR/SeatForm.lean); its test on the plan: `flat_ok` (Johnson/P5J/FoldJ1.lean); what is left
of the state in front: `headFrontItems_of_thr`, `headLink_at` (Honest/K6/Law/FrontAt.lean),
`K6FrontItems.k6Left` (Johnson/Desc/K6/Honest/Law/FrontItems.lean); the driver's guard on the reply:
`same_of_eq` (Johnson/P4SR/K6BackAtSeat.lean); canonical writing: `steps_decl`, `okViewW_nil`,
`yields_drawn` (Honest/Law/Run.lean), `play_yields`, `drawsFit_bare`, `okViewW_of_yields`
(Honest/Law/Play.lean), `canonical_of_okViewW` (Law/K6Frame.lean); the tests: `good_of_silent`
(Honest/K6/GoodSilent.lean), `goodK6_iff`, `goodK6Nz_iff` (Honest/K6/GoodRounds.lean); the border:
`k6_border_good` (Honest/K6/GoodLaw/Runs.lean). Over files that have not yet landed in the library:
these of Honest/, Johnson/Desc/K6/Honest/Law/FrontItems.lean, Law/K6WayUp.lean,
Law/K6WayUpAtSeat.lean, and what they import.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Runs
import Johnson.Desc.ProofFile.Honest.K6.GoodMark
import Johnson.Desc.ProofFile.Honest.K6.GoodSilent
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontAt
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.Desc.Kinds.Law.K6OrdLeft
import Johnson.Desc.Kinds.Law.K6Frame
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.P5J.FoldJ1
import Johnson.Desc.ProofFile.Honest.Law.Run
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K6.GoodLaw
open VerifiableInference.Desc (Block Chain Claim OpenedColumn Place Strs noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (parOf seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (K6MemberIs K6Left Canonical SlotsIn workOf)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- **THE INVARIANT BEHIND AN ACCEPTING STEP OF THE MEMBER AS THE IOP AS WRITTEN IN LEAN SEATS IT**:
`k6_border_good` with the seat's tests and the makers' guards around the sub-protocol. The step is
the plain one, with rounds in canonical writing (hcan). hLook: the lookup's side's debt, as there.
No frame, no thread. -/
theorem good_at_member {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool}
    {a : Place} {blk : Block S Claim} (M : K6MemberIs W l same a blk)
    (hk : a.kind ≠ VerifiableInference.Desc.KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (hp : blk.planOk = true)
    {ft n : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hstep : blk.step ft s rs cols = .ok (s', n)) (hcan : Canonical rs) (hL : K6Left W s)
    (gd : goodK6 (parOf W.hS (workOf W)) ((rs.map noDigest).map (·.drawn)) = true)
    (nz : goodK6Nz (parOf W.hS (workOf W)) ((rs.map noDigest).map (·.drawn)) = true)
    (hLook : ∀ gl, s'.lookHeard? = some gl →
      SlotsIn 0 ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next gl.cEnd) :
    K6GoodAt W.hS (Head.Law.readsOf W) (parOf W.hS (workOf W))
      ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next
      (((seatAt W.hS (Head.Law.readsOf W)).ledger s).next + headWindow (parOf W.hS (workOf W)))
      s' := by
  obtain ⟨hbare, hstart⟩ := (M.step_iff hk hsm ft s s' rs cols n).1 hstep
  have hOn : VerifiableInference.Desc.Kinds.Head.Law.K6On W s := by
    obtain ⟨ms, bS, name, hS, hla⟩ := M
    exact VerifiableInference.Desc.Kinds.Head.Law.k6On_of_start hS
      ((IM.alone_planOk hla).symm.trans hp) hstart hL
  exact k6_border_good W l _ M.bare ft s rs cols s' n hOn hcan hbare gd nz hLook

/-- The two tests read sampled elements alone: striking the sealed digests turns neither. -/
theorem good_bare (p : VerifiableInference.Desc.Kinds.Head.Par) (ds : List Fmt.Drawn) :
    goodK6 p (ds.map bare) = goodK6 p ds ∧ goodK6Nz p (ds.map bare) = goodK6Nz p ds := by
  have e : ∀ r, elemOf (ds.map bare) r = elemOf ds r := by
    intro r
    unfold elemOf
    rw [List.getElem?_map]
    cases ds[r]? <;> rfl
  constructor
  · apply Bool.eq_iff_iff.2
    rw [goodK6_iff, goodK6_iff]
    simp only [e]
  · apply Bool.eq_iff_iff.2
    rw [goodK6Nz_iff, goodK6Nz_iff]
    simp only [e]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **FROM THE MARK's SILENCE TO THE INVARIANT BEHIND THE MEMBER's STEP, AT THE FIRST CHAIN's THREAD
AT THE LIBRARY's OWN LETTERS**: under the one hypothesis h, at every Said (nothing of it is spent),
at every place a and every list fr of challenges in front (the mark reads neither). hLook: the
lookup's side's debt, as in `k6_border_good`. -/
theorem good_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (a : Place)
    (fr : List Fmt.Drawn) :
    ∀ blk k s m E ds y cols s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      ((goodK6Mark (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) a).test fr ds).isSome = false →
      (∀ gl, s'.lookHeard? = some gl → SlotsIn 0
        ((seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).ledger s).next gl.cEnd) →
      K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
        (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))
        ((seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).ledger s).next
        (((seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).ledger s).next +
          headWindow (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) s' := by
  intro blk k s m E ds y cols s' hblk hT hd hS hsil hLook
  obtain ⟨b, hb, M⟩ := P4.k6_member_at_mg h.toAtMg
  have hblk' : cF.blocksInOrder[341]? = some blk := hblk
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk')
  obtain ⟨hm, R⟩ := headFrontItems_of_thr
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) h.𝔇 rfl rfl rfl rfl hT.1
  have hL := R.k6Left (headLink_at h)
  obtain ⟨hM, hstep⟩ := hS
  unfold Thread.Moved at hM
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  have hdl : l.map (·.decl) = b.rounds := by
    rw [steps_decl hl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hY := play_yields _ _ _ _ _ hy
  have h1 := okViewW_of_yields _ _ _ _ hY (by rw [hdl]; exact drawsFit_bare _ _ hd) okViewW_nil
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ hY
  have hnd : ((roundsOf y.1).map noDigest).map (·.drawn) = ds.map bare := by
    rw [← hdr, List.map_map, List.map_map]
    rfl
  have hrounds : b.rounds = (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).rounds :=
    M.rounds.trans rfl
  rw [hrounds] at hd
  obtain ⟨-, g1, g2⟩ := good_of_silent _ a fr ds hd hsil
  exact good_at_member M (by decide) (fun _ _ e => P4.same_of_eq e)
    (P5J.flat_ok h.toAtMg b (List.mem_of_getElem? hb)) hstep
    (VerifiableInference.Desc.Kinds.Head.Law.Came.canonical_of_okViewW h1) hL
    (by rw [hnd, (good_bare _ _).1]; exact g1) (by rw [hnd, (good_bare _ _).2]; exact g2)
    hLook

#print axioms good_at_member
#print axioms good_bare
#print axioms good_at_head

end ProofFile.Honest.K6.GoodLaw
