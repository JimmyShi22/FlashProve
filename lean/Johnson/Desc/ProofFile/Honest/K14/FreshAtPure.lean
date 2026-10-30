-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshAtPure.lean: kind K14: UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean), WHERE THE FRAME's MAKER onlineProverFromPublicFiles (Honest/AtPure.lean) YIELDS A: AT A's OWN
BOOK AND A's OWN ORDER OF PLACES, AT THE ROWS OF BOTH SENDINGS OF THE SHARED CHAIN, ExactMember
(Honest/Small/Field.lean: THE TEXT OF THE FIELD exact OF THE FRAME's RECORD Good WITHOUT ITS PREMISE
ON opened) AND THE FIELD fresh BOTH HOLD, WITH NO PREMISE ON A TEST LEFT, AND fresh IS NOT MET FOR
NOTHING. The field exact in its own form (ExactMemberAt pre) follows at every pre by
exactAt_of_exact (the same file): a step that this file does not take. With the step by which that
is had, general in the book and the order. Statements with their proofs. No definition.

ONE PREMISE STAYS BESIDE THE HEAD: THAT onlineProverFromPublicFiles YIELDS, at any file, at any filling: NOT SHOWN HERE:
BY THIS FILE THE STATEMENT MAY BE EMPTY. (That it yields at one filling, under the library's head, a
public test on the files and the premise that bookWhole returns at the written description:
atPure_returns_fullIn_of_written, Honest/K5/Law/ReturnsFromWritten.lean; with the last premise met
in the side library: atPure_returns_fullIn_closed, AtFullSide/K5/ReturnsClosed.lean, with that
file's limits.)

  spentBy_of_whole   where wholeOrSpent (Honest/K14/OwnerWholeTest.lean) accepts a book at an owner:
                  an entry spends of the owner's coins (that it is the only one is not said); its
                  start and count are those that the test names; it stands in ProverCoinCounts.spentBy at the
                  owner and its own spender
  freshMember_at  the member for the field fresh at one member (FreshMember,
                  Honest/Small/Field.lean), AT LETTERS: UNDER the test on the job's shapes (hfit),
                  that the row is a sending's part, the side's declared rounds (hr, hd), the bound
                  at fullAsks at every number and all challenges (hbud), AN ENTRY WITH A COIN BY
                  WHICH SOME PART SPENDS OF THE OWNER's COINS (hsp: a premise here, handed through),
                  and the field fresh itself (hF): at that spender p, at EVERY stand: drawsFit, the
                  bound, no second stop (the field's three premises, in its order); "some ..." at
                  all coins (shows_tie_two, Honest/K14/MaskTie.lean, which asks nothing of what the
                  stand has heard); and the field's equation at p. GENERAL IN THE JOB J; AND hfit
                  ALONE DOES NOT PIN THAT A FRESH TABLE IS LAID AS FRESH: a job that lays the mask's
                  message by the sort "plain" passes that test. At the kind's two jobs (jobU,
                  jobOmega: Honest/K14/Sendings.lean) the sort is written, not chosen. Whoever
                  quotes this statement at a job names beside it the job's own text, or that its
                  sorts name a fresh table just where the frame's maker does
  sendings_fresh_of_tests   THE STEP, general in the book and the order: under the head, at every
                  book Bk and order ord at which the two short tests (maskWholeB,
                  Honest/K14/MaskWholeTest.lean; spWholeB, Honest/K14/OwnerWholeTest.lean) and the
                  two owners' tests (maskOwner, spOwner) accept, at Bk and ord, at each row of the
                  two sendings: a row with letters (one with trivial sentences A and B) is there,
                  and a stand where the types are inhabited; at every such row a side; at every side
                  fits, a member, ExactMember and fresh; and the member for fresh. All premises of
                  freshMember_at are met inside its proof, from the head and the four tests
  sendings_fresh_at_head   **the statement of the title**: the step at A's book and order, where the
                  four tests accept by maskAtBook_at_atPure (Honest/K14/BookAtUPure.lean) and
                  spOwner_ok_at_atPure (Honest/K14/BookAtPure.lean)

Of the letters sp, ca and m of the field fresh, m alone ranges here: a sending's part spends and
carries no run, so sp and ca are of one-point types.

What is not claimed. That onlineProverFromPublicFiles yields. That any book passes the four tests. All that the heads of
Honest/K14/SendingRowsStated.lean and Honest/K14/SendingRowsLaw.lean say is not claimed or is left.
Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.MemberKit
import Johnson.Desc.ProofFile.Honest.K14.MaskTie
import Johnson.Desc.ProofFile.Honest.K14.OwnerWholeTest
import Johnson.Desc.ProofFile.Honest.K14.BookAtUPure
import Johnson.Desc.ProofFile.Honest.K14.RowsAtShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain)
open OnBytes.SendSim.At (budAt)
open Desc.K14 (St)
open ProofFile.Honest.Small (ExactMember FreshMember)

-- An instance of the library (Cb/Obj/LdObjectReqStd.lean) is offered to every search for
-- Nonempty and sends it after a field that nothing determines; it is struck inside this
-- namespace, in this file.
attribute [-instance] Cb.instNonemptyPGD

/-- **Where the short test on a book accepts at an owner, an entry spends of the owner's coins, and
it is the run that the test names**: it stands in ProverCoinCounts.spentBy at the owner and its own spender. -/
theorem spentBy_of_whole (st ct : Due) (ms : List (Due × Due)) (B : ProverCoinCounts) (o : Addr)
    (h : wholeOrSpent st ct ms B o = true) :
    ∃ e, e ∈ B.spentBy o e.spender ∧ e.start = st ∧ e.count = ct := by
  unfold wholeOrSpent at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  match hs : spendersOf B o, h1 with
  | [e], h1 =>
    rw [Bool.and_eq_true] at h1
    have he : e ∈ spendersOf B o := by
      rw [hs]
      exact List.mem_singleton.2 rfl
    unfold spendersOf at he
    obtain ⟨ha, hb⟩ := List.mem_filter.1 he
    rw [Bool.and_eq_true] at hb
    refine ⟨e, ?_, eq_of_beq h1.1, eq_of_beq h1.2⟩
    unfold ProverCoinCounts.spentBy
    refine List.mem_filter.2 ⟨ha, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hb.2, beq_self_eq_true _⟩, hb.1⟩

section letters
variable {S Cl X₀ W₀ Rc Ky : Type}

/-- **The member for the field fresh at one side whose row is a sending's part**: at letters: under
the test on the job's shapes, the side's declared rounds, the bound at fullAsks at every number and
all challenges, an entry with a coin by which some part spends of the owner's coins, and the field
fresh itself. General in the job: what the test on the shapes does not pin: see the head. -/
theorem freshMember_at (J : SendJob) (hfit : sendShapeFits J = true)
    (wit : Common W₀ Rc Ky → Ask) (σ : Side S Cl Empty (Common W₀ Rc Ky) X₀ Ky) (sim : Sim Ky)
    (hrow : σ.row = [(liftSend wit (sendingPart J), sim)])
    (hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds J.Q) (hd : SendDeclared σ.block J)
    (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (pl : Place)
    (hbud : ∀ j ds, bud j ds (fullAsks pl))
    (hsp : ∃ p, ∃ e ∈ Bk.spentBy ⟨σ.block.place, 0⟩ p, 0 < e.count.e)
    (hF : ∀ u ∈ σ.members, FreshMember .shared σ Bk ord bud u) :
    ∀ u ∈ σ.members, ∃ p : Addr, Bk.spentBy ⟨σ.block.place, u.number⟩ p ≠ [] ∧
      (∃ e ∈ Bk.spentBy ⟨σ.block.place, u.number⟩ p, 0 < e.count.e) ∧
      ∀ (sp : CsAll u.part.spends) (ca : CsAll u.part.carries) (m : Mid (Common W₀ Rc Ky) X₀),
      drawsFit (u.rounds.map (·.1)) (onesAt J.Q) = true ∧
      bud u.number (onesAt J.Q) (fullAsks pl) ∧
      u.part.stopAt (Face.shared.sees m.st.input) m.loc (onesAt J.Q) ≠ some .hid ∧
      (∀ c : Cs u.part.takes,
        ∃ y, σ.shows .shared u (c, sp, ca) m (onesAt J.Q) (fullAsks pl) = some y) ∧
      (Prob.unif (Cs u.part.takes)).map (fun c =>
          (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p),
            σ.shows .shared u (c, sp, ca) m (onesAt J.Q) (fullAsks pl),
            cutAll c (Bk.knownBy (ord) ⟨σ.block.place, u.number⟩ p))) =
        (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
            Cs u.part.takes)).map fun a =>
          (some a.1, σ.shows .shared u (a.2, sp, ca) m (onesAt J.Q) (fullAsks pl),
            cutAll a.2 (Bk.knownBy (ord) ⟨σ.block.place, u.number⟩ p)) := by
  intro u hu
  have hF' := hF u hu
  have hu' : u = sendingMember σ J wit sim := by
    rw [members_send σ _ sim hrow] at hu
    exact List.mem_singleton.1 hu
  subst hu'
  obtain ⟨p, e, he, hc⟩ := hsp
  refine ⟨p, List.ne_nil_of_mem he, ⟨e, he, hc⟩, fun sp ca m => ?_⟩
  have k1 : drawsFit ((sendingMember σ J wit sim).rounds.map (·.1)) (onesAt J.Q) = true := by
    rw [sendingMember_rounds σ J wit sim hr hd]
    exact onesAt_fits J.Q
  have hb : bud (sendingMember σ J wit sim).number (onesAt J.Q) (fullAsks pl) := hbud _ _
  have k3 : (sendingMember σ J wit sim).part.stopAt (Face.shared.sees m.st.input) m.loc
      (onesAt J.Q) ≠ some .hid := stop_send J wit _ _ _
  refine ⟨k1, hb, k3, fun c => ⟨_, shows_tie_two J hfit wit .shared σ sim hd m _ _ _ c⟩, ?_⟩
  exact hF' p sp ca m (onesAt J.Q) (fullAsks pl) k1 hb k3

end letters

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Under the library's head, at every book and order at which the two short tests and the two
owners' tests accept: at each row of the two sendings: a row with letters (one with trivial
sentences A and B) is there, and a stand where the types are inhabited; at every such row a side is
there; at every side: fits, a member, ExactMember, fresh; and the member for fresh.** General in the
book and the order. -/
theorem sendings_fresh_of_tests (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) (Bk : ProverCoinCounts)
    (ord : List Place) (wU : maskWholeB ⟨qAt Zp Np, 0⟩ Bk = true)
    (okU : (maskOwner ⟨qAt Zp Np, 0⟩).ok Bk ord { place := sendPlace 2, part := 0 } = true)
    (wO : spWholeB ⟨qAt Zp Np, 0⟩ Bk = true)
    (okO : (spOwner ⟨qAt Zp Np, 0⟩).ok Bk ord { place := sendPlace 5, part := 0 } = true) :
    ∀ (W₀ Rc Ky X₀ : Type) (weights : W₀ → Weights) (rand : Rc → TableRand)
      (r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky),
      r ∈ sendingRows ⟨qAt Zp Np, 0⟩ weights rand →
      ∀ J : SendJob,
      (r.place = sendPlace 2 ∧ J = jobU ⟨qAt Zp Np, 0⟩ ∨
        r.place = sendPlace 5 ∧ J = jobOmega ⟨qAt Zp Np, 0⟩) →
      (∃ L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky,
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) ∧
      (∀ (T : Common W₀ Rc Ky → Thread Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
        (Sd : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop),
        (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).place = r.place ∧
        (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).row = r.row ∧
        (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).On = r.On ∧
        (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).bud = r.bud) ∧
      (∀ (i : Common W₀ Rc Ky) (y : X₀),
        ∃ m : Mid (Common W₀ Rc Ky) X₀, m.st.input = i ∧ m.st.own = y) ∧
      ∀ L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky,
      L.place = r.place → L.row = r.row → L.On = r.On → L.bud = r.bud →
      (∀ fs : List (Fall St),
        ∃ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder fs = some σ) ∧
      ∀ (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky),
      L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder fs = some σ →
      σ.fits = true ∧ σ.members ≠ [] ∧
      σ.block.place = r.place ∧ (∀ u ∈ σ.members, u.number = 0) ∧
      (∀ u ∈ σ.members, ExactMember .shared σ 1 0 L.On L.bud u) ∧
      (∀ u ∈ σ.members, FreshMember .shared σ Bk (ord) L.bud u) ∧
      ∀ u ∈ σ.members, ∃ p : Addr, Bk.spentBy ⟨σ.block.place, u.number⟩ p ≠ [] ∧
        (∃ e ∈ Bk.spentBy ⟨σ.block.place, u.number⟩ p, 0 < e.count.e) ∧
        ∀ (sp : CsAll u.part.spends) (ca : CsAll u.part.carries) (m : Mid (Common W₀ Rc Ky) X₀),
        drawsFit (u.rounds.map (·.1)) (onesAt J.Q) = true ∧
        L.bud u.number (onesAt J.Q) (fullAsks r.place) ∧
        u.part.stopAt (Face.shared.sees m.st.input) m.loc (onesAt J.Q) ≠ some .hid ∧
        (∀ c : Cs u.part.takes,
          ∃ y, σ.shows .shared u (c, sp, ca) m (onesAt J.Q) (fullAsks r.place) = some y) ∧
        (Prob.unif (Cs u.part.takes)).map (fun c =>
            (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p),
              σ.shows .shared u (c, sp, ca) m (onesAt J.Q) (fullAsks r.place),
              cutAll c (Bk.knownBy (ord) ⟨σ.block.place, u.number⟩ p))) =
          (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
              Cs u.part.takes)).map fun a =>
            (some a.1, σ.shows .shared u (a.2, sp, ca) m (onesAt J.Q) (fullAsks r.place),
              cutAll a.2 (Bk.knownBy (ord) ⟨σ.block.place, u.number⟩ p)) := by
  have hfit := (sendings_at_head h).1
  refine fun W₀ Rc Ky X₀ weights rand r hr J hJ =>
    ⟨⟨⟨r.place, r.row, fun _ _ _ _ => True, fun _ _ _ _ => True, r.On, r.bud⟩, rfl, rfl, rfl, rfl⟩,
      fun _ _ => ⟨rfl, rfl, rfl, rfl⟩,
      fun i y => ⟨⟨⟨i, [], y⟩, [], [], none⟩, rfl, rfl⟩,
      fun L c1 c2 c3 c4 => ⟨fun fs => ?_, fun fs σ hσ => ?_⟩⟩
  · obtain ⟨⟨σ₂, g2, -⟩, σ₅, g5, -⟩ := seated_declares_head (Cl := ProofFile.Cl) h 0 L.row fs
    unfold sendingRows at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨σ₂, by unfold Lettered.side; rw [c1]; exact g2⟩
    · exact ⟨σ₅, by unfold Lettered.side; rw [c1]; exact g5⟩
  have hσ' : Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs =
      some σ := by
    rw [← c1, ← c2]
    exact hσ
  obtain ⟨f1, f2, f3⟩ :=
    (rowsServe_at_shared h X₀ W₀ Rc Ky weights rand fs Bk ord r hr).2 σ hσ'
  have fr := f3 okU okO
  rw [c3, c4]
  unfold sendingRows at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain rfl : J = jobU ⟨qAt Zp Np, 0⟩ := by
      rcases hJ with ⟨-, e⟩ | ⟨e, -⟩
      · exact e
      · exact absurd (show sendPlace 2 = sendPlace 5 from e) (by decide)
    obtain ⟨⟨σ₀, h0, -, hpl, hrd, hdc⟩, -⟩ :=
      seated_declares_head (Cl := ProofFile.Cl) h 0 L.row fs
    obtain rfl : σ₀ = σ := Option.some.inj (h0.symm.trans (by
      have hσ2 := hσ
      unfold Lettered.side at hσ2
      rw [c1] at hσ2
      exact hσ2))
    have hrow := (side_ok hσ).2.2.trans c2
    refine ⟨f1, ?_, hpl, ?_, f2, fr, ?_⟩
    · rw [members_send σ₀ _ _ hrow]
      exact List.cons_ne_nil _ _
    · intro u hu
      rw [members_send σ₀ _ _ hrow] at hu
      rw [List.mem_singleton.1 hu]
    · refine freshMember_at (jobU ⟨qAt Zp Np, 0⟩) (fit_u _ hfit) _ σ₀ _ hrow hrd hdc Bk
        ord _ (sendPlace 2) (fun _ _ => (full_u_at_files h.scope h.laid 0).1) ?_ fr
      rw [hpl]
      obtain ⟨e, he, -, hc⟩ := spentBy_of_whole _ _ _ Bk _ wU
      exact ⟨e.spender, e, he, by rw [hc]; exact Nat.succ_pos _⟩
  · obtain rfl : J = jobOmega ⟨qAt Zp Np, 0⟩ := by
      rcases hJ with ⟨e, -⟩ | ⟨-, e⟩
      · exact absurd (show sendPlace 5 = sendPlace 2 from e) (by decide)
      · exact e
    obtain ⟨-, σ₀, h0, -, hpl, hrd, hdc⟩ :=
      seated_declares_head (Cl := ProofFile.Cl) h 0 L.row fs
    obtain rfl : σ₀ = σ := Option.some.inj (h0.symm.trans (by
      have hσ2 := hσ
      unfold Lettered.side at hσ2
      rw [c1] at hσ2
      exact hσ2))
    have hrow := (side_ok hσ).2.2.trans c2
    refine ⟨f1, ?_, hpl, ?_, f2, fr, ?_⟩
    · rw [members_send σ₀ _ _ hrow]
      exact List.cons_ne_nil _ _
    · intro u hu
      rw [members_send σ₀ _ _ hrow] at hu
      rw [List.mem_singleton.1 hu]
    · refine freshMember_at (jobOmega ⟨qAt Zp Np, 0⟩) (fit_omega _ hfit) _ σ₀ _ hrow hrd hdc Bk
        ord _ (sendPlace 5) (fun _ _ => (full_omega_at_files h.scope h.laid 0).1) ?_ fr
      rw [hpl]
      obtain ⟨e, he, -, hc⟩ := spentBy_of_whole _ _ _ Bk _ wO
      exact ⟨e.spender, e, he, by rw [hc]; exact Nat.one_pos⟩

/-- **UNDER THE LIBRARY's HEAD, WHERE onlineProverFromPublicFiles YIELDS A: at A's own book and order of places, at each
row of the two sendings: a row with letters (one with trivial sentences A and B) is there, and a
stand where the types are inhabited; at every such row a side is there; at every side: fits, a
member, ExactMember, fresh with no premise on a test left; and the member for fresh.** ONE PREMISE
STAYS BESIDE THE HEAD: THAT onlineProverFromPublicFiles YIELDS: not shown here: by this file the statement may be empty
(see the head). -/
theorem sendings_fresh_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) :
    ∀ (V₀ Vc Tr Y₀ Y : Type) (P : OnlineProverParts V₀ Vc Tr Y₀ Y) (A : OnlineProverWithDescription V₀ Vc Tr Y₀ Y),
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A →
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧
      ∀ (W₀ Rc Ky X₀ : Type) (weights : W₀ → Weights) (rand : Rc → TableRand)
        (r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky),
        r ∈ sendingRows ⟨qAt Zp Np, 0⟩ weights rand →
        ∀ J : SendJob,
        (r.place = sendPlace 2 ∧ J = jobU ⟨qAt Zp Np, 0⟩ ∨
          r.place = sendPlace 5 ∧ J = jobOmega ⟨qAt Zp Np, 0⟩) →
        (∃ L : Lettered A.B St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky,
          L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) ∧
        (∀ (T : Common W₀ Rc Ky → Thread A.B St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
          (Sd : Common W₀ Rc Ky → Nat → Coins A.B → Mid (Common W₀ Rc Ky) X₀ → Prop),
          (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).place = r.place ∧
          (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).row = r.row ∧
          (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).On = r.On ∧
          (r.lay T Sd (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).bud = r.bud) ∧
        (∀ (i : Common W₀ Rc Ky) (y : X₀),
          ∃ m : Mid (Common W₀ Rc Ky) X₀, m.st.input = i ∧ m.st.own = y) ∧
        ∀ L : Lettered A.B St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky,
        L.place = r.place → L.row = r.row → L.On = r.On → L.bud = r.bud →
        (∀ fs : List (Fall St),
          ∃ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder fs = some σ) ∧
        ∀ (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky),
        L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder fs = some σ →
        σ.fits = true ∧ σ.members ≠ [] ∧
        σ.block.place = r.place ∧ (∀ u ∈ σ.members, u.number = 0) ∧
        (∀ u ∈ σ.members, ExactMember .shared σ 1 0 L.On L.bud u) ∧
        (∀ u ∈ σ.members, FreshMember .shared σ A.B (orderOf A.F) L.bud u) ∧
        ∀ u ∈ σ.members, ∃ p : Addr, A.B.spentBy ⟨σ.block.place, u.number⟩ p ≠ [] ∧
          (∃ e ∈ A.B.spentBy ⟨σ.block.place, u.number⟩ p, 0 < e.count.e) ∧
          ∀ (sp : CsAll u.part.spends) (ca : CsAll u.part.carries) (m : Mid (Common W₀ Rc Ky) X₀),
          drawsFit (u.rounds.map (·.1)) (onesAt J.Q) = true ∧
          L.bud u.number (onesAt J.Q) (fullAsks r.place) ∧
          u.part.stopAt (Face.shared.sees m.st.input) m.loc (onesAt J.Q) ≠ some .hid ∧
          (∀ c : Cs u.part.takes,
            ∃ y, σ.shows .shared u (c, sp, ca) m (onesAt J.Q) (fullAsks r.place) = some y) ∧
          (Prob.unif (Cs u.part.takes)).map (fun c =>
              (cutAll c (A.B.spentBy ⟨σ.block.place, u.number⟩ p),
                σ.shows .shared u (c, sp, ca) m (onesAt J.Q) (fullAsks r.place),
                cutAll c (A.B.knownBy (orderOf A.F) ⟨σ.block.place, u.number⟩ p))) =
            (Prob.unif (CsAll ((A.B.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
                Cs u.part.takes)).map fun a =>
              (some a.1, σ.shows .shared u (a.2, sp, ca) m (onesAt J.Q) (fullAsks r.place),
                cutAll a.2 (A.B.knownBy (orderOf A.F) ⟨σ.block.place, u.number⟩ p)) := by
  intro V₀ Vc Tr Y₀ Y P A hA
  obtain ⟨-, eF, -, wU, -, -, okU⟩ := maskAtBook_at_atPure h.scope h.laid 0 hA
  obtain ⟨-, -, wO, okO⟩ := spOwner_ok_at_atPure h.scope h.laid 0 hA
  exact ⟨eF, sendings_fresh_of_tests h A.B (orderOf A.F) wU okU wO okO⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.spentBy_of_whole
#print axioms ProofFile.Honest.K14.freshMember_at
#print axioms ProofFile.Honest.K14.sendings_fresh_of_tests
#print axioms ProofFile.Honest.K14.sendings_fresh_at_head
