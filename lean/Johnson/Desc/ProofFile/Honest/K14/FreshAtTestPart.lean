-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshAtTestPart.lean: kind K14: the label of the linear claim's
sub-protocols: "send o_u" (the owner ⟨sendPlace 2, 0⟩) AT THE PART p := ⟨⟨2, none, 9, .K12⟩, 0⟩, the
part 0 of the test on G_u: **AT A BOOK THAT HAS THE FOUR ENTRIES (MaskFourAt,
Honest/K14/BookAtU.lean) WHAT IS SPENT TO p IS JUST ONE ENTRY; AT THE FILES ITS NUMBERS ARE: FROM
COIN (0, 10808), (0, 15) COINS; WHAT IS KNOWN AT p IS JUST ONE ENTRY: o_u's WHOLE RUN, FROM (0, 0),
(0, 10808) COINS; AND, WHERE THE FRAME's MAKER onlineProverFromPublicFiles YIELDS A, UNDER THE LIBRARY's ONE HYPOTHESIS
AT THE FULL SIZE (P5J.AtMgA, Johnson/P5J/MgAtAll.lean; below: the head): AT A's BOOK AND ORDER OF
PLACES, AT EVERY SIDE OF THE SENDING's ROW, THE FIELD fresh's EQUATION AT THAT p.** Four theorems;
no definition. Short steps and calls; no evaluation at the files' sizes is new.

What it is not. THE OWNER's HALF ALONE: it is the field fresh of the frame's Good at the member of
the sending part at ⟨sendPlace 2, 0⟩; of the parts that carry these coins nothing is said. NOTHING
NEW IS SHOWN ON COINS: the equation is FreshMember's own text (Honest/Small/Field.lean) as the
theorems called here have it, taken at one part p; what is new is on the book alone: that at that p
just one entry is spent, with its numbers. THAT onlineProverFromPublicFiles YIELDS IS A PREMISE of the fourth theorem: it
is shown nowhere in this file: BY THIS FILE THAT STATEMENT MAY BE EMPTY. WHERE THE EQUATION SPEAKS:
its three premises are shown met TOGETHER at one written pair alone (the written challenges onesAt
and the written positions fullAsks, Honest/K14/MemberKit.lean: not positions that a run asks), at
every stand, and there what the part shows is "some ..." at all coins. The types are free: where one
is empty the clauses at a stand say nothing. THE bud IS A PREMISE of the equation, at the row's own
letter (budAt at the sending's parameters, Honest/K14/ExactRows.lean): beyond that one written pair
it is not said here where it is met. THAT A FILLING HAS SUCH A ROW IS NOT SHOWN: the side is that of
any row with letters over the book that has the sending's place, row, On and bud; that such a row
and a side are there, and that the side has a member, is said; the row that is shown to be there has
trivial sentences A and B. A book's number is a claim on a sender's text: what the part's text
spends is not read here. fresh is never to be read without what is known at p and the order of
places: both stand in the statement. The frame's test over a list of owners (ownersClearBy) is part
of no test here. The sort of the first mask's message is jobU's own text (Honest/K14/Sendings.lean):
the public test on shapes alone does not pin it. The challenges and the positions are letters in
front of the equation. One request. Stands that no run reaches are among those at which it speaks.
The full size alone; at the earlier hash. It holds of the frame's texts as they lie beneath this
file. All limits of the files named hold here. No property is claimed. Nothing on soundness,
completeness or hiding.
How. spent_of_four: MaskFourAt's equation of lists, a filter of a filter. uFigures_at_files:
uNumbers_written (Honest/K14/BookAtUHead.lean) carried by the library's sized_at and written_proof.
testPart_of_mask: these two and MaskAtBook's first and fourth clauses. fresh_u_at_test_part_head:
sendings_fresh_at_head (Honest/K14/FreshAtPure.lean) at jobU: out of it all clauses but those on the
book at p; maskAtBook_at_atPure (Honest/K14/BookAtUPure.lean); testPart_of_mask. "∀ p, p = ... →": p
is pinned by an equation. ⟨σ.block.place, u.number⟩ is left as FreshMember has it, and is said to be
⟨sendPlace 2, 0⟩ by the two equations in front.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain)
open Desc.K14 (St)
open VerifierAndGoals (InScope)
open P5J (LaidAt TS)
open AtPublicFiles.TreeReads (sized_at written_proof)

-- An instance of the library (Cb/Obj/LdObjectReqStd.lean) is offered to every search for
-- Nonempty and sends it after a field that nothing determines; it is struck inside this
-- namespace, in this file (as in FreshAtPure.lean).
attribute [-instance] Cb.instNonemptyPGD

/-- **Out of the four entries: what is spent to p is one entry**, with its four fields. -/
theorem spent_of_four {B : ProverCoinCounts} {p q : Addr} {k first len : Nat}
    (h : MaskFourAt B.ahead p q k first len) :
    ∃ e₁, B.spentBy { place := sendPlace 2, part := 0 } p = [e₁] ∧ e₁.once = true ∧
      e₁.spender = p ∧ e₁.start = ⟨0, first⟩ ∧ e₁.count = ⟨0, 2 * k + 1⟩ := by
  obtain ⟨e₁, x₁, x₂, x₃, hf, ⟨a1, a2, a3, a4⟩, ⟨b1, -⟩, ⟨c1, -⟩, ⟨d1, -⟩⟩ := h
  refine ⟨e₁, ?_, a1, a2, a3, a4⟩
  have e : B.spentBy { place := sendPlace 2, part := 0 } p =
      (B.ahead.filter (fun e => e.owner == ({ place := sendPlace 2, part := 0 } : Addr))).filter
        (fun e => e.spender == p && e.once) := by
    unfold ProverCoinCounts.spentBy
    rw [List.filter_filter]
    congr 1
    funext e
    simp only [Bool.and_assoc, Bool.and_comm]
  rw [e, hf]
  simp [List.filter, a1, a2, b1, c1, d1]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The numbers at the files**: the fold has seven variables; o_u's run has 10,808 coins. -/
theorem uFigures_at_files (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (a : Nat) :
    maskRounds ⟨qAt Zp Np, a⟩ = 7 ∧ maskFirstCoin ⟨qAt Zp Np, a⟩ = 10808 := by
  constructor
  · show ((Zp.p.chains.made.sized.proof.batch.shape).testU.head?.map (·.k)).getD 0 = 7
    rw [sized_at scope L, written_proof]
    exact uNumbers_written.2.1
  · have e : (jobU ⟨qAt Zp Np, a⟩).Q.sent = (Desc.K14.withU (qAt Zp Np).S).getD #[] :=
      Desc.K14.Law.parK1_sent _ _ _ _
    unfold maskFirstCoin
    rw [e]
    show offsetOf Zp.p.chains.made.sized.proof.codes
      ((Desc.K14.withU Zp.p.chains.made.sized.proof.batch.shape).getD #[])
      (uSortOf Zp.p.chains.made.sized.proof.batch.shape) 1 = 10808
    rw [sized_at scope L, written_proof]
    exact uNumbers_written.2.2.1

/-- **The book's half at the test's part 0, the numbers written out**: at whatever book has
MaskAtBook there. -/
theorem testPart_of_mask (scope : InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {a : Nat} {B : ProverCoinCounts}
    {ord : List Place} {q : Addr}
    (h : MaskAtBook ⟨qAt Zp Np, a⟩ B ord
      { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 } q) :
    (∃ e₁, B.spentBy { place := sendPlace 2, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 } = [e₁] ∧
      e₁.once = true ∧
      e₁.spender = { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 } ∧
      e₁.start = ⟨0, 10808⟩ ∧ e₁.count = ⟨0, 15⟩) ∧
    ∃ x, B.knownBy ord { place := sendPlace 2, part := 0 }
        { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 } = [x] ∧
      x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, 10808⟩ := by
  obtain ⟨h4, -, -, ⟨x, hx, x1, x2⟩, -⟩ := h
  obtain ⟨e₁, he, a1, a2, a3, a4⟩ := spent_of_four h4
  obtain ⟨f1, f2⟩ := uFigures_at_files scope L a
  rw [f2] at a3 x2
  rw [f1] at a4
  exact ⟨⟨e₁, he, a1, a2, a3, a4⟩, x, hx, x1, x2⟩

/-- **WHERE onlineProverFromPublicFiles YIELDS A, UNDER THE HEAD: A's DESCRIPTION IS THE HEAD's; AT A's BOOK AND ORDER,
AT THE ROW OF "send o_u": THE ROW IS THERE; A ROW WITH LETTERS IS THERE; A STAND IS THERE WHERE THE
TYPES ARE INHABITED; AT EVERY SUCH ROW A SIDE IS THERE; EVERY SIDE HAS A MEMBER; AT EVERY MEMBER AND
STAND fresh's THREE PREMISES HOLD TOGETHER AT ONE WRITTEN PAIR, AND THE PART SHOWS "some ..." THERE
AT ALL COINS; AND AT THE TEST's PART 0: ONE ENTRY IS SPENT, ONE IS KNOWN, WITH THEIR NUMBERS, AND
fresh's EQUATION HOLDS UNDER ITS THREE PREMISES.** The owner's half alone. That onlineProverFromPublicFiles yields is a
premise: the statement may be empty. No property is claimed. -/
theorem fresh_u_at_test_part_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∀ (V₀ Vc Tr Y₀ Y : Type) (P : OnlineProverParts V₀ Vc Tr Y₀ Y) (A : OnlineProverWithDescription V₀ Vc Tr Y₀ Y),
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A →
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧
      ∀ (W₀ Rc Ky X₀ : Type) (weights : W₀ → Weights) (rand : Rc → TableRand),
        (∃ r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky,
          r ∈ sendingRows ⟨qAt Zp Np, 0⟩ weights rand ∧ r.place = sendPlace 2) ∧
        ∀ r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky,
        r ∈ sendingRows ⟨qAt Zp Np, 0⟩ weights rand → r.place = sendPlace 2 →
        (∃ L : Lettered A.B St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky,
          L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) ∧
        (∀ (i : Common W₀ Rc Ky) (y : X₀),
          ∃ m : Mid (Common W₀ Rc Ky) X₀, m.st.input = i ∧ m.st.own = y) ∧
        ∀ L : Lettered A.B St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky,
        L.place = r.place → L.row = r.row → L.On = r.On → L.bud = r.bud →
        (∀ fs : List (Fall St),
          ∃ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder fs = some σ) ∧
        ∀ (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky),
        L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder fs = some σ →
        σ.members ≠ [] ∧
        (∀ u ∈ σ.members, ∀ (sp : CsAll u.part.spends) (ca : CsAll u.part.carries)
          (m : Mid (Common W₀ Rc Ky) X₀),
          drawsFit (u.rounds.map (·.1)) (onesAt (jobU ⟨qAt Zp Np, 0⟩).Q) = true ∧
          L.bud u.number (onesAt (jobU ⟨qAt Zp Np, 0⟩).Q) (fullAsks r.place) ∧
          u.part.stopAt (Face.shared.sees m.st.input) m.loc (onesAt (jobU ⟨qAt Zp Np, 0⟩).Q) ≠
            some .hid ∧
          ∀ c : Cs u.part.takes, ∃ y, σ.shows .shared u (c, sp, ca) m
            (onesAt (jobU ⟨qAt Zp Np, 0⟩).Q) (fullAsks r.place) = some y) ∧
        ∀ u ∈ σ.members, ∀ p : Addr,
        p = { place := { chain := 2, link := none, piece := 9, kind := .K12 }, part := 0 } →
        σ.block.place = sendPlace 2 ∧ u.number = 0 ∧
        (∃ e₁, A.B.spentBy ⟨σ.block.place, u.number⟩ p = [e₁] ∧ e₁.once = true ∧ e₁.spender = p ∧
          e₁.start = ⟨0, 10808⟩ ∧ e₁.count = ⟨0, 15⟩) ∧
        (∃ x, A.B.knownBy (orderOf A.F) ⟨σ.block.place, u.number⟩ p = [x] ∧
          x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, 10808⟩) ∧
        ∀ (sp : CsAll u.part.spends) (ca : CsAll u.part.carries) (m : Mid (Common W₀ Rc Ky) X₀)
          (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
          drawsFit (u.rounds.map (·.1)) ds = true → L.bud u.number ds asks →
          u.part.stopAt (Face.shared.sees m.st.input) m.loc ds ≠ some .hid →
          (Prob.unif (Cs u.part.takes)).map (fun c =>
              (cutAll c (A.B.spentBy ⟨σ.block.place, u.number⟩ p),
                σ.shows .shared u (c, sp, ca) m ds asks,
                cutAll c (A.B.knownBy (orderOf A.F) ⟨σ.block.place, u.number⟩ p))) =
            (Prob.unif (CsAll ((A.B.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
                Cs u.part.takes)).map fun a =>
              (some a.1, σ.shows .shared u (a.2, sp, ca) m ds asks,
                cutAll a.2 (A.B.knownBy (orderOf A.F) ⟨σ.block.place, u.number⟩ p)) := by
  intro V₀ Vc Tr Y₀ Y P A hA
  obtain ⟨hF, rest⟩ := sendings_fresh_at_head h V₀ Vc Tr Y₀ Y P A hA
  refine ⟨hF, ?_⟩
  intro W₀ Rc Ky X₀ weights rand
  refine ⟨⟨_, List.mem_cons_self, rfl⟩, ?_⟩
  intro r hr hp
  obtain ⟨hL, -, hst, big⟩ :=
    rest W₀ Rc Ky X₀ weights rand r hr (jobU ⟨qAt Zp Np, 0⟩) (Or.inl ⟨hp, rfl⟩)
  refine ⟨hL, hst, ?_⟩
  intro L l1 l2 l3 l4
  obtain ⟨hσ', big⟩ := big L l1 l2 l3 l4
  refine ⟨hσ', ?_⟩
  intro fs σ hσ
  obtain ⟨-, hne, s1, s2, -, fr, mem⟩ := big fs σ hσ
  refine ⟨hne, ?_, ?_⟩
  · intro u hu sp ca m
    obtain ⟨_, -, -, hh⟩ := mem u hu
    exact ⟨(hh sp ca m).1, (hh sp ca m).2.1, (hh sp ca m).2.2.1, (hh sp ca m).2.2.2.1⟩
  intro u hu p hp0
  have e1 : σ.block.place = sendPlace 2 := s1.trans hp
  have e2 : u.number = 0 := s2 u hu
  obtain ⟨t1, t2⟩ :=
    testPart_of_mask h.scope h.laid (maskAtBook_at_atPure h.scope h.laid 0 hA).2.2
  refine ⟨e1, e2, ?_, ?_, ?_⟩
  · rw [e1, e2, hp0]; exact t1
  · rw [e1, e2, hp0]; exact t2
  · intro sp ca m ds asks g1 g2 g3
    exact fr u hu p sp ca m ds asks g1 g2 g3

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.spent_of_four
#print axioms ProofFile.Honest.K14.uFigures_at_files
#print axioms ProofFile.Honest.K14.testPart_of_mask
#print axioms ProofFile.Honest.K14.fresh_u_at_test_part_head
