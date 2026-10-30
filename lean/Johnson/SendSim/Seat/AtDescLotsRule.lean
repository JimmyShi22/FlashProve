-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescLotsRule.lean: wherever the maker returns (IM.Open), the four premises
that the frame's rule asks row by row hold at every row of the two lots of the kind K1, if two
public tests and the plan's own accept. It claims no property of the protocol: not hiding, not zero
knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The premises are IM.Open and F.planOk = true (the description's tests on its
plan; a premise of the rule too). The rows are those of our two lots (sendLots) at the ground Bs.G₀,
with the rule's predicates substituted (Unlettered.lay).
  lots_hand_in     Suppose that (i) the test lotsOkB accepts at every owner of a spending entry of
                   the book that is one of our senders, and (ii) the test on queried positions
                   lotsReadsB accepts. Then four things hold at every row. A member is at the row's
                   place (the rule's seat₁). Every side of the row has Good for some A₁ and B₁
                   (hand₁). The row's bound on queried positions holds at every due list of
                   challenges (the field bud₁ of BudDebts). The row's condition On follows from
                   every thread (on₁).
  hand_of_spenders   The second of these, from the premise on the book at the spenders alone
                     (SpendersClearAny at every job).
  bud_of_lots      The third, from our clause BudClause at every job.
  on_of_lots       The fourth: our rows' On is the condition that always holds.
  the example at the end
                   A check that the four have the form of the rule's own premises: Lean accepts them
                   as the arguments seat₁, hand₁, hbud.bud₁ and on₁ of file_owed_rows, at a first
                   chain whose rows are any list of other rows followed by ours. All other premises
                   of the rule, and the same four at the other rows, are hypotheses of the example,
                   as are IM.Open and the two tests (i) and (ii) at the order orderOf F. It proves
                   nothing of use by itself.

How it fits. file_owed_rows is in Johnson/Desc/ProofFile/Honest/Thread/Rows.lean. The tests are in
LotsGuard.lean and LotsTest.lean beside this file, their ties in LotsGuardTie.lean and
LotsTestTie.lean. Meant as steps toward index privacy (Johnson/WholeKey/Statement.lean); nothing in
this folder derives index privacy from them. Not one of the release's goal statements.

Limits. All limits of AtDescLots.lean hold here too. In addition:
Test (ii) is proved to accept, and F.planOk to hold, at all public files in the goals' scope at
which the library's gate accepts (reads_of_live, plan_of_live, handIn_of_live, at OnBytes.secondHashFunction,
ReadsAtLive.lean). Test (i) is proved to accept, in scope, where the gate accepts and the maker
onlineProverFromPublicFiles returns, at the book that the maker returns and the returned description's own order of
places, at every owner of a spending entry that is one of our senders (door_closed,
AtFullSide/M1/LotsThinClosed.lean, side library; it speaks at two owners, the opening's and W's
sender, and is idle at the fifty others: AtFullSide/M1/LotsDoor.lean, "How far"); a book that lists
nobody passes it.
The rule has further premises, among them: the book's own test, that the run can be made ready at
one value of the coins, premises on the input relation, that each part can be played, what is passed
on, that the verifier accepts, the seams between the chains, and all four of the above at the other
rows and chains. They are not this folder's, and nothing is said of them here.
-/
import Johnson.SendSim.Seat.AtDescLotsProof
import Johnson.SendSim.Seat.AtDescLotsSpenders
import Johnson.SendSim.Seat.LotsGuardTie
import Johnson.SendSim.Seat.LotsTestTie
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {V W X Xi Pb : Type}

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Where the description's maker returns: the rule's premise on a row's side, at every row of our
two lots, from the premise on the book at the spenders alone.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem hand_of_spenders {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (O : IM.Open o pol lay KL F Z Bs base c A B)
    (φ : Face V W Pb) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place) (chain ft : Nat)
    (T : W → Thread Bk F.S₁ F.Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (fs : List (Fall F.S₁))
    (hB : ∀ J ∈ lotJobs (X := X) no D Z Bs.G₀ ++ wJobs (X := X) no D Z Bs.G₀,
      SpendersClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩) :
    ∀ r ∈ rowsOfLots Z Bs.G₀ (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      ∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁ (r.lay T Sd F.first.blocksInOrder).On
          (r.lay T Sd F.first.blocksInOrder).bud := by
  intro r hr σ hσ
  obtain ⟨J, hJ, rfl⟩ := row_of_lots wit no D Z Bs.G₀ hr
  obtain ⟨-, h⟩ :=
    fieldsAtLots V W X Xi Pb o pol lay KL F Z Bs base c A B O φ wit no D chain ft fs J hJ
  obtain ⟨hf, he, -⟩ := h σ hσ
  exact ⟨_, _, good_of_fields hf he (freshAtLots_of_spenders O φ wit no D hJ hσ Bk ord (hB J hJ))⟩

end

/-- The first field of the rule's premise on queried positions, at every row of our two lots, from
our clause at every job. -/
theorem bud_of_lots (F : FileDescription ProofFile.Inst) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (h : ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G,
      BudClause (V := V) (Pb := Pb) F J.P.place (jobOver J wit)) {Bk : ProverCoinCounts}
    (T : W → Thread Bk F.S₁ F.Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop) :
    ∀ r ∈ rowsOfLots Z G (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      ∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
        F.first.blocksInOrder = pre ++ σ.block :: t →
        n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
        ∀ ρ : ProofFile.Honest.Draws, ρ.due F = true →
        (r.lay T Sd F.first.blocksInOrder).bud u.number ((ρ.first.drop n).take u.rounds.length)
          (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
            (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro r hr σ hσ u hu pre t n hc hn ρ hρ
  obtain ⟨J, hJ, rfl⟩ := row_of_lots wit no D Z G hr
  exact h J hJ Bk _ _ σ hσ u hu pre t n hc hn ρ hρ

/-- The rule's premise on a row's condition On, at every row of our two lots: that condition always
holds. -/
theorem on_of_lots {S Cl : Type} {Bk : ProverCoinCounts} (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (T : W → Thread Bk S Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (bs : List (Block S Cl)) (T' : Thread Bk S Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (len : Nat → Nat → Nat) :
    ∀ r ∈ rowsOfLots Z G (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      OnFromS T' Said (r.lay T Sd bs) b len := by
  intro r hr
  obtain ⟨J, -, rfl⟩ := row_of_lots wit no D Z G hr
  intro σ _ u _ k m E ca front _ _ _
  exact trivial

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Where the description's maker returns and the description passes its tests on the plan: the
four premises that the rule asks row by row, at every row of our two lots, if the two public tests
accept.**
pre₀ is tied to no description; of Good's fields exact alone reads it, and at each pre₀ that field
says no more than ExactAt. -/
theorem lots_hand_in {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (plan : F.planOk = true)
    (φ : Face V W Pb) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place) (chain ft : Nat)
    (T : W → Thread Bk F.S₁ F.Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (fs : List (Fall F.S₁))
    (hBook : ∀ e ∈ Bk.ahead, e.once = true → lotsMine Z Bs.G₀ e.owner = true →
      lotsOkB Z Bs.G₀ Bk ord e.owner = true)
    (hReads : lotsReadsB F Z Bs.G₀ = true) :
    ∀ r ∈ rowsOfLots Z Bs.G₀ (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      F.first.blocksInOrder.any (fun b => b.place == r.place) = true ∧
      (∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre₀ φ σ Bk ord chain ft A₁ B₁ (r.lay T Sd F.first.blocksInOrder).On
          (r.lay T Sd F.first.blocksInOrder).bud) ∧
      (∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
        F.first.blocksInOrder = pre ++ σ.block :: t →
        n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
        ∀ ρ : ProofFile.Honest.Draws, ρ.due F = true →
        (r.lay T Sd F.first.blocksInOrder).bud u.number ((ρ.first.drop n).take u.rounds.length)
          (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
            (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum)) ∧
      ∀ w b len, OnFromS (T w) (Sd w) (r.lay T Sd F.first.blocksInOrder) b len :=
  fun r hr => ⟨seat_of_lots O wit no D r hr,
    hand_of_spenders O φ wit no D Bk ord chain ft T Sd fs (spendersClear_all no D hBook) r hr,
    bud_of_lots F wit no D Z Bs.G₀ (budClause_of_lotsReadsB F wit no D Z Bs.G₀
      (decide_eq_true (places_nodup ((F.planOk_ok).1 plan).places).1) hReads) T Sd r hr,
    fun w b len => on_of_lots wit no D Z Bs.G₀ T Sd F.first.blocksInOrder (T w) (Sd w) b len r hr⟩

/-- A check of form: Lean accepts the four as the rule's own premises, at a first chain whose rows
are any other rows followed by ours. Everything else that the rule asks is a hypothesis here, as are
IM.Open and the two tests at the order orderOf F. lots_hand_in is taken here at the rule's own pre,
which depends on the row's place: that it holds at every pre₀ is what lets one lemma serve all rows.
-/
example {W₀ Rc Ky Tr X₀ X Xj : Type} {Bk : ProverCoinCounts} (O : IM.Open o pol lay KL F Z Bs base c A B)
    {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
    {Rel : W₀ → Rc → ProofFile.Inst → Prop} (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xj)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj)
    (rest : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (T₁ : Local W₀ Rc ProofFile.Inst Tr →
      Thread Bk F.S₁ F.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc ProofFile.Inst Tr →
      Thread Bk F.S₃ F.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (S₁ : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (r₂ : List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky))
    (r₃ : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hG : G = laySides F T₁ T₂ T₃ S₁ S₂ S₃
      (rest ++ rowsOfLots Z Bs.G₀ (sendLots wit no D)) r₂ r₃ f₁ f₂ f₃)
    (hBook : ∀ e ∈ Bk.ahead, e.once = true → lotsMine Z Bs.G₀ e.owner = true →
      lotsOkB Z Bs.G₀ Bk (orderOf F) e.owner = true)
    (hReads : lotsReadsB F Z Bs.G₀ = true)
    (seatR : ∀ r ∈ rest, F.first.blocksInOrder.any (fun b => b.place == r.place) = true)
    (handR : ∀ r ∈ rest, ∀ σ, (r.lay T₁ S₁ F.first.blocksInOrder).side F.first.blocksInOrder f₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder (r.lay T₁ S₁ F.first.blocksInOrder).place) .own σ
        Bk (orderOf F) 0 0 A' B' (r.lay T₁ S₁ F.first.blocksInOrder).On (r.lay T₁ S₁ F.first.blocksInOrder).bud)
    (budR : ∀ r ∈ rest, ∀ σ, (r.lay T₁ S₁ F.first.blocksInOrder).side F.first.blocksInOrder = some σ →
      ∀ u ∈ σ.members, ∀ pre t n, F.first.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
      ∀ ρ : ProofFile.Honest.Draws, ρ.due F = true →
      (r.lay T₁ S₁ F.first.blocksInOrder).bud u.number ((ρ.first.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum))
    (onR : ∀ w, ∀ r ∈ rest, ∀ b blk, F.first.blocksInOrder[b]? = some blk →
      blk.place = (r.lay T₁ S₁ F.first.blocksInOrder).place →
      OnFromS (T₁ w) (S₁ w) (r.lay T₁ S₁ F.first.blocksInOrder) b (depthAt F))
    (bud₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      F.shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
      ∀ ρ : ProofFile.Honest.Draws, ρ.due F = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum))
    (bud₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      F.second.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
      ∀ ρ : ProofFile.Honest.Draws, ρ.due F = true →
      L.bud u.number ((ρ.second.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length)).sum))
    (plan : F.planOk = true) (book : Bk.word F = none)
    (seat₂ : ∀ r ∈ r₂, F.shared.blocksInOrder.any (fun b => b.place == r.place) = true)
    (seat₃ : ∀ r ∈ r₃, F.second.blocksInOrder.any (fun b => b.place == r.place) = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (hand₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud)
    (hand₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
        (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    {w₁ : W₀} {rc₁ : Rc} {x₁ : ProofFile.Inst} {k₁ : Coins Bk} {R₁ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hone : ready F Bk (G.prover H) w₁ rc₁ x₁ k₁ = .ok R₁)
    (sits : ∀ w w', Sits F (G.prover H) (T₁ w) (T₂ w') (T₃ w))
    (o₁ : ∀ w, OwesS (T₁ w) (S₁ w)) (o₂ : ∀ w, OwesS (T₂ w) (S₂ w))
    (o₃ : ∀ w, OwesS (T₃ w) (S₃ w))
    (n₁ : ∀ w b, SaidNext (T₁ w) (S₁ w) b) (n₂ : ∀ w b, SaidNext (T₂ w) (S₂ w) b)
    (n₃ : ∀ w b, SaidNext (T₃ w) (S₃ w) b)
    (y₁ : ∀ w, YesS (T₁ w) (S₁ w) (fallsBy G.falls₁ F.first.blocksInOrder))
    (y₂ : ∀ w, YesS (T₂ w) (S₂ w) (fallsBy G.falls₂ F.shared.blocksInOrder))
    (y₃ : ∀ w, YesS (T₃ w) (S₃ w) (fallsBy G.falls₃ F.second.blocksInOrder))
    (a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₁ F (G.prover H) (T₁ R.own) w₀ rc x k R)
    (a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₂ F (G.prover H) (T₂ R.common) w₀ rc x k R)
    (a₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehind F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ m₁ m₂ o₁ o₂, S₁ R.own F.first.blocksInOrder.length k m₁ →
        S₂ R.common F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ R.own 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) })
    (on₂ : ∀ w, ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F))
    (on₃ : ∀ w, ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    Owed F Bk H G Rel := by
  subst hG
  have hin := fun pre₀ => lots_hand_in (pre₀ := pre₀) O plan .own wit no D Bk (orderOf F) 0 0 T₁ S₁
    f₁ hBook hReads
  have both : ∀ {Q : Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst →
      Prop}, (∀ r ∈ rest, Q r) → (∀ r ∈ rowsOfLots Z Bs.G₀ (sendLots wit no D), Q r) →
      ∀ r ∈ rest ++ rowsOfLots Z Bs.G₀ (sendLots wit no D), Q r :=
    fun h1 h2 r hr => (List.mem_append.1 hr).elim (h1 r) (h2 r)
  exact file_owed_rows T₁ T₂ T₃ S₁ S₂ S₃ _ r₂ r₃ f₁ f₂ f₃ rfl plan book
    (both seatR fun r hr => (hin [] r hr).1) seat₂ seat₃ hq hroot
    (forall_lay (both handR fun r hr => (hin _ r hr).2.1)) hand₂ hand₃ input hst hone
    ⟨forall_lay (both budR fun r hr => (hin [] r hr).2.2.1), bud₂, bud₃⟩ sits o₁ o₂ o₃ n₁ n₂ n₃ y₁
    y₂ y₃ a₁ a₂ a₃ e₁ e₂ e₃
    (fun w => forall_lay (both (onR w) fun r hr b _ _ _ => (hin [] r hr).2.2.2 w b (depthAt F)))
    on₂ on₃

end

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.hand_of_spenders
#print axioms OnBytes.SendSim.Seat.bud_of_lots
#print axioms OnBytes.SendSim.Seat.on_of_lots
#print axioms OnBytes.SendSim.Seat.lots_hand_in
