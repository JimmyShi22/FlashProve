-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsAtLive.lean: at all public files in the goals' scope at which the
library's gate accepts, the public test on queried positions accepts at the 52 jobs of the kind K1
on the proof file's first chain; so three of the four premises that the frame's rule asks row by row
hold at our rows with no further premise, and the fourth under the public test on the book alone. It
claims no property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. P is any public files with VerifierAndGoals.InScope P = true and FlashProve.protocolDataWellFormed
(asDescriptionFiles P) = true; both are tests on the public files. O is any opening of the maker's value at P
(IM.Open at OnBytes.secondHashFunction, P.pol, P.lay, P.KL, with the description F, the public part Z and the
ground Bs.G₀).
  Spec.readsAt P   The statement at P: at every opening, lotsReadsB F Z Bs.G₀ = true. That test
                   (LotsTest.lean) asks, for each job of lotJobs and wJobs and each of its messages:
                   the positions that all rounds of F's three chains sample for the message's tree,
                   counted once for each opening, are at most as many as the random symbols that the
                   message's code appends to a row, for the main rows' code and for the mask rows'
                   code.
  reads_of_live    Spec.readsAt P holds. reads_there_of_live: and there is such an opening, of a
                   description whose run is the one that the library's verifier asks; so it does not
                   hold vacuously.
  bud_of_live      So our clause of the rule's premise on queried positions (BudClause, Bud.lean)
                   holds at every job: at every due list of challenges the positions read meet
                   budAt, the bound that is a premise inside exact and fresh. It uses two public
                   facts: that the test accepts, and that no two members of the first chain are at
                   one place, which is one of the tests on the plan (places_nodup).
  handIn_of_live   At every row of our two lots the rule's seat₁, bud₁ and on₁ hold with no further
                   premise. on₁ holds because our rows' On always holds. The rule's hand₁ (Good for
                   some A₁ and B₁) holds if the test lotsOkB accepts at every owner of a spending
                   entry of the book that is one of our senders: that premise stands inside the
                   second part alone. The parts are those of lots_hand_in (AtDescLotsRule.lean).
  D_in_scope       In scope, where the maker's pin on the sizes has accepted, the public part's
                   declared rounds are the written value DW (Johnson/AtFull/Pub/PubOfMade.lean).
                   plan_of_live: at an opening at files at which the gate accepts, the description
                   passes its tests on the plan and the maker's entry tests have accepted.

How it fits. The test reads three things. (a) F's declared rounds: they are DW, because F passes its
tests on the plan, its plan is the public part's, and D_in_scope. (b) The first chain's places,
numbers of rounds and oracle messages: they are the written rows cutFirstFull, by one of the maker's
entry tests (asks_pins, Johnson/Desc/Laid/ProofAsksLaw2.lean; cutIs_eq,
Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean). (c) The jobs' public numbers: they are the written
ones (likeFull_in_scope, gpOf_in_scope, Johnson/HB/LLHARD/PlanInScope.lean; view_in_scope,
Johnson/AtFull/Desc/Lots/K1/View.lean). At these written values the test is checked by evaluation in
Lean's kernel (readsW, ReadsAtWritten.lean, through lotsReadsB_of_written). The law on the trees in
front of a place also wants that each member has as many lists of oracle messages as rounds: a
clause of the tests on the plan (PlanOk.blocks₁, Block.shaped). One set of written tables serves all
files in scope, because the gate's own entry tests compare the maker's values with the written ones.
At named files the library proves the first premise and the side library the second. Meant as steps
toward index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy
from them. Not one of the release's goal statements.

Limits.
The test has no slack where that was tried: one more position sampled for the first chain's tree 0,
tree 2 or tree 82 makes it reject (readsW_rejects, ReadsAtWritten.lean; drawnW there lists the
positions sampled for each tree). So a change of the protocol that opens one of these trees a second
time would make it reject.
It speaks of the trees of the 52 jobs alone. The test asks more than the bound: it counts a position
once for each opening, whether or not two positions are equal modulo a code's length. The count is
of one run of the proof file's description: one proof of one request. These trees are made anew in
each run; that is said of the protocol, and no Lean statement here speaks of two runs.
The test on the book is proved to accept, in scope, where the gate accepts and the maker onlineProverFromPublicFiles
returns, at the book that the maker returns and the returned description's own order of places, at
every owner of a spending entry that is one of our senders (door_closed,
AtFullSide/M1/LotsThinClosed.lean, side library); a book that lists nobody passes it. Where the
premise on the book is proved at these senders: the table of premises in Johnson/SendSim/Defs.lean,
"the book is clear". fresh has content at two of the 52 rows alone. That a list of challenges is due
at F is proved apart, of one written list that meets a test of form (due_of_live, DueAtLive.lean).
All other limits of AtDescLots.lean and AtDescLotsRule.lean.
At the earlier hash function OnBytes.secondHashFunction alone. That the gate accepts at given files is not shown
here.
-/
import Johnson.Goal.Description.ProofSeat
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Second.Seam.AnswersOneInScope
import Johnson.Desc.Laid.ProofAsksLaw2
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.First.Att.Row.K5FrontPlans
import Johnson.HB.LLHARD.PlanInScope
import Johnson.AtFull.Desc.Lots.K1.View
import Johnson.AtFull.Desc.Ledger
import Johnson.AtFull.Plans.PlansSix
import Johnson.AtFull.ProofBack.Back
import Johnson.SendSim.Seat.ReadsAtWritten
import Johnson.SendSim.Seat.AtDescLotsRule

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.Number.ByRuns (proofThree proof_fit0 proof_fit1 proof_fit2)

/-- In the goals' scope, where the maker's pin on the sizes has accepted, the public part's declared
rounds are the written ones. -/
theorem D_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.D = Johnson.AtFull.Pub.DW := by
  have hpl := VerifiableInference.PlanWritten.Joined.proof_plans_in_scope hW h hy
  obtain ⟨ls, _, hc, hk, hD⟩ := ProofFile.Law.pub_configure h
  obtain ⟨g1, g2, g3⟩ := OnBytes.Params.proof_read_made hc hk (fun P hP => by
    rw [hpl] at hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact proof_fit0
    · exact proof_fit1
    · exact proof_fit2) hpl
  have d := Johnson.AtFull.ProofBack.declPOf_at_fields (m := Z.made)
    (Second.Seam.sized_proof_in_scope hW h hy)
    (VerifiableInference.PlanWritten.Joined.sends_in_scope hW h hy) g1 g2 g3 H2K5.Row.E0
    Johnson.AtFull.Plans.O0 Johnson.AtFull.Plans.E1 Johnson.AtFull.Plans.O1
    Johnson.AtFull.Plans.E2 Johnson.AtFull.Plans.O2
  rw [Johnson.AtFull.ProofBack.declPOf_blank] at d
  exact Except.ok.inj (hD.symm.trans d)

/-- The statement at public files P; proved as reads_of_live below, under two tests on P. At every
opening of the maker's value at P, the public test on queried positions accepts over the jobs of the
two lists. -/
def Spec.readsAt (P : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
    IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B →
    lotsReadsB F Z Bs.G₀ = true

section
variable {P : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block First.S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At an opening of the maker's value at files at which the gate accepts, the description passes
its tests on the plan and the maker's entry tests have accepted. -/
theorem plan_of_live (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    F.planOk = true ∧ ∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction P.pol P.lay P.KL F
      (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles P)), t.2 = true := by
  obtain ⟨F', h1, h2, -, h4, -⟩ := FlashProve.pseat_name P hL
  obtain rfl : F' = F := Except.ok.inj (h1.symm.trans (Johnson.AtFull.Desc.descPure_of_open O))
  exact ⟨h2, h4⟩

end

/-- **Spec.readsAt P holds at all public files P that are in the goals' scope and at which the
library's gate accepts.** -/
theorem reads_of_live {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true) : Spec.readsAt P := by
  intro F Z Bs base c A B O
  obtain ⟨h2, h4⟩ := plan_of_live hL O
  have PO := (F.planOk_ok).1 h2
  -- the first chain's rows, and the pin
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨hm, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  have hcut := (VerifiableInference.PlanWritten.cutIs_eq hc).1
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row (Z := Z) (by rw [hm, Bool.or_true])
  -- the jobs' public numbers
  have hLZ := VerifiableInference.Desc.K13.Law.likeFull_in_scope hS O.pub hy
  have hg := VerifiableInference.Desc.K13.Law.gpOf_in_scope hS O.pub hy
  have hLG : K1.LikeFull Bs.G₀.first := by rw [O.first]; exact hLZ
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  have hv := Johnson.AtFull.Desc.K1Lot.view_in_scope hS hR O.pub O.blank
  -- the declared rounds
  have hD : Z.D = Johnson.AtFull.Pub.DW := D_in_scope hS O.pub hy
  have hpl : F.plans = Z.D := by rw [O.desc]; rfl
  have hd : F.roundsDeclaredByBlocks = Johnson.AtFull.Pub.DW := by
    rw [← hD, ← hpl]
    exact Prod.ext PO.decl₁ (Prod.ext PO.decl₂ PO.decl₃)
  have hs : ∀ b ∈ F.first.blocksInOrder, b.oracles.length = b.rounds.length := fun b hb => by
    have h := (PO.blocks₁ b hb).2
    unfold Block.shaped at h
    rw [Bool.and_eq_true] at h
    exact beq_iff_eq.1 h.1
  exact lotsReadsB_of_written hd hcut hs (lotPars_written hLG hLZ hg hv)

/-- In scope, where the gate accepts, there is an opening of the maker's value, so Spec.readsAt P
does not hold vacuously: the maker returns a description that passes its tests on the plan; its run
is the one that the library's verifier asks; and at its opening the public test on queried positions
accepts. -/
theorem reads_there_of_live {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block First.S ProofFile.Cl)) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
      (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧ F.planOk = true ∧
      FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles P) = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      lotsReadsB F Z Bs.G₀ = true := by
  obtain ⟨F, hF, hp, -, -, hrun⟩ := FlashProve.pseat_name P hL
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨F, Z, Bs, base, c, A, B, hF, O, hp, hrun, reads_of_live hS hL F Z Bs base c A B O⟩

section
variable {V W X Xi Pb : Type} {P : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope, where the gate accepts: at every opening of the maker's value, our clause of the
rule's premise on queried positions holds at every job of the two lists. -/
theorem bud_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (wit : W → PlaceIn Xi) (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    ∀ J ∈ lotJobs (X := X) no D Z Bs.G₀ ++ wJobs (X := X) no D Z Bs.G₀,
      BudClause (V := V) (Pb := Pb) F J.P.place (jobOver J wit) :=
  budClause_of_lotsReadsB F wit no D Z Bs.G₀
    (decide_eq_true (places_nodup ((F.planOk_ok).1 (plan_of_live hL O).1).places).1)
    (reads_of_live hS hL F Z Bs base c A B O)

/-- **In scope, where the gate accepts: at every opening of the maker's value, the four premises
that the rule asks row by row, at every row of our two lots.** Three hold with no further premise.
The second, Good for some A₁ and B₁, holds if the public test on the book accepts.
pre₀ is tied to no description; of Good's fields exact alone reads it, and at each pre₀ that field
says no more than ExactAt. -/
theorem handIn_of_live {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (φ : Face V W Pb) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place) (chain ft : Nat)
    (T : W → Thread Bk F.S₁ F.Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (fs : List (Fall F.S₁)) :
    ∀ r ∈ rowsOfLots Z Bs.G₀ (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      F.first.blocksInOrder.any (fun b => b.place == r.place) = true ∧
      ((∀ e ∈ Bk.ahead, e.once = true → lotsMine Z Bs.G₀ e.owner = true →
          lotsOkB Z Bs.G₀ Bk ord e.owner = true) →
        ∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs = some σ →
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
    fun hBook => hand_of_spenders O φ wit no D Bk ord chain ft T Sd fs
      (spendersClear_all no D hBook) r hr,
    bud_of_lots F wit no D Z Bs.G₀ (bud_of_live hS hL O wit no D) T Sd r hr,
    fun w b len => on_of_lots wit no D Z Bs.G₀ T Sd F.first.blocksInOrder (T w) (Sd w) b len r hr⟩

end

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.D_in_scope
#print axioms OnBytes.SendSim.Seat.plan_of_live
#print axioms OnBytes.SendSim.Seat.reads_of_live
#print axioms OnBytes.SendSim.Seat.reads_there_of_live
#print axioms OnBytes.SendSim.Seat.bud_of_live
#print axioms OnBytes.SendSim.Seat.handIn_of_live
#print axioms OnBytes.SendSim.Seat.Spec.readsAt
