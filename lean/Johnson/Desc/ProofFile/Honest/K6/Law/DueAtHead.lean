-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/DueAtHead.lean: WHAT THE OUTPUT HEAD's LAW ASKS OF THE
VERIFIER's STATE BEHIND ITS OWN SUB-PROTOCOL (`RecordDue`, Johnson/Desc/Kinds/Law/K6OpenedCut.lean)
STANDS BEHIND THE MEMBER's STEP AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS
(`lettersHead`, Honest/Thread/FirstHead.lean). CONDITIONAL on that file's one hypothesis h, and on
nothing else but, at the top, that Lk is the first chain's link 24. Three lemmas, by calls.

  `strict_of_stepped`   general in the thread: a member's step at a thread, at challenges that fit
                    its rounds, where no column is read, is a yes of the same step behind the test
                    "every word that is shown is below the prime"
  `dueFront_at_head`   the nine facts on the state in front (`K6DueFront`,
                    Johnson/Desc/K6/Honest/Law/Due.lean), wherever the thread stands at border 341
  `due_at_head`     **the field due of `K6ShareDebts` (Honest/K6/Law/Share.lean), to the letter, at
                    these letters**

What it is not. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE, as h. (The library has a member
of that hypothesis, `P5J.AtMgA`, under four premises on the three public files:
`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) That the
thread holds at any run is shown nowhere. FACTS ON THE VERIFIER's STATE AND ON PUBLIC DATA: none of
the twelve clauses holds a value of the witness. The letters are fixed: border 341, segment 24, the
mask row's message num 24 0, whose mask rows are numbered by 0 bits, the reads' public part `p8K6
(At.X Zp) 24`, the states of the link Lk. NOTHING OF Said IS SPENT: the thread's half of the pair
alone. WHO PAYS WHAT. The member's form and number: `k6_member_at_mg`
(Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean). Its test on the plan: `flat_ok`
(Johnson/P5J/FoldJ1.lean). No column: `step_iff` (Johnson/Top/H0/StepLaws/StepLaws.lean) with
`K6MemberIs.want`. The strict yes: `steps_decl`, `play_yields`, `drawsFit_bare`,
`okViewW_of_yields`, `okViewW_nil` (Honest/Law/Run.lean, Play.lean), as in the first lines of the
proof of `saidNext_ok` (Honest/Thread/SaidOk.lean), which are no lemma there; then `step_below`
(Honest/Thread/SaidOk.lean). Seven of the nine facts: `headFrontItems_of_thr`, `headLink_at`
(Honest/K6/Law/FrontAt.lean) and `dueFront_of_items` (Honest/Law/DueMade.lean), with the hypothesis'
field on the public parameters, `trees_at_const`, `ns_at_const`. The five facts on every reached
state: five fields of `foldFacts_thr` (Honest/Thread/ReachFacts.lean), laid one by one:
`foldAt_of_facts` (Law/K6RestOfFold.lean) is typed at another form of statement and cannot be
called. No tables: `k6Reached_341` (Johnson/P4R/K6ReachedAt341.lean) at `thr_reach`. The five on
public data: `duePub_at_head` at the written list of seats (`laid_at_head`,
Johnson/P5J/ReadsTestsAtHead.lean). The twelve: `due_of_step`. The readers: `paid_at_const`'s field.
The data with two fields turned have the same arr, N, St and Rd by definition. Over files that have
not yet landed in the library: Honest/Law/Due.lean, DueMade.lean, Honest/K6/Law/FrontAt.lean,
Law/K6WayUpAtSeat.lean, the files on threads, and what these import.
Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.DueMade
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontAt
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.P4R.K6ReachedAt341

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Claim OpenedColumn Link Place Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below linksFull mgBase MsgT)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (RecordDue p8K6 k6Silent dAt)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (FoldAt K6DueFront)
open ProofFile.Honest.FirstThread (Script WtF lettersHead foldFacts_thr thr_reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- The written list of places, at the full chain. -/
local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **THE STRICT YES, FROM THE MEMBER's STEP AT A THREAD**, general in the thread: what play lays is
below the prime by make (the first lines of the proof of saidNext_ok, Honest/Thread/SaidOk.lean,
which are no lemma there); no column is read. -/
theorem strict_of_stepped {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk St Cl V W X Pb)
    {blk : Block St Cl} {k : Coins Bk} {s s' : St} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn} (hd : drawsFit blk.rounds ds = true)
    (hS : T.Stepped blk k s m E ds y cols s') (hc : cols = []) :
    (below blk).step T.ft s (roundsOf y.1) cols = .ok (s', cols.length) := by
  subst hc
  obtain ⟨hM, hstep⟩ := hS
  unfold Thread.Moved at hM
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  have hdl : l.map (·.decl) = blk.rounds := by
    rw [steps_decl hl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have h1 := okViewW_of_yields _ _ _ _ (play_yields _ _ _ _ _ hy)
    (by rw [hdl]; exact drawsFit_bare _ _ hd) okViewW_nil
  exact step_below hstep h1 (fun x hx => by cases hx)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE NINE FACTS ON THE STATE IN FRONT, WHEREVER THE THREAD STANDS AT BORDER 341**, at the full
size's written list of seats. -/
theorem dueFront_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E) :
    K6DueFront (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp) (dAt h).cs (dAt h).shape (dAt h).pubD.dS
      VerifiableInference.Desc.K13.Law.LFull
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)
      ((dAt h).sent.arrayOf.getD 24 #[]) PS[341]? s := by
  obtain ⟨hm, R⟩ := headFrontItems_of_thr
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) h.𝔇 rfl rfl rfl rfl hT
  obtain ⟨b, hb341, -⟩ := P4.k6_member_at_mg h.toAtMg
  have hb : 341 ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb341).1
  have FF := foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  have F : FoldAt VerifiableInference.Desc.K13.Law.LFull
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) (dAt h).cs (dAt h).shape
      (P5J.At.layout Zp) s :=
    ⟨FF.seatsCarried 341 (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hm,
      FF.msgShapes 341 (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hm,
      (FF.codes 341 (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hm).trans rfl,
      (FF.liveShape 341 (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hm).trans rfl,
      (FF.liveLayout 341 (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hm).trans rfl⟩
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have Z1 := (P4.k6Reached_341 h.scope h.reads O
    (fun b3 hb3 => P5J.flat_ok h.toAtMg b3 (List.mem_of_getElem? hb3))
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)).noTab
  exact VerifiableInference.Desc.Kinds.Head.Law.AtFold.dueFront_of_items (dAt h) mgBase _ R
    (headLink_at h) h.pubOne (VerifiableInference.Desc.Kinds.Head.Law.AtTable.trees_at_const h)
    (VerifiableInference.Desc.Kinds.Head.Law.AtTable.ns_at_const h) (P5J.At.layout Zp) _ _ F Z1

/-- **THE FIELD due OF `K6ShareDebts`, AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS,
UNDER THE ONE HYPOTHESIS h**, at every Said (nothing of it is spent) and at every Lk that is the
chain's link 24. -/
theorem due_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (Lk : Link S Claim)
    (hlk : cF.links[24]? = some Lk) :
    ∀ blk k s m E ds y cols s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      ∃ aK cU, RecordDue
        ({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } :
          VerifiableInference.Desc.Sound.MgData _ _ _ _ _ _ _).arr
        ({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } :
          VerifiableInference.Desc.Sound.MgData _ _ _ _ _ _ _).N
        (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) (P5J.At.num Zp 24 0) 0
        (p8K6 (P5J.At.X Zp) 24)
        ({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } :
          VerifiableInference.Desc.Sound.MgData _ _ _ _ _ _ _).St
        (VerifiableInference.Desc.K9.statesOfLink Lk)
        (({ h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } :
          VerifiableInference.Desc.Sound.MgData _ _ _ _ _ _ _).Rd 24) s' aK cU := by
  intro blk k s m E ds y cols s' hblk hT hd hS
  obtain ⟨b, hb, M⟩ := P4.k6_member_at_mg h.toAtMg
  have hblk' : cF.blocksInOrder[341]? = some blk := hblk
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk')
  have hc : cols = [] := by
    have h3 := ((VerifiableInference.Desc.step_iff _ b s s' _ cols _).1 hS.2).2.2
    rw [M.want] at h3
    exact List.eq_nil_of_length_eq_zero h3
  have hstr := strict_of_stepped _ hd hS hc
  obtain ⟨aK, cU, hR⟩ := VerifiableInference.Desc.Kinds.Head.Law.AtFold.due_of_step M (by decide)
    (fun _ _ e => P4.same_of_eq e) (P5J.flat_ok h.toAtMg b (List.mem_of_getElem? hb)) hstr
    (dueFront_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1) (dAt h).St Lk
    (VerifiableInference.Desc.Kinds.Head.Law.AtFold.duePub_at_head h Lk hlk _
      (P5J.laid_at_head h.toAtMg))
    VerifiableInference.Desc.K9.smallReader
  refine ⟨aK, cU, ?_⟩
  have hRd := (VerifiableInference.Desc.Kinds.Head.Law.AtTable.paid_at_const h Lk hlk).readers
  show RecordDue (dAt h).arr (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
    (P5J.At.num Zp 24 0) 0 (p8K6 (P5J.At.X Zp) 24) (dAt h).St
    (VerifiableInference.Desc.K9.statesOfLink Lk) ((dAt h).Rd 24) s' aK cU
  rw [hRd]
  exact hR

#print axioms strict_of_stepped
#print axioms dueFront_at_head
#print axioms due_at_head

end ProofFile.Honest.K6
