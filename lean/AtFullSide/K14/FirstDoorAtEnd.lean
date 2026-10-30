-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/FirstDoorAtEnd.lean: the linear claim's second part ("K14, second part", the first
member of a proof file's last chain): THE EIGHT TESTS firstDoorB (Johnson/Desc/Last/ShapeDoor.lean)
ON WHAT THE LAST CHAIN's START IS HANDED OF THE FIRST CHAIN's LAST STATE: SEVEN FROM THE FIRST
CHAIN's INVARIANT AT ITS LAST BORDER, THE EIGHTH ("the mask has come") FROM THE START's RETURN
ALONE; under the library's hypothesis at the full size (P5J.AtMgA, Johnson/P5J/MgAtAll.lean), at the
format's second hash function. They are one of the three parts into which the last chain's form at
border 0
(fillZ's test) falls (shapeAt_zero_iff, ShapeDoor.lean): the start's return, these eight, and five
on the shared chain's end.

The eight: the statement is tidy; the book fits; one pending row, with lawful weights; the own group
has two members; each has one sample row; the group's open rows name messages of the statement
alone; it has an open row; the mask has come.

THE EIGHTH IS NOT LIFTED. The start refuses unless a mask's number is handed just where the plan
sends the masks ahead; so under the start's return the test is true, and that an honest run's last
state hands such a number is owed by whoever shows that the start returns.

How. The theorems join lemmas of the library on the verifier's states (among them
Johnson/Desc/Last/). What these lemmas ask of a state follows here from the invariant, which says
that the state is reached by the verifier's own steps and bears no failure mark, and which holds the
first table's promise at the last border, at the meaning adapted to the honest side; that meaning's
public tests are the library's.

  ocEnd_at_end        the first table's promise at its last border, read out of the invariant
  four_at_end         no failure mark, and the library's four facts on the state (FourFacts,
                      Johnson/Desc/Last/ShapeDoorFold.lean)
  doorStays_at_end    what the door asks of the first table's meaning and lists, at that meaning
  first_six_at_end    **six of the eight, and with them the seventh, from the invariant alone**: the
                      library's text doorFirstB (Johnson/Desc/Last/DoorTexts.lean)
  first_door_at_end   **the eight**
  first_door_saidS    the eight in the form in which the last chain's entering asks them: from the
                      invariant with any `Said` beside it, at the description's own count of members
  order_at_return     the statement of the state that the last chain's start returns is in order

What is not claimed. That the invariant holds at any state, or that the start returns. THAT WHAT THE
LAST THREAD IS HANDED IS THE PAIR OF THESE TWO LAST STATES: the form reads the thread's field for
what is handed, which is a free letter (Johnson/Desc/ProofFile/Honest/Thread/Last.lean). The five
tests on the shared chain's end. SO fillZ's TEST AT BORDER 0 IS SHOWN AT NO STATE BY THIS
FILE: it needs the start's return and these five as well. Nothing on completeness, soundness or
hiding. Terms. border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Johnson/Desc/ProofFile/Honest/Thread/Thr.lean).
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondDoor
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.Desc.Last.ShapeDoorAtTexts
import Johnson.Desc.Kinds.Law.RowLenAtConst
import Johnson.IMR.AtReachFits
import Johnson.P5J.ThreeAtFreeHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (onAt openSets pubSets)
open VerifiableInference.Desc.Sound (MsgT ocEnd mgBase)
open VerifiableInference.Desc.Third (S₃ firstOfS)
open VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Door (seatsCarriedB msgShapesB msgsOfChain)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (Script WtF lettersHead noStrs)
open P5J (AtMgA CellsM TS)
open Desc.K14 (St)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The first table's promise at its last border, read out of the invariant there**, at the
meaning adapted to the honest side and at the empty family of oracles' strings. -/
theorem ocEnd_at_end {k₁ : Coins Bk} {s₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k₁ s₁ m₁ E₁) :
    ocEnd (fun a : ProofFile.InstPub × TS => (a.1, a.2)) (P5J.At.N Zp cF)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP P5J.At.links P5J.At.ps
      (m₁.st.input.x.pub, s₁) noStrs := by
  unfold Thr at hT
  obtain ⟨-, -, ⟨-, hP⟩, -, -, -, -⟩ := hT
  have hP' : onAt (P5J.At.N Zp cF)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP P5J.At.links P5J.At.ps[358]?
      (((openSets P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.start P5J.At.links))[358]?).getD [])
      (((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP.more P5J.At.links
        P5J.At.ps)[358]?).getD []) (m₁.st.input.x.pub, s₁) noStrs := hP
  have e : P5J.At.ps[358]? = none :=
    List.getElem?_eq_none (le_of_eq VerifiableInference.Desc.Kinds.Head.Law.ps_length)
  rw [e] at hP'
  unfold ocEnd
  rw [VerifiableInference.Desc.Kinds.Head.Law.ps_length]
  exact hP'

/-- **No failure mark, and the library's four facts on the first chain's last state**: the statement
is tidy, the book fits, the pending rows' weights are lawful, and the own group's two members sit at
the plan's two seats. -/
theorem four_at_end {k₁ : Coins Bk} {s₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k₁ s₁ m₁ E₁) :
    s₁.failed = none ∧ FourFacts (LLT25.vAt Zp (P5J.At.N Zp cF)) s₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := flat_358 h.scope h.reads O
  have hoc := ocEnd_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 358 (m₁.st.input.x.pub, s₁) := thr_reach_of
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).first
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf m₁.st.input.x)
    (le_of_eq hlen.symm) (fun _ h0 => h0) hT
  have hm : s₁.failed = none := by
    unfold Thr at hT
    obtain ⟨-, -, ⟨hf, -⟩, -, -, -, -⟩ := hT
    have hf' : s₁.failed.isNone = true := hf
    exact Option.isNone_iff_eq_none.1 hf'
  have hp := flat_planOk_at h.toAtMg
  have hB := Meaning.K2.sendsAre_of_madeRow h.scope h.reads O h.laid.planOk h.toAtMg.pins.1
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row h.toAtMg.row_at_head
  have foldOf : ∀ (k : ℕ) (a : ProofFile.InstPub × TS), Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a →
      ∃ rs cols r q, VerifiableInference.Desc.foldBlocks 0 (cF.blocksInOrder.take k)
        (ProofFile.startS Zp (id a).1) rs cols = .ok ((id a).2, r, q) :=
    fun _ _ g => let ⟨_, rs, cols, f⟩ := g.fold; ⟨rs, cols, [], [], f⟩
  have hEnd : ∀ z s, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 358 (z, s) → s.failed = none →
      seatsCarriedB VerifiableInference.Desc.K13.Law.LFull s.book = true ∧
        msgShapesB (msgsOfChain Zp.made.proof.1) s.st = true :=
    fun z s g hu =>
      ⟨IM.seatsCarried_field h.scope h.reads O (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) id
          foldOf h.laid.planOk hB h.toAtMg.laid_codes_at_head 358 (z, s) g hu,
        IM.msgShapes_field h.scope h.reads O (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) id
          foldOf h.laid.planOk hB 358 (z, s) g hu⟩
  have T : ToldDesc.PlanSits VerifiableInference.Desc.K13.Law.LFull (msgsOfChain Zp.made.proof.1)
      (LLT25.vAt Zp (P5J.At.N Zp cF))
      (P5J.At.N Zp cF).indexNo 197 := by
    rw [h.toAtMg.indexNo_at]
    exact Second.Seam.planSits_at_N h.scope h.laid.pub hy (Desc.K14.Law.Sh.laidPOf_at_head h) cF
  have own := ownSitsB_at_promise_end h.scope h.reads O
    (ToldDesc.handsBack_reach 0 cF.blocksInOrder (ProofFile.startS Zp)) getAt (fun _ _ => rfl) (P5J.At.N Zp cF)
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP P5J.fullLinks P5J.At.ps
    pinI_open_full (fun a => mgAll_indexIs (h.toAtMg.𝔇 h.𝔇) mgBase a) (hsp_at_head h.toAtMg) T
    h.toAtMg.num_at_head hEnd (m₁.st.input.x.pub, s₁) noStrs hoc hr hm
  exact ⟨hm, Means.tidy4B_iff.2 (tidy_at_head h.toAtMg 358 _ hr),
    Meaning.K2.bookFits_field O hp (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
      (fun _ _ g => g) 358 (m₁.st.input.x.pub, s₁) hr hm,
    Meaning.K2.weights_at_open O hp 0 358 (m₁.st.input.x.pub, s₁) hr, own⟩

/-- What the door asks of the first table's meaning and lists (DoorStays,
Johnson/Desc/Last/ShapeDoorFold.lean), at the meaning adapted to the honest side: its public tests
are the library's. -/
theorem doorStays_at_end :
    DoorStays (P5J.At.N Zp cF) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP
      P5J.At.links P5J.At.ps (h.toAtMg.𝔇 h.𝔇).pubD.P13 (LLT25.vAt Zp (P5J.At.N Zp cF)) := by
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row h.toAtMg.row_at_head
  have H0 := doorStays_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase (P5J.At.N Zp cF)
    (LLT25.vAt Zp (P5J.At.N Zp cF)) (vAt_index _ _) (vAt_w _ _)
    (by exact (Second.Seam.answers_one_in_scope h.scope h.laid.pub hy).1)
    (by exact (Second.Seam.answers_one_in_scope h.scope h.laid.pub hy).2)
  exact ⟨H0.laid, H0.held, H0.laidOpen, H0.indexIn, H0.wIn, H0.oneIndex, H0.oneW⟩

/-- **The library's text on the first chain's last state** (doorFirstB: where something is handed to
the last chain's start, six of the eight tests say yes of it), from the invariant alone. -/
theorem first_six_at_end {k₁ : Coins Bk} {s₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k₁ s₁ m₁ E₁) :
    doorFirstB s₁ = true := by
  obtain ⟨hm, hF⟩ := four_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  exact doorFirstB_of_fold (fun a : ProofFile.InstPub × TS => (a.1, a.2)) (P5J.At.N Zp cF)
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP P5J.At.links P5J.At.ps _
    (LLT25.vAt Zp (P5J.At.N Zp cF)) (doorStays_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁)
    (m₁.st.input.x.pub, s₁) noStrs (ocEnd_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT)
    hm hF

/-- **The eight tests on what the last chain's start is handed of the first chain's last state.**
hT: the first chain's invariant at its last border, at s₁. hs: the last chain's start returns at s₁
and some state of the shared chain; of it only "a mask's number is handed just where the plan sends
the masks ahead" is spent, and the eighth test rests on that alone. -/
theorem first_door_at_end {k₁ : Coins Bk} {s₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E₁ : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k₁ s₁
      m₁ E₁)
    (x : ProofFile.InstPub) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    ∀ f, firstOfS s₁ = some f → firstDoorB f = true := by
  intro f hf
  have hlen : cF.blocksInOrder.length = 358 := by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    exact flat_358 h.scope h.reads O
  have door := first_six_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ (hlen ▸ hT)
  obtain ⟨f', e, -, hf', -, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
  exact firstDoorB_of_six (firstSix_of_text door hf)
    ((VerifiableInference.Desc.Third.Law.start_mask_ahead _ _ _ _ _ _ _ _ _ _ _ hst).trans
      (ahead_at_seat h.laid.pub))

/-- The eight, from the invariant with any `Said` beside it, at the description's own count of the
first chain's members. -/
theorem first_door_saidS (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (k₁ : Coins Bk) (x : ProofFile.InstPub) :
    ∀ (s₁ : TS) (m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E₁ : Env) (s₂ : St) (s : S₃),
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length k₁ s₁ m₁ E₁ →
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s →
      ∀ f, firstOfS s₁ = some f → firstDoorB f = true :=
  fun _ _ _ s₂ s u hs =>
    first_door_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ u.1 x s₂ s hs

/-- **The statement of the state that the last chain's start returns is in order**: it is the first
chain's last statement, which is tidy. -/
theorem order_at_return {k₁ : Coins Bk} {s₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k₁ s₁
      m₁ E₁)
    (x : ProofFile.InstPub) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) : Means.InOrder s.st := by
  have hlen : cF.blocksInOrder.length = 358 := by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    exact flat_358 h.scope h.reads O
  have hT' : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k₁ s₁ m₁
      E₁ := hlen ▸ hT
  obtain ⟨-, ht, -⟩ := four_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT'
  obtain ⟨f, e, -, hf, -, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  obtain ⟨-, -, -, -, e5, -⟩ := start_gives _ f _ s hst
  obtain ⟨_, -, e1, -⟩ := firstOfS_at hf
  rw [e5, e1]
  exact (Means.tidy4B_iff.1 ht).inOrder

end AtFullSide.K14

#print axioms AtFullSide.K14.ocEnd_at_end
#print axioms AtFullSide.K14.four_at_end
#print axioms AtFullSide.K14.doorStays_at_end
#print axioms AtFullSide.K14.first_six_at_end
#print axioms AtFullSide.K14.first_door_at_end
#print axioms AtFullSide.K14.first_door_saidS
#print axioms AtFullSide.K14.order_at_return
