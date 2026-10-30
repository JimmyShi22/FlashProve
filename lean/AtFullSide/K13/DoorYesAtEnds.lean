-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/DoorYesAtEnds.lean: WHAT THE LAST CHAIN's START AND THE FILE's LAST TEST READ OF THE
TWO EARLIER CHAINS' ENDS, OFF THE VERIFIER's FOLDS. The start refuses unless the first chain stands
at its end and the shared chain has ended. Both are said by the two chains' last blocks, so both
follow from how the thread says the state was made.

  asks_at_357      the first chain's last block says yes only where its clauses hold
  end_asks_at_first_end, fin_at_first_end   so at the chain's last border: S.fin
  untested_all     nothing is left untested, as the two chains' last tests read it
  tested_of_last, tested_at_shared_end   the shared chain has ended
  start_yes_of     what the last chain's own start asks
  doorYes_of_start   the door says yes, from the last chain's own start at the two ends
  start_req, req_at_first_end   the request's words at the first chain's end
  fin₃_of_last, fin₃_at_second_end   the last chain's seat says yes
  finYes_of_parts  the file's last test says yes, from its third clause on the instance

What these are. Conditional lemmas under the library's one hypothesis at the full size, h. None is
one of the library's goals. They say nothing of soundness, completeness or hiding.

Limits.
  * doorYes_of_start keeps one premise, hstart: the last chain's own start returns at the two ends.
    start_yes_of cuts that into six statements on the two ends. None of the six is shown here.
  * finYes_of_parts keeps one premise, hthird: where the last position is not covered, what is asked
    is 0. It reads the request's words and the reply alone, so no thread's clause says it.
  * Each statement speaks of a stand at a last border. That a run reaches such a stand is not said.
-/
import AtFullSide.K13.GAtFirstEnd
import Johnson.Desc.ProofFile.Honest.Thread.ChainEnds
import Johnson.Desc.ProofFile.Honest.Thread.FileD
import Johnson.Desc.ChainEndFold
import Johnson.Desc.Plain.StartThreeAtPure
import Johnson.AtFull.Shape.ReqReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (endAsks untestedButOwnL)
open VerifiableInference.Desc.K13.Honest (foldCutAt)
open VerifiableInference.Desc.Sound (MsgT)
open Desc.K14 (p14Of beforePointOf chainOf)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **The first chain's last block says yes only where its clauses hold.** -/
theorem asks_at_357 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[357]? = some b) {ft : Nat} {s s' : TS} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {n : Nat} (hy : b.step ft s rs cols = .ok (s', n)) :
    s' = s ∧ ∀ c ∈ endAsks s, c.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', -, rfl, hla⟩ := IM.seal_seated O
  obtain rfl := Option.some.inj ((IM.back_numbers h.scope h.reads O).2.symm.trans hb)
  obtain ⟨⟨rs', gs, hd⟩, -, -⟩ := IM.bare_alone_yes hla (by decide) hy
  have hd' : (VerifiableInference.Desc.ChainEnd.chainEnd (Cl := Unit) 1 5 true
      (VerifiableInference.Desc.K13.inFrontOf Zp) endAsks).decide s rs' gs = .ok s' := hd
  exact (VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff (Cl := Unit) 1 5 true
    (VerifiableInference.Desc.K13.inFrontOf Zp) endAsks s s' rs' gs).1 hd'

/-- What the first chain's end names has a number for W. -/
theorem firstEnd_w {s : TS} {e : OnBytes.Proof.FirstEnd} (he : s.firstEnd? = some e) :
    (e.lin.w != noId) = true := by
  unfold VerifiableInference.Desc.First.S.firstEnd? at he
  split at he
  · simp only [Option.bind_eq_some_iff] at he
    obtain ⟨l, -, he⟩ := he
    split at he
    · obtain rfl := Option.some.inj he
      assumption
    · cases he
  · cases he

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The clauses of the first chain's last block hold at its last border.** -/
theorem end_asks_at_first_end {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k s m
      En) :
    ∀ c ∈ endAsks s, c.2 = true := by
  unfold Thr at hT
  obtain ⟨-, -, -, -, hM, -, -⟩ := hT
  unfold Thread.Made at hM
  obtain ⟨-, -, -, -, s₀, cols, hb, -, hf⟩ := hM
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  subst hb'
  have hf0 : foldBlocks 0 (cF.blocksInOrder.take cF.blocksInOrder.length) (ProofFile.startS Zp m.st.input.x.pub) m.seen
      cols = .ok (s, [], []) := hf
  rw [List.take_length] at hf0
  have hl : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  obtain ⟨blk, hblk⟩ : ∃ blk, cF.blocksInOrder[357]? = some blk :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨sj, sj', c₀, n, -, h2, h3⟩ := foldCutAt 0 cF.blocksInOrder 357 blk hblk _ m.seen cols _ hf0
  obtain ⟨e, hc⟩ := asks_at_357 h hblk h2
  have hnil : cF.blocksInOrder.drop (357 + 1) = [] := List.drop_eq_nil_of_le (by omega)
  rw [hnil] at h3
  have es : sj' = s := by
    unfold foldBlocks at h3
    exact congrArg Prod.fst (Except.ok.inj h3)
  rw [← es, e]
  exact hc

/-- **The first chain stands at its end.** -/
theorem fin_at_first_end {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k s m
      En) : s.fin = true := by
  have ha := end_asks_at_first_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  have hm : s.failed.isNone = true := hT.2.2.1.1
  have h1 : s.closeOk = true := ha ("end: no count of claims is owed", s.closeOk) (by
    simp [endAsks])
  have h2 : (s.firstEnd?.any fun e => (s.st.oracles[e.lin.w]?).any fun x =>
      x.groups == [e.lin.own]) = true :=
    ha _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨e, he⟩ : ∃ e, s.firstEnd? = some e := by
    cases q : s.firstEnd? with
    | none => rw [q] at h2; cases h2
    | some e => exact ⟨e, rfl⟩
  have hw : (e.lin.w != noId) = true := firstEnd_w he
  show (s.failed.isNone && s.noneWaits &&
    ((s.firstEnd?.map fun e => e.lin.w != noId).getD false)) = true
  rw [hm, he]
  simp only [Bool.true_and, Option.map_some, Option.getD_some, hw, Bool.and_true]
  exact h1

end

/-- Nothing is left untested, as the two chains' last tests read it. -/
theorem untested_all (S : OnBytes.Statement)
    (hc : ∀ c ∈ VerifiableInference.Desc.ChainEnd.untestedL S, c.2 = true) :
    (S.groups.all (·.inRun) && S.oracles.all fun x => !x.sampled || !x.groups.isEmpty) = true := by
  have h1 : (S.groups.all (·.inRun)) = true := hc _ List.mem_cons_self
  have h2 : (S.oracles.all fun x => !x.sampled ||
      x.groups.any fun g => (S.groups[g]?).any (·.inRun)) = true :=
    hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [h1, Bool.true_and]
  rw [Array.all_eq_true] at h2 ⊢
  intro i hi
  have q := h2 i hi
  cases hs : (S.oracles[i]).sampled with
  | false => simp
  | true =>
    rw [hs] at q
    simp only [Bool.not_true, Bool.false_or] at q
    simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true']
    cases hg : (S.oracles[i]).groups with
    | nil => rw [hg] at q; simp at q
    | cons a l => simp

/-- **The shared chain's last block says yes only where nothing is left untested.** -/
theorem tested_of_last (front : List (Block Desc.K14.St Unit)) (d d' : Desc.K14.St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs = .ok d') :
    Desc.K14.tested d' = true := by
  obtain ⟨e, hc⟩ := (VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff (Cl := Unit) 2 11 true
    (front.flatMap (·.rounds)) (fun d : Desc.K14.St =>
      VerifiableInference.Desc.ChainEnd.untestedL d.st) d d' rs gs).1 hd
  rw [e]
  exact untested_all d.st hc

/-- **The shared chain has ended**, at a thread that stands at the chain's last border. -/
theorem tested_at_shared_end {Bk : ProverCoinCounts} {V W X Pb : Type}
    (T : Thread Bk Desc.K14.St ProofFile.Cl V W X Pb)
    (hbs : T.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) (hah : T.ahead = [])
    {k : Coins Bk} {s : Desc.K14.St} {m : Mid W X} {E : Env}
    (hM : T.Made T.bs.length k s m E) : Desc.K14.tested s = true := by
  obtain ⟨-, -, -, -, s₀, cols, -, -, hf⟩ := hM
  have hfr : T.front = 0 := by simp [Thread.front, hah]
  rw [List.take_length, hfr, List.drop_zero, hbs] at hf
  obtain ⟨l, hl⟩ : ∃ l, (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = l ++
      [{ (F0T OnBytes.secondHashFunction Zp Np cF).shared.last with
          planOk := (F0T OnBytes.secondHashFunction Zp Np cF).shared.last.planOk &&
            (F0T OnBytes.secondHashFunction Zp Np cF).shared.last.hasNoClaimsAndNothingAfter }] := ⟨_, rfl⟩
  rw [hl] at hf
  refine VerifiableInference.Desc.ChainEnd.foldBlocks_last T.ft _
    (fun d => Desc.K14.tested d = true) ?_ l _ _ _ _ hf
  intro d rs gs d' hd
  exact tested_of_last (Desc.K14.blocksOr (p14Of Zp.p.chains (beforePointOf Np)) ++
    VerifiableInference.Desc.K12.Seat.tests Np) d d' rs gs hd

section
open VerifiableInference.Desc.Third

/-- **What the last chain's own start asks**, read off its text: the shape is lawful at the codes;
the first chain's end names one row; the numbers of W, of the own group and of the mask are as the
shape says; both ends have the chain's codes; the first chain has received a root for each tree. -/
theorem start_yes_of (p : P₁₄) {Xp : Type} (x : Xp) {e₁ : TS} {fe : OnBytes.Proof.FirstEnd}
    (d : OnBytes.Proof.SharedEnd) (he : e₁.firstEnd? = some fe) {r : OnBytes.TensorRow}
    (hr : e₁.rows = [r])
    (hl : (p.codes.lengthsOk && OnBytes.linOk p.codes p.S) = true)
    (hp : (plainArm p.S && fe.lin.mask.isSome == p.S.masksAhead) = true)
    (hn : numbersOk p.S
      { st := e₁.st, book := e₁.book, roots := e₁.roots, g := r.g, w := fe.lin.w
        own := fe.lin.own, mask := fe.lin.mask } = true)
    (h₁ : e₁.st.codes = p.codes) (h₂ : d.st.codes = p.codes)
    (hb : rootsB e₁.roots e₁.book = true) :
    ∃ s, startAtEnds p x e₁ d = .ok s := by
  have hf : firstOfS e₁ = some
      { st := e₁.st, book := e₁.book, roots := e₁.roots, w := fe.lin.w
        own := fe.lin.own, mask := fe.lin.mask, pending := e₁.rows } := by
    unfold firstOfS
    rw [he]
    rfl
  show ∃ s, (match firstOfS e₁ with
    | none => .error "the first chain's end names no W"
    | some f => start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending
        (sharedOfEnd d)) = (.ok s : Except String S₃)
  rw [hf]
  show ∃ s, start₃E p.codes p.S e₁.st e₁.book e₁.roots fe.lin.w fe.lin.own fe.lin.mask e₁.rows
    (sharedOfEnd d) = .ok s
  rw [hr]
  unfold start₃E firstOutFrom
  simp only [hl, Bool.not_true, Bool.false_eq_true, if_false, hp, if_true, hn]
  have hc : (decide (e₁.st.codes = p.codes) && decide ((sharedOfEnd d).st.codes = p.codes) &&
      rootsB e₁.roots e₁.book) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h₁, h₂⟩, hb⟩
  unfold start₃
  rw [if_pos hc]
  exact ⟨_, rfl⟩

end

/-- **The last chain's last block says yes only where nothing is left untested.** -/
theorem fin₃_of_last (front : List (Block VerifiableInference.Desc.Third.S₃ Unit))
    (d d' : VerifiableInference.Desc.Third.S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hd : (VerifiableInference.Desc.Third.end₃ front).decide d rs gs = .ok d') :
    VerifiableInference.Desc.Third.fin₃ d' = true := by
  obtain ⟨e, hc⟩ := (VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff (Cl := Unit) 3 3 false
    (front.flatMap (·.rounds)) (fun d : VerifiableInference.Desc.Third.S₃ =>
      VerifiableInference.Desc.ChainEnd.untestedL d.st) d d' rs gs).1 hd
  rw [e]
  exact untested_all d.st hc

/-- **The last chain's seat says yes at that chain's last border.** -/
theorem fin₃_at_second_end {Bk : ProverCoinCounts} {V W X Pb : Type}
    (T : Thread Bk VerifiableInference.Desc.Third.S₃ ProofFile.Cl V W X Pb)
    (hbs : T.bs = (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder)
    {k : Coins Bk} {s : VerifiableInference.Desc.Third.S₃} {m : Mid W X} {E : Env}
    (hM : T.Made T.bs.length k s m E) : VerifiableInference.Desc.Third.fin₃ s = true := by
  obtain ⟨-, -, -, -, s₀, cols, -, -, hf⟩ := hM
  rw [List.take_length, hbs] at hf
  obtain ⟨l, hl⟩ : ∃ l, (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = l ++
      [{ (F0T OnBytes.secondHashFunction Zp Np cF).second.last with
          planOk := (F0T OnBytes.secondHashFunction Zp Np cF).second.last.planOk &&
            (F0T OnBytes.secondHashFunction Zp Np cF).second.last.hasNoClaimsAndNothingAfter }] := ⟨_, rfl⟩
  rw [hl] at hf
  refine VerifiableInference.Desc.ChainEnd.foldBlocks_last T.ft _
    (fun d => VerifiableInference.Desc.Third.fin₃ d = true) ?_ l _ _ _ _ hf
  intro d rs gs d' hd
  exact fin₃_of_last [] d d' rs gs hd

/-- The first chain's start, without a mark, holds the instance's words. -/
theorem start_req (Z : ProofFile.Pub) (p : ProofFile.InstPub) (h : (ProofFile.startS Z p).failed = none) :
    (ProofFile.startS Z p).req = OnBytes.Model.Verify.words32 p.request := by
  unfold ProofFile.startS at h ⊢
  dsimp only at h ⊢
  split
  · rfl
  · rename_i hq
    rw [if_neg hq] at h
    cases h

section
open VerifiableInference.Desc.Third (startAtEnds)

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X' Wt₂ : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)
  {T₂ : Thread Bk Desc.K14.St ProofFile.Cl Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop}
  {ξ : ProofFile.Inst} {k : Coins Bk}

/-- **The request's words in the first chain's last state are the instance's.** -/
theorem req_at_first_end {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k s m
      En) : s.req = OnBytes.Model.Verify.words32 m.st.input.x.pub.request := by
  have hm : s.failed = none := Option.isNone_iff_eq_none.1 hT.2.2.1.1
  have hM := hT.2.2.2.2.1
  unfold Thread.Made at hM
  obtain ⟨-, -, -, -, s₀, cols, hb, -, hf⟩ := hM
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  subst hb'
  have hf0 : foldBlocks 0 (cF.blocksInOrder.take cF.blocksInOrder.length) (ProofFile.startS Zp m.st.input.x.pub) m.seen
      cols = .ok (s, [], []) := hf
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have q := Meaning.K2.open_fold_all Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial
    (fun _ _ _ => trivial) (Johnson.AtFull.Shape.plans_at h) cF.blocksInOrder.length hf0
  have e1 : s.req = (ProofFile.startS Zp m.st.input.x.pub).req := q.1
  rw [e1]
  exact start_req Zp _ (q.2 hm)

/-- **THE FILE's LAST TEST SAYS YES**, from what no thread's clause says: hthird, the third clause of
S.finAsked. -/
theorem finYes_of_parts (hb₀ : b₀ ≤ cF.blocksInOrder.length) (hw : w₁.x = ξ)
    (hbs : T₂.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) (hah : T₂.ahead = [])
    {T₃ : Thread Bk VerifiableInference.Desc.Third.S₃ ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hb₃ : T₃.bs = (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder)
    {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop}
    (hthird : ∀ e₁ m₁ E₁,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread S₁
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length k e₁ m₁ E₁ →
      (!decide (e₁.rowE < e₁.reqT) || ξ.asked == OnBytes.Model.ofNat 0) = true) :
    FinYesS (F0T OnBytes.secondHashFunction Zp Np cF)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread T₂ T₃ S₁ S₂ S₃ ξ k := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ u₁ u₂ u₃
  have t₁ := u₁.1
  have i₁ : m₁.st.input = w₁ := t₁.2.2.2.2.2.2.1
  have hx : m₁.st.input.x = ξ := by rw [i₁]; exact hw
  have hf := fin_at_first_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ t₁
  have hr : e₁.out.reply = some m₁.st.input.x.asked :=
    ProofFile.Honest.FirstThread.head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb₀
      t₁.2.2.2.2.2.1
  rw [hx] at hr
  have hq := req_at_first_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ t₁
  rw [hx] at hq
  have hM : T₂.Made T₂.bs.length k e₂ m₂ E₂ := by
    rw [hbs]
    exact u₂.1.2.2.2.2.1
  have ht := tested_at_shared_end (Zp := Zp) (Np := Np) (cF := cF) T₂ hbs hah hM
  have hd : (Desc.K14.ended e₂).isSome = true := by
    unfold Desc.K14.ended
    rw [if_pos ht]
    rfl
  have hM₃ : T₃.Made T₃.bs.length k e₃ m₃ E₃ := by
    rw [hb₃]
    exact u₃.1.2.2.2.2.1
  have hdn := fin₃_at_second_end (Zp := Zp) (Np := Np) (cF := cF) T₃ hb₃ hM₃
  have h3 := hthird e₁ m₁ E₁ u₁
  show (e₁.finAsked ξ.asked && e₁.req == OnBytes.Model.Verify.words32 ξ.pub.request &&
    (Desc.K14.ended e₂).isSome && VerifiableInference.Desc.Third.fin₃ e₃) = true
  rw [hd, hdn, hq]
  unfold VerifiableInference.Desc.First.S.finAsked
  rw [hf, hr, h3]
  simp

/-- **THE DOOR SAYS YES**, from the last chain's own start at the two ends. -/
theorem doorYes_of_start (hbs : T₂.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
    (hah : T₂.ahead = [])
    (hstart : ∀ e₁ m₁ E₁ e₂ m₂ E₂ d,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread S₁
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k e₂ m₂ E₂ →
      Desc.K14.ended e₂ = some d → ∃ s, startAtEnds (ProofFile.pAt Zp) ξ.pub e₁ d = .ok s) :
    DoorYesS (F0T OnBytes.secondHashFunction Zp Np cF)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread T₂ S₁ S₂ ξ k := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
  have hf := fin_at_first_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ u₁.1
  have hM : T₂.Made T₂.bs.length k e₂ m₂ E₂ := by
    rw [hbs]
    exact u₂.1.2.2.2.2.1
  have ht := tested_at_shared_end (Zp := Zp) (Np := Np) (cF := cF) T₂ hbs hah hM
  obtain ⟨d, hd⟩ : ∃ d, Desc.K14.ended e₂ = some d := by
    unfold Desc.K14.ended
    rw [if_pos ht]
    exact ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := hstart e₁ m₁ E₁ e₂ m₂ E₂ d u₁ u₂ hd
  exact ⟨s, (ProofFile.fileDescBy_start₃_iff OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (ProofFile.sharedAt Zp Np)
    (P2Third.secondSeatOf Zp Np) (fun s => s) (ProofFile.startS Zp) cF ξ.pub e₁ e₂ s).2
    ⟨hf, d, hd, hs⟩⟩

end

end AtFullSide.K13

#print axioms AtFullSide.K13.doorYes_of_start
#print axioms AtFullSide.K13.start_req
#print axioms AtFullSide.K13.req_at_first_end
#print axioms AtFullSide.K13.fin₃_of_last
#print axioms AtFullSide.K13.fin₃_at_second_end
#print axioms AtFullSide.K13.finYes_of_parts
#print axioms AtFullSide.K13.start_yes_of
#print axioms AtFullSide.K13.firstEnd_w
#print axioms AtFullSide.K13.untested_all
#print axioms AtFullSide.K13.tested_of_last
#print axioms AtFullSide.K13.asks_at_357
#print axioms AtFullSide.K13.end_asks_at_first_end
#print axioms AtFullSide.K13.fin_at_first_end
#print axioms AtFullSide.K13.tested_at_shared_end
