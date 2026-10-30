-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaSeatAtEnd.lean: the linear claim's shared rounds (kind K14):
where the message Omega sits in the shared chain's last state, at an honest run: its number in the
chain's statement, its seat by the state's own book of trees, and the state's table of codes.
Statements with their proofs; no definition.

Whoever reads Omega's words off a witness of tables at the shared chain's last state (`wordsShared`,
Johnson/Desc/Sound/WordsAt.lean) reads them at the number that the state notes, at the seat that the
state's book gives that number, in the layout that the state's codes give. The library has two tests
on a state of this chain that say all three, with a law for each sub-protocol of the chain: from a
state that passes in front, an accepting decision returns a state that passes behind (`sharedX`,
Johnson/Desc/Sound/SharedX.lean; `codX`, Johnson/Desc/K14/Law/LedgerOne.lean, LedgerNew.lean). These
laws were written for the soundness proof. Here they are walked along an honest run's own fold.

  `rung_of`   one step of the walk: general in the sentence that is handed on
  `endX_of_fold12`   where the fold over the chain's twelve sub-protocols returns from the chain's
     first state, both tests accept the state returned, at border 12
  `endX_at_twelve`   so wherever a thread's invariant (`Thr`,
     Johnson/Desc/ProofFile/Honest/Thread/Thr.lean) holds at border 12
  `layU_at_head`   under the library's head h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): the trees of
     the chain's first sending can be laid
  `omega_seat_at_shared_end`   **under h, wherever the invariant of the shared chain's thread holds
     at the chain's last border, whatever the thread's other parameters are**: Omega's number is the
     number of messages of the first sending, which is 2; the state's codes are the plan's; and at
     every count t of trees in front of the chain, the state's book seats Omega at the tenant that
     the library's table of numbers gives it (`tenantSh`, Johnson/Desc/Sound/SharedMembers.lean)
  `shape_of_omegaEnd`, `point_of_omegaEnd`, `omega_written_at_shared_end`   two facts that the test
     `omegaEndB` holds; and the same in written numbers, with Omega's
     shape: number 2, the plan's shape and codes, and the tenant at the library's written layouts

Limits.
  * That the invariant holds at any state is not shown here.
  * Public book-keeping alone: numbers, places and codes. Nothing on what a message holds.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.SharedEnds
import Johnson.Desc.Sound.SharedX
import Johnson.Desc.K14.Law.LedgerNew
import Johnson.Desc.K14.Law.LedgerLast
import Johnson.Desc.K12.Law.FirstTreeOfMade
import Johnson.Desc.K12.Law.PlacesNums
import Johnson.HB.LLHARD.FiveWritten
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay TableKey layTrees)
open VerifiableInference.Desc (Block Chain OpenedColumn Place foldBlocks)
open VerifiableInference.Desc.Shared (NumbersS MeaningS Msg2)
open VerifiableInference.Desc.Sound (seatBy noShared)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St first p14Of beforePointOf withU withOmega)
open Desc.K14.Honest (Like FlatAt Eight)
open Desc.K14.Law (codX codX_iff codX_first codX_front codX_k14 codX_onGu codX_onGomega codX_codes
  seat_at_last)
open Desc.K14.Law.Fence (sharedX sharedX_first sharedX_front sharedX_k14 sharedX_onGu
  sharedX_onGomega sharedX_end sharedX_twelve tenantSh)

/-- One step of the walk. X: the sentence that is handed on, border by border. -/
theorem rung_of {Cl : Type} {xs : List (Block St Cl)} {X : Nat → St → Prop} {ft k : Nat}
    {x : Block St Cl} {b : Block St Unit} {d0 : St} (hx : xs[k]? = some x) (hl : Like x b)
    (step : ∀ d d' rs gs, b.decide d rs gs = .ok d' → X k d → X (k + 1) d')
    (prev : ∀ s rs rs' cl cl', foldBlocks ft (xs.take k) d0 rs cl = .ok (s, rs', cl') → X k s) :
    ∀ s rs rs' cl cl', foldBlocks ft (xs.take (k + 1)) d0 rs cl = .ok (s, rs', cl') →
      X (k + 1) s := by
  intro s rs rs' cl cl' h
  obtain ⟨t, _, _, hf, _, _, kd⟩ := fold_rung hx h
  rw [hl.decide] at kd
  exact step _ _ _ _ kd (prev _ _ _ _ _ hf)

section run
variable {P : P14} {sentU : Array OracleNotice} {layU layO : TreeLay} {B : Eight P} {ft : Nat}
  {Cl : Type} {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {p₉ p₁₀ : P12}
  {front : List (Block St Unit)}

/-- **Where the fold over the twelve sub-protocols returns from the chain's first state, both tests
accept the state returned.** hU, hlU, hlO, hS, hm, f₉, f₁₀: facts on the plan. -/
theorem endX_of_fold12 (F : FlatAt xs c B) (Tl : TailAt xs p₉ p₁₀ front)
    (hU : withU P.S = some sentU) (hlU : layTrees P.codes sentU = some layU)
    (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (hS : P.par.S.sharedSplitNeeded = true) (hm : P.par.S.masksAhead = true)
    (f₉ : p₉.nums.firstTree = P.par.toGPar.firstTree)
    (f₁₀ : p₁₀.nums.firstTree = P.par.toGPar.firstTree) (key : TableKey) :
    ∀ s rs rs' cl cl', foldBlocks ft (xs.take 12) (first P.codes key) rs cl = .ok (s, rs', cl') →
      sharedX P sentU layU layO 12 s = true ∧ codX P 12 s = true := by
  obtain ⟨x9, h9, l9⟩ := Tl.nine
  obtain ⟨x10, h10, l10⟩ := Tl.ten
  obtain ⟨x11, h11, l11⟩ := Tl.eleven
  have e₉ := H2K.JointK.early_of_planOk p₉ Tl.plan₉
  have a₉ := H2K.JointK.answers_of_planOk p₉ Tl.plan₉
  have e₁₀ := H2K.JointK.early_of_planOk p₁₀ Tl.plan₁₀
  have a₁₀ := H2K.JointK.answers_of_planOk p₁₀ Tl.plan₁₀
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have k14 : ∀ (i : Nat) (b : Block St Unit),
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8][i]? = some b → ∀ d d' rs gs,
      b.decide d rs gs = .ok d' →
      (sharedX P sentU layU layO (i + 1) d = true ∧ codX P (i + 1) d = true) →
      (sharedX P sentU layU layO (i + 1 + 1) d' = true ∧ codX P (i + 1 + 1) d' = true) :=
    fun i b hb d d' rs gs h a =>
      ⟨sharedX_k14 P _ _ _ _ _ _ _ _ B.made sentU hU layU layO hlU hlO hS hm i b hb d d' rs gs h
          a.1,
        codX_k14 P _ _ _ _ _ _ _ _ B.made b (List.mem_of_getElem? hb) _ _ d d' rs gs h a.2⟩
  have r0 : ∀ s rs rs' cl cl',
      foldBlocks ft ((x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).take 0)
        (first P.codes key) rs cl = .ok (s, rs', cl') →
      (sharedX P sentU layU layO 0 s = true ∧ codX P 0 s = true) := by
    intro s rs rs' cl cl' h
    obtain rfl : first P.codes key = s := congrArg Prod.fst (Except.ok.inj h)
    exact ⟨sharedX_first P sentU layU layO P.codes key, codX_first P key⟩
  have r1 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 0) rfl l0 (fun d d' rs gs h a => ⟨sharedX_front P sentU layU layO c d d' rs gs h a.1,
      codX_front P c d d' rs gs h a.2⟩) r0
  have r2 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 1) rfl l1 (k14 0 B.b1 rfl) r1
  have r3 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 2) rfl l2 (k14 1 B.b2 rfl) r2
  have r4 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 3) rfl l3 (k14 2 B.b3 rfl) r3
  have r5 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 4) rfl l4 (k14 3 B.b4 rfl) r4
  have r6 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 5) rfl l5 (k14 4 B.b5 rfl) r5
  have r7 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 6) rfl l6 (k14 5 B.b6 rfl) r6
  have r8 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 7) rfl l7 (k14 6 B.b7 rfl) r7
  have r9 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 8) rfl l8 (k14 7 B.b8 rfl) r8
  have r10 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 9) h9 l9 (fun d d' rs gs h a =>
      ⟨sharedX_onGu P sentU layU layO p₉ f₉ e₉ a₉ d d' rs gs h a.1,
        codX_onGu P p₉ e₉ a₉ _ _ d d' rs gs h a.2⟩) r9
  have r11 := rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 10) h10 l10 (fun d d' rs gs h a =>
      ⟨sharedX_onGomega P sentU layU layO p₁₀ f₁₀ e₁₀ a₁₀ d d' rs gs h a.1,
        codX_onGomega P p₁₀ e₁₀ a₁₀ _ _ d d' rs gs h a.2⟩) r10
  exact rung_of (X := fun k d => sharedX P sentU layU layO k d = true ∧ codX P k d = true)
    (k := 11) h11 l11 (fun d d' rs gs h a => by
      obtain ⟨rfl, -⟩ := closing_same front d d' rs gs h
      exact ⟨sharedX_end P sentU layU layO _ a.1, codX_codes P 11 12 _ _ rfl a.2⟩) r11

end run

section thread
variable {Bk : ProverCoinCounts} {Cl V Wt X Pb : Type} {Q : P14} {sentU : Array OracleNotice}
  {layU layO : TreeLay} {T : Thread Bk St Cl V Wt X Pb} {c : OnBytes.Model.Verify.Chains}
  {key : Wt → TableKey} {p₉ p₁₀ : P12} {front : List (Block St Unit)}

/-- **So wherever a thread's invariant holds at border 12.** -/
theorem endX_at_twelve (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) (hlU : layTrees Q.codes sentU = some layU)
    (f₉ : p₉.nums.firstTree = Q.par.toGPar.firstTree)
    (f₁₀ : p₁₀.nums.firstTree = Q.par.toGPar.firstTree)
    {k : Coins Bk} {s : St} {m : Mid Wt X} {E : Env} (hA : Thr T 12 k s m E) :
    sharedX Q sentU layU layO 12 s = true ∧ codX Q 12 s = true := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  exact endX_of_fold12 (hT.bs B) hL hQ.facts.goes hlU hQ.facts.trees hQ.facts.two hQ.facts.ahead f₉
    f₁₀ (key m.st.input) s _ _ _ _ hfold

end thread

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head the trees of the chain's first sending can be laid.** -/
theorem layU_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {sentU : Array OracleNotice}
    (hU : withU (p14Of Zp.p.chains (beforePointOf Np)).S = some sentU) :
    ∃ layU, layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes sentU = some layU := by
  have hs : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made h.toAtMg.made_accepts)
  have e : (layTrees Zp.p.chains.made.sized.proof.codes
      ((withU Zp.p.chains.made.sized.proof.batch.shape).getD #[])).isSome = true := by
    rw [hs, VerifiableInference.PlanWritten.codes_written]
    exact Desc.K14.Law.lays_written.2.1
  have e' : (withU Zp.p.chains.made.sized.proof.batch.shape).getD #[] = sentU := by
    have hU' : withU Zp.p.chains.made.sized.proof.batch.shape = some sentU := hU
    rw [hU']
    rfl
  rw [e'] at e
  exact Option.isSome_iff_exists.1 e

section letters
variable (Zp Np cF) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **Where Omega sits at the shared chain's last border**, wherever the thread's invariant holds
there, under the library's head, whatever the thread's other parameters are. sentU, layU, layO: what
the chain's first sending sends, and how the two sendings' trees are laid: the plan's. -/
theorem omega_seat_at_shared_end (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E) :
    ∃ sentU layU layO, Plan2 (p14Of Zp.p.chains (beforePointOf Np)) sentU layO ∧
      layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes sentU = some layU ∧
      s₂.loc.oOmega = sentU.size ∧ sentU.size = 2 ∧
      s₂.st.codes = (p14Of Zp.p.chains (beforePointOf Np)).codes ∧
      ∀ t, seatBy (noShared t) s₂.book s₂.loc.oOmega = some (tenantSh t layU layO .oOmega) := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨layU, hlU⟩ := layU_at_head h hQ.facts.goes
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope h.scope Zp ProofFile.pureRoad.links Np cF
    h.laid.planOk (LPFD.asks_written h.laid.asks)
  obtain ⟨B⟩ := hQ.eight
  rw [shared_twelve Zp Np cF B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made] at hA
  obtain ⟨h9, h10⟩ := plans_at_shared Zp Np cF nO hO h.laid.planOk
  have pf := H2K.Made.places_firstTree Zp.made Np h.laid.places
  have f₉ : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U).nums.firstTree = 0 :=
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ Np.U h9)).trans pf.2.1
  have f₁₀ : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.firstTree = 0 :=
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO h10)).trans
      (pf.2.2.1 nO hO)
  obtain ⟨hX, hC⟩ := endX_at_twelve hQ
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
    (tailAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w B.b1
      B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made h9 h10) hlU f₉ f₁₀ hA
  have hO2 : 0 < (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S).size := by
    have e2 : (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S).size = 2 :=
      (Desc.K14.Honest.withOmega_two hQ.facts.two).1
    rw [e2]
    exact Nat.succ_pos _
  have hn := (sharedX_twelve _ sentU layU layO s₂ hO2 hX).2.1
  refine ⟨sentU, layU, layO, hQ, hlU, hn, hQ.facts.goesTwo, (codX_iff _ 12 s₂).1 hC, fun t => ?_⟩
  rw [hn, seat_at_last _ sentU layU layO s₂ hO2 hX t]
  show some (t + (0 + (layU.shapes.size + layO.tree.getD 0 0)), layO.part.getD 0 0) =
    some (t + layU.shapes.size + layO.tree.getD 0 0, layO.part.getD 0 0)
  rw [Nat.zero_add, Nat.add_assoc]

/-- Omega's entry in the statement has the plan's shape, where the test `omegaEndB`
(Johnson/Desc/ProofFile/Honest/K14/OmegaEnd.lean) accepts. -/
theorem shape_of_omegaEnd {S : OnBytes.Params.LinShape} {d : St} (h : omegaEndB S d = true) :
    (d.st.oracles[d.loc.oOmega]?).map (·.shape) = some S.omega := by
  unfold omegaEndB at h
  rw [Bool.and_eq_true] at h
  have h := h.1
  unfold omegaEndL at h
  have e0 : (VerifiableInference.Desc.Third.Law.oOf d).book.place[
      (VerifiableInference.Desc.Third.Law.oOf d).omega]? = d.book.place[d.loc.oOmega]? := rfl
  rw [e0] at h
  cases hq : d.book.place[d.loc.oOmega]? with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    dsimp only at h
    have f0 : (VerifiableInference.Desc.Third.Law.oOf d).book.trees[q.1]? = d.book.trees[q.1]? :=
      rfl
    rw [f0] at h
    cases ht : d.book.trees[q.1]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      dsimp only at h
      have g0 : (VerifiableInference.Desc.Third.Law.oOf d).st.oracles[
          (VerifiableInference.Desc.Third.Law.oOf d).omega]? = d.st.oracles[d.loc.oOmega]? := rfl
      rw [g0] at h
      cases hy : d.st.oracles[d.loc.oOmega]? with
      | none => rw [hy] at h; cases h
      | some y =>
        rw [hy] at h
        simp only [VerifiableInference.Desc.Ground.ok, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true, decide_eq_true_eq] at h
        show some y.shape = some S.omega
        rw [h.2.1]

/-- The shared point has as many coordinates as a column's number has bits, where `omegaEndB`
accepts. -/
theorem point_of_omegaEnd {S : OnBytes.Params.LinShape} {d : St} (h : omegaEndB S d = true) :
    d.loc.psiSh.length = S.kCol := by
  unfold omegaEndB at h
  rw [Bool.and_eq_true] at h
  have h := h.1
  unfold omegaEndL at h
  have e0 : (VerifiableInference.Desc.Third.Law.oOf d).book.place[
      (VerifiableInference.Desc.Third.Law.oOf d).omega]? = d.book.place[d.loc.oOmega]? := rfl
  rw [e0] at h
  cases hq : d.book.place[d.loc.oOmega]? with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    dsimp only at h
    have f0 : (VerifiableInference.Desc.Third.Law.oOf d).book.trees[q.1]? = d.book.trees[q.1]? :=
      rfl
    rw [f0] at h
    cases ht : d.book.trees[q.1]? with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      dsimp only at h
      have g0 : (VerifiableInference.Desc.Third.Law.oOf d).st.oracles[
          (VerifiableInference.Desc.Third.Law.oOf d).omega]? = d.st.oracles[d.loc.oOmega]? := rfl
      rw [g0] at h
      cases hy : d.st.oracles[d.loc.oOmega]? with
      | none => rw [hy] at h; cases h
      | some y =>
        rw [hy] at h
        simp only [VerifiableInference.Desc.Ground.ok, List.all_cons, List.all_nil, Bool.and_true,
          Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        exact h.2.2.2

/-- **The same in written numbers**: at the shared chain's last border Omega is message number 2; it
has the plan's shape; the state's codes are the plan's; and at every count t of trees in front of
the chain the state's book seats it at the tenant that the library's table gives it at the written
layouts. -/
theorem omega_written_at_shared_end (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E) :
    s₂.loc.oOmega = 2 ∧ s₂.st.codes = (p14Of Zp.p.chains (beforePointOf Np)).codes ∧
      (s₂.st.oracles[2]?).map (·.shape) = some (p14Of Zp.p.chains (beforePointOf Np)).S.omega ∧
      ∀ t, seatBy (noShared t) s₂.book 2 =
        some (tenantSh t Desc.K14.Law.layUFull Desc.K14.Law.layOFull .oOmega) := by
  obtain ⟨sentU, layU, layO, hQ, hlU, hn, h2, hc, hseat⟩ :=
    omega_seat_at_shared_end Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
      w h hA
  have hs : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made h.toAtMg.made_accepts)
  have hU' : withU Zp.p.chains.made.sized.proof.batch.shape = some sentU := hQ.facts.goes
  have hlU' : layTrees Zp.p.chains.made.sized.proof.codes sentU = some layU := hlU
  have hlO' : layTrees Zp.p.chains.made.sized.proof.codes
      (withOmega Zp.p.chains.made.sized.proof.batch.shape) = some layO := hQ.facts.trees
  rw [hs] at hU' hlU' hlO'
  rw [VerifiableInference.PlanWritten.codes_written] at hlU' hlO'
  have eS : Desc.K14.Law.sentUFull = sentU := by
    unfold Desc.K14.Law.sentUFull Desc.K14.Law.shFull
    rw [hU']
    rfl
  have eU : Desc.K14.Law.layUFull = layU := by
    unfold Desc.K14.Law.layUFull
    rw [eS, hlU']
    rfl
  have eO : Desc.K14.Law.layOFull = layO := by
    unfold Desc.K14.Law.layOFull Desc.K14.Law.shFull
    rw [hlO']
    rfl
  have e2 : s₂.loc.oOmega = 2 := hn.trans h2
  have hsh := shape_of_omegaEnd (omega_at_shared_end Zp Np cF H N Mg shape nothingLeft order wit
    table fixed n₁ n₂ Vd Rd Kp w h hA).1
  rw [e2] at hsh
  refine ⟨e2, hc, hsh, fun t => ?_⟩
  rw [eU, eO, ← e2]
  exact hseat t

end letters

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.rung_of
#print axioms ProofFile.Honest.K14.endX_of_fold12
#print axioms ProofFile.Honest.K14.endX_at_twelve
#print axioms ProofFile.Honest.K14.layU_at_head
#print axioms ProofFile.Honest.K14.omega_seat_at_shared_end
#print axioms ProofFile.Honest.K14.shape_of_omegaEnd
#print axioms ProofFile.Honest.K14.point_of_omegaEnd
#print axioms ProofFile.Honest.K14.omega_written_at_shared_end
