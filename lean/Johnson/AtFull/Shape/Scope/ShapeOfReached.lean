-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ShapeOfReached.lean: THE SHAPE OF A REACHED STATE OF THE FIRST CHAIN IS THE TABLE's AT
THAT BORDER, WITH NO FAMILY J AND NO SILENCE OF A STOP OR A FALL. A joining; nothing is evaluated.

* ReqPasses Zp p: the request at p passes.
* Weak, weak_cases: the members at which the table has only CarriesV: 14 l + 9 (l < 24) and 347.
* **BlockYesGivesVals**: THE ONE NAMED PREMISE: at those members, at a state reached from a start at z
  with Q z, a yes of the member's own step gives the table's tests on values at that step's rounds and
  columns. No coin, no prover.
* carries_or: at every member the strong Carries, or the member is Weak and CarriesU holds.
* reach_start: Reach from one state start z is Reach from the function start at z.
* **shape_of_reached**: under the head, baseOf's return, hyes and that premise: at a state reached from
  ProofFile.startS Zp at a request that passes, the family shapeJ holds.
* **shape_of_thr**: the same at a thread's invariant at ft = 0: Thr ⊢ shapeJ.

Limits. BlockYesGivesVals is a premise: nothing here shows it, and it may fail. hyes stays a premise
(yes_of_pieces_in_scope gives it from RunsAll's pieces). hbeg is the caller's. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ReachHeld
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)

/-- The request at p passes. -/
def ReqPasses (Zp : ProofFile.Pub) (p : ProofFile.InstPub) : Prop :=
  (Zp.s₀.withReq (Verify.words32 p.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true

/-- The members at which the table has CarriesV alone. -/
def Weak (j : Nat) : Prop := j < 358 ∧ framed j = false

/-- They are the batchings. -/
theorem weak_cases {j : Nat} (h : Weak j) : (∃ l, l < 24 ∧ j = 14 * l + 9) ∨ j = 347 := by
  obtain ⟨hj, hf⟩ := h
  have k : framedV j = true := List.all_eq_true.1 framedV_all j (List.mem_range.2 hj)
  unfold framedV at k
  rw [hf] at k
  simp only [Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at k
  rcases k with ⟨h1, h2⟩ | k
  · exact Or.inl ⟨(j - 1) / 14, by omega, by omega⟩
  · exact Or.inr k

/-- **THE ONE NAMED PREMISE.** -/
def BlockYesGivesVals {P : Type} (Zs : Shape S) (ft : Nat) (bs : List (Block S ProofFile.Cl))
    (start : P → S) (Q : P → Prop) : Prop :=
  ∀ b, Weak b → ∀ z, Q z → ∀ (blk : Block S ProofFile.Cl) (s : S) (R : List Fmt.RoundView) (c : List OpenedColumn)
    (s' : S), Reach ft bs start b (z, s) → bs[b]? = some blk →
    R.length = blk.rounds.length → blk.step ft s R c = .ok (s', c.length) →
    Zs.vals b s (R.map noDigest) (blk.shown ft R c) = true

/-- Reach from one state start z is Reach from the function start at z. -/
theorem reach_start {P σ Cl : Type} {ft : Nat} {bs : List (Block σ Cl)} {start : P → σ} (z : P)
    {b : Nat} {a : Unit × σ} (h : Reach ft bs (fun _ : Unit => start z) b a) :
    Reach ft bs start b (z, a.2) := by
  induction h with
  | zero u => exact Reach.zero z
  | succ _ hb hy ih => exact Reach.succ ih hb hy

/-- From the premise, every reached state is reached with the values held. -/
theorem held_of_reach {P : Type} {Zs : Shape S} {ft : Nat} {bs : List (Block S ProofFile.Cl)}
    {start : P → S} {Q : P → Prop} (hL : BlockYesGivesVals Zs ft bs start Q) {b : Nat} {a : P × S}
    (hq : Q a.1) (h : Reach ft bs start b a) : ReachHeld Zs ft bs start Weak b a := by
  induction h with
  | zero z => exact ReachHeld.zero z
  | succ r hb hy ih =>
    obtain ⟨R, c, hR, hs⟩ := hy
    exact ReachHeld.succ (ih hq) hb hR hs fun hu => hL _ hu _ hq _ _ _ _ _ r hb hR hs

/-- The general step: a run that returns at n and a state reached with the values held. -/
theorem shapeJ_of_held {P : Type} (Zs : Shape S) {ft : Nat} {bs : List (Block S ProofFile.Cl)}
    {start : P → S} {U : Nat → Prop} (hC : ∀ j, Carries bs ft Zs j ∨ (U j ∧ CarriesU bs ft Zs j))
    {a₀ : Zs.Sh} {n b : Nat} {a : P × S} (hh : ReachHeld Zs ft bs start U b a)
    (hyes : Zs.yes a₀ n = true) (hb : b ≤ n) (e0 : Zs.sh (start a.1) = a₀) :
    shapeJ Zs a₀ b a.2 := by
  obtain ⟨e, he⟩ := run_front Zs a₀ n b hb hyes
  have e1 := shape_reachU Zs hC hh e (by rw [e0]; exact he)
  show Zs.run b a₀ = .ok (Zs.sh a.2)
  rw [he, e1]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- At every member the strong Carries, or the member is one of the 25 with CarriesU. -/
theorem carries_or (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (ft j : Nat) :
    Carries cF.blocksInOrder ft (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) j ∨
      (Weak j ∧ CarriesU cF.blocksInOrder ft (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) j) := by
  by_cases hj : j < 358
  · cases hf : framed j with
    | false => exact Or.inr ⟨⟨hj, hf⟩, carriesU_of_V (table_all h hB j hj ft).1⟩
    | true => exact Or.inl (table_frames h hB j hf ft).1
  · refine Or.inl fun blk hb => ?_
    have e : cF.blocksInOrder[j]? = none := List.getElem?_eq_none (by rw [flat_len h]; omega)
    rw [e] at hb
    cases hb

/-- **THE SHAPE OF A REACHED STATE.** -/
theorem shape_of_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (ft : Nat)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true)
    (hL : BlockYesGivesVals (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) ft cF.blocksInOrder
      (ProofFile.startS Zp) (ReqPasses Zp))
    {z : ProofFile.InstPub} (hq : ReqPasses Zp z) {b : Nat} (hb : b ≤ 358) {s : S}
    (hr : Reach ft cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) :
    shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA b s := by
  have hh : ReachHeld (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) ft cF.blocksInOrder (ProofFile.startS Zp) Weak
      b (z, s) := held_of_reach (Q := ReqPasses Zp) (a := (z, s)) hL hq hr
  have e0 : shA (ProofFile.startS Zp z) = startShA := start_shA h z hq
  exact shapeJ_of_held (a := (z, s)) (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀))
    (carries_or h hB ft) hh hyes hb e0

/-- **AT A THREAD's INVARIANT: NO FAMILY J AS A PREMISE.** -/
theorem shape_of_thr (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true)
    (hL : BlockYesGivesVals (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) 0 cF.blocksInOrder
      (ProofFile.startS Zp) (ReqPasses Zp))
    (hbeg : ∀ k w hh s₀, T.valid w → T.begun k w hh s₀ →
      ∃ p, s₀ = ProofFile.startS Zp p ∧ ReqPasses Zp p)
    {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (hb : b ≤ 358)
    (hA : Thr T b k s m E) :
    shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA b s := by
  unfold Thr Thread.Made at hA
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hg, -, hf⟩, -, hval⟩ := hA
  have hr : Reach T.ft T.bs (fun _ : Unit => s₀) b ((), s) :=
    reach_of_fold b (by rw [hbs, flat_len h]; exact hb) s _ _ _ _ hf
  rw [hbs, hft] at hr
  obtain ⟨p, rfl, hq⟩ := hbeg _ _ _ _ hval hg
  exact shape_of_reached h hB 0 hyes hL hq hb (reach_start p hr)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.weak_cases
#print axioms Johnson.AtFull.Shape.Scope.reach_start
#print axioms Johnson.AtFull.Shape.Scope.held_of_reach
#print axioms Johnson.AtFull.Shape.Scope.carries_or
#print axioms Johnson.AtFull.Shape.Scope.shape_of_reached
#print axioms Johnson.AtFull.Shape.Scope.shape_of_thr
