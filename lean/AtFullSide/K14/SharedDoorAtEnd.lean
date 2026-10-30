-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K14/SharedDoorAtEnd.lean: kind K14: at the full size, wherever the invariant of the
shared chain's honest thread holds at that chain's last border and the state's statement is in
order: the five tests that the last chain's form at its first border makes on the shared chain's end
(sharedDoorB, Johnson/Desc/Last/ShapeDoor.lean) all say yes, of whatever Desc.K14.ended returns at
that state. That it returns there is ended_at_shared_end (Honest/K14/SharedEnds.lean), under the
same premises. One abbreviation, no other definition; statements with their proofs.

The five tests: the last statement is in order; the book of trees fits; in that book Omega is part 0
of its tree; Omega is there with the plan's shape; Omega has one sample row.

How. The thread's invariant says that the state is what the chain's twelve sub-protocols' decide
functions return, one after the other, from the chain's first state. The library's soundness side
has, for each sub-protocol, a law that hands a public test on the state from one border to the next:
for the book-keeping of seats and members (sharedX), the codes (codX), "Omega has its shape, its
mark and as many sample rows as answers" (omY) and "the book fits" (fitsX). This file walks the
twelve with all four, as endX_of_fold12 (Honest/K14/OmegaSeatAtEnd.lean) does with the first two,
and then calls the library's doorSharedB_of_parts, door_two_three and sharedDoor_of_text.

  fourX               the four tests at a border, as one sentence (an abbreviation); fourX_mk,
                      fourX_parts: into it and out of it
  four_of_fold12      where the fold over the twelve returns from the chain's first state, the four
                      hold of the state returned
  four_at_twelve      so wherever a thread's invariant holds at the border 12
  omega_one_answer    at the full size the plan's shape of Omega has one answer: from
                      omega_one_answer_written, an evaluation at the written sizes
  door_of_four        from the four and "in order": the library's text doorSharedB
  shared_door_at_end  **the statement**, at every p whose shape of Omega is the plan's
  shared_door_pAt     at the last chain's own public parameters ProofFile.pAt Zp
  shared_door_ordered the same at a thread whose letter order gives "in order": then the invariant
                      alone is asked

Premises of shared_door_at_end beside hp (p's shape of Omega is the plan's): h (the library's
hypothesis at the full size, P5J.AtMgA, Johnson/P5J/MgAtAll.lean, at the hash OnBytes.secondHashFunction); hA
(the invariant holds at the last border); hI (the statement is in order: at a thread whose letter
order is OnBytes.Means.InOrder of the statement it is a clause of hA: shared_door_ordered). NONE IS
SHOWN HERE.

Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean).

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaSeatAtEnd
import Johnson.Desc.K14.Law.LedgerNineTen
import Johnson.Desc.Sound.BookFitsCarried
import Johnson.Desc.Last.ShapeDoorParts
import Johnson.Desc.Last.ShapeDoorAtTexts
import Johnson.Desc.Plain.StartThreeAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open OnBytes (OracleNotice TreeLay TableKey layTrees)
open VerifiableInference.Desc (Block Chain OpenedColumn Place foldBlocks)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Third (P₁₄ sharedOfEnd)
open VerifiableInference.Desc.Last (doorSharedB sharedDoorB doorSharedB_of_parts
  sharedDoor_of_text)
open Desc.K14 (P14 St first p14Of beforePointOf withU withOmega)
open Desc.K14.Honest (Like FlatAt Eight)
open Desc.K14.Law
open Desc.K14.Law.Fence
open ProofFile.Honest ProofFile.Honest.K14

/-- The four public tests at the border k, as one sentence. sh: Omega's shape; the number at which
Omega is looked for is the number of messages of the chain's first sending; up to the border 5 the
test on Omega asks nothing. The test on the codes is taken along for later callers: nothing in this
file spends it. -/
abbrev fourX (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
    (sh : OnBytes.OracleShape) (k : Nat) (d : St) : Prop :=
  ((sharedX P sentU layU layO k d && codX P k d) && omY sh sentU.size k d) = true ∧
    fitsX k d = true

/-- Into the abbreviation. -/
theorem fourX_mk {P : P14} {sentU : Array OracleNotice} {layU layO : TreeLay}
    {sh : OnBytes.OracleShape} {k : Nat} {d : St} (a : sharedX P sentU layU layO k d = true)
    (b : codX P k d = true) (c : omY sh sentU.size k d = true) (e : fitsX k d = true) :
    fourX P sentU layU layO sh k d :=
  ⟨by rw [a, b, c]; rfl, e⟩

/-- Out of the abbreviation. -/
theorem fourX_parts {P : P14} {sentU : Array OracleNotice} {layU layO : TreeLay}
    {sh : OnBytes.OracleShape} {k : Nat} {d : St} (h : fourX P sentU layU layO sh k d) :
    sharedX P sentU layU layO k d = true ∧ codX P k d = true ∧ omY sh sentU.size k d = true ∧
      fitsX k d = true := by
  obtain ⟨x, e⟩ := h
  obtain ⟨y, c⟩ := Bool.and_eq_true_iff.1 x
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 y
  exact ⟨a, b, c, e⟩

section run
variable {P : P14} {sentU : Array OracleNotice} {layU layO : TreeLay} {B : Eight P} {ft : Nat}
  {Cl : Type} {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {p₉ p₁₀ : P12}
  {front : List (Block St Unit)}

/-- **Where the fold over the twelve sub-protocols returns from the chain's first state, the four
tests accept the state returned.** The premises beside F and Tl are facts on the plan. -/
theorem four_of_fold12 (F : FlatAt xs c B) (Tl : TailAt xs p₉ p₁₀ front)
    (hU : withU P.S = some sentU) (hlU : layTrees P.codes sentU = some layU)
    (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (hS : P.par.S.sharedSplitNeeded = true) (hm : P.par.S.masksAhead = true)
    (f₉ : p₉.nums.firstTree = P.par.toGPar.firstTree)
    (f₁₀ : p₁₀.nums.firstTree = P.par.toGPar.firstTree) (h2 : sentU.size = 2)
    (h0 : 0 < (shapesOf (parO P)).length) (hk : sampledAt (parO P) ⟨0, h0⟩) (key : TableKey) :
    ∀ s rs rs' cl cl', foldBlocks ft (xs.take 12) (first P.codes key) rs cl = .ok (s, rs', cl') →
      fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩) 12 s := by
  obtain ⟨x9, h9, l9⟩ := Tl.nine
  obtain ⟨x10, h10, l10⟩ := Tl.ten
  obtain ⟨x11, h11, l11⟩ := Tl.eleven
  have e₉ := H2K.JointK.early_of_planOk p₉ Tl.plan₉
  have a₉ := H2K.JointK.answers_of_planOk p₉ Tl.plan₉
  have e₁₀ := H2K.JointK.early_of_planOk p₁₀ Tl.plan₁₀
  have a₁₀ := H2K.JointK.answers_of_planOk p₁₀ Tl.plan₁₀
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have hA := (handsOn_sharedX P _ _ _ _ _ _ _ _ B.made sentU hU layU layO hlU hlO hS hm).and
    (handsOn_codX P _ _ _ _ _ _ _ _ B.made)
  have hB := hands_omY P _ _ _ _ _ _ _ _ B.made _ hA sentU.size (fun d hd =>
    ((membX45 sentU.size d 5 (.inr rfl)).1
      ((sharedX_parts P sentU layU layO 5 d).1 (Bool.and_eq_true_iff.1 hd).1).2.2.1).2.2.2.1) h0 hk
  have k14 : ∀ (i : Nat) (b : Block St Unit), 1 ≤ i →
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8][i]? = some b → ∀ d d' rs gs,
      b.decide d rs gs = .ok d' →
      fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩) (i + 1) d →
      fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩) (i + 1 + 1) d' :=
    fun i b hi hb d d' rs gs h a =>
      ⟨hB.step i b hi hb d d' rs gs h a.1,
        fitsX_k14 P _ _ _ _ _ _ _ _ B.made b (List.mem_of_getElem? hb) _ _ d d' rs gs h a.2⟩
  have r0 : ∀ s rs rs' cl cl',
      foldBlocks ft ((x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).take 0)
        (first P.codes key) rs cl = .ok (s, rs', cl') →
      fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩) 0 s := by
    intro s rs rs' cl cl' h
    obtain rfl : first P.codes key = s := congrArg Prod.fst (Except.ok.inj h)
    exact fourX_mk (sharedX_first P sentU layU layO P.codes key) (codX_first P key)
      ((omY_iff _ _ 0 _).2 (Or.inl (by omega))) (fitsX_first P.codes key)
  have r1 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 0) rfl l0 (fun d d' rs gs h a => by
      obtain ⟨a1, a2, -, a4⟩ := fourX_parts a
      exact fourX_mk (sharedX_front P sentU layU layO c d d' rs gs h a1)
        (codX_front P c d d' rs gs h a2) ((omY_iff _ _ 1 _).2 (Or.inl (by omega)))
        (fitsX_front c d d' rs gs h a4)) r0
  have r2 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 1) rfl l1 (fun d d' rs gs h a => by
      obtain ⟨a1, a2, -, a4⟩ := fourX_parts a
      exact fourX_mk
        (sharedX_k14 P _ _ _ _ _ _ _ _ B.made sentU hU layU layO hlU hlO hS hm 0 B.b1 rfl d d' rs gs
          h a1)
        (codX_k14 P _ _ _ _ _ _ _ _ B.made B.b1 (by simp) _ _ d d' rs gs h a2)
        ((omY_iff _ _ 2 _).2 (Or.inl (by omega)))
        (fitsX_k14 P _ _ _ _ _ _ _ _ B.made B.b1 (by simp) _ _ d d' rs gs h a4)) r1
  have r3 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 2) rfl l2 (k14 1 B.b2 (by omega) rfl) r2
  have r4 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 3) rfl l3 (k14 2 B.b3 (by omega) rfl) r3
  have r5 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 4) rfl l4 (k14 3 B.b4 (by omega) rfl) r4
  have r6 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 5) rfl l5 (k14 4 B.b5 (by omega) rfl) r5
  have r7 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 6) rfl l6 (k14 5 B.b6 (by omega) rfl) r6
  have r8 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 7) rfl l7 (k14 6 B.b7 (by omega) rfl) r7
  have r9 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 8) rfl l8 (k14 7 B.b8 (by omega) rfl) r8
  have r10 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 9) h9 l9 (fun d d' rs gs h a => by
      obtain ⟨a1, a2, a3, a4⟩ := fourX_parts a
      have hmk : d.loc.firstMask ≠ some sentU.size := by
        rw [(membX_nine sentU.size d ((sharedX_parts P sentU layU layO 9 d).1 a1).2.2.1).2, h2]
        decide
      exact fourX_mk (sharedX_onGu P sentU layU layO p₉ f₉ e₉ a₉ d d' rs gs h a1)
        (codX_onGu P p₉ e₉ a₉ _ _ d d' rs gs h a2) (omY_onGu _ _ p₉ e₉ a₉ d d' rs gs h hmk a3)
        (fitsX_onGu p₉ e₉ a₉ _ _ d d' rs gs h a4)) r9
  have r11 := rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 10) h10 l10 (fun d d' rs gs h a => by
      obtain ⟨a1, a2, a3, a4⟩ := fourX_parts a
      exact fourX_mk (sharedX_onGomega P sentU layU layO p₁₀ f₁₀ e₁₀ a₁₀ d d' rs gs h a1)
        (codX_onGomega P p₁₀ e₁₀ a₁₀ _ _ d d' rs gs h a2)
        (omY_onGomega _ _ p₁₀ e₁₀ a₁₀ d d' rs gs h a3)
        (fitsX_onGomega p₁₀ e₁₀ a₁₀ _ _ d d' rs gs h a4)) r10
  exact rung_of (X := fourX P sentU layU layO (shapeAt (parO P) ⟨0, h0⟩))
    (k := 11) h11 l11 (fun d d' rs gs h a => by
      obtain ⟨rfl, -⟩ := closing_same front d d' rs gs h
      exact ⟨hB.last _ a.1, a.2⟩) r11

end run

section thread
variable {Bk : ProverCoinCounts} {Cl V Wt X Pb : Type} {Q : P14} {sentU : Array OracleNotice}
  {layU layO : TreeLay} {T : Thread Bk St Cl V Wt X Pb} {c : OnBytes.Model.Verify.Chains}
  {key : Wt → TableKey} {p₉ p₁₀ : P12} {front : List (Block St Unit)}

/-- **Wherever a thread's invariant holds at the border 12, the four tests accept the state.** hQ:
facts on the plan; hT, hL: the thread's sub-protocols and first state are this chain's. -/
theorem four_at_twelve (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) (hlU : layTrees Q.codes sentU = some layU)
    (f₉ : p₉.nums.firstTree = Q.par.toGPar.firstTree)
    (f₁₀ : p₁₀.nums.firstTree = Q.par.toGPar.firstTree)
    (h0 : 0 < (shapesOf (parO Q)).length) (hk : sampledAt (parO Q) ⟨0, h0⟩)
    {k : Coins Bk} {s : St} {m : Mid Wt X} {E : Env} (hA : Thr T 12 k s m E) :
    fourX Q sentU layU layO (shapeAt (parO Q) ⟨0, h0⟩) 12 s := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  exact four_of_fold12 (hT.bs B) hL hQ.facts.goes hlU hQ.facts.trees hQ.facts.two hQ.facts.ahead f₉
    f₁₀ hQ.facts.goesTwo h0 hk (key m.st.input) s _ _ _ _ hfold

/-- **From the four tests at the border 12 and "in order": the library's text of the five tests on
the shared chain's end.** That text is yes where the chain has not ended. h1a: the plan's shape of
Omega has one answer. As door_of_record (Johnson/Desc/K14/Law/LedgerDoor.lean) on the soundness
side, with "in order" as a premise where that one has a test on the statement's tidiness. -/
theorem door_of_four (p : P₁₄) (hlO : layTrees Q.codes (withOmega Q.S) = some layO)
    (h0 : 0 < (shapesOf (parO Q)).length) (hp : p.S.omega = Q.par.S.omega)
    (h1a : Q.par.S.omega.answers = 1) (hO : 0 < (withOmega Q.S).size) {s : St}
    (hI : OnBytes.Means.InOrder s.st)
    (hX : fourX Q sentU layU layO (shapeAt (parO Q) ⟨0, h0⟩) 12 s) : doorSharedB p s = true := by
  obtain ⟨g1, -, g3, g4⟩ := fourX_parts hX
  obtain ⟨-, e, -, -⟩ := sharedX_twelve Q sentU layU layO s hO g1
  obtain ⟨y, hy, hs, -, hr⟩ := ((omY_iff _ sentU.size 12 s).1 g3).resolve_left (by omega)
  rw [shape_omega Q h0] at hs hr
  refine doorSharedB_of_parts (OnBytes.Means.inOrderB_of hI)
    (fun ψ => door_two_three Q sentU layU layO Q.codes hlO hO s g1 g4 ψ) ⟨y, ?_, ?_, ?_⟩
  · rw [e]
    exact hy
  · rw [hs, hp]
  · rw [hr, h1a]

end thread

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 1000000 in
/-- At the written sizes the shape of Omega has one answer. -/
theorem omega_one_answer_written :
    VerifiableInference.PlanWritten.proofSizedFull.batch.shape.omega.answers = 1 := by
  decide +kernel

/-- **At the full size the plan's shape of Omega has one answer.** -/
theorem omega_one_answer (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    (p14Of Zp.p.chains (beforePointOf Np)).par.S.omega.answers = 1 := by
  have hs : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made h.toAtMg.made_accepts)
  show Zp.p.chains.made.sized.proof.batch.shape.omega.answers = 1
  rw [hs]
  exact omega_one_answer_written

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

/-- **AT THE SHARED CHAIN's LAST BORDER THE FIVE TESTS OF THE LAST CHAIN's FORM ON THAT CHAIN's END
SAY YES**, of whatever Desc.K14.ended returns at that state, wherever the thread's invariant holds
there and the statement is in order, whatever the thread's other parameters are. -/
theorem shared_door_at_end (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (p : P₁₄)
    (hp : p.S.omega = (p14Of Zp.p.chains (beforePointOf Np)).par.S.omega)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E)
    (hI : OnBytes.Means.InOrder s₂.st) :
    ∀ e, Desc.K14.ended s₂ = some e → sharedDoorB p (sharedOfEnd e) = true := by
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
  have e2 : (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S).size = 2 :=
    (Desc.K14.Honest.withOmega_two hQ.facts.two).1
  have hO2 : 0 < (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S).size := by
    rw [e2]
    exact Nat.succ_pos _
  have h0 : 0 < (shapesOf (parO (p14Of Zp.p.chains (beforePointOf Np)))).length := by
    unfold shapesOf
    rw [List.length_map, Array.length_toList, parK1_sent]
    exact hO2
  have h1a := omega_one_answer h
  have hk : sampledAt (parO (p14Of Zp.p.chains (beforePointOf Np))) ⟨0, h0⟩ := by
    show (shapeAt (parO (p14Of Zp.p.chains (beforePointOf Np))) ⟨0, h0⟩).answers ≠ 0
    rw [shape_omega _ h0, h1a]
    exact Nat.one_ne_zero
  have hX := four_at_twelve hQ
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
    (tailAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w B.b1
      B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made h9 h10) hlU f₉ f₁₀ h0 hk hA
  intro e he
  exact sharedDoor_of_text (door_of_four p hQ.facts.trees h0 hp h1a hO2 hI hX) he

/-- **The same at the last chain's own public parameters.** -/
theorem shared_door_pAt (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E)
    (hI : OnBytes.Means.InOrder s₂.st) :
    ∀ e, Desc.K14.ended s₂ = some e → sharedDoorB (ProofFile.pAt Zp) (sharedOfEnd e) = true :=
  shared_door_at_end Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h
    (ProofFile.pAt Zp) rfl hA hI

/-- **The same at a thread whose letter order gives "in order"**: the invariant alone is asked. -/
theorem shared_door_ordered (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hord : ∀ s, order s → OnBytes.Means.InOrder s.st)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E) :
    ∀ e, Desc.K14.ended s₂ = some e → sharedDoorB (ProofFile.pAt Zp) (sharedOfEnd e) = true :=
  shared_door_pAt Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
    (hord s₂ hA.2.2.1.2)

end letters

end AtFullSide.K14

#print axioms AtFullSide.K14.fourX_mk
#print axioms AtFullSide.K14.fourX_parts
#print axioms AtFullSide.K14.four_of_fold12
#print axioms AtFullSide.K14.four_at_twelve
#print axioms AtFullSide.K14.door_of_four
#print axioms AtFullSide.K14.omega_one_answer_written
#print axioms AtFullSide.K14.omega_one_answer
#print axioms AtFullSide.K14.shared_door_at_end
#print axioms AtFullSide.K14.shared_door_pAt
#print axioms AtFullSide.K14.shared_door_ordered
