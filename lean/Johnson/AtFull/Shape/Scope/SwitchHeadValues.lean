-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/SwitchHeadValues.lean: the first chain's test on values at the number 339, the code
switch at the head's place, accepts behind a state of the thread.

1. here_head_at: at a state reached at the border 339 the head's record stands: the step in front,
   the reply, returns only there.
2. switchHead_values: the field switchHead of the values' fold, in the form ValuesJ at number 339.
   The table's cell there asks headW HP s: headOnesV s and headQuietV HP s. The first is the test on
   the carried rows at the head's copy of the frame: onesV_true_reached. The second is the test that
   the covered positions can be made: headQuietV_eq and covered_reach.

What the law reads of the thread T: hft: its first number is 0 · hbeg: its first state is the start
of the input's public part zOf w · hst: the stored words lie below the prime · hform: the invariant's
form says that the state bears no mark: so the request passed, by start_clean and start_passes.

What it reads of Said: hSaid: Said gives SaidOk.

It is not empty at lettersHead's thread, where switchHead_at_head pays all but Said. J and fall are
not read. At a Said that never holds, or at a valid that holds of no input, the law is idle.
The full size and the format's second hash function alone.
-/
import Johnson.AtFull.Shape.K1ValuesHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.AtFull.Shape.TableSwitch
import Johnson.AtFull.Shape.SwitchOnesPlain
import Johnson.AtFull.Shape.ReqReplyReach
import Johnson.Desc.First.Shape.SwitchEndsVals
import Johnson.Desc.K2.Honest.Returns.DoorReached
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes.Model
open VerifiableInference.Desc (Chain fieldPrimeWord)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (headOnesV headQuietV_eq)
open VerifiableInference.Desc.Sound (below)
open Johnson.AtFull.Shape
open Johnson.Desc.First.Walk.Tied (Reach reach_raw reach_cuts_below)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **At a state reached at the border 339 the head's record stands.** -/
theorem here_head_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {a : ProofFile.InstPub × S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 a) : ∃ o, a.2.here = .head o := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, f₀, cuts⟩ := reach_cuts_below hr
  obtain ⟨tm, rm, cm, hm, fm⟩ := cuts 338 (by omega)
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits h.scope h.reads O
  have i0 : cF.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope h.scope h.reads O (by decide : 24 ≤ 24) 0).trans
      (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := Meaning.K2.fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes h.scope h.reads O hj d0).1
  obtain ⟨mm, -, a2⟩ := Meaning.K2.andThen_yes d0'
  obtain ⟨o, _, ho, hc, -, -, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.reply_record 24 _ a2
  refine ⟨o, ?_⟩
  rw [e]
  exact ho

/-- h, hB, hbs, hft, hbeg, hst, hform AND hSaid ARE PREMISES. **THE FIELD switchHead: AT THE NUMBER
339 THE TABLE's TEST ON VALUES ACCEPTS.** -/
theorem switchHead_values (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (hft : T.ft = 0) (zOf : W → ProofFile.InstPub)
    (hbeg : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp (zOf w))
    (hst : ∀ w i y u, T.stored w i y = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hform : ∀ b k s m, T.Form b k s m → s.failed = none)
    (Said : Nat → Coins Bk → Mid W X → Prop) (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (J : Nat → S → Prop) (fall : Nat → S → List Fmt.Drawn → Option String) :
    ValuesJ T Said J (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall 339 := by
  intro blk hblk k s m E ds y cols hA _ _ _ _ _
  have hlt : 339 ≤ T.bs.length := by
    by_contra c
    rw [List.getElem?_eq_none (Nat.le_of_lt (Nat.lt_of_not_le c))] at hblk
    cases hblk
  have hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (zOf m.st.input, s) := by
    have r₀ := reach_below T (ProofFile.startS Zp) (zOf m.st.input) hlt
      (fun s₀ hs₀ => hbeg k m.st.input _ s₀ hs₀) hst ⟨hA.1, hSaid _ _ _ hA.2⟩
    rw [hbs, hft] at r₀
    exact r₀
  obtain ⟨B', P', n, HP, e1, e2, e3, e4, -⟩ := switch_head_both h
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ 339 = Tab.switchHead Zp Bs.G₀ :=
    cells_head Zp Bs.G₀ 2 (by omega) rfl
  unfold Tab.switchHead at hc
  rw [e2] at hc
  simp only [Option.bind_some, e3, e4] at hc
  show Tab.vals Zp Bs.G₀ 339 s _ _ = true
  rw [cell_v hc]
  show headW HP s = true
  unfold headW
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · obtain ⟨o, ho⟩ := here_head_at h hr
    have ho' : s.here = .head o := ho
    have hmem : o.fr ∈ Meaning.K2.framesIn s := by
      simp [Meaning.K2.framesIn, ho']
    have t := onesV_true_reached h (by omega) hr o.fr hmem
    unfold headOnesV
    rw [ho']
    exact t
  · rw [headQuietV_eq]
    obtain ⟨Bs', hB', hW, hT, hV, -⟩ := nums_at h
    obtain rfl := base_one hB hB'
    obtain ⟨Xl, -, rfl⟩ := Option.map_eq_some_iff.1 e4
    show (s.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V).toOption.isSome = true
    rw [hW, hT, hV]
    have hcl := hform _ _ _ _ hA.1.2.2.1
    have hA1 := hA.1
    unfold Thr ProofFile.Honest.Thread.Made at hA1
    obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hb₀, -, hfold⟩, -, -⟩ := hA1
    rw [hbs, hft, hbeg _ _ _ _ hb₀] at hfold
    have hq := start_passes Zp _ (start_clean h 339 0 _ _ _ _ hfold hcl)
    obtain ⟨cov, hcov⟩ := covered_reach h (reach_raw hr) hq (Nat.le_refl _)
    have hcov' : s.covered Zp.p.X.T Zp.p.X.P.h.V = .ok cov := hcov
    rw [hcov']
    rfl

open VerifiableInference.Desc (Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (CellsM TS)
open ProofFile.Honest.FirstThread (Script lettersHead WtF)

/-- **THE FIELD switchHead AT lettersHead's THREAD, AT ALL ITS LETTERS.** -/
theorem switchHead_at_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    {Bs : ProofFile.PureBase} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) (J : Nat → TS → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall (337 + 2) :=
  switchHead_values h hB _ rfl rfl (fun v => v.x.pub) (fun _ _ _ _ h0 => h0)
    (fun v i p u hu => storedWords_lt H v.w₀ v.rc i p u hu)
    (fun _ _ s _ hF => by
      have t : s.failed.isNone = true := hF.1
      simpa using t)
    Said hS J fall

end Johnson.AtFull.Shape.Scope

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.AtFull.Shape.Scope.here_head_at
#print axioms Johnson.AtFull.Shape.Scope.switchHead_values
#print axioms Johnson.AtFull.Shape.Scope.switchHead_at_head
