-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/EvalAloneAtEnd.lean: kind K13 (the members' batching): at the end of the proof file's
first chain the request's own group holds just one open row, the row (Eval) (`EvalAlone`,
Johnson/Desc/K13/Honest/EvalAlone.lean). The full size, and the hash function `OnBytes.secondHashFunction`,
alone. Statements with their proofs; no definition.

What it is for. The last chain's first member reads every open row of the own group; the first
chain's thread knows of the one row (Eval) that it says its claim (the item "wrow"). `evAll_of_wRow`
(Johnson/Desc/ProofFile/Honest/K14/EvAtLastStart.lean) goes from the one to all under `EvalAlone` at
the first chain's last state. This file shows `EvalAlone` there: at every state that the verifier's
own steps reach behind all 358 members, and so wherever the first chain's thread holds at its last
border.

Main names.
  `atM4_rowsB`: a yes of W's commitment with the block `rowsB` joined behind it holds a yes of
    `rowsB`.
  `evalAlone_behind_356`: behind an accepting step of number 356.
  `evalAlone_of_reach`: at every state reached behind number 357, under the hypothesis h
    (`P5J.AtMgA`).
  `len358`: under h the first chain has just 358 members (the library's `flat_358`,
    Johnson/Desc/Last/IndexAtEnd.lean).
  `k13_evalAlone_at_end`: **wherever the thread holds at border 358**, at the first chain's thread
    as `lettersHead` makes it (Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean), every argument
    of `lettersHead` a variable. 358 is the chain's last border: `len358`.
  `k13_evAll_at_end`: there, from (Eval)'s sentence `WRow` at the state's own words: every open row
    of the own group holds (`evAll` at the reader of the first chain's state fun q => q.2).

How. Number 356 is W's commitment with `rowsB` behind it (`IM.at_356`, Johnson/IMR/LastFour.lean);
behind `rowsB`'s yes the sentence holds (`K13RowsKeeps.alone`); number 357 returns the state that it
is handed (`IM.at_357`). The thread at a border gives that its state is reached (`thr_reach_of`,
Johnson/Desc/ProofFile/Honest/Thread/ReachBack.lean).

Limits. Conditional on h. Statements on the verifier's public state alone; of the thread only its
clause that the state was made by the verifier's steps is read. Where the thread holds at no run the
last two statements say nothing. That (Eval) says its claim is a premise of `k13_evAll_at_end`. The
facts beneath rest on evaluations in Lean's kernel.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.EvAtLastStart
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.IMR.LastFour
import Johnson.Desc.Last.IndexAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block OpenedColumn FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.K13 (Where whereOf atM4 rowsB atS)
open VerifiableInference.Desc.K13.Law (ebind_ok WRow)
open VerifiableInference.Desc.K13.Honest (EvalAlone rowsB_rowsKeeps K13RowsKeeps.alone)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K14 (evAll evAll_of_wRow)

/-- A yes of W's commitment with the block `rowsB` joined behind it holds a yes of `rowsB`. -/
theorem atM4_rowsB {Cl : Type} {P : Where} {w : Block S Cl} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM4 P w).decide s rs gs = .ok s') :
    ∃ s₁ rs₂ g₂, (rowsB (Cl := Cl) atS P).decide s₁ rs₂ g₂ = .ok s' := by
  have h' : (w.decide s (rs.take w.rounds.length) (gs.take w.openings)).bind (fun m =>
      (rowsB (Cl := Cl) atS P).decide m (rs.drop w.rounds.length) (gs.drop w.openings)) =
      .ok s' := h
  obtain ⟨s₁, _, h2⟩ := ebind_ok.1 h'
  exact ⟨s₁, _, _, h2⟩

/-- **Behind an accepting step of number 356.** -/
theorem evalAlone_behind_356 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[356]? = some b) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ}
    (hy : b.step ft s rs cols = .ok (s', n)) : EvalAlone (whereOf Z) s' := by
  obtain ⟨w, _, ⟨rs', gs, y⟩, -, -⟩ := IM.at_356 hS hR O hb hy
  obtain ⟨s₁, rs₂, g₂, h2⟩ := atM4_rowsB y
  exact (rowsB_rowsKeeps h2).alone

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- **At every state that the verifier's own steps reach behind number 357.** -/
theorem evalAlone_of_reach {Pz : Type} {ft : ℕ} {start : Pz → TS} {z : Pz} {s : TS}
    (hr : Reach ft cF.blocksInOrder start (356 + 1 + 1) (z, s)) : EvalAlone (whereOf Zp) s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases hr with
  | succ hr₁ hb₁ hy₁ =>
    cases hr₁ with
    | succ _ hb₀ hy₀ =>
      obtain ⟨_, _, _, e₁⟩ := hy₁
      obtain ⟨_, _, _, e₀⟩ := hy₀
      rw [IM.at_357 h.scope h.reads O hb₁ e₁]
      exact evalAlone_behind_356 h.scope h.reads O hb₀ e₀

include h in
/-- Under h the first chain has just 358 members. -/
theorem len358 : cF.blocksInOrder.length = 358 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact VerifiableInference.Desc.Last.flat_358 h.scope h.reads O

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **Wherever the first chain's thread holds at its last border, (Eval) is the own group's one open
row.** -/
theorem k13_evalAlone_at_end {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k s m En) :
    EvalAlone (whereOf Zp) s :=
  evalAlone_of_reach h (thr_reach_of
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).first
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf m.st.input.x)
    (le_of_eq (len358 h).symm) (fun _ h0 => h0) hT)

/-- hR is a premise. **There, if (Eval) says its claim of the words read through the state's own
book, every open row of the own group does.** -/
theorem k13_evAll_at_end {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k s m En)
    (arr : ℕ → ℕ → ℕ) (z : ProofFile.InstPub) (y : Strs) (v : WtF)
    (hR : WRow (whereOf Zp) s (wordsFirst arr s.st s.book v)) :
    evAll arr (fun q : ProofFile.InstPub × TS => q.2) (z, s) y v :=
  evAll_of_wRow (fs := fun q : ProofFile.InstPub × TS => q.2) (whereOf Zp) (z, s) y v
    (k13_evalAlone_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT) hR

end AtFullSide.K13

#print axioms AtFullSide.K13.atM4_rowsB
#print axioms AtFullSide.K13.evalAlone_behind_356
#print axioms AtFullSide.K13.evalAlone_of_reach
#print axioms AtFullSide.K13.len358
#print axioms AtFullSide.K13.k13_evalAlone_at_end
#print axioms AtFullSide.K13.k13_evAll_at_end
