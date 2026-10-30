-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/DotAtStart.lean: the linear claim (kinds K13 and K14): the item (Dot) holds at the
start of the proof file's last chain, at an honest run. (Dot) says that the vector W, at the shared
point psi, is the row weights g applied to the vector Omega. Statements with their proofs; no
definition. At the full size, under the library's head h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean).

The item's meaning here is the library's own filling `dotI`
(Johnson/Desc/Third/Law/Row0DotOm.lean): the row weights are read off the first chain's last state,
the point and Omega's number off the shared chain's last state, Omega's words off the witness at
that state's own statement and book of trees, and W's words off the witness at the first chain's
last state.

  `drawn_firstRv`   the first challenge heard, read in two ways
  `lin_is_shared`   under h the first chain's shape of the linear claim is the shared chain's
  `point_at_shared_end`   at the shared chain's last border the point that the state notes is the
     first challenge heard on that chain, and it has the shape's number of coordinates
  `dotI_at_the_door`   **(Dot), in that meaning, at the two earlier chains' last states**, wherever
     the two threads' invariants hold there, at any witness v that holds W's text (hW) and, at
     Omega's number, the honest words of the shared chain at the first challenge heard there (hOm)

How. The row weights are what the prover makes of the challenges heard on the first chain
(`g_at_door`, AtFullSide/K13/DotAtTheDoor.lean); the point is the first challenge heard on the
shared chain (`point_at_door`, the same file); Omega's number, its layout's codes and the point's
length are book-keeping at the shared chain's end
(Johnson/Desc/ProofFile/Honest/K14/OmegaSeatAtEnd.lean); the equation at the honest words is the
library's `dot_at` (Johnson/Desc/K14/Honest/ItemsHold.lean).

Limits.
  * hW and hOm are hypotheses on the witness. Both read one matrix: the weights Wt.
  * That either thread's invariant holds at any state is not shown here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K13.DotAtTheDoor
import Johnson.Desc.ProofFile.Honest.K14.OmegaSeatAtEnd
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Flat.Last.RowZeroWeights
import Johnson.Desc.Third.Law.Row0DotOm
import Johnson.Desc.K14.Honest.ItemsHold

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13 ProofFile.Honest.K14
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K1 (qAt)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Sound (MsgT wordsShared)
open VerifiableInference.Desc.Third.Law (dotI gOfS wvW)
open Desc.K14 (St p14Of beforePointOf drawn)
open Desc.K14.Law (DotEq DotOmAt omegaOf VIs gLaid)
open Desc.K14.Honest (words2 Inputs dot_at omegaAt)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead sentFirstOf)
open AtFullSide.K13 (gWords gMade g_at_door point_at_door)

/-- The first challenge heard, read in two ways. -/
theorem drawn_firstRv (hd : List Fmt.Drawn) : drawn (firstRv hd) = Door.pointHeard hd := by
  cases hd <;> rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the first chain's shape of the linear claim is the shared chain's. -/
theorem lin_is_shared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    Zp.first.lin = (qAt Zp Np).S := by
  have h1 : Zp.first.lin = VerifiableInference.PlanWritten.proofSizedFull.batch.shape :=
    (VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
      (P5J.pins_of_laid h.scope h.laid).1).2.1
  have hs : Zp.p.chains.made.sized.proof = VerifiableInference.PlanWritten.proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made h.toAtMg.made_accepts)
  show Zp.first.lin = Zp.p.chains.made.sized.proof.batch.shape
  rw [h1, hs]

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X' P₁ Wt₂ : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)
  (N₂ : NumbersS) (Mg₂ : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt₂)
  (shape₂ : Nat → St → Bool) (nothingLeft₂ : St → Bool) (order₂ : St → Prop)
  (wit₂ : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt₂)
  (table₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed₂ : Fmt.TreeSource → Nat) (a₁ a₂ : Nat) (Vd₂ : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd₂ : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp₂ : Place → St → St → Prop)
  (w₂ : Common W₀ Rc OnBytes.TableKey)

include h in
/-- At the shared chain's last border the point that the state notes is the first challenge heard on
that chain, and it has as many coordinates as a column's number has bits. -/
theorem point_at_shared_end {k : Coins Bk} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : Thr (SharedThread.lettersShared Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂
      fixed₂ a₁ a₂ Vd₂ Rd₂ Kp₂ w₂).thread (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k e₂ m₂
      E₂) :
    e₂.loc.psiSh = Door.pointHeard m₂.st.heard ∧ e₂.loc.psiSh.length = (qAt Zp Np).S.kCol := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  have hbs : (SharedThread.lettersShared Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂
      fixed₂ a₁ a₂ Vd₂ Rd₂ Kp₂ w₂).thread.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder :=
    SharedThread.shared_bs Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂ fixed₂ a₁ a₂
      Vd₂ Rd₂ Kp₂ w₂
  exact ⟨point_at_door (Zp := Zp) (Np := Np) (cF := cF)
      (SharedThread.lettersShared Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂ fixed₂
        a₁ a₂ Vd₂ Rd₂ Kp₂ w₂).thread B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.two
      hbs rfl (by rw [hbs]; exact u₂.2.2.2.2.1),
    point_of_omegaEnd (omega_at_shared_end Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂
      fixed₂ a₁ a₂ Vd₂ Rd₂ Kp₂ w₂ h u₂).1⟩

/-- **(Dot), in the library's own filling of the item's meaning, at the two earlier chains' last
states.** Wt, rd: the index's weights and the table's random values. Hh: what the prover holds on
the shared chain; hRw: its rows are the stored table's at Wt and rd. v: the witness. hW: it holds
W's text at the row weights made of the challenges heard on the first chain. hOm: at Omega's number
it holds the shared chain's honest words at the first challenge heard there. -/
theorem dotI_at_the_door (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {F : VerifiableInference.Desc.Sound.Frame} (y₀ : F.E.Str) (hb₀ : b₀ ≤ cF.blocksInOrder.length)
    (arr : ℕ → ℕ → ℕ) (t₁ : ℕ) (Wt : Weights) (rd : TableRand) (Hh : Inputs)
    (hRw : Hh.Rw = fun i j => OnBytes.Slice.rdE.val (rowsOf (qAt Zp Np).S Wt rd i j))
    (key : OnBytes.TableKey)
    {k : Coins Bk} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k e₁
      m₁ E₁)
    (u₂ : Thr (SharedThread.lettersShared Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂
      fixed₂ a₁ a₂ Vd₂ Rd₂ Kp₂ w₂).thread (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k e₂ m₂
      E₂)
    (v : WtF)
    (hW : ∀ c < 2 ^ Zp.first.lin.kCol,
      wvW arr (ToldDesc.p14At Zp) (fun q : ProofFile.InstPub × TS => q.2) (w₁.x.pub, e₁) v c =
        wVec Zp.first.lin Wt (gWords Zp Bs w₁.x m₁.st.heard) c)
    (hOm : ∀ i, wordsShared arr t₁ e₂.st e₂.book v 2 .main i =
      words2 (qAt Zp Np) (sentFirstOf Zp Np) (Desc.K14.first (qAt Zp Np).codes key)
        (firstRv m₂.st.heard) Hh 2 .main i) (y : Strs) :
    dotI (ToldDesc.p14At Zp).S (fun q : ProofFile.InstPub × TS => gOfS q.2)
      (fun d w => wordsShared arr t₁ d.st d.book w)
      (fun q => wvW arr (ToldDesc.p14At Zp) (fun q : ProofFile.InstPub × TS => q.2) q)
      (w₁.x.pub, e₁) e₂ y v := by
  -- the first chain's end: the row weights
  have i₁ : m₁.st.input = w₁ := u₁.2.2.2.2.2.2.1
  have hr : ReplyIs ProofFile.Inst.asked m₁.st.input.x e₁ :=
    ProofFile.Honest.FirstThread.head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hb₀
      u₁.2.2.2.2.2.1
  have hE := AtFullSide.K13.k13_evalLaid_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ y₀ k e₁
    m₁ E₁ u₁
  have hgl : gLaid (whereOf Zp) (fun q : ProofFile.InstPub × TS => q) (w₁.x.pub, e₁) =
      gMade Zp Bs w₁.x m₁.st.heard := by
    have a := g_at_door h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Bs hB
      (fun q : ProofFile.InstPub × TS => q) (q := (w₁.x.pub, e₁)) u₁ rfl hr hE
    rw [i₁] at a
    exact a
  have hg : gOfS e₁ = gMade Zp Bs w₁.x m₁.st.heard :=
    (VerifiableInference.OnPublicFiles.Last.gLaid_is_gOfS (whereOf Zp)
      (fun q : ProofFile.InstPub × TS => q) (w₁.x.pub, e₁) hE).symm.trans hgl
  -- the shared chain's end: the plan, Omega's number, the codes, the point
  obtain ⟨sentU, layU, layO, hQ, -, -, -, -, -⟩ :=
    omega_seat_at_shared_end Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂ fixed₂ a₁ a₂
      Vd₂ Rd₂ Kp₂ w₂ h u₂
  obtain ⟨ho, hc, -, -⟩ :=
    omega_written_at_shared_end Zp Np cF H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂ fixed₂ a₁
      a₂ Vd₂ Rd₂ Kp₂ w₂ h u₂
  obtain ⟨hpt, hlen⟩ := point_at_shared_end h H N₂ Mg₂ shape₂ nothingLeft₂ order₂ wit₂ table₂ fixed₂
    a₁ a₂ Vd₂ Rd₂ Kp₂ w₂ u₂
  have hsent : sentFirstOf Zp Np = sentU := by
    have hU : Desc.K14.withU (qAt Zp Np).S = some sentU := hQ.facts.goes
    unfold sentFirstOf
    rw [hU]
    rfl
  have hlin := lin_is_shared h
  rw [hlin] at hW
  rw [hsent] at hOm
  have hp1 : (drawn (firstRv m₂.st.heard)).length = (qAt Zp Np).par.S.kCol := by
    rw [drawn_firstRv, ← hpt]
    exact hlen
  have hV : VIs (qAt Zp Np).S (gOfS e₁) Hh.Rw
      (wvW arr (ToldDesc.p14At Zp) (fun q : ProofFile.InstPub × TS => q.2) (w₁.x.pub, e₁) v) := by
    intro c hc'
    rw [hW c hc', Door.wVec_is_sum (qAt Zp Np).S Wt _ hc', hg, hRw]
    exact Finset.sum_congr rfl fun y hy => by
      rw [Door.rows_matOf (qAt Zp Np).S Wt rd (Finset.mem_range.1 hy)]
      rfl
  have hD := dot_at hQ.facts (Desc.K14.first (qAt Zp Np).codes key) (firstRv m₂.st.heard) Hh hp1
    (gOfS e₁) _ hV
  rw [drawn_firstRv, ← hpt] at hD
  show DotEq _ _ (gOfS e₁) (omegaOf e₂.loc (linLayOmega e₂.st.codes (qAt Zp Np).S)
    (wordsShared arr t₁ e₂.st e₂.book v)) _ _
  unfold DotEq at hD ⊢
  refine (Finset.sum_congr rfl fun y _ => ?_).trans hD
  show _ * wordsShared arr t₁ e₂.st e₂.book v e₂.loc.oOmega .main _ = _
  rw [ho, hOm, hc]
  rfl

end

end AtFullSide.K14

#print axioms AtFullSide.K14.drawn_firstRv
#print axioms AtFullSide.K14.lin_is_shared
#print axioms AtFullSide.K14.point_at_shared_end
#print axioms AtFullSide.K14.dotI_at_the_door
