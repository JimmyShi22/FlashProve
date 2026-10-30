-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SymbolsOfSenders.lean: one message that a code switch reads, as the record MemberSent
asks it, from its seat and its sender.

  tree_front           a tree of a sender in front stands below the border's count of trees
  memberSent_of        the record from the seat, the sender and the table

Limits. The head, the opening, the yes and the thread's table are premises.
-/
import AtFullSide.K2.SymbolsOfMembers
import AtFullSide.K2.BookTrees
import AtFullSide.K2.SymbolsTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open OnBytes.Slice (codeOf)
open Johnson.Prover.Send (Rows shapeAt)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes)
open VerifiableInference.Desc.Sound (allOf EAll seatBy noFirst)
open VerifiableInference.Desc.K2.Honest (Sizes)
open VerifiableInference.Desc.K13.Law (LFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest (ProverCoinCounts Coins Mid Thread treesTo)
open ProofFile.Honest.K1 (seatAtMember treeTables)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}

/-- **A tree of a sender in front of a border stands below the border's count of trees.** -/
theorem tree_front {b n₀ τ : Nat} {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[b]? = some blk)
    (hlt : b < n₀) (hτ : τ < (blk.oracles.flatMap id).length) :
    treesTo cF.blocksInOrder b + τ < treesTo cF.blocksInOrder n₀ := by
  have e := ProofFile.Honest.treesTo_succ (bs := cF.blocksInOrder) hb
  have m := ProofFile.Honest.FirstThread.treesTo_mono cF.blocksInOrder (show b + 1 ≤ n₀ by omega)
  omega

/-- **One message, from its seat and its sender.** -/
theorem memberSent_of {Bk : ProverCoinCounts} {V W X Pb : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {nb : Nat}
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch nb a) {s₁ t : TS} (hbk : s₁.book = a.1.2.book) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Y rows G cd)
    (T : Thread Bk TS ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : q.firstTree = 0) (k : Coins Bk)
    (m : Mid W X) (Zs : Sizes) (old : SingleRows) (w : Nat)
    {P : VerifiableInference.Desc.K1.Par} {b : Nat} (hP : SenderAt Zp Bs P b) (hb : b < nb)
    (Vr : Nat → Rows) (kn : Nat) (Xo : Oracle) (plan : VerifiableInference.Desc.K1.planOkOwn P = true)
    (below : kn < P.sent.size) (oracle : Xo.shape = shapeAt P kn)
    (maskCode : (shapeAt P kn).maskRows ≠ 0 →
      P.codes.mask.getD (shapeAt P kn).maskCode default = Zs.codes.mask.getD Zs.maskCode default)
    (place : ∀ hw : w < (singleRowsOracles old).size,
      z.book.place[(singleRowsOracles old)[w]]? = some (seatAtMember cF.blocksInOrder b P kn))
    (stated : ∀ hw : w < (singleRowsOracles old).size,
      z.st.oracles[(singleRowsOracles old)[w]]? = some Xo)
    (hτ : ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0 <
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).shapes.size)
    (logMask : ∀ t : TreeShape, LFull.shapes[(seatAtMember cF.blocksInOrder b P kn).1]? = some t →
      (shapeAt P kn).maskRows ≠ 0 → (codeOf (Zs.codes.mask.getD Zs.maskCode default)).a ≤ t.logN)
    {n₀ : Nat}
    (front : treesTo cF.blocksInOrder b +
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0 <
        treesTo T.bs n₀)
    (table : (treeTables P Vr)[((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD
        {}).tree.getD kn 0]? =
      some (T.tableAt (.own (treesTo cF.blocksInOrder b +
        ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0)) k m).2) :
    ∃ tr : Tree, MemberSent T n₀ k m q Zs old z w P Vr kn Xo (seatAtMember cF.blocksInOrder b P kn) tr ∧
      LFull.shapes[(seatAtMember cF.blocksInOrder b P kn).1]? = some tr.shape := by
  obtain ⟨tr, e1, e2, e3, e4⟩ := tree_at_yes h O a hr hbk A hP hb hτ
  have ee : VerifiableInference.Desc.Own.treesMade P.codes P.sent = layTrees P.codes P.sent :=
    VerifiableInference.Desc.Own.treesMade_eq _ _
  have es : seatAtMember cF.blocksInOrder b P kn = (treesTo cF.blocksInOrder b +
               ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0,
               ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).part.getD kn 0) := by
    show (treesTo cF.blocksInOrder b + ((layTrees P.codes P.sent).getD {}).tree.getD kn 0,
      ((layTrees P.codes P.sent).getD {}).part.getD kn 0) = _
    rw [ee]
  have e4' : LFull.shapes[(seatAtMember cF.blocksInOrder b P kn).1]? = some tr.shape := by
    rw [es]
    exact e4
  refine ⟨tr, ⟨plan, below, oracle, maskCode, place, stated, ?_, e3, ?_, logMask _ e4', ?_, ?_⟩, e4'⟩
  · rw [es]
    exact e1
  · rw [es]
  · rw [hft, e2, Nat.sub_zero]
    exact front
  · rw [hft, e2, Nat.sub_zero]
    exact table

end AtFullSide.K2

#print axioms AtFullSide.K2.tree_front
#print axioms AtFullSide.K2.memberSent_of
