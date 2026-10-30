-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/BookTreesB.lean: a helper of AtFullSide/K2/BookTrees.lean: under the head `P5J.AtMg`
and the opening, where the book of commitment trees stands at a state that the first chain's own
steps reach at a border from 2 on: it has as many trees as the sub-protocols in front state oracle
messages; the tree at place j bears the number j; its shape is the written list's (`LFull`) number
j. One theorem with its proof: calls of the library's laws; no definition.

No "no mark" is asked of the state: from border 2 on the request has passed its test
(`reqOk_reached`), which is all that the law on the seats (`IM.seats_planOk`) asks of the start.
-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.FoldJ1
import Johnson.P5J.FoldJ3
import Johnson.P5J.ReadsTestsAtHead
import Johnson.P5J.AtMgRAtHead
import Johnson.IMR.AtReach
import Johnson.IMR.RootsWhole
import Johnson.IMR.SeatsField
import Johnson.ToldDescR.BookAtW
import Johnson.Desc.ProofFile.Honest.Small.FixedSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K13.Law (LFull)
open OnBytes.Maker (WholeD)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest (treesTo)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **Where the book of trees stands at a reached state**, from border 2 on. -/
theorem book_at_reached (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {nb : Nat} {z : ProofFile.InstPub} {s : TS} (R : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) nb (z, s))
    (h2 : 2 ≤ nb) :
    s.book.trees.size = treesTo cF.blocksInOrder nb ∧
      ∀ (j : Nat) (T : Tree), s.book.trees[j]? = some T →
        T.number = j ∧ LFull.shapes[j]? = some T.shape := by
  obtain ⟨hle, rs, cols, f⟩ := R.fold
  have hp := P5J.flat_ok h
  have hlen : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.scope O
  have hk : nb ≤ 358 := hlen ▸ hle
  have hroots : s.roots = (ProofFile.startS Zp z).roots +
      Johnson.G.OfPlan.rootsOf (H2K.First.declOf (cF.blocksInOrder.take nb)) :=
    Meaning.Carry.roots_at_cut_whole h.scope h.reads O 0 _ rs cols nb hk
      (fun b hb => hp b (List.mem_of_mem_take hb)) _ f
  have hst : (ProofFile.startS Zp z).roots = 0 := (Meaning.K2.start_empty O.pub z).2
  have hbk : VerifiableInference.Desc.K12.Door.bookInOrderB 0 s.book s.roots = true :=
    Meaning.K2.atFirstBook_all O hp R
  unfold VerifiableInference.Desc.K12.Door.bookInOrderB at hbk
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hbk
  have hu : (ProofFile.startS Zp z).failed = none :=
    Meaning.K2.start_noMark O.pub (Meaning.K2.reqOk_reached h.scope h.reads O R h2)
  have hseat : VerifiableInference.Desc.K12.Door.seatsCarriedB LFull s.book = true :=
    (IM.seats_planOk h.scope h.reads O z h.laid.planOk hu
      (P5J.sends_at O (P5J.sendsB_of_madeRow h (P5J.madeRow_at_head h))) (P5J.laid_at_head h) hk
      f).1
  have hL : ∀ x ∈ cF.blocksInOrder, ProofFile.Honest.Small.Listed x := fun x hx =>
    ProofFile.Honest.Small.lists_of_shaped
      (((VerifiableInference.Desc.FileDescription.planOk_ok _).1 h.laid.planOk).blocks₁ x hx).2
  refine ⟨?_, fun j T hT => ⟨?_, ToldDesc.tree_shape_of_seats hseat hT⟩⟩
  · rw [← hbk.1, hroots, hst, Nat.zero_add, ProofFile.Honest.Small.treesTo_roots cF.blocksInOrder hL nb]
    rfl
  · have hj : j < s.book.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
    have e := hbk.2 j (List.mem_range.2 hj)
    rw [hT] at e
    have e' : (T.number == 0 + j) = true := e
    rw [beq_iff_eq, Nat.zero_add] at e'
    exact e'

end AtFullSide.K2

#print axioms AtFullSide.K2.book_at_reached
