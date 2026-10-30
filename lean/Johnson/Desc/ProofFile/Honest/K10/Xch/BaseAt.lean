-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/BaseAt.lean: at the first chain's thread under the library's head: where the
invariant holds at the border before the closing of a segment (kind K10) and the closing's own step accepts, the
twenty facts of `CloseBase` (Johnson/Desc/K10/Honest/Base.lean) hold of the record before the step, given two of them
as premises. No definition; one local notation.

The words.
  A thread: the structure of parameters of one chain's invariant (`Thread`, `Thr`: Honest/Thread/Thr.lean).
  The head: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), here at the older hash. The head's
      thread is the field `thread` of `lettersHead` at its parameters (Honest/Thread/FirstHead.lean).
  Border b: the position in the chain before sub-protocol number b. The closing of segment l is sub-protocol number
      14 l + `IM.nAt l` + 5, where `IM.nAt l` is 9 at l = 24 and 7 elsewhere (Johnson/IMR/WrittenList.lean).
  The block: a block blk with `Tied cF Zp l p Qc blk` (Honest/K10/SimLot.lean): the chain's block at that number,
      which is the kind's block at the numbers Qc, lifted to the chain's state and seated under two guards.
  The record: `K9.recOf s`, the part of the first chain's state s that the closing reads: what is owed, the live
      frame, the statement. The group: the group of the statement at the number that the record's frame names.

What is proved.
  `groups_k_le`: every group of the written request's shape at the full size has at most 8 row variables. From the
      library's `shapeFull_groups` (Johnson/Desc/ReqLit/Full.lean), which writes them out.
  `logEll_full`: the `logEll` of the main code that the written shape names, among the written codes, is at most 55.
      By `decide +kernel`: Lean's kernel evaluates the comparison itself; no compiled code is trusted and no axiom is
      added.
  `facts_at_thr`: wherever the invariant holds at a border of the chain: the statement is in order (`InOrder`); its
      codes are the head's; the live frame's shape is the head's; the live frame's groups are those of its shape. Four
      of the 26 fields of `FoldFacts`, at `foldFacts_thr` (Honest/Thread/ReachFacts.lean): tidy, codes, liveShape,
      liveGroups.
  `closeBase_at_step`: from Td, hT, hs, hTerms and hMask: there is D₀ with `CloseBase Qc (K9.recOf s) D₀`.
  `closeBase_at_stepped`: the same with the acceptance taken from a thread's step (hS: `Thread.Stepped`,
      Honest/Thread/Pays.lean).

By: `closeBase_of_closing` (Johnson/Desc/K10/Honest/BaseOfYes.lean), whose head says where each of the twenty facts
comes from; `tied_decides` (Xch/Behind.lean): the seated block's acceptance is the lifted block's decision's;
`foldFacts_thr`; under the head, the program's test on the codes' lengths accepts (`P5J.AtMgA.three`,
Johnson/P5J/K03OneOwnAt.lean), and the codes and the shape are the written ones (`AtMg.codes_full`,
`AtMg.shapeAt_full`, Johnson/P5J/CodesFullAtMg.lean).

The notation, and the option in front of it. 𝕋 stands for the head's thread, written out once. It declares no new
name, neither a definition nor a theorem: each use is that text, elaborated anew. A field of it is written with
brackets, `(𝕋).Stepped`: without them Lean reads `𝕋.Stepped` as one name. When a notation is declared, Lean looks
through its text for names that are not bound, and that early look has no case for a field access.
`set_option quotPrecheck false in` turns that one look off for the one command behind it; it loosens nothing in what
Lean checks of a theorem.

Limits. Every premise of the two main statements, by name.
  h: the head.
  Td: `Tied`: blk is the chain's block at the closing of segment l.
  hT: the invariant holds at the border before that closing.
  hs (hS): the block's step accepts at the state s.
  hTerms: every structured vector among the terms on a main table, of every row that the proximity test on the group
      takes in, is in order (`Tensor.ok`). This is `CloseBase`'s field termsOk, asked of whichever group is there.
  hMask: the group's mask code is the one that the frame's shape names. This is `CloseBase`'s field maskCode, asked
      of whichever group is there.
hTerms and hMask are shown of no state here, and neither is derived from the invariant or from the acceptance. On
hTerms: `RowIn` and `InOrder` do not ask `Tensor.ok` of a row's terms, and none of the four fields of `FoldFacts` that
are used here speaks of it. Further along the road from `CloseBase` to the sentence of the item carry, termsOk and bits
are spent again: in `closeFront_all` (Johnson/Desc/K10/Honest/Base.lean), `closeBase_holds` (Holds.lean) and
`rows_named` (LeftClaim.lean), and in `base_row` (Johnson/Desc/ProofFile/Honest/K10/AskLaw.lean), where termsOk is spent
for two things. An acceptance gives one of the facts that they serve, the yes of the test `Own.foldRowFits` at the
element drawn (`CloseFront.rowfits`, Front.lean). Whether forms of these laws over an acceptance could do without the
two fields is not looked into here. On hMask: the acceptance ties the mask code of those members alone that have mask
rows, and it does not say that there is one. The library's sentence on the members' shapes (`ShapesAre`: `AtMg.hinge`,
Johnson/P5J/HingeAtMg.lean, and its like at the first and the last segment) with its closed fact `written_codes`
(Johnson/Desc/First/Close/Law/LengthsOfShapes.lean) names such a member; that sentence is stated at a stronger sense of
"reached" than the invariant gives, and it is not called here. The prover H, the book Bk and the further parameters of
`lettersHead` (Sc, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, w) are variables. The statements are implications: they
are idle at a border at which the invariant holds at no state, and where the step rejects. Without an acceptance nothing
is said: this is not the claim that the closing accepts. It is not shown that the invariant holds in any run. Whether
the head can be had at any files is not shown here. The full size and the older hash alone. No property of the protocol
is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Behind
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.K10.Honest.BaseOfYes
import Johnson.Desc.ReqLit.Full
import Johnson.P5J.K03OneOwnAt
import Johnson.P5J.CodesFullAtMg
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place Strs OpenedColumn)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.ReqLit (shapeFull shapeFull_groups)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.G (codesFull2)
open OnBytes.Means (InOrder)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-! ## Two closed facts at the full size -/

/-- Every group of the written request's shape has at most 8 row variables. -/
theorem groups_k_le : ∀ G ∈ (OnBytes.reqGroups shapeFull).toList, G.k ≤ 8 := by
  intro G hG
  have h1 : (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain)) ∈
      (OnBytes.reqGroups shapeFull).toList.map (fun G =>
        (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain))) :=
    List.mem_map.2 ⟨G, hG, rfl⟩
  rw [shapeFull_groups] at h1
  have h2 : ∀ y ∈ ((8, 0, []) ::
      ((List.replicate 12 [(7, 0, [(9, false), (3, true)]), (8, 0, [(3, false)])]).flatten ++
        [(1, 0, [])]) : List (Nat × Nat × List (Nat × Bool))), y.1 ≤ 8 := by
    decide
  exact h2 _ h1

/-- The `logEll` of the main code that the written shape names, among the written codes, is at most 55. -/
theorem logEll_full : (codesFull2.base.getD shapeFull.code default).logEll ≤ 55 := by
  decide +kernel

/-! ## At the head's thread -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: this file's head, "The notation, and the
-- option in front of it".
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- Wherever the invariant holds at a border of the chain: the statement is in order, its codes and the live frame's
shape are the head's, and the live frame's groups are those of its shape. -/
theorem facts_at_thr {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length) (hT : Thr 𝕋 b k s m E) :
    InOrder s.st ∧ s.st.codes = P5J.At.cs Zp ∧ s.live.frame.shape = P5J.At.shape Zp ∧
      s.live.frame.groups = OnBytes.reqGroups s.live.frame.shape := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, -, -, -, -⟩ := hT'
  have hn : s.failed.isNone = true := hP.1
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hn
  have FF := foldFacts_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w
  have f1 := FF.tidy b (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hf
  have f2 := FF.codes b (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hf
  have f3 := FF.liveShape b (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hf
  have f4 := FF.liveGroups b (m.st.input.x.pub, s) ⟨hb, k, m, E, hT, rfl⟩ hf
  exact ⟨(OnBytes.Means.tidy4B_iff.1 f1).inOrder, f2, f3, f4⟩

/-- **Where the invariant holds at the border before the closing of segment l and the closing's block's step accepts**,
the facts `CloseBase` hold of the record before the step, given its fields termsOk and maskCode. -/
theorem closeBase_at_step {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m E) {ft : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat}
    (hs : blk.step ft s rs cols = .ok (s', n))
    (hTerms : ∀ G, (recOf s).st.groups[(recOf s).frame.group]? = some G →
      ∀ q ∈ (OnBytes.Slice.runRows (recOf s).st G).toList, ∀ u ∈ q.terms.toList, u.part = .main → u.v.ok = true)
    (hMask : ∀ G, (recOf s).st.groups[(recOf s).frame.group]? = some G →
      G.maskCode = (recOf s).frame.shape.maskCode) :
    ∃ D₀ : BaseData, CloseBase Qc (recOf s) D₀ := by
  obtain ⟨-, -, hD, -, -⟩ := tied_decides Td hs
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hb : 14 * l + IM.nAt l + 5 ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  obtain ⟨hI, hc, hsh, hg⟩ := facts_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hC : s.st.codes.lengthsOk = true := by
    rw [hc]
    exact h.three.1
  have hBits : ∀ Gq, (recOf s).frame.groups[(recOf s).frame.link]? = some Gq →
      Gq.k + ((recOf s).st.codes.base.getD (recOf s).frame.shape.code default).logEll ≤ 63 := by
    intro Gq hq
    have hq' : s.live.frame.groups[s.live.frame.link]? = some Gq := hq
    rw [hg, hsh, h.toAtMg.shapeAt_full] at hq'
    have hk : Gq.k ≤ 8 := groups_k_le Gq (Array.mem_toList_iff.2 (Array.mem_of_getElem? hq'))
    have hle : (s.st.codes.base.getD s.live.frame.shape.code default).logEll ≤ 55 := by
      rw [hc, hsh, h.toAtMg.codes_full, h.toAtMg.shapeAt_full]
      exact logEll_full
    show Gq.k + (s.st.codes.base.getD s.live.frame.shape.code default).logEll ≤ 63
    omega
  exact YesFree.closeBase_of_closing hD hI hC hTerms hMask hBits

/-- **The same with the acceptance taken from a thread's step at the closing's block.** -/
theorem closeBase_at_stepped {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m E) {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hS : (𝕋).Stepped blk k s m E ds y cols s')
    (hTerms : ∀ G, (recOf s).st.groups[(recOf s).frame.group]? = some G →
      ∀ q ∈ (OnBytes.Slice.runRows (recOf s).st G).toList, ∀ u ∈ q.terms.toList, u.part = .main → u.v.ok = true)
    (hMask : ∀ G, (recOf s).st.groups[(recOf s).frame.group]? = some G →
      G.maskCode = (recOf s).frame.shape.maskCode) :
    ∃ D₀ : BaseData, CloseBase Qc (recOf s) D₀ :=
  closeBase_at_step h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hT hS.2 hTerms hMask

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.groups_k_le
#print axioms ProofFile.Honest.K10.logEll_full
#print axioms ProofFile.Honest.K10.facts_at_thr
#print axioms ProofFile.Honest.K10.closeBase_at_step
#print axioms ProofFile.Honest.K10.closeBase_at_stepped
