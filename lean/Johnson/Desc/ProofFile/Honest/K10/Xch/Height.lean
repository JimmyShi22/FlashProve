-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Height.lean: at the first chain's thread under the library's head, at the border
before the closing of segment l (kind K10): the plan's h at the closing is the h of the frame's group. This is the
conclusion of the premise height of `CarryOwed` (Xch/CarryTop.lean) and of `CarryDebt` (Xch/Carry.lean), proved from the
head, `Tied`, the invariant at the border and `CloseBase`. No definition; five theorems; one local notation.

What it rests on. Both sides are 0. At the full size every group that the program makes of the written request's shape
has h = 0 (`shapeFull_groups`, Johnson/Desc/ReqLit/Full.lean, writes the groups out). Under the head the plan's h is
read off such a group, and so is the h of the frame's group at the border. So `height_at_thr` is a fact of the full
size's written shape and not a law of the kind: the two sides are read off one list, the groups of the written shape,
and are not shown to be read at one index of it; at another shape nothing is claimed.

The words are those of the heads of Xch/Carry.lean and Xch/BaseAt.lean: a thread, the head, a border, the record
`K9.recOf s`, `CloseBase`, `Tied`. The first state: the field s₀ of the public part (`ProofFile.Pub`,
Johnson/Desc/ProofFile/Pub.lean), the state before the first segment. The plan's numbers at a closing: the value of
`ProofFile.k10Par` (Johnson/Desc/ProofFile/Lot/K9.lean).

  `groups_h_zero`   every group of the written request's shape at the full size has h = 0. From `shapeFull_groups`;
      the twin of `groups_k_le` (Xch/BaseAt.lean)
  `k10Par_group`   where `ProofFile.k10Par Z xs p` returns P: the frame of Z's first state has a group at the index p.link,
      and P's k and h are that group's. By the text of `ProofFile.k10Par`; the twin of `IM.k10Par_fields`
      (Johnson/IMR/LinkSeat.lean). At every Z, xs and p; no head
  `first_frame_groups`   where the plain road returns the public part Z: the groups of the frame of Z's first state
      are those that the program makes of the first chain's shape. By `Meaning.K2.pub_start` (Johnson/IMR/RecRun.lean)
      and the text of `S.startP` and `S.firstRecord` (Johnson/Desc/First/State.lean). At every earlier hash; no head
  `k10Par_h_head`   under `P5J.AtMg` (Johnson/P5J/AtMg.lean), at every earlier hash: where `ProofFile.k10Par Zp xs p` returns
      Q, Q.h = 0. The shape is the written one by `P5J.AtMg.shape_full` (Johnson/P5J/ShapeFullAtMg.lean)
  **`height_at_thr`**   at a block that `Tied` names (Td): wherever the invariant holds at the border before the closing
      of segment l and `CloseBase` holds of the record at D: Qc.h = D.Gq.h. The live frame's groups are those of the
      head's shape (`facts_at_thr`, Xch/BaseAt.lean), which is the written one (`P5J.AtMg.shapeAt_full`,
      Johnson/P5J/CodesFullAtMg.lean). At every value of the thread's parameter carryX

The notation, and the option in front of it. 𝕋 stands for the head's thread at a variable carryX, as in
Xch/CarryTop.lean. It declares no new name, neither a definition nor a theorem: each use is that text, elaborated anew.
When a notation is declared, Lean looks through its text for names that are not bound, and that early look has no case
for a field access. `set_option quotPrecheck false in` turns that one look off for the one command behind it; it loosens
nothing in what Lean checks of a theorem.

Limits. Every premise of `height_at_thr`, by name. h: the head. Td: `Tied`; of it the proof spends two members, that
`ProofFile.k10Par` returns Qc and that the chain has a block at the closing's number. hT: the invariant holds at the border.
Hb: `CloseBase`; of it the proof spends the field group alone. None of the four is shown of a run, a prover, a script or
a state. The statement is an implication: it is idle at a border at which the invariant holds at no state, and where
`CloseBase` holds at no D. It says nothing on whether the closing accepts. That p.link is the link of the live frame at
the border is neither used nor shown. The written shape comes through the first of the head's two entry tests on written
values (`P5J.AtMg.pins`, Johnson/P5T/FenceAtMg.lean), by the text of `P5J.AtMg.shape_full`. No theorem of this file lays
the equation into `CarryOwed` or `CarryDebt`: both keep their field height. The prover H, the book Bk and the further
parameters of `lettersHead` (Sc, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, w) are variables. Whether the head can be
had at any files is not shown here. The full size alone; `height_at_thr` at the older hash alone. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.BaseAt
import Johnson.Desc.ProofFile.Honest.K10.SimLot
import Johnson.Desc.ProofFile.Lot.K9
import Johnson.Desc.K10.Honest.Base
import Johnson.Desc.ReqLit.Full
import Johnson.IMR.RecRun
import Johnson.IMR.WrittenList
import Johnson.P5J.ShapeFullAtMg
import Johnson.P5J.CodesFullAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.ReqLit (shapeFull shapeFull_groups)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-! ## A closed fact at the full size -/

/-- Every group of the written request's shape has h = 0. -/
theorem groups_h_zero : ∀ G ∈ (OnBytes.reqGroups shapeFull).toList, G.h = 0 := by
  intro G hG
  have h1 : (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain)) ∈
      (OnBytes.reqGroups shapeFull).toList.map (fun G =>
        (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain))) :=
    List.mem_map.2 ⟨G, hG, rfl⟩
  rw [shapeFull_groups] at h1
  have h2 : ∀ y ∈ ((8, 0, []) ::
      ((List.replicate 12 [(7, 0, [(9, false), (3, true)]), (8, 0, [(3, false)])]).flatten ++
        [(1, 0, [])]) : List (Nat × Nat × List (Nat × Bool))), y.2.1 = 0 := by
    decide
  exact h2 _ h1

/-! ## The plan's numbers at a closing, and the first state's frame -/

/-- Where `ProofFile.k10Par` returns, the frame of the first state has a group at the index p.link, and the k and the h that
are returned are that group's. -/
theorem k10Par_group {Z : ProofFile.Pub} {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)}
    {p : VerifiableInference.Desc.K9.Where} {P : Par} (h : ProofFile.k10Par Z xs p = some P) :
    ∃ Gr, Z.s₀.check.frame.groups[p.link]? = some Gr ∧ P.k = Gr.k ∧ P.h = Gr.h := by
  unfold ProofFile.k10Par at h
  obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Gr, hG, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    exact ⟨Gr, hG, rfl, rfl⟩
  · cases h

/-- Where the plain road returns the public part, the groups of the frame of its first state are those that the program
makes of the first chain's shape. -/
theorem first_frame_groups {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    Z.s₀.check.frame.groups = OnBytes.reqGroups Z.first.shape := by
  have k := Meaning.K2.pub_start hZ
  unfold VerifiableInference.Desc.First.S.startP at k
  split at k
  · rw [← Option.some.inj k]
    rfl
  · cases k

/-- Under `P5J.AtMg`: the h that `ProofFile.k10Par` returns is 0. -/
theorem k10Par_h_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (h : P5J.AtMg o Z D₀ r Zp Np cF)
    {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)} {p : VerifiableInference.Desc.K9.Where} {Q : Par}
    (hQ : ProofFile.k10Par Zp xs p = some Q) : Q.h = 0 := by
  obtain ⟨Gr, hG, -, hh⟩ := k10Par_group hQ
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  rw [first_frame_groups hZ, h.shape_full] at hG
  rw [hh]
  exact groups_h_zero Gr (Array.mem_toList_iff.2 (Array.mem_of_getElem? hG))

/-! ## At the head's thread, at every value of the parameter carryX -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
variable (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: this file's head, "The notation, and the
-- option in front of it".
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a block that `Tied` names: wherever the invariant holds at the border before the closing of segment l and
`CloseBase` holds of the record, the plan's h at the closing is the h of the frame's group.** Both are 0: a fact of the
full size's written shape. -/
theorem height_at_thr {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) {D : BaseData} (Hb : CloseBase Qc (K9.recOf s) D) :
    Qc.h = D.Gq.h := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hb : 14 * l + IM.nAt l + 5 ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  obtain ⟨-, -, hsh, hg⟩ := facts_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hq : s.live.frame.groups[s.live.frame.link]? = some D.Gq := Hb.group
  rw [hg, hsh, h.toAtMg.shapeAt_full] at hq
  have hR : D.Gq.h = 0 := groups_h_zero D.Gq (Array.mem_toList_iff.2 (Array.mem_of_getElem? hq))
  exact (k10Par_h_head h.toAtMg Td.2.1).trans hR.symm

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.groups_h_zero
#print axioms ProofFile.Honest.K10.k10Par_group
#print axioms ProofFile.Honest.K10.first_frame_groups
#print axioms ProofFile.Honest.K10.k10Par_h_head
#print axioms ProofFile.Honest.K10.height_at_thr
