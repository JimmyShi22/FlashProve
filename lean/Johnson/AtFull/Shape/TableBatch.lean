-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableBatch.lean: THE 25 BATCHING MEMBERS AT THE TABLE, AND THE SUM: AT ALL 358
MEMBERS, IN THE WEAKER FORM. Under the head P5J.AtMgA. Two closed facts on numbers are evaluated by
the kernel.

Why a weaker form. At a batching member the shape behind hangs on whether each run of claims
returns, and that hangs on values: so "where the member says yes and the step on shapes returns, it
returns the shape behind" is shown there only under the member's own tests on values. CarriesV
(BatchFrames.lean) says just that; its text is that of CarriesU in another house's third family for
 (Johnson/Desc/ProofFile/Honest/Thread/ShapeJ.lean, which is not imported here).

  `carriesV_of`: Carries gives CarriesV. `BothV cF Z G n`: for every ft: CarriesV and Returns at n
    at firstZA (Tab.g Z G) (Tab.vals Z G). `bothV_of`. `order_at`: the link's order of runs is the
    library's orderOf at the link's sort.
  `tab_batch_lay` (12), `tab_batch_att` (12), `tab_batch_head`: BothV at 14 l + 9 and at 347: the
    table's cell Tab.batch Z G l is the term that the seats' laws pin (BatchCells.lean,
    BatchCellsAtt.lean).
  `framedV` : Nat → Bool, `framedV_count` (358), `framedV_all`, `table_framesV`, **`table_all`**:
    under the head, with Bs what the maker's own ProofFile.baseOf returns at the public part: for every n
    < 358: BothV cF Zp Bs.G₀ n.

Limits. NOT ACCEPTANCE: TWO PREMISES, AT EVERY MEMBER, OF ONE RULE: the rule for acceptance in its
third family (another house's Johnson/Desc/ProofFile/Honest/Thread/ShapeJ.lean: nextJ_of_shape,
acceptedJ_of_shape; RuleAtTable.lean lays this table into it). THE ELDER RULE (accepted_of_shape,
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) ASKS THE STRONG Carries AT EVERY MEMBER: THE TABLE
HAS IT AT 333 OF 358 (TableFramesAll.lean): IT DOES NOT MEET THAT RULE. Both premises stand under
"the step on shapes returns": 26 steps have a guard on the shape in front, and IN WHAT THIS FILE
REACHES NO STATE IS SHOWN AT WHICH A STEP RETURNS, A GUARD ACCEPTS OR A TEST ACCEPTS: where a step
refuses, both premises say nothing. THREE LAWS SAY "IT ACCEPTS AT EVERY STATE REACHED IN FRONT OF
ITS MEMBER": of the closings' test closeInOrdB (CloseInOrder.lean, which this file reaches:
TableFramesAll.lean's Limits) and, in files that this one does not reach, of switchW, the test at
the links' code switches and at the finish (switchW_under_head, LinkGuardCell.lean), and of linkGd,
the guard at the links' code switches (linkGd_under_head, LinkGuardHead.lean); none of them shows
that a state is reached in front of any member but the first. The third family asks more: that the
run on shapes returns; the fits; the values; the first state's shape. WHAT THE TABLE TESTS AS
"VALUES" IS MORE THAN VALUES at the one equation's 25 numbers and at the 25 closings
(TableFramesAll.lean's Limits). The batching's test on values runs the member's own gathering: it is
as dear as the member. That the head has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableFramesAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)
open ProofFile.Honest (Carries Returns Shape)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- "Carries" gives "carries under the member's own tests on values". -/
theorem carriesV_of {Cl : Type} {bs : List (Block S Cl)} {ft : Nat} {Zs : Shape S} {b : Nat}
    (h : Carries bs ft Zs b) : CarriesV bs ft Zs b :=
  fun blk hb s rs cols s' n t hs hg _ => h blk hb s rs cols s' n t hs hg

/-- The two premises in the weaker form, at the table's own letters. -/
def BothV (cF : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (G : ProofFile.Ground) (n : Nat) : Prop :=
  ∀ ft : Nat, CarriesV cF.blocksInOrder ft (firstZA (Tab.g Z G) (Tab.vals Z G)) n ∧
    Returns cF.blocksInOrder ft (firstZA (Tab.g Z G) (Tab.vals Z G)) n

/-- The stronger pair gives the weaker. -/
theorem bothV_of {G : ProofFile.Ground} {n : Nat} (h : Both cF Zp G n) :
    BothV cF Zp G n := fun ft => ⟨carriesV_of (h ft).1, (h ft).2⟩

/-- The link's order of runs, under the head. -/
theorem order_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {Lk : Link S ProofFile.Cl} (hL : cF.links[l]? = some Lk) :
    Lk.order = VerifiableInference.Desc.First.orderOf (subAt l) := by
  obtain ⟨Lk', -, -, -, e, -, -, -, ho, -⟩ := batch_named h l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hL)
  exact ho

/-- The batching of a layers' link: the weaker pair at 14 (2 k) + 9, at the table's own cell. -/
theorem tab_batch_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (hk : k < 12) : BothV cF Zp Bs.G₀ (14 * (2 * k) + 9) := fun ft => by
  obtain ⟨B', Lk, p, w, e1, hL, e2, e3, hf⟩ := layers_batch h k hk
  obtain rfl := base_one hB e1
  rw [(numbers_at h (by omega) hL).1, order_at h (by omega) hL] at hf
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k) + 9) = Tab.batch Zp Bs.G₀ (2 * k) :=
    cells_link Zp Bs.G₀ (2 * k) 8 (by omega) (by omega) rfl
  unfold Tab.batch at hc
  rw [e2, e3] at hc
  simp only [show (2 * k == 24) = false from beq_eq_false_iff_ne.2 (by omega),
    show ((2 * k) % 2 == 0) = true from beq_iff_eq.2 (by omega), Bool.false_eq_true, if_false,
    if_true, show 2 * k / 2 = k from by omega] at hc
  exact hf ft _ _ (cell_g hc) (cell_v hc)

/-- The batching of an attention link: the weaker pair at 14 (2 k + 1) + 9. -/
theorem tab_batch_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (hk : k < 12) : BothV cF Zp Bs.G₀ (14 * (2 * k + 1) + 9) := fun ft => by
  obtain ⟨B', Lk, p, w, A, q, e1, hL, e2, e3, e4, e5, hf⟩ := att_batch h k hk
  obtain rfl := base_one hB e1
  rw [(numbers_at h (by omega) hL).1, order_at h (by omega) hL] at hf
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k + 1) + 9) = Tab.batch Zp Bs.G₀ (2 * k + 1) :=
    cells_link Zp Bs.G₀ (2 * k + 1) 8 (by omega) (by omega) rfl
  unfold Tab.batch at hc
  rw [e2, e3] at hc
  simp only [show (2 * k + 1 == 24) = false from beq_eq_false_iff_ne.2 (by omega),
    show ((2 * k + 1) % 2 == 0) = false from beq_eq_false_iff_ne.2 (by omega), Bool.false_eq_true,
    if_false, show (2 * k + 1) / 2 = k from by omega, e4, e5] at hc
  exact hf ft _ _ (cell_g hc) (cell_v hc)

/-- The batching of the head's link: the weaker pair at 347. -/
theorem tab_batch_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    BothV cF Zp Bs.G₀ 347 := fun ft => by
  obtain ⟨B', Lk, p, w, iU3, q, e1, hL, e2, e3, e4, e5, hf⟩ := head_batch h
  obtain rfl := base_one hB e1
  rw [(numbers_head h hL).2.1, order_at h (by omega) hL] at hf
  have hc : Tab.cells Zp Bs.G₀ 347 = Tab.batch Zp Bs.G₀ 24 :=
    cells_head Zp Bs.G₀ 10 (by omega) rfl
  unfold Tab.batch at hc
  rw [e2, e3] at hc
  simp only [beq_self_eq_true, if_true, e4, e5] at hc
  exact hf ft _ _ (cell_g hc) (cell_v hc)

/-- The numbers at which the two premises stand in the weaker form: the framed ones and the 25
batchings. -/
def framedV (n : Nat) : Bool :=
  framed n || (n < 337 && (n - 1) % 14 == 8) || n == 347

/-- All 358 numbers below 358 are among them. (It follows from framedV_all; a second line of Lean's
kernel for one fact.) -/
theorem framedV_count : ((List.range 358).filter framedV).length = 358 := by decide +kernel

/-- Every number below 358 is among them. -/
theorem framedV_all : (List.range 358).all framedV = true := by decide +kernel

/-- **"Carries under the member's own tests on values", and "returns", at the table's own steps and
tests**, at every number that `framedV` names. -/
theorem table_framesV (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (n : Nat)
    (hn : framedV n = true) : BothV cF Zp Bs.G₀ n := by
  unfold framedV at hn
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
  rcases hn with (hf | ⟨h1, hj⟩) | rfl
  · exact bothV_of (table_frames h hB n hf)
  · obtain ⟨k, hk⟩ : ∃ k, n = 14 * (2 * k) + 9 ∨ n = 14 * (2 * k + 1) + 9 :=
      ⟨(n - 1) / 28, by omega⟩
    rcases hk with rfl | rfl
    · exact tab_batch_lay h hB k (by omega)
    · exact tab_batch_att h hB k (by omega)
  · exact tab_batch_head h hB

/-- **AT ALL 358 MEMBERS**: the WEAKER pair (BothV: "carries" under the member's own tests on
values; "returns"). -/
theorem table_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (n : Nat) (hn : n < 358) :
    BothV cF Zp Bs.G₀ n :=
  table_framesV h hB n (List.all_eq_true.1 framedV_all n (List.mem_range.2 hn))

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.carriesV_of
#print axioms Johnson.AtFull.Shape.order_at
#print axioms Johnson.AtFull.Shape.tab_batch_lay
#print axioms Johnson.AtFull.Shape.tab_batch_att
#print axioms Johnson.AtFull.Shape.tab_batch_head
#print axioms Johnson.AtFull.Shape.framedV_count
#print axioms Johnson.AtFull.Shape.framedV_all
#print axioms Johnson.AtFull.Shape.table_framesV
#print axioms Johnson.AtFull.Shape.table_all
#print axioms Johnson.AtFull.Shape.bothV_of
#print axioms Johnson.AtFull.Shape.BothV
#print axioms Johnson.AtFull.Shape.framedV
