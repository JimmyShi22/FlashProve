-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TakenRowsOrder.lean: UNDER THE HEAD `P5J.AtMgA`: AT EVERY STATE THAT THE PROOF
FILE's OWN FIRST CHAIN REACHES FROM ITS OWN START AT A BORDER UP TO THE LAST CODE SWITCH, WHOEVER
PLAYS, EVERY ROW THAT A PROXIMITY TEST ON ANY GROUP OF THE STATEMENT WOULD TAKE IN IS IN ORDER
(`OrderRow`, OnBytes/Slice/BlkProxOrder.lean: in each tensor among its terms and in its forms each
written-out variable is named once and has the pair (1, 1)). A joining of laws; nothing is
evaluated.

Why it holds. The rows that a test takes in (`runRows`, OnBytes/Slice/BlkBegin.lean) are the group's
open rows of two kinds and its members' stored sample rows. The open rows have passed `Tensor.ok`
where they were laid (OpenRowsOrder.lean). The stored sample rows are the program's own sample rows
at some seeds, and such a row has no written-out factor at all.

By what. The library has "every stored sample row is `Send.form` at some seed" as an invariant of
the first chain (`SampleGoodS`, Johnson/Top/H0/K2Hands/SampleChainS.lean) at the opening's own chain
(`P1K2.both_at_open`, Johnson/P1K2R/FoldSide.lean), that such a row is plain (`plainRow_form`,
OnBytes/Slice/BlkPlain.lean), that a plain row is in order (`orderRow_of_plain`, BlkProxOrder.lean),
and that a tensor that passes `Tensor.ok` is in order (`Tensor.inOrder_of_ok`,
OnBytes/Iop/FixLaws.lean).

Main names.
* `SamplesPlain T`: no stored sample row of any message of T has a written-out factor.
* `plain_of_rowsAre`, `samplesPlain_of_good`: the library's invariant gives it.
* `orderRow_of_rowOrd`: a row all of whose tensors pass `Tensor.ok` is in order.
* `runRows_order`: GENERAL: OpenOrd T and SamplesPlain T: every row of runRows T G is in order, at
  every group G of T.
* `samplesPlain_reached`: under the head, k ≤ 353: SamplesPlain at every state reached at border k.
* `openOrd_reach`: OpenRowsOrder.lean's top in the form "reached", at every border.
* `taken_order_reached`: under the head, k ≤ 353: the sentence of this file's first lines.

What it is for. The law by which a segment's closing returns asks one thing of values: that the rows
which go into the batching are in order. At a reached state that is this file's top.

Limits. "REACHED" IS TAKEN WITH THE TEST ON THE WORDS IN FRONT OF EACH DECISION (`Reach 0
(cF.blocksInOrder.map below) …`): the library's invariant on the sample rows stands at that family alone;
whoever holds a state that the chain's bare blocks reach owes that the words shown were below the
prime. BORDERS UP TO 353 ALONE: behind the last code switch the invariant on the sample rows is not
carried here: so not the state in front of the chain's last proximity test (border 354). "In order"
is less than `Tensor.ok`: nothing here bounds the number of a sample row's variables. NOT the rows
that a frame carries from a closing to the next code switch. Where a group has no row and no member
the sentence holds for nothing. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. At the format's second hash
function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.OpenRowsOrder
import Johnson.P1K2R.FoldSide
import Johnson.IMR.FinPin
import OnBytes.Slice.BlkPlain
import OnBytes.Slice.BlkProxOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Slice.ProxRun (OrderRow OrderForm orderRow_of_plain)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (RowsAre SampleGoodS)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-! ## 1 The stored sample rows -/

/-- **No stored sample row of any message has a written-out factor.** -/
def SamplesPlain (T : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), T.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, PlainRow r

/-- The rows that are the program's own sample rows at some seeds are plain. -/
theorem plain_of_rowsAre {codes : Codes} {s : OracleShape} {o : Nat} {seeds : List SampleSeed}
    {rows : Array OnBytes.Row} (h : RowsAre codes s o seeds rows) :
    ∀ r ∈ rows.toList, PlainRow r := by
  intro r hr
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hr
  have hi' : i < rows.size := by simpa using hi
  obtain ⟨seed, row, y, -, hf, hy⟩ := h.2 i (h.1 ▸ hi')
  have e' : rows[i]? = some r := by
    rw [Array.getElem?_eq_getElem hi']
    simpa using e
  obtain rfl : ({ row with target := y } : OnBytes.Row) = r := Option.some.inj (hy.symm.trans e')
  exact plainRow_form codes s o seed i row hf

/-- The library's invariant on the stored sample rows gives it. -/
theorem samplesPlain_of_good {T : Statement} (h : SampleGoodS T) : SamplesPlain T := by
  intro o x hx r hr
  have hs : x.sampleRows.size ≠ 0 := by
    intro e
    have : x.sampleRows.toList = [] := by
      rw [← List.length_eq_zero_iff]
      simpa using e
    rw [this] at hr
    cases hr
  obtain ⟨seeds, hA, -⟩ := h o x hx hs
  exact plain_of_rowsAre hA r hr

/-! ## 2 From the two sentences to the library's "in order" -/

/-- A row all of whose tensors pass Tensor.ok is in order. -/
theorem orderRow_of_rowOrd {r : OnBytes.Row} (h : RowOrd r) : OrderRow r :=
  ⟨fun t ht => Tensor.inOrder_of_ok _ (h.1 t ht),
    fun f hf v hv => Tensor.inOrder_of_ok _ (h.2 f hf v hv)⟩

/-- **EVERY ROW THAT A PROXIMITY TEST ON A GROUP TAKES IN IS IN ORDER**, where the open rows pass
Tensor.ok and the stored sample rows are plain. -/
theorem runRows_order {T : Statement} (hO : OpenOrd T) (hP : SamplesPlain T) {g : Nat} {G : Group}
    (hG : T.groups[g]? = some G) : ∀ r ∈ (runRows T G).toList, OrderRow r := by
  have key : ∀ (l : List Nat) (acc : Array OnBytes.Row), (∀ r ∈ acc.toList, OrderRow r) →
      ∀ r ∈ (l.foldl (fun a o => a ++ ((T.oracles[o]?).map (·.sampleRows)).getD #[]) acc).toList,
        OrderRow r := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons o l ih =>
      intro acc hacc
      refine ih _ fun r hr => ?_
      rw [Array.toList_append, List.mem_append] at hr
      rcases hr with hr | hr
      · exact hacc r hr
      · cases hx : T.oracles[o]? with
        | none =>
          rw [hx] at hr
          cases hr
        | some x =>
          rw [hx] at hr
          exact orderRow_of_plain (hP o x hx r hr)
  intro r hr
  unfold runRows at hr
  rw [Array.toList_append, Array.toList_append, List.mem_append, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · rw [Array.toList_filter] at hr
    exact orderRow_of_rowOrd (hO g G hG r (List.mem_filter.1 hr).1)
  · rw [← Array.foldl_toList] at hr
    exact key _ _ (fun _ h => by cases h) r hr
  · rw [Array.toList_filter] at hr
    exact orderRow_of_rowOrd (hO g G hG r (List.mem_filter.1 hr).1)

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The stored sample rows are plain at every state that is reached, with the test on the words in
front of each decision, at a border up to the last code switch. -/
theorem samplesPlain_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 353)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (p, s)) :
    SamplesPlain s.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact samplesPlain_of_good (P1K2.both_at_open O h.laid.value h.laid.planOk
    (by rw [Meaning.K2.front_len h.scope h.reads O]; exact hk) hr).1

/-- The open rows pass Tensor.ok at every reached state. -/
theorem openOrd_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} {p : ProofFile.InstPub}
    {s : S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (p, s)) : OpenOrd s.st := by
  obtain ⟨-, rs, cols, hf⟩ := hr.fold
  exact openOrd_reached h k 0 p rs cols _ hf

/-- **UNDER THE HEAD: AT SUCH A STATE EVERY ROW THAT A PROXIMITY TEST ON ANY OF ITS GROUPS WOULD
TAKE IN IS IN ORDER.** -/
theorem taken_order_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 353)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (p, s)) {g : Nat}
    {G : Group} (hG : s.st.groups[g]? = some G) : ∀ r ∈ (runRows s.st G).toList, OrderRow r :=
  runRows_order (openOrd_reach h (reach_raw hr)) (samplesPlain_reached h hk hr) hG

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.plain_of_rowsAre
#print axioms Johnson.AtFull.Shape.samplesPlain_of_good
#print axioms Johnson.AtFull.Shape.orderRow_of_rowOrd
#print axioms Johnson.AtFull.Shape.runRows_order
#print axioms Johnson.AtFull.Shape.samplesPlain_reached
#print axioms Johnson.AtFull.Shape.openOrd_reach
#print axioms Johnson.AtFull.Shape.taken_order_reached
