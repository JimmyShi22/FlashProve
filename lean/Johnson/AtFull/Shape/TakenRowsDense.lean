-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TakenRowsDense.lean: UNDER THE HEAD `P5J.AtMgA`: AT EVERY STATE THAT THE PROOF
FILE's OWN FIRST CHAIN REACHES AT A BORDER UP TO 354, WHOEVER PLAYS, EVERY ROW THAT A PROXIMITY TEST
ON ANY GROUP OF THE STATEMENT WOULD TAKE IN IS DENSE (`DenseRow`, OnBytes/Slice/BlkProxDense.lean:
in each tensor among its terms and in its forms no written-out variable is named twice, each has the
pair (1, 1), and the slice lies inside its vector). So of the state with which the chain's last
proximity test goes in. A joining of laws; nothing is evaluated.

Why "dense" and not "in order". TakenRowsOrder.lean and TakenRowsAt354.lean end in the library's
`OrderRow`, which lacks the clause on the slice. The verifier's own test on a form (`Own.formFits`,
Johnson/Desc/Own/Shapes.lean) has that clause, and "in order" does not give it (a tensor with one
written-out variable, the pair (1, 1) and no values is in order, and its slice leaves its vector:
`inOrder_not_dense`); "dense" does (`formFits_of_dense`, Johnson/Desc/Means/Dense.lean). What these
two files stand on gives the stronger sentence at no cost: the open rows pass the whole of
`Tensor.ok` (OpenRowsOrder.lean), and the stored sample rows have no written-out factor at all.

Main names.
* `denseRow_of_rowOrd`: a row all of whose tensors pass Tensor.ok is dense (`denseTensor_of_test`,
  Means/Dense.lean; `Own.tensorInOrder_agrees`, Johnson/Desc/Own/ShapesAgree.lean).
  `inOrder_not_dense`: there is a tensor that is in order and not dense.
* `runRows_denseOf`: GENERAL: OpenOrd T and SamplesPlain T: every row of runRows T G is dense, at
  every group G of T.
* `samplesPlain_upto_354`: under the head, k ≤ 354: SamplesPlain at every state reached at border k.
* `taken_dense_reached`: under the head, k ≤ 354: the sentence of this file's first lines.
* `taken_dense_entered`: where `enterFinish` (Johnson/Desc/K12/AtFinish.lean) makes the proximity
  test's own state t of a state reached at border 354: every row of runRows t.st G is dense at the
  group G number t.g.
* `samplesPlain_entered`, `samples_dense_entered`: the stored sample rows alone, at that t: they are
  plain; and, member by member of a group, dense.

Limits. "REACHED" IS TAKEN WITH THE TEST ON THE WORDS IN FRONT OF EACH DECISION (`Reach 0
(cF.blocksInOrder.map below) …`). Borders up to 354: nothing behind the proximity test. "Dense" is less than
`Tensor.ok`: nothing here bounds the number of a sample row's variables. NO LAW ON THE PROXIMITY
TEST IS CALLED OR SHOWN HERE: that it returns at any state is not said. That the head has a member
is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TakenRowsAt354
import Johnson.Desc.Means.Dense
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes.Means (denseTensor_of_test)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-! ## 1 General -/

/-- A row all of whose tensors pass Tensor.ok is dense. -/
theorem denseRow_of_rowOrd {r : OnBytes.Row} (h : RowOrd r) : DenseRow r :=
  ⟨fun t ht => denseTensor_of_test
      (by rw [← VerifiableInference.Desc.Own.tensorInOrder_agrees]; exact h.1 t ht),
    fun f hf v hv => denseTensor_of_test
      (by rw [← VerifiableInference.Desc.Own.tensorInOrder_agrees]; exact h.2 f hf v hv)⟩

/-- **"In order" does not give "dense"**: a tensor with one written-out variable, the pair (1, 1)
and no values is in order, and its slice leaves its vector. -/
theorem inOrder_not_dense : ∃ v : Tensor, v.InOrder ∧ ¬ OnBytes.Slice.ProxRun.DenseTensor v := by
  refine ⟨{ pairs := [(oneE, oneE)], denseVars := [0] }, ⟨by simp, ?_⟩, ?_⟩
  · intro d hd
    obtain rfl : d = 0 := by simpa using hd
    rfl
  · rintro ⟨-, h | h⟩
    · exact absurd h (by simp)
    · exact absurd h (by decide)

/-- **Every row that a proximity test on a group takes in is dense**, where the open rows pass
Tensor.ok and the stored sample rows are plain. -/
theorem runRows_denseOf {T : Statement} (hO : OpenOrd T) (hP : SamplesPlain T) {g : Nat}
    {G : Group} (hG : T.groups[g]? = some G) : ∀ r ∈ (runRows T G).toList, DenseRow r := by
  have key : ∀ (l : List Nat) (acc : Array OnBytes.Row), (∀ r ∈ acc.toList, DenseRow r) →
      ∀ r ∈ (l.foldl (fun a o => a ++ ((T.oracles[o]?).map (·.sampleRows)).getD #[]) acc).toList,
        DenseRow r := by
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
          exact denseRow_of_plain (hP o x hx r hr)
  intro r hr
  unfold runRows at hr
  rw [Array.toList_append, Array.toList_append, List.mem_append, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · rw [Array.toList_filter] at hr
    exact denseRow_of_rowOrd (hO g G hG r (List.mem_filter.1 hr).1)
  · rw [← Array.foldl_toList] at hr
    exact key _ _ (fun _ h => by cases h) r hr
  · rw [Array.toList_filter] at hr
    exact denseRow_of_rowOrd (hO g G hG r (List.mem_filter.1 hr).1)

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- No stored sample row has a written-out factor, at every border up to 354. -/
theorem samplesPlain_upto_354 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 354)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (p, s)) :
    SamplesPlain s.st := by
  rcases Nat.lt_or_ge k 354 with hlt | hge
  · exact samplesPlain_reached h (by omega) hr
  · obtain rfl : k = 354 := by omega
    exact samplesPlain_at_354 h hr

/-- **UNDER THE HEAD, AT EVERY STATE REACHED AT A BORDER UP TO 354: EVERY ROW THAT A PROXIMITY TEST
ON ANY GROUP OF THE STATEMENT WOULD TAKE IN IS DENSE.** -/
theorem taken_dense_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 354)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (p, s)) {g : Nat}
    {G : Group} (hG : s.st.groups[g]? = some G) : ∀ r ∈ (runRows s.st G).toList, DenseRow r :=
  runRows_denseOf (openOrd_reach h (reach_raw hr)) (samplesPlain_upto_354 h hk hr) hG

/-- **So of the state with which the chain's last proximity test goes in.** -/
theorem taken_dense_entered (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s))
    {t : VerifiableInference.Desc.K12.T12}
    (he : VerifiableInference.Desc.K12.enterFinish s = .ok t) :
    ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r := by
  obtain ⟨o, -, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s t he
  exact fun G hG => taken_dense_reached h (Nat.le_refl _) hr hG

/-- No stored sample row of that state's statement has a written-out factor. -/
theorem samplesPlain_entered (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s))
    {t : VerifiableInference.Desc.K12.T12}
    (he : VerifiableInference.Desc.K12.enterFinish s = .ok t) : SamplesPlain t.st := by
  obtain ⟨o, -, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s t he
  exact samplesPlain_at_354 h hr

/-- The members' stored sample rows alone, in the letters of a law that has the open rows from
elsewhere. -/
theorem samples_dense_entered (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub}
    {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s))
    {t : VerifiableInference.Desc.K12.T12}
    (he : VerifiableInference.Desc.K12.enterFinish s = .ok t) (G : Group) :
    ∀ o ∈ G.members.toList, ∀ y, t.st.oracles[o]? = some y →
      ∀ r ∈ y.sampleRows.toList, DenseRow r := by
  obtain ⟨o', -, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s t he
  exact fun o _ y hy r hr' => denseRow_of_plain (samplesPlain_at_354 h hr o y hy r hr')

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.denseRow_of_rowOrd
#print axioms Johnson.AtFull.Shape.inOrder_not_dense
#print axioms Johnson.AtFull.Shape.runRows_denseOf
#print axioms Johnson.AtFull.Shape.samplesPlain_upto_354
#print axioms Johnson.AtFull.Shape.taken_dense_reached
#print axioms Johnson.AtFull.Shape.taken_dense_entered
#print axioms Johnson.AtFull.Shape.samplesPlain_entered
#print axioms Johnson.AtFull.Shape.samples_dense_entered
