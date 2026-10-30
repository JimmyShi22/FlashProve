-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/Terms.lean: the closing of a segment (K10): at every state that the first chain
reaches in front of a closing, every structured vector on a main table, among the terms of every row that the proximity
test on the segment's group takes in, passes the library's test `Tensor.ok`. This is the field termsOk of `CloseBase`
(Johnson/Desc/K10/Honest/Base.lean).

Why it holds. The rows taken in (`runRows`) are the group's open rows and its members' stored sample rows. The open rows
passed `Tensor.ok` where they were laid (Johnson/AtFull/Shape/OpenRowsOrder.lean). A stored sample row is the program's
own sample row at some seed; its one term on the main table is an equality vector at the first coordinates of the seed's
point, as many as the main table has index bits; it has no written-out factor, so `Tensor.ok` asks only that these bits
are at most 63. The members' shapes are the written ones, and at the written codes each has at most 63: by the kernel.

  `eq_ok`             an equality vector at a point of at most 63 coordinates passes `Tensor.ok`
  `sample_main_ok`    so does the main term of each of the program's sample rows, where the main table has at most 63 bits
  `runRows_main_ok`   general: open rows that pass, and members whose sample rows' main terms pass: so do all rows taken in
  `written_mainBits`  at the 25 written lists and the written codes each member's main table has at most 63 index bits
  **`terms_reached`**  the sentence of the first lines, under the head

Limits. "Reached" is taken with the test on the words in front of each decision (`Reach 0 (cF.blocksInOrder.map below) …`): the
library's invariant on the sample rows stands at that family. Terms on a mask table are not spoken of. Where the group
has no row and no member the sentence holds for nothing. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.AtFull.Shape.TakenRowsOrder
import OnBytes.Slice.BlkSend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2 (RowsAre SampleGoodS)
open VerifiableInference.Desc.First.Close (ShapesAre)
open VerifiableInference.Desc.Sound (below)
open Johnson.G (linksFullLit codesFull2)
open Johnson.AtFull.Shape (OpenOrd RowOrd openOrd_reach)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- An equality vector at a point of at most 63 coordinates passes `Tensor.ok`. -/
theorem eq_ok (z : List E) (c : E) (h : z.length ≤ 63) : (Tensor.eq z c).ok = true := by
  simp [Tensor.ok, Tensor.eq, Tensor.vars, distinctNats, h]

/-- The main term of each of the program's own sample rows passes `Tensor.ok`, where the message's main table has at
most 63 index bits. -/
theorem sample_main_ok {codes : Codes} {s : OracleShape} {o : Nat} {seeds : List SampleSeed}
    {rows : Array OnBytes.Row} (h : RowsAre codes s o seeds rows) (hb : (Send.cube codes s).mainBits ≤ 63) :
    ∀ q ∈ rows.toList, ∀ t ∈ q.terms.toList, t.part = .main → t.v.ok = true := by
  intro q hq t ht hp
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hq
  have hi' : i < rows.size := by simpa using hi
  obtain ⟨seed, row, y, -, hf, hy⟩ := h.2 i (h.1 ▸ hi')
  have e' : rows[i]? = some q := by
    rw [Array.getElem?_eq_getElem hi']
    simpa using e
  obtain rfl : ({ row with target := y } : OnBytes.Row) = q := Option.some.inj (hy.symm.trans e')
  have ht' : t ∈ row.terms.toList := ht
  rw [(form_parts codes s o seed i row hf).1, List.mem_append] at ht'
  have hmain : (sendTensor codes s seed.z .main).ok = true :=
    eq_ok _ _ (Nat.le_trans (List.length_take_le _ _) hb)
  rcases ht' with ht' | ht'
  · split at ht'
    · rcases List.mem_singleton.1 ht' with rfl
      exact hmain
    · cases ht'
  · split at ht'
    · rcases List.mem_singleton.1 ht' with rfl
      cases hp
    · cases ht'

/-- **Every main term of every row that a proximity test on a group takes in passes `Tensor.ok`**, where the open rows
pass it and the main terms of the members' stored sample rows do. -/
theorem runRows_main_ok {T : Statement} (hO : OpenOrd T) {g : Nat} {G : Group} (hG : T.groups[g]? = some G)
    (hS : ∀ o ∈ G.members.toList, ∀ x, T.oracles[o]? = some x → ∀ q ∈ x.sampleRows.toList,
      ∀ t ∈ q.terms.toList, t.part = .main → t.v.ok = true) :
    ∀ q ∈ (runRows T G).toList, ∀ t ∈ q.terms.toList, t.part = .main → t.v.ok = true := by
  have key : ∀ (l : List Nat) (acc : Array OnBytes.Row), (∀ o ∈ l, o ∈ G.members.toList) →
      (∀ q ∈ acc.toList, ∀ t ∈ q.terms.toList, t.part = .main → t.v.ok = true) →
      ∀ q ∈ (l.foldl (fun a o => a ++ ((T.oracles[o]?).map (·.sampleRows)).getD #[]) acc).toList,
        ∀ t ∈ q.terms.toList, t.part = .main → t.v.ok = true := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons o l ih =>
      intro acc hl hacc
      refine ih _ (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) fun q hq => ?_
      rw [Array.toList_append, List.mem_append] at hq
      rcases hq with hq | hq
      · exact hacc q hq
      · cases hx : T.oracles[o]? with
        | none =>
          rw [hx] at hq
          cases hq
        | some x =>
          rw [hx] at hq
          exact hS o (hl o (List.mem_cons_self ..)) x hx q hq
  intro q hq
  unfold runRows at hq
  rw [Array.toList_append, Array.toList_append, List.mem_append, List.mem_append] at hq
  rcases hq with (hq | hq) | hq
  · rw [Array.toList_filter] at hq
    exact fun t ht _ => (hO g G hG q (List.mem_filter.1 hq).1).1 t ht
  · rw [← Array.foldl_toList] at hq
    exact key _ _ (fun _ h => h) (fun _ h => by cases h) q hq
  · rw [Array.toList_filter] at hq
    exact fun t ht _ => (hO g G hG q (List.mem_filter.1 hq).1).1 t ht

set_option maxRecDepth 100000 in
/-- At the 25 written lists and the written codes each member's main table has at most 63 index bits: by the kernel. -/
theorem written_mainBits :
    ((List.range 25).all fun l => (VerifiableInference.Desc.First.Close.membersOf (linksFullLit.getD l [])).all fun i =>
      decide ((Send.cube codesFull2 ((linksFullLit.getD l []).get i).1).mainBits ≤ 63)) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, in front of each closing: every main term of every row that the test on the segment's group takes
in passes `Tensor.ok`.** -/
theorem terms_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub}
    {s : TS} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s))
    (hf : s.failed = none) :
    ∀ G, (VerifiableInference.Desc.K9.recOf s).st.groups[(VerifiableInference.Desc.K9.recOf s).frame.group]? =
        some G →
      ∀ q ∈ (runRows (VerifiableInference.Desc.K9.recOf s).st G).toList, ∀ t ∈ q.terms.toList,
        t.part = .main → t.v.ok = true := by
  intro G hG
  have hr0 := reach_raw hr
  have hk : 14 * l + IM.nAt l + 5 ≤ 353 := by
    unfold IM.nAt
    split <;> omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hGood : SampleGoodS s.st := (P1K2.both_at_open O h.laid.value h.laid.planOk
    (by rw [Meaning.K2.front_len h.scope h.reads O]; exact hk) hr).1
  have HS := shapes_reached h hl hr0 hf G hG
  obtain ⟨-, hc, -, -, -⟩ := facts_reached h hr0 hf
  refine runRows_main_ok (T := s.st) (openOrd_reach h hr0) hG ?_
  intro o ho y hy q hq
  have hs : y.sampleRows.size ≠ 0 := by
    intro e
    have : y.sampleRows.toList = [] := by
      rw [← List.length_eq_zero_iff]
      simpa using e
    rw [this] at hq
    cases hq
  obtain ⟨seeds, hA, -⟩ := hGood o y hy hs
  rw [HS.members] at ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
  have hsh := HS.shape i hi
  have hy' : (VerifiableInference.Desc.K9.recOf s).st.oracles[_]? = some y := hy
  rw [hy'] at hsh
  have e1 : y.shape = ((linksFullLit.getD l []).get i).1 := Option.some.inj hsh
  have hb : (Send.cube s.st.codes y.shape).mainBits ≤ 63 := by
    rw [hc, h.toAtMg.codes_full, e1]
    exact of_decide_eq_true (List.all_eq_true.1
      (List.all_eq_true.1 written_mainBits l (List.mem_range.2 hl)) i hi)
  exact sample_main_ok hA hb q hq

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.eq_ok
#print axioms ProofFile.Honest.K10.sample_main_ok
#print axioms ProofFile.Honest.K10.runRows_main_ok
#print axioms ProofFile.Honest.K10.written_mainBits
#print axioms ProofFile.Honest.K10.terms_reached
