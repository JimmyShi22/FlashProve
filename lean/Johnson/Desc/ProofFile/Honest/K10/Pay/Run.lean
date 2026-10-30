-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/Run.lean: the closing of a segment (K10): four of the facts that the closing's
decision asks of the record in front of it (`CloseBase`, Johnson/Desc/K10/Honest/Base.lean), at the border in front of a
closing, under the library's head (`P5J.AtMgA`, at the older hash): the proximity test may begin (`beginRun`), the plan's
number of rows is the number of rows that the test takes in (`rows`), the group is in order (`inOrder`), and every row
taken in has passed the tests of the adding of a row (`rowsIn`).

First, with no head:
  `idle_of_held`      the table's test `rowsHeld` says of an open segment's group that no proximity test on it has begun
  `beginRun_ok`       the four clauses of `Ground.beginRunL` from four facts on the group
  `size_samples_one`, `runRows_size`   where each member holds one stored sample row, the test takes in the plain rows,
                    one row a member, and the generator rows
  `written_answers`, `written_one`, `written_member`   closed facts on the written lists of the 25 segments, by Lean's
                    kernel: every written message counts one answer; each list has a member
Then at a state that the chain's own blocks reach (`Reach`), without a mark of failure:
  `run_group_reached`, `run_inOrder_reached`, `run_rowsIn_reached`, `run_begin_reached`, `run_rows_reached`
Last at the head's thread: `run_held_thr`, `run_begin`, `run_rows`, `run_inOrder`, `run_rowsIn`.

Limits. `run_begin` takes as a premise that the group which the frame names is there. `run_begin_reached` and
`run_rows_reached` take the table's test `rowsHeld` at the border as a premise; the thread's invariant gives it.
`run_rows_reached` is at the reach by the blocks with the test on the words in front of each decision (`below`);
`run_rows` takes the thread's invariant together with `SaidOk`. Whether the head can be had at any files is not shown
here, nor that the invariant holds in any run. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.Desc.ProofFile.Honest.K10.Xch.Says
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.LPFE1R.RowsDueAt
import Johnson.LPFE1R.K10Small
import Johnson.Top.H0.Tw.K2C.OneStored
import Johnson.AtFull.Shape.TakenRowsOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (rowsHeld rowSegs Numbers Item)
open VerifiableInference.Desc.First.Close (Par ShapesAre kbAt noK10 codesZero written_codes kind entries)
open VerifiableInference.Desc.First.K2 (SampleGoodS AnsweredStored one_stored)
open VerifiableInference.Desc.LinkJoin (hm_at covered_laid k10_rows_due plain_of_held gens_of_held)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (MsgT below)
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.Means (InOrder GroupOk RowIn)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## 1 No head -/

/-- The table's test on the open rows says of an open segment's group that no proximity test on it has begun. -/
theorem idle_of_held {N : Numbers} {O : List Item} {s : TS} {m : Nat} {G : OnBytes.Group}
    (h : rowsHeld N O s = true) (hm : m ∈ rowSegs O) (hG : s.st.groups[N.groupAt m]? = some G) :
    G.inRun = false := by
  unfold rowsHeld at h
  have h1 := List.all_eq_true.1 h m hm
  simp only [hG, Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨h0, -⟩, -⟩ := h1
  simpa using h0

/-- The four clauses in front of the beginning of a proximity test. -/
theorem beginRun_ok {T : OnBytes.Statement} {g : Nat} {G : OnBytes.Group} (hG : T.groups[g]? = some G)
    (h1 : G.inRun = false) (h2 : G.members.size ≠ 0) (h3 : ∀ o ∈ G.members.toList, o < T.oracles.size) :
    Ground.ok (Ground.beginRunL T g) = true := by
  have n2 : G.members.isEmpty = false := by simp [Array.isEmpty, h2]
  have n3 : (G.members.all fun o => decide (o < T.oracles.size)) = true := by
    rw [← Array.all_toList]
    exact List.all_eq_true.2 fun o ho => decide_eq_true (h3 o ho)
  unfold Ground.ok Ground.beginRunL
  simp [hG, Ground.has, h1, n2, n3]

/-- Where each listed message holds one stored sample row, the gathering of the sample rows adds one row a message. -/
theorem size_samples_one (T : OnBytes.Statement) : ∀ (l : List Nat) (A : Array OnBytes.Row),
    (∀ o ∈ l, ∃ x : OnBytes.Oracle, T.oracles[o]? = some x ∧ x.sampleRows.size = 1) →
    (l.foldl (fun a o => a ++ ((T.oracles[o]?).map (·.sampleRows)).getD #[]) A).size = A.size + l.length
  | [], _, _ => rfl
  | o :: l, A, h => by
    obtain ⟨x, hx, h1⟩ := h o (List.mem_cons_self ..)
    rw [List.foldl_cons, size_samples_one T l _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')),
      Array.size_append, hx]
    show A.size + x.sampleRows.size + l.length = A.size + (l.length + 1)
    omega

/-- The number of rows that a proximity test takes in, where each member holds one stored sample row. -/
theorem runRows_size {T : OnBytes.Statement} {G : OnBytes.Group}
    (h : ∀ o ∈ G.members.toList, ∃ x : OnBytes.Oracle, T.oracles[o]? = some x ∧ x.sampleRows.size = 1) :
    (OnBytes.Slice.runRows T G).size = (G.rows.filter (·.kind == .plain)).toList.length +
      G.members.toList.length + (G.rows.filter (·.kind == .generator)).toList.length := by
  unfold OnBytes.Slice.runRows
  rw [Array.size_append, Array.size_append, ← Array.foldl_toList, size_samples_one T _ _ h]
  show _ + (0 + _) + _ = _
  simp only [Array.length_toList, Nat.zero_add]

set_option maxRecDepth 1000000 in
/-- Every message of the written lists counts one answer to its sample. -/
theorem written_answers : ∀ lo ∈ linksFullLit, ∀ x ∈ lo, x.1.answers = 1 := by decide +kernel

/-- The same at the list of one segment. -/
theorem written_one {l : Nat} (hl : l < 25) : ∀ x ∈ linksFullLit.getD l [], x.1.answers = 1 := by
  have hn : l < linksFullLit.length := by
    have e : linksFullLit.length = 26 := by decide
    omega
  intro x hx
  rw [List.getD_eq_getElem _ _ hn] at hx
  exact written_answers _ (List.getElem_mem hn) x hx

/-- Each of the 25 written lists has a member. -/
theorem written_member {l : Nat} (hl : l < 25) : (VerifiableInference.Desc.First.Close.membersOf (linksFullLit.getD l [])).length ≠ 0 := by
  have hz : codesZero (linksFullLit.getD l []) = true :=
    List.all_eq_true.1 written_codes.1 l (List.mem_range.2 hl)
  unfold codesZero at hz
  obtain ⟨h1, -⟩ := Bool.and_eq_true _ _ ▸ hz
  obtain ⟨i, hi, -⟩ := List.any_eq_true.1 h1
  exact fun e => by
    rw [List.length_eq_zero_iff.1 e] at hi
    cases hi

/-! ## 2 At what the chain's own blocks reach -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- In front of the closing of segment l the group that the record's frame names is the table's number for l. -/
theorem run_group_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub}
    {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) :
    (K9.recOf s).frame.group = (P5J.At.N Zp cF).groupAt l := by
  obtain ⟨-, rs, cols, hfd⟩ := hr.fold
  have hn : IM.nAt l = if l = 24 then 9 else 7 := rfl
  have b1 : 14 * l + 3 + (if l = 24 then 1 else 0) ≤ 14 * l + IM.nAt l + 5 := by
    rw [hn]
    split <;> omega
  have b2 : 14 * l + IM.nAt l + 5 ≤ 14 * l + 14 + (if l = 24 then 2 else 0) := by
    rw [hn]
    split <;> omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, hL, -, hg⟩ := _root_.Meaning.K2.group_all h.scope h.reads O hl b1 b2 hfd
  show (K9.recOf s).frame.group = l
  rw [frame_of_open hL]
  exact hg

/-- The group that the record's frame names is in order. At every border. -/
theorem run_inOrder_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) (hf : s.failed = none) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G → GroupOk (K9.recOf s).st G :=
  fun G hG => (facts_reached h hr hf).1.groups _ G hG

/-- Every row that a proximity test on that group takes in has passed the tests of the adding of a row. At every
border. -/
theorem run_rowsIn_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) (hf : s.failed = none) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G →
      ∀ q ∈ (OnBytes.Slice.runRows (K9.recOf s).st G).toList, RowIn (K9.recOf s).st G q :=
  fun G hG => (facts_reached h hr hf).1.runRows _ G hG

/-- **In front of a closing the proximity test on the frame's group may begin**, where the group is there and the
table's test on the open rows says yes. -/
theorem run_begin_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub}
    {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    (hH : rowsHeld (P5J.At.N Zp cF) (P5J.oAt (14 * l + IM.nAt l + 5)) s = true)
    (hG : ∃ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) :
    Ground.ok (Ground.beginRunL (K9.recOf s).st (K9.recOf s).frame.group) = true := by
  obtain ⟨G, hG⟩ := hG
  have e2 : LPFK10.ixK10 l = 14 * l + IM.nAt l + 5 := YesFree.number_is l
  rw [← e2] at hH
  have hG' : s.st.groups[(P5J.At.N Zp cF).groupAt l]? = some G := by
    rw [← run_group_reached h hl hr]
    exact hG
  have HS := shapes_reached h hl hr hf G hG
  refine beginRun_ok hG (idle_of_held hH (hm_at hl) hG') ?_ ((run_inOrder_reached h hr hf G hG).there)
  rw [HS.size]
  exact written_member hl

/-- **In front of a closing the plan's number of rows is the number of rows that the proximity test takes in.** blk: the
chain's block at the closing's number, with the rounds of the kind's block at Qc. -/
theorem run_rows_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub}
    {s : TS} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s))
    (hf : s.failed = none)
    (hH : rowsHeld (P5J.At.N Zp cF) (P5J.oAt (14 * l + IM.nAt l + 5)) s = true)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk) {Qc : Par}
    (hrd : blk.rounds = (kind (Cl := Unit) Qc).rounds) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G →
      Qc.rows = (OnBytes.Slice.runRows (K9.recOf s).st G).size := by
  intro G hG
  have hr0 := reach_raw hr
  have e2 : LPFK10.ixK10 l = 14 * l + IM.nAt l + 5 := YesFree.number_is l
  rw [← e2] at hH hblk
  have hG' : s.st.groups[(P5J.At.N Zp cF).groupAt l]? = some G := by
    rw [← run_group_reached h hl hr0]
    exact hG
  have hc := covered_laid h.scope h.laid hl
  have p1 := plain_of_held hH (hm_at hl) hG' hc
  have p3 := gens_of_held hH (hm_at hl) hG' hc
  have HS := shapes_reached h hl hr0 hf G hG
  have hk : 14 * l + IM.nAt l + 5 ≤ 353 := by
    have hn : IM.nAt l = if l = 24 then 9 else 7 := rfl
    rw [hn]
    split <;> omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hSG, hAS⟩ := P1K2.both_at_open O h.laid.value h.laid.planOk
    (by rw [Meaning.K2.front_len h.scope h.reads O]; exact hk) hr
  have hone : ∀ o ∈ G.members.toList, ∃ y : OnBytes.Oracle, (K9.recOf s).st.oracles[o]? = some y ∧
      y.sampleRows.size = 1 := by
    intro o ho
    rw [HS.members] at ho
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
    obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 (HS.shape i hi)
    have hy' : s.st.oracles[noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l i]? = some y := hy
    have ha : y.shape.answers = 1 := by
      rw [ey]
      exact written_one hl _ (List.get_mem _ _)
    have e1 := one_stored hSG hAS hy' ha
    rw [Array.getD_eq_getD_getElem?, hy'] at e1
    exact ⟨y, hy, e1⟩
  rw [k10_rows_due h.scope h.laid hl hblk hrd, runRows_size hone, p1, p3, HS.members, List.length_map]

end

/-! ## 3 At the head's thread -/

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

-- The first chain's thread under the head. The option turns off one early look at the notation's text, which has no
-- case for a field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- Wherever the invariant holds at a border: no mark of failure, and the table's test on the open rows says yes. -/
theorem run_held_thr {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 b k s m En) :
    s.failed = none ∧ rowsHeld (P5J.At.N Zp cF) (P5J.oAt b) s = true := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, -, -, -, -⟩ := hT'
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hF : (𝕋).formP b (m.st.input.x.pub, s) := hP.2
  exact ⟨hf, (held_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w b hF hf).1⟩

/-- **`CloseBase`'s field beginRun at a stand in front of a closing**, where the frame's group is there. -/
theorem run_begin {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En)
    (hG : ∃ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) :
    Ground.ok (Ground.beginRunL (K9.recOf s).st (K9.recOf s).frame.group) = true := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  obtain ⟨hf, hH⟩ := run_held_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT
  exact run_begin_reached h (link_lt h hlt)
    (thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT) hf hH hG

/-- **`CloseBase`'s field rows at a stand in front of a closing.** -/
theorem run_rows {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : ThrS 𝕋 SaidOk (14 * l + IM.nAt l + 5) k s m En) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G →
      Qc.rows = (OnBytes.Slice.runRows (K9.recOf s).st G).size := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  obtain ⟨hf, hH⟩ := run_held_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT.1
  have hrd : blk.rounds = (kind (Cl := Unit) Qc).rounds := by
    rw [Td.2.2.2.2.2.2.1]
    show _ = (entries Qc).map (fun e => ({ entry := e } : Fmt.DeclaredRound))
    unfold closeRounds
    rw [List.map_map]
    rfl
  exact run_rows_reached h (link_lt h hlt)
    (thrS_reach_below h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT) hf hH hblk hrd

/-- **`CloseBase`'s field inOrder at a stand.** -/
theorem run_inOrder {b : Nat} (hb : b ≤ cF.blocksInOrder.length) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env} (hT : Thr 𝕋 b k s m En) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G → GroupOk (K9.recOf s).st G :=
  run_inOrder_reached h (thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (run_held_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT).1

/-- **`CloseBase`'s field rowsIn at a stand.** -/
theorem run_rowsIn {b : Nat} (hb : b ≤ cF.blocksInOrder.length) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env} (hT : Thr 𝕋 b k s m En) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G →
      ∀ q ∈ (OnBytes.Slice.runRows (K9.recOf s).st G).toList, RowIn (K9.recOf s).st G q :=
  run_rowsIn_reached h (thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (run_held_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hT).1

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.idle_of_held
#print axioms ProofFile.Honest.K10.beginRun_ok
#print axioms ProofFile.Honest.K10.size_samples_one
#print axioms ProofFile.Honest.K10.runRows_size
#print axioms ProofFile.Honest.K10.written_answers
#print axioms ProofFile.Honest.K10.written_one
#print axioms ProofFile.Honest.K10.written_member
#print axioms ProofFile.Honest.K10.run_group_reached
#print axioms ProofFile.Honest.K10.run_inOrder_reached
#print axioms ProofFile.Honest.K10.run_rowsIn_reached
#print axioms ProofFile.Honest.K10.run_begin_reached
#print axioms ProofFile.Honest.K10.run_rows_reached
#print axioms ProofFile.Honest.K10.run_held_thr
#print axioms ProofFile.Honest.K10.run_begin
#print axioms ProofFile.Honest.K10.run_rows
#print axioms ProofFile.Honest.K10.run_inOrder
#print axioms ProofFile.Honest.K10.run_rowsIn
