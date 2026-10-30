-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BatchValuesJ.lean: AT THE 25 BATCHINGS OF THE FIRST CHAIN THE TABLE's TEST ON VALUES ACCEPTS ON THE HONEST SIDE: the premise
`ValuesJ` (Honest/Thread/ShapeJV.lean) of the rule on shapes (`first_chain_debts_halved`, Johnson/AtFull/Shape/RuleAtTable.lean), at the table's own
tests `Tab.vals`, from one named premise a kind on the state in front of the batching. It joins `cellV_lay`, `cellV_att`, `cellV_head`
(Honest/K9/BatchValues.lean) with the table's cells, with what the prover's step shows at a place at which it has no side, and with
two facts on every reached state: the open ledger has its sizes (Honest/K9/SizedAtStand.lean) and is empty
(Honest/K9/FreshAtHead.lean).

THE THREAD T IS A LETTER. What is read of it:
  hbs      its list of sub-protocols is the first chain's
  hft      its trees are counted from 0 (so it is at each first chain's thread of the library: Honest/Thread/First.lean, FileRow.lean,
           FallRow.lean)
  hstart   its first state is the description's own first state at some public part of an instance
  hno      no side of the prover's list stands at a place of the batching's kind
Said IS A LETTER, AND NOTHING IS READ OF IT. fall IS A LETTER: where it is silent at the batching's number, the smallness test's named
fall `K8.k8Front` is silent (hfall).

  `StandJ T Said J b s`   s is a state in front of member b at which the invariant holds with what is said, and J
  `cellV_cols`           the table's test at a batching does not read the columns
  **`valuesJ_of_cell`**    `ValuesJ` at a batching's number, from the cell's equation and the cell's yes at the draw's one round
  `vals_lay`, `vals_att`, `vals_head`   the table's test at the three sorts of batching is `cellV` at that sort's rows
  `reach_of_stand`       the invariant at a border gives "reached" there
  `link_of_fork`, **`empty_at_batching`**   the open ledger in front of a batching is empty, at every reached state
  **`batch_values_lay`**, **`batch_values_att`**, **`batch_values_head`**   `ValuesJ` at 14 (2 g) + 8 + 1, at 14 (2 g + 1) + 8 + 1, at 337 + 10
  **`batch_values`**       at 14 l + 8 + 1 for every l below 24

WHAT IS LEFT, as premises, each at every `StandJ`: held (the smallness test's tables are held) · env (the feed-forward kind's
`planEnvB`) · vals (the attention kind's `valsTS`) · ends (the head's kind's `endsS`).

Limits. The four premises are shown of no state. That the invariant holds at any run is not shown: at a Said that never holds, or a fall
that always speaks, the statements are idle. The full size and the hash function `secondHashFunction` alone. This file proves no property of a
prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.BatchValues
import Johnson.Desc.ProofFile.Honest.K9.FreshAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (valsTS)
open Johnson.AtFull.Shape (cellV rowsLay rowsAtt rowsHead endsS firstZA cells_link cells_head cell_v)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA)

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A stand in front of member b**, with J in hand. -/
def StandJ (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) (J : ℕ → S → Prop) (b : ℕ)
    (s : S) : Prop := ∃ k m E, ThrS T Said b k s m E ∧ J b s

/-- The table's test at a batching does not read the columns. -/
theorem cellV_cols (p : Desc.K9.Where) (rows : List ((ℕ × String) × Johnson.AtFull.Shape.Row))
    (os : List (ℕ × String)) (s : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    cellV p rows os s rs gs = cellV p rows os s rs [] := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Lk : Link S ProofFile.Cl}
  {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **`ValuesJ` at a batching's number, from the cell.** -/
theorem valuesJ_of_cell {l k b : ℕ} (Sd : SeatedFree cF Zp l k Lk p w) (hb : b = 14 * l + k + 2)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hno : ∀ g ∈ T.hs, g.place.kind ≠ KindName.K9)
    (Said : ℕ → Coins Bk → Mid W X → Prop) (J : ℕ → S → Prop) (Zs : Shape S)
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall b s ds = none → K8.k8Front s ds = none)
    {rows : List ((ℕ × String) × Johnson.AtFull.Shape.Row)} (hv : Zs.vals b = cellV p rows Lk.order)
    (cell : ∀ s tr, StandJ T Said J b s → K8.k8Front s [⟨[tr], [], [], none⟩] = none →
      cellV p rows Lk.order s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = true) :
    ValuesJ T Said J Zs fall b := by
  intro blk hblk κ s m En ds y cols hT hJ hd _ hf hM
  rw [hbs, hb, Sd.batching] at hblk
  cases hblk
  obtain ⟨h1, h2, _⟩ := Sd.shape
  rw [h1] at hd
  obtain ⟨tr, rfl⟩ := draws_one p ds hd
  obtain ⟨hy, rfl⟩ := moved_noSide T p _ h1 h2 (none_at_batching Sd T.hs hno) κ m En _ y cols hM
  rw [hv, hy, cellV_cols]
  exact cell s tr ⟨κ, m, En, hT, hJ⟩ (hfall s _ hf)

/-! ## The table's cells -/

theorem vals_lay {g k : ℕ} (hg : g < 12) (Sd : SeatedFree cF Zp (2 * g) k Lk p w) (G : ProofFile.Ground) :
    Johnson.AtFull.Shape.Tab.vals Zp G (14 * (2 * g) + 8 + 1) = cellV p (rowsLay G.W g) Lk.order := by
  have hc : Johnson.AtFull.Shape.Tab.cells Zp G (14 * (2 * g) + 8 + 1) = Johnson.AtFull.Shape.Tab.batch Zp G (2 * g) :=
    cells_link Zp G (2 * g) 8 (by omega) (by omega) rfl
  unfold Johnson.AtFull.Shape.Tab.batch at hc
  rw [Sd.numbers, Sd.tested] at hc
  simp only [show (2 * g == 24) = false from beq_eq_false_iff_ne.2 (by omega),
    show ((2 * g) % 2 == 0) = true from beq_iff_eq.2 (by omega), Bool.false_eq_true, if_false,
    if_true, show 2 * g / 2 = g from by omega] at hc
  rw [Sd.order]
  exact cell_v hc

theorem vals_att {g k : ℕ} (hg : g < 12) (Sd : SeatedFree cF Zp (2 * g + 1) k Lk p w) (G : ProofFile.Ground)
    {A : Attention.Plan} {q : VerifiableInference.Desc.First.Look.P} (hA : G.W.A[g]? = some A)
    (hq : VerifiableInference.Desc.First.Look.placeAt G.W (2 * g + 1) false = some q) :
    Johnson.AtFull.Shape.Tab.vals Zp G (14 * (2 * g + 1) + 8 + 1) = cellV p (rowsAtt A q.lm) Lk.order := by
  have hc : Johnson.AtFull.Shape.Tab.cells Zp G (14 * (2 * g + 1) + 8 + 1) = Johnson.AtFull.Shape.Tab.batch Zp G (2 * g + 1) :=
    cells_link Zp G (2 * g + 1) 8 (by omega) (by omega) rfl
  unfold Johnson.AtFull.Shape.Tab.batch at hc
  rw [Sd.numbers, Sd.tested] at hc
  simp only [show (2 * g + 1 == 24) = false from beq_eq_false_iff_ne.2 (by omega),
    show ((2 * g + 1) % 2 == 0) = false from beq_eq_false_iff_ne.2 (by omega), Bool.false_eq_true,
    if_false, show (2 * g + 1) / 2 = g from by omega, hA, hq] at hc
  rw [Sd.order]
  exact cell_v hc

theorem vals_head {k : ℕ} (Sd : SeatedFree cF Zp 24 k Lk p w) (G : ProofFile.Ground) {iU3 : ℕ}
    {q : VerifiableInference.Desc.First.Look.P} (hU : G.W.H.tl.ix.U.getD 2 none = some iU3)
    (hq : VerifiableInference.Desc.First.Look.placeAt G.W 24 false = some q) :
    Johnson.AtFull.Shape.Tab.vals Zp G (337 + 10) = cellV p (rowsHead G.W iU3 q.lm) Lk.order := by
  have hc : Johnson.AtFull.Shape.Tab.cells Zp G (337 + 10) = Johnson.AtFull.Shape.Tab.batch Zp G 24 := cells_head Zp G 10 (by omega) rfl
  unfold Johnson.AtFull.Shape.Tab.batch at hc
  rw [Sd.numbers, Sd.tested] at hc
  simp only [beq_self_eq_true, if_true, hU, hq] at hc
  rw [Sd.order]
  exact cell_v hc

/-! ## Two facts on the state in front -/

/-- The invariant at a border gives "reached" there. -/
theorem reach_of_stand (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hstart : ∀ k w hd, ∃ z, ∀ s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp z)
    {Said : ℕ → Coins Bk → Mid W X → Prop} {J : ℕ → S → Prop} {b : ℕ} (hb : b ≤ cF.blocksInOrder.length) {s : S}
    (hS : StandJ T Said J b s) : ∃ z, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s) := by
  obtain ⟨k, m, E, hT, -⟩ := hS
  obtain ⟨z, hz⟩ := hstart k m.st.input (m.st.heard.take T.front)
  have hR := thr_reach_of T (ProofFile.startS Zp) z (by rw [hbs]; exact hb) hz hT.1
  rw [hbs, hft] at hR
  exact ⟨z, hR⟩

/-- Where a ledger is open, a segment's book-keeping is. -/
theorem link_of_fork {s : S} {G : Fork} (h : s.fork? = some G) : ∃ L, s.link? = some L := by
  cases hh : s.here with
  | between => simp [S.fork?, hh] at h
  | fin _ => simp [S.fork?, hh] at h
  | mem _ => simp [S.fork?, hh] at h
  | lay a => exact ⟨a.L, by simp [S.link?, hh]⟩
  | att a => exact ⟨a.L, by simp [S.link?, hh]⟩
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at h
    | true => exact ⟨a.L, by simp [S.link?, hh, ho]⟩

/-- **The open ledger in front of a batching is empty, at every reached state.** -/
theorem empty_at_batching (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub}
    {s : S} (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 2) (z, s)) :
    ∀ G, s.fork? = some G → Desc.K9.ledgerEmpty G = true := by
  intro G hG
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, hL⟩ := link_of_fork hG
  obtain ⟨L₀, G₀, ho, -, e, -⟩ := back_to_open h.scope h.reads O hl hz hL hG
  exact (fresh_of_cr e ho.fresh).empty

/-- "Reached" in front of the batching of segment l, at a stand. -/
theorem reach_at_batching (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (T : Thread Bk S ProofFile.Cl V W X Pb)
    (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hstart : ∀ k w hd, ∃ z, ∀ s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp z)
    {Said : ℕ → Coins Bk → Mid W X → Prop} {J : ℕ → S → Prop} {l b : ℕ} (hb : b = 14 * l + IM.nAt l + 2) (hl : l < 25)
    {s : S} (hS : StandJ T Said J b s) : ∃ z, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 2) (z, s) := by
  subst hb
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  refine reach_of_stand T hbs hft hstart ?_ hS
  rw [hlen]
  rcases ix_facts l with ⟨-, -, -, a⟩ | ⟨-, -, -, a⟩ <;> omega

/-! ## The premise of the rule on shapes -/

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
  (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (T : Thread Bk S ProofFile.Cl V W X Pb)
  (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
  (hstart : ∀ k w hd, ∃ z, ∀ s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp z)
  (hno : ∀ g ∈ T.hs, g.place.kind ≠ KindName.K9) (Said : ℕ → Coins Bk → Mid W X → Prop) (J : ℕ → S → Prop)
  (fall : ℕ → S → List Fmt.Drawn → Option String)
include h hB hbs hft hstart hno

/-- **At the feed-forward segment 2 g.** -/
theorem batch_values_lay {g : ℕ} (hg : g < 12)
    (hfall : ∀ s ds, fall (14 * (2 * g) + 8 + 1) s ds = none → K8.k8Front s ds = none)
    (held : ∀ s, StandJ T Said J (14 * (2 * g) + 8 + 1) s → ∀ tl funs, s.tl? = some tl → s.funs? = some funs →
      tl.funsHeld funs = true)
    (env : ∀ s, StandJ T Said J (14 * (2 * g) + 8 + 1) s →
      OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers s = true) :
    ValuesJ T Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (14 * (2 * g) + 8 + 1) := by
  have hl : 2 * g < 25 := by omega
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h (2 * g) hl
  rw [if_neg (by omega)] at Sd
  have hn : IM.nAt (2 * g) = 7 := by simp [IM.nAt]; omega
  refine valuesJ_of_cell Sd (by omega) T hbs hno Said J _ fall hfall (vals_lay hg Sd Bs.G₀) ?_
  intro s tr hS hfr
  obtain ⟨z, hz⟩ := reach_at_batching h T hbs hft hstart (by rw [hn]) hl hS
  exact cellV_lay h hg Sd hB (empty_at_batching h hl hz) hfr (held s hS) (env s hS)

/-- **At the attention segment 2 g + 1.** -/
theorem batch_values_att {g : ℕ} (hg : g < 12)
    (hfall : ∀ s ds, fall (14 * (2 * g + 1) + 8 + 1) s ds = none → K8.k8Front s ds = none)
    (held : ∀ s, StandJ T Said J (14 * (2 * g + 1) + 8 + 1) s → ∀ tl funs, s.tl? = some tl →
      s.funs? = some funs → tl.funsHeld funs = true)
    (vals : ∀ A, Bs.G₀.W.A[g]? = some A → ∀ s, StandJ T Said J (14 * (2 * g + 1) + 8 + 1) s → valsTS A s = true) :
    ValuesJ T Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (14 * (2 * g + 1) + 8 + 1) := by
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h (2 * g + 1) hl
  rw [if_neg (by omega)] at Sd
  have hn : IM.nAt (2 * g + 1) = 7 := by simp [IM.nAt]; omega
  obtain ⟨Bs', A, q, hB', hA, hq, -⟩ := tied_att h hg Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  refine valuesJ_of_cell Sd (by omega) T hbs hno Said J _ fall hfall (vals_att hg Sd Bs.G₀ hA hq) ?_
  intro s tr hS hfr
  obtain ⟨z, hz⟩ := reach_at_batching h T hbs hft hstart (by rw [hn]) hl hS
  exact cellV_att h hg Sd hB hA hq (empty_at_batching h hl hz) hfr (held s hS) (sized_at_batching h hl hz)
    (vals A hA s hS)

/-- **At the last segment.** -/
theorem batch_values_head
    (hfall : ∀ s ds, fall (337 + 10) s ds = none → K8.k8Front s ds = none)
    (held : ∀ s, StandJ T Said J (337 + 10) s → ∀ tl funs, s.tl? = some tl → s.funs? = some funs →
      tl.funsHeld funs = true)
    (ends : ∀ s, StandJ T Said J (337 + 10) s →
      endsS (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) s = true) :
    ValuesJ T Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (337 + 10) := by
  have hl : 24 < 25 := by omega
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h 24 hl
  rw [if_pos rfl] at Sd
  obtain ⟨Bs', iU3, q, hB', hU, hq, -⟩ := tied_head h Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  refine valuesJ_of_cell Sd rfl T hbs hno Said J _ fall hfall (vals_head Sd Bs.G₀ hU hq) ?_
  intro s tr hS hfr
  obtain ⟨z, hz⟩ := reach_at_batching h T hbs hft hstart rfl hl hS
  exact cellV_head h Sd hB hU hq (empty_at_batching h hl hz) hfr (held s hS) (ends s hS)

/-- **At every segment in front of the last.** -/
theorem batch_values
    (hfall : ∀ l, l < 24 → ∀ s ds, fall (14 * l + 8 + 1) s ds = none → K8.k8Front s ds = none)
    (held : ∀ l, l < 24 → ∀ s, StandJ T Said J (14 * l + 8 + 1) s → ∀ tl funs, s.tl? = some tl →
      s.funs? = some funs → tl.funsHeld funs = true)
    (env : ∀ g, g < 12 → ∀ s, StandJ T Said J (14 * (2 * g) + 8 + 1) s →
      OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers s = true)
    (vals : ∀ g, g < 12 → ∀ A, Bs.G₀.W.A[g]? = some A → ∀ s, StandJ T Said J (14 * (2 * g + 1) + 8 + 1) s →
      valsTS A s = true) :
    ∀ l, l < 24 → ValuesJ T Said J (firstZA (Johnson.AtFull.Shape.Tab.g Zp Bs.G₀) (Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀)) fall (14 * l + 8 + 1) := by
  intro l hl
  by_cases hev : l % 2 = 0
  · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
    exact batch_values_lay h hB T hbs hft hstart hno Said J fall (by omega) (hfall _ hl) (held _ hl)
      (env g (by omega))
  · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    exact batch_values_att h hB T hbs hft hstart hno Said J fall (by omega) (hfall _ hl) (held _ hl)
      (vals g (by omega))

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.cellV_cols
#print axioms ProofFile.Honest.K9.valuesJ_of_cell
#print axioms ProofFile.Honest.K9.vals_lay
#print axioms ProofFile.Honest.K9.vals_att
#print axioms ProofFile.Honest.K9.vals_head
#print axioms ProofFile.Honest.K9.reach_of_stand
#print axioms ProofFile.Honest.K9.link_of_fork
#print axioms ProofFile.Honest.K9.empty_at_batching
#print axioms ProofFile.Honest.K9.reach_at_batching
#print axioms ProofFile.Honest.K9.batch_values_lay
#print axioms ProofFile.Honest.K9.batch_values_att
#print axioms ProofFile.Honest.K9.batch_values_head
#print axioms ProofFile.Honest.K9.batch_values
