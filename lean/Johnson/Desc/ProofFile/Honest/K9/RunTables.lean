-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RunTables.lean: THE TIE `Tied` (Honest/K9/RunFrame.lean) WITH THE RUN WRITTEN OUT: at each entry of a
segment's order, the run that the entry stands for is the run of the library's table of rows for that sort of segment
(`rowsLay`, `rowsHead`: Johnson/AtFull/Shape/BatchCells.lean; `rowsAtt`: BatchCellsAtt.lean). The library's slots say which block states
which bare run, and each slot is a block laid alone with a run under the entry's name.

  `tied_of_slot`, `tied_of_slotAt`   a slot at the entry gives the tie to its bare run
  **`tied_lay`**, **`tied_att`**, **`tied_head`**   under the hypothesis `AtMgA`, at the seated link of each sort of segment: every entry of
                      the order is tied to the run of its row; the table's letters are named by their equations
  **`tied_rows`**         at each of the 25 segments: there is a table of rows such that every entry is tied to its row's run
  **`tied_fun`**          so there is f with `Tied Lk j (f j)` at every j below the order's length: the premise `tied` of the gathering theorem

Limits. The rows name the runs and say nothing of what a run does. The full size and the hash function `secondHashFunction` alone, as in the
hypothesis. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.RunTied
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.AtFull.Shape.BatchCellsAtt
import Johnson.AtFull.Shape.BatchTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9.Shape (Slot)
open Johnson.AtFull.Shape (SlotAt tabOf rowsLay rowsAtt rowsHead k4_slotAt k5_slotAt k6_slotAt k8_slotAt k11_slotAt
  k3_two_at k3_planes_att k3_planes_head)
open P5J (AtMgA)

/-- **A slot at the entry gives the tie to its bare run.** -/
theorem tied_of_slot {Lk : Link S Claim} {j : ℕ} {o : ℕ × String} (T : Slot ProofFile.sameReply Lk.hear o)
    (ho : Lk.order[j]? = some o) : Tied Lk j T.bare :=
  tied_of_alone ho T.seated rfl T.states

theorem tied_of_slotAt {Lk : Link S Claim} {j : ℕ} {o : ℕ × String} {run : ClaimsRun}
    {g : ℕ → Shape.ChainSh → Except String (List Shape.ClaimSh × Shape.ChainSh)} {V : ℕ → S → Bool}
    (T : SlotAt Lk.hear o run g V) (ho : Lk.order[j]? = some o) : Tied Lk j run := by
  obtain ⟨T, rfl, -, -⟩ := T
  exact tied_of_slot T ho

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {k : ℕ} {Lk : Link S ProofFile.Cl}
  {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- At every entry, a slot at the row of a table. -/
theorem tied_of_table {rows : List ((ℕ × String) × Johnson.AtFull.Shape.Row)}
    (H : ∀ o ∈ Lk.order, SlotAt Lk.hear o (tabOf rows o).run (tabOf rows o).g (tabOf rows o).pre) :
    ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o → Tied Lk j (tabOf rows o).run :=
  fun _ o ho => tied_of_slotAt (H o (List.mem_of_getElem? ho)) ho

/-- **At the feed-forward segment 2 g.** -/
theorem tied_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g) k Lk p w) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o → Tied Lk j (tabOf (rowsLay Bs.G₀.W g) o).run := by
  have hl : 2 * g < 25 := by omega
  have h24 : 2 * g ≠ 24 := by omega
  have hsub : IM.subAt (2 * g) = .layers := by
    unfold IM.subAt
    rw [if_neg h24, if_pos (Nat.mul_mod_right 2 g)]
  have i1 : IM.k3Ix (2 * g) false = 1 := by simp [IM.k3Ix, h24]
  have i6 : IM.k3Ix (2 * g) true = 6 := by simp [IM.k3Ix, h24]
  have eL := Sd.link
  have hord := Sd.order
  obtain ⟨Bs, L4, hB, e4, s4f, s4b⟩ := k4_slotAt h g hg
  obtain rfl : Lk = L4 := Option.some.inj (eL.symm.trans e4)
  obtain ⟨L8, e8, s8⟩ := k8_slotAt h (2 * g) hl
  obtain rfl : Lk = L8 := Option.some.inj (eL.symm.trans e8)
  obtain ⟨La, ea, sao, sag⟩ := k3_two_at h (2 * g) hl false
  obtain rfl : Lk = La := Option.some.inj (eL.symm.trans ea)
  obtain ⟨Lb, eb, sbo, sbg⟩ := k3_two_at h (2 * g) hl true
  obtain rfl : Lk = Lb := Option.some.inj (eL.symm.trans eb)
  rw [hsub] at s8 hord
  rw [i1] at sao sag
  rw [i6] at sbo sbg
  refine ⟨Bs, hB, tied_of_table ?_⟩
  rw [hord]
  intro o ho
  simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sao
  · exact sag
  · exact s4f
  · exact sbo
  · exact sbg
  · exact s8
  · exact s4b

/-- **At the attention segment 2 g + 1.** -/
theorem tied_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g + 1) k Lk p w) :
    ∃ (Bs : ProofFile.PureBase) (A : Attention.Plan) (q : VerifiableInference.Desc.First.Look.P),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ Bs.G₀.W.A[g]? = some A ∧
      VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W (2 * g + 1) false = some q ∧
      ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o → Tied Lk j (tabOf (rowsAtt A q.lm) o).run := by
  have hl : 2 * g + 1 < 25 := by omega
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have hsub : IM.subAt (2 * g + 1) = .attention := by
    unfold IM.subAt
    rw [if_neg h24, if_neg (by omega)]
  have i1 : IM.k3Ix (2 * g + 1) false = 1 := by simp [IM.k3Ix, h24]
  have i6 : IM.k3Ix (2 * g + 1) true = 6 := by simp [IM.k3Ix, h24]
  have eL := Sd.link
  have hord := Sd.order
  obtain ⟨Bs, L5, A, hB, e5, hA, s1, s2, s3, s4⟩ := k5_slotAt h g hg
  obtain rfl : Lk = L5 := Option.some.inj (eL.symm.trans e5)
  obtain ⟨Bp, Lp, Ap, q, hBp, ep, hAp, hq, spl⟩ := k3_planes_att h g hg
  obtain rfl : Bs = Bp := Except.ok.inj (hB.symm.trans hBp)
  obtain rfl : Lk = Lp := Option.some.inj (eL.symm.trans ep)
  obtain rfl : A = Ap := Option.some.inj (hA.symm.trans hAp)
  obtain ⟨L8, e8, s8⟩ := k8_slotAt h (2 * g + 1) hl
  obtain rfl : Lk = L8 := Option.some.inj (eL.symm.trans e8)
  obtain ⟨La, ea, sao, sag⟩ := k3_two_at h (2 * g + 1) hl false
  obtain rfl : Lk = La := Option.some.inj (eL.symm.trans ea)
  obtain ⟨Lb, eb, sbo, sbg⟩ := k3_two_at h (2 * g + 1) hl true
  obtain rfl : Lk = Lb := Option.some.inj (eL.symm.trans eb)
  rw [hsub] at s8 hord
  rw [i1] at sao sag
  rw [i6] at sbo sbg
  refine ⟨Bs, A, q, hB, hA, hq, tied_of_table ?_⟩
  rw [hord]
  intro o ho
  simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sao
  · exact sag
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact spl
  · exact sbo
  · exact sbg
  · exact s8

/-- **At the head's segment.** -/
theorem tied_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Sd : SeatedFree cF Zp 24 k Lk p w) :
    ∃ (Bs : ProofFile.PureBase) (iU3 : ℕ) (q : VerifiableInference.Desc.First.Look.P),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false = some q ∧
      ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o →
        Tied Lk j (tabOf (rowsHead Bs.G₀.W iU3 q.lm) o).run := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  have i2 : IM.k3Ix 24 false = 2 := rfl
  have i7 : IM.k3Ix 24 true = 7 := rfl
  have eL := Sd.link
  have hord := Sd.order
  obtain ⟨Bs, L6, iU3, hB, e6, hU, s3, s6j⟩ := k6_slotAt h
  obtain rfl : Lk = L6 := Option.some.inj (eL.symm.trans e6)
  obtain ⟨Bp, Lp, iP, q, hBp, ep, hUp, hq, spl⟩ := k3_planes_head h
  obtain rfl : Bs = Bp := Except.ok.inj (hB.symm.trans hBp)
  obtain rfl : Lk = Lp := Option.some.inj (eL.symm.trans ep)
  obtain rfl : iU3 = iP := Option.some.inj (hU.symm.trans hUp)
  obtain ⟨L8, e8, s8⟩ := k8_slotAt h 24 hl
  obtain rfl : Lk = L8 := Option.some.inj (eL.symm.trans e8)
  obtain ⟨L11, e11, s11⟩ := k11_slotAt h
  obtain rfl : Lk = L11 := Option.some.inj (eL.symm.trans e11)
  obtain ⟨La, ea, sao, sag⟩ := k3_two_at h 24 hl false
  obtain rfl : Lk = La := Option.some.inj (eL.symm.trans ea)
  obtain ⟨Lb, eb, sbo, sbg⟩ := k3_two_at h 24 hl true
  obtain rfl : Lk = Lb := Option.some.inj (eL.symm.trans eb)
  rw [hsub] at s8 hord
  rw [i2] at sao sag
  rw [i7] at sbo sbg
  refine ⟨Bs, iU3, q, hB, hU, hq, tied_of_table ?_⟩
  rw [hord]
  intro o ho
  simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sao
  · exact sag
  · exact s3 "norm" (by simp)
  · exact s6j
  · exact s3 "policy" (by simp)
  · exact spl
  · exact sbo
  · exact sbg
  · exact s8
  · exact s3 "logits" (by simp)
  · exact s11

/-- **At each of the 25 segments: a table of rows, and every entry tied to its row's run.** -/
theorem tied_rows (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) :
    ∃ rows : List ((ℕ × String) × Johnson.AtFull.Shape.Row), ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o →
      Tied Lk j (tabOf rows o).run := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Bs, iU3, q, -, -, -, T⟩ := tied_head h Sd
    exact ⟨_, T⟩
  · by_cases hev : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      obtain ⟨Bs, -, T⟩ := tied_lay h (by omega) Sd
      exact ⟨_, T⟩
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      obtain ⟨Bs, A, q, -, -, -, T⟩ := tied_att h (by omega) Sd
      exact ⟨_, T⟩

/-- **The premise `tied` of the gathering theorem, at each of the 25 segments.** -/
theorem tied_fun (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) : ∃ f : ℕ → ClaimsRun, ∀ j, j < Lk.order.length → Tied Lk j (f j) := by
  obtain ⟨rows, T⟩ := tied_rows h hl Sd
  refine ⟨fun j => match Lk.order[j]? with
    | some o => (tabOf rows o).run
    | none => Johnson.AtFull.Shape.Row.idle.run, ?_⟩
  intro j hj
  have ho : Lk.order[j]? = some Lk.order[j] := List.getElem?_eq_getElem hj
  show Tied Lk j (match Lk.order[j]? with
    | some o => (tabOf rows o).run
    | none => Johnson.AtFull.Shape.Row.idle.run)
  rw [ho]
  exact T j _ ho

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.tied_of_slot
#print axioms ProofFile.Honest.K9.tied_of_slotAt
#print axioms ProofFile.Honest.K9.tied_of_table
#print axioms ProofFile.Honest.K9.tied_lay
#print axioms ProofFile.Honest.K9.tied_att
#print axioms ProofFile.Honest.K9.tied_head
#print axioms ProofFile.Honest.K9.tied_rows
#print axioms ProofFile.Honest.K9.tied_fun
