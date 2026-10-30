-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/BatchYesAtt.lean: AT AN ATTENTION SEGMENT THE BATCHING's ONE TEST ON VALUES ACCEPTS WHEREVER THE
MEMBER HAS SAID YES AT A REACHED STATE (BatchYes.lean's form): each of the five rows that test valsTS has it off its
own run's return (AttRunsRead.lean).

  **cellV_yes_att**      cellV from the member's yes.
  **vals_of_step_att**   the table's test on values there, from a reached state and the member's step.

Limits. Implications. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.BatchYes
import Johnson.AtFull.Shape.Scope.AttRunsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (attPre)
open Johnson.AtFull.Shape (cellV tabOf rowsAtt)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Lk : Link S ProofFile.Cl}
  {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} {k : ℕ}

/-- **AT AN ATTENTION SEGMENT, AT A REACHED STATE: cellV FROM THE MEMBER's YES.** -/
theorem cellV_yes_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g + 1) k Lk p w) {Bs : ProofFile.PureBase} {A : Attention.Plan}
    {q : VerifiableInference.Desc.First.Look.P}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (hA : Bs.G₀.W.A[g]? = some A)
    (hq : VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W (2 * g + 1) false = some q)
    {z : ProofFile.InstPub} {s s' : S}
    (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + IM.nAt (2 * g + 1) + 2) (z, s))
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s rs gs = .ok s') :
    cellV p (rowsAtt A q.lm) Lk.order s rs gs = true := by
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨Bs', A', q', hB', hA', hq', tied⟩ := tied_att h hg Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  obtain rfl : A = A' := Option.some.inj (hA.symm.trans hA')
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  have PT := plainTies_att_at_head h hg Sd
  refine cellV_of_yes tied (fun g R => rests_at_head h hl Sd g R) (cores_at_head h hl Sd)
    (carries_at_head h hl Sd) PT Lk.each
    (empty_at_batching h hl hz) (fun _ _ => rfl) ?_ hy
  intro t₁ hd o ho n u r₀ y hu hr hv
  have hO : o ∈ Lk.order := by
    rw [PT.order]
    rcases ho with ho | ho
    · exact List.mem_append_left _ ho
    · cases ho
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hO
  have ht : (tabOf (rowsAtt A q.lm) o).run n u = .ok y := (tied j o hj).under o r₀ hj hr n u y hv
  simp only [attPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact Johnson.AtFull.Shape.Scope.pre_of_row (Or.inl rfl) ht
  · exact Johnson.AtFull.Shape.Scope.pre_of_row (Or.inr (Or.inl rfl)) ht
  · exact Johnson.AtFull.Shape.Scope.pre_of_row (Or.inr (Or.inr (Or.inl rfl))) ht
  · exact Johnson.AtFull.Shape.Scope.pre_of_row (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) ht
  · exact Johnson.AtFull.Shape.Scope.pre_of_row (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) ht
  · rfl
  · rfl

/-- **THE TABLE's TEST ON VALUES AT THE BATCHING OF AN ATTENTION SEGMENT, FROM A REACHED STATE AND THE MEMBER's STEP.** -/
theorem vals_of_step_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {blk : Block S ProofFile.Cl} (hblk : cF.blocksInOrder[14 * (2 * g + 1) + 8 + 1]? = some blk) {z : ProofFile.InstPub}
    {s s' : S} (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 8 + 1) (z, s)) {ft n : ℕ}
    {R : List Fmt.RoundView} {c : List VerifiableInference.Desc.OpenedColumn} (hs : blk.step ft s R c = .ok (s', n)) :
    Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀ (14 * (2 * g + 1) + 8 + 1) s (R.map noDigest)
      (blk.shown ft R c) = true := by
  have hl : 2 * g + 1 < 25 := by omega
  have hn : IM.nAt (2 * g + 1) = 7 := by simp [IM.nAt]; omega
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h (2 * g + 1) hl
  rw [if_neg (by omega)] at Sd
  obtain ⟨Bs', A, q, hB', hA, hq, -⟩ := tied_att h hg Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  have eb : 14 * (2 * g + 1) + 8 + 1 = 14 * (2 * g + 1) + 7 + 2 := by omega
  have hbk := Sd.batching
  rw [← eb, hblk] at hbk
  obtain rfl := Option.some.inj hbk
  obtain ⟨a, ka, la⟩ := Sd.alone
  have h3 := (VerifiableInference.Desc.step_iff ft _ s s' R c n).1 hs
  have hb := ((IM.yes_alone la ka s s' _ _).1 h3.2.1).1
  rw [vals_att hg Sd Bs.G₀ hA hq]
  exact cellV_yes_att h hg Sd hB hA hq (by rw [hn, ← eb]; exact hz) hb

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.cellV_yes_att
#print axioms ProofFile.Honest.K9.vals_of_step_att
