-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/CellVHead.lean: AT THE HEAD's BATCHING (347), THE ONE TEST ON VALUES (cellV) ACCEPTS WHEREVER THE
MEMBER HAS SAID YES AT A REACHED STATE. The sister of cellV_yes_lay (BatchYes.lean): the rows' test endsS by the rows' own yes
(EndsOfRun.lean), "K8.equations" inside cellV_of_yes.

  `cellV_yes_head`      cellV at the head's rows, from the yes
  `vals_of_step_head`   the table's test on values at 347, from a reached state and the member's step

Limits. Implications. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.BatchYes
import Johnson.AtFull.Shape.Scope.EndsOfRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (headPre headPost)
open Johnson.AtFull.Shape (cellV tabOf rowsHead)
open Johnson.AtFull.Shape.Scope (endsS_of_three endsS_of_join)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Lk : Link S ProofFile.Cl}
  {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} {k : ℕ}

/-- **AT THE HEAD's SEGMENT, AT A REACHED STATE: cellV FROM THE MEMBER's YES.** -/
theorem cellV_yes_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Sd : SeatedFree cF Zp 24 k Lk p w) {Bs : ProofFile.PureBase} {iU3 : ℕ}
    {q : VerifiableInference.Desc.First.Look.P}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hU : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3)
    (hq : VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false = some q)
    {z : ProofFile.InstPub} {s s' : S} (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (337 + 10) (z, s))
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s rs gs = .ok s') :
    cellV p (rowsHead Bs.G₀.W iU3 q.lm) Lk.order s rs gs = true := by
  have hl : 24 < 25 := by omega
  obtain ⟨Bs', iU3', q', hB', hU', hq', tied⟩ := tied_head h Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  obtain rfl : iU3 = iU3' := Option.some.inj (hU.symm.trans hU')
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  have PT := plainTies_head_at_head h Sd
  have under : ∀ o, o ∈ Lk.order → ∀ (r' : ClaimsRun), claimsRunOf Lk.hear o = some r' → ∀ n u y,
      r' n u = .ok y → (tabOf (rowsHead Bs.G₀.W iU3 q.lm) o).run n u = .ok y := by
    intro o ho r' hr n u y hv
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
    exact (tied j o hj).under o r' hj hr n u y hv
  refine cellV_of_yes tied (fun g R => rests_at_head h hl Sd g R) (cores_at_head h hl Sd)
    (carries_at_head h hl Sd) PT Lk.each (empty_at_batching h hl hz) (fun _ _ => rfl) ?_ hy
  intro t₁ hd o ho n u r' y hu hr hv
  have hO : o ∈ Lk.order := by
    rw [PT.order]
    rcases ho with ho | ho <;> simp [ho]
  have hf := under o hO r' hr n u y hv
  simp only [headPre, headPost, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  · rfl
  · rfl
  · exact endsS_of_three _ _ (by simp) hf
  · exact endsS_of_join _ _ (n := n) hf
  · exact endsS_of_three _ _ (by simp) hf
  · rfl
  · rfl
  · rfl
  · exact endsS_of_three _ _ (by simp) hf
  · rfl

/-- **THE TABLE's TEST ON VALUES AT THE HEAD's BATCHING, FROM A REACHED STATE AND THE MEMBER's STEP:** no silence of a fall, no
coin in the premises. -/
theorem vals_of_step_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {blk : Block S ProofFile.Cl}
    (hblk : cF.blocksInOrder[337 + 10]? = some blk) {z : ProofFile.InstPub} {s s' : S}
    (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (337 + 10) (z, s)) {ft n : ℕ} {R : List Fmt.RoundView}
    {c : List VerifiableInference.Desc.OpenedColumn} (hs : blk.step ft s R c = .ok (s', n)) :
    Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀ (337 + 10) s (R.map noDigest) (blk.shown ft R c) = true := by
  have hl : 24 < 25 := by omega
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h 24 hl
  rw [if_pos rfl] at Sd
  obtain ⟨Bs', iU3, q, hB', hU, hq, -⟩ := tied_head h Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  have hbk : cF.blocksInOrder[337 + 10]? = _ := Sd.batching
  rw [hblk] at hbk
  obtain rfl := Option.some.inj hbk
  obtain ⟨a, ka, la⟩ := Sd.alone
  have h3 := (VerifiableInference.Desc.step_iff ft _ s s' R c n).1 hs
  have hb := ((IM.yes_alone la ka s s' (R.map noDigest) _).1 h3.2.1).1
  rw [vals_head Sd Bs.G₀ hU hq]
  exact cellV_yes_head h Sd hB hU hq hz hb

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.cellV_yes_head
#print axioms ProofFile.Honest.K9.vals_of_step_head
