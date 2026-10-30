-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Guest.lean: identity at3 of an attention segment ("the denominator of a
row is the sum of the row's softmax weights") at the lookup's point: what the first joint of the
segment's own rounds gives.

Statements and proofs. No protocol of its own. The lookup with riders
(Johnson/Top/H/LookupCRModel.lean: `crDen`, `crDen_tgt`) wants, in the joint behind it, `denOut D C
z t = 0` (Cb/Pv/Att/Mean/DenStep.lean). The chain of the own rounds has the first joint "Dn and
Todo" (Cb/Pv/Att/OwnAt.lean: `ownAt_knowAt`, `ownAt_todo`). Todo holds one half: the batch of the
reads of the rows' sums is the hidden scalar ZC. The other half, that the hidden ZC is the batch of
the reads of the committed denominators (the rule value `rv` at `.zc`,
Inst/Model/Att/KeyForms.lean), is a linear claim that no equation of the chain reads: it can stand
only in the free letter `OwnPar.LE`.
Main names:
  `zcAt P x m`: the rule value of ZC at the lookup's point.
  `ZCRead P`: a premise on the letter LE: whatever LE accepts has hidden ZC = `zcAt`.
  `guest_at_point`: `ZCRead P` and Todo give `denOut P.D P.C (P.zOf x) (P.tOf m) = 0`.
  `todo_iff`: where LM and LD accept all and LE is the reading and nothing else, Todo holds exactly
    if `denOut` = 0 and the identities at2 and at1 vanish on their cubes.
  `todo_iff_free`: where LE accepts all too, Todo holds exactly if the two families vanish: nothing
    is left of at3. So `ZCRead` is needed.
  `cellsAt`, `bad_guest`, `good_guest`: cells at which every identity at1 and at2 is 0 and `denOut`
    at the point 0 is 1 (where 1 ≤ D.nb ≤ 2 ^ (C.a 2 - D.lW)); cells at which all three kinds
    vanish.
  `joint_bites`, `joint_free_takes_bad`: under the reading Todo fails at the first cells (at the
    point 0) and holds at the second; where LE accepts all it holds at the first.
`att_seam` (Cb/Pv/Att/End/Seam.lean) gives the same equation from Todo where the three
letters are those of Cb/Pv/Att/End/Hid.lean and there are two plane messages; `guest_at_point` asks
`ZCRead` of LE alone.
Used of Cb, Inst and Blocks: plain records, pure functions and lemmas on them alone:
`theMeans`, `pubOfZ`, `ownAt_todo`, `OwnPar` (tOf, iZC, iZO, iACC), `denOut`, `denOut_split`,
`scoreIdnG`, `bitIdnT`, `bitArr`, `rv`, `idnVal`, `denV`, `EF`, `den_out`, `ext_congr_point`,
`ext_cubePt`.
Limits: `ZCRead` is a premise; that a verifier's claim on ZC means it is not shown here. In
`joint_bites` and `joint_free_takes_bad`, "the cells of the message m are these" is a premise: that
a message with these cells exists is for whoever gives `rd` and `msg`. That the first statement's
point is the lookup's is not stated here. `denOut` = 0 speaks of one point: it does not give at3 at
every index (`den_not_back`, Cb/G6/Rider/Model/Denom.lean). Nothing on an honest prover or on
hiding.

-/
import Cb.Pv.Att.OwnAt
import Cb.G6.Rider.Model.Denom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Cb.Pv.Att Inst.Model Inst.Model.AttSeg Finset

variable {K M X : Type} [Field K] [Fintype K]

/-- The rule value of ZC at the lookup's point: the batch of the reads of the committed
denominators. -/
def zcAt (P : OwnPar K M X) (x : X) (m : M) : K :=
  AttSeg.rv P.D P.C (pubOfZ K (P.zOf x)) (P.tOf m) .zc

/-- The premise: the free linear claim on the further scalars of the sumcheck "denominator times
output" holds ZC's reading. -/
def ZCRead (P : OwnPar K M X) : Prop :=
  ∀ (s : Seen K X) (r : Fin (5 + P.D.lT + 2) → K) (m : M), P.LE s r m →
    r P.iZC - P.msg m (P.kE P.iZC) = zcAt P s.1 m

/-- **The first joint of the own rounds gives the host's target at the lookup's point.** -/
theorem guest_at_point (P : OwnPar K M X) (hZ : ZCRead P) (x : X) (m : M)
    (h : (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m) :
    denOut P.D P.C (P.zOf x) (P.tOf m) = 0 := by
  obtain ⟨rM, _, _, _, rD, _, _, _, rE, hLE, _, _, ⟨_, hc⟩, _, _⟩ := (ownAt_todo P x m).1 h
  have hz := hZ _ _ _ hLE
  rw [denOut_split, hc, hz]
  exact sub_self _

/-! ### What the first joint says, exactly; cells at which it fails and holds -/

omit [Fintype K] in
theorem ppt_nonempty : ∀ l : List (Cb.PFmt K), Nonempty (Cb.PPt l)
  | [] => ⟨()⟩
  | _ :: l => (ppt_nonempty l).elim fun p => ⟨((0 : K), p)⟩

omit [Fintype K] in
theorem out_nonempty (Y : Cb.PscPar K) (st : Y.St) : Nonempty Y.Out :=
  (ppt_nonempty Y.fmt).elim fun p => ⟨⟨st, 0, p, 0, fun _ => 0⟩⟩

/-- The further scalars that make the three sums and the two gaps true: free where nothing is asked.
-/
private theorem three_places (P : OwnPar K M X) : P.iACC ≠ P.iZO ∧ P.iACC ≠ P.iZC ∧ P.iZO ≠ P.iZC := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> simp [OwnPar.iACC, OwnPar.iZO, OwnPar.iZC] at this

/-- **What the first joint says, where LE is ZC's reading and nothing else**: the guest at the
point, beside the two families. -/
theorem todo_iff (P : OwnPar K M X) (hM : ∀ s r m, P.LM s r m) (hD : ∀ s r m, P.LD s r m)
    (hE : ∀ s r m, P.LE s r m ↔ r P.iZC - P.msg m (P.kE P.iZC) = zcAt P s.1 m) (x : X) (m : M) :
    (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m ↔
      denOut P.D P.C (P.zOf x) (P.tOf m) = 0 ∧
      (∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g1, scoreIdnG P.D (P.tOf m) i Y = 0) ∧
      ∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g2, bitIdnT P.D (P.tOf m) i Y = 0 := by
  constructor
  · intro h
    refine ⟨guest_at_point P (fun s r m h => (hE s r m).1 h) x m h, ?_⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2⟩ := (ownAt_todo P x m).1 h
    exact ⟨h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    obtain ⟨n1, n2, n3⟩ := three_places P
    rw [ownAt_todo]
    refine ⟨fun _ => AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6b + P.msg m (P.kM (Fin.last _)),
      hM _ _ _, (add_sub_cancel_right _ _).symm, (out_nonempty _ (P.uM.cl (x, []) fun _ => 0).2).some, ?_⟩
    refine ⟨fun _ => AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6d + P.msg m (P.kD (Fin.last _)),
      hD _ _ _, (add_sub_cancel_right _ _).symm, (out_nonempty _ (P.uD.cl (x, []) fun _ => 0).2).some, ?_⟩
    refine ⟨fun j => if j = P.iZO then AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s8 + P.msg m (P.kE P.iZO)
        else if j = P.iACC then AttSeg.rv P.D P.C (pubOfZ K (P.zOf x)) (P.tOf m) .acc + P.msg m (P.kE P.iACC)
        else zcAt P x m + P.msg m (P.kE P.iZC), ?_, ?_, (out_nonempty _ (P.sE.cl (x, []) fun _ => 0).2).some, ⟨?_, ?_⟩, h1, h2⟩
    · rw [hE]
      rw [if_neg n3.symm, if_neg n2.symm]
      ring
    · beta_reduce
      rw [if_pos rfl]
      exact (add_sub_cancel_right _ _).symm
    · beta_reduce
      rw [if_neg n1, if_pos rfl]
      ring
    · beta_reduce
      rw [if_neg n3.symm, if_neg n2.symm]
      rw [denOut_split, sub_eq_zero] at h0
      rw [← h0]
      exact (add_sub_cancel_right _ _).symm

/-- **Where LE accepts all, the guest is gone**: the first joint says the two families alone. So
ZCRead is needed. -/
theorem todo_iff_free (P : OwnPar K M X) (hM : ∀ s r m, P.LM s r m) (hD : ∀ s r m, P.LD s r m)
    (hE : ∀ s r m, P.LE s r m) (x : X) (m : M) :
    (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m ↔
      (∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g1, scoreIdnG P.D (P.tOf m) i Y = 0) ∧
      ∀ i : Fin P.D.nb, ∀ Y < 2 ^ P.g2, bitIdnT P.D (P.tOf m) i Y = 0 := by
  constructor
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2⟩ := (ownAt_todo P x m).1 h
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨n1, n2, n3⟩ := three_places P
    rw [ownAt_todo]
    refine ⟨fun _ => AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6b + P.msg m (P.kM (Fin.last _)),
      hM _ _ _, (add_sub_cancel_right _ _).symm, (out_nonempty _ (P.uM.cl (x, []) fun _ => 0).2).some, ?_⟩
    refine ⟨fun _ => AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s6d + P.msg m (P.kD (Fin.last _)),
      hD _ _ _, (add_sub_cancel_right _ _).symm, (out_nonempty _ (P.uD.cl (x, []) fun _ => 0).2).some, ?_⟩
    refine ⟨fun j => if j = P.iZO then AttSeg.sumPhi P.D P.C (P.pub0 (x, [])) (P.tOf m) .s8 + P.msg m (P.kE P.iZO)
        else if j = P.iACC then AttSeg.rv P.D P.C (pubOfZ K (P.zOf x)) (P.tOf m) .acc + P.msg m (P.kE P.iACC)
        else (∑ b ∈ Finset.range P.D.nb, AttSeg.wp P.D P.C (P.zOf x) .w3 b *
          AttSeg.rd2 P.D (AttSeg.yg P.D P.C (P.zOf x)) (AttSeg.eqT P.D (AttSeg.yi P.D P.C (P.zOf x)))
            (AttSeg.EF P.D (P.tOf m) b)) + P.msg m (P.kE P.iZC),
      hE _ _ _, ?_, (out_nonempty _ (P.sE.cl (x, []) fun _ => 0).2).some, ⟨?_, ?_⟩, h1, h2⟩
    · beta_reduce
      rw [if_pos rfl]
      exact (add_sub_cancel_right _ _).symm
    · beta_reduce
      rw [if_neg n1, if_pos rfl]
      ring
    · beta_reduce
      rw [if_neg n3.symm, if_neg n2.symm]
      exact (add_sub_cancel_right _ _).symm

section Cells
omit [Fintype K]

/-- Cells: every softmax weight 0; every denominator 0 but, if `one` is set, that of pair 0, head 0,
position 0, which is 1; all else 0. -/
def cellsAt (one : Bool) : Raw → K
  | .den k b g i => if one = true ∧ k = 0 ∧ b = 0 ∧ g = 0 ∧ i = 0 then 1 else 0
  | .c _ jj _ _ => if jj = 3 then -128 else 0
  | _ => 0

theorem cells_own1 (D : Dim) (one : Bool) (k b g i : ℕ) : idnVal D (cellsAt one : Raw → K) (.at1 k b g i) = 0 := by
  simp [idnVal, ibV, cellsAt]

theorem cells_own2 (D : Dim) (one : Bool) (b g i : ℕ) : idnVal D (cellsAt one : Raw → K) (.at2 b g i) = 0 := by
  simp [idnVal, mxV, qryV, cellsAt]

theorem cells_at3 (D : Dim) (one : Bool) (b g i : ℕ) :
    idnVal D (cellsAt one : Raw → K) (.at3 b g i) = if one = true ∧ b = 0 ∧ g = 0 ∧ i = 0 then 1 else 0 := by
  have hE : EF D (cellsAt one : Raw → K) b g i = 0 := by
    simp [EF, rowSum, wtV, w0, w1, cellsAt]
  have hd : denV (cellsAt one : Raw → K) b g i = if one = true ∧ b = 0 ∧ g = 0 ∧ i = 0 then 1 else 0 := by
    simp [denV, sum_range_succ, cellsAt]
  show denV _ b g i - EF D _ b g i = _
  rw [hE, hd, sub_zero]

theorem cells_fam2 (D : Dim) (one : Bool) (b Y : ℕ) : scoreIdnG D (cellsAt one : Raw → K) b Y = 0 :=
  cells_own2 D one b _ _

theorem cells_fam1 (D : Dim) (one : Bool) (b Y : ℕ) : bitIdnT D (cellsAt one : Raw → K) b Y = 0 := by
  unfold bitIdnT bitArr
  split
  · exact cells_own1 D one _ _ _ _
  · rfl

/-- **The bad cells**: own1 and own2 hold everywhere, and the guest at the point 0 is 1. -/
theorem bad_guest (D : Dim) (C : Calls) (hN : D.nb ≤ 2 ^ (C.a 2 - D.lW)) (hb : 1 ≤ D.nb) :
    denOut D C (fun _ => 0) (cellsAt true : Raw → K) = 1 := by
  rw [← Cb.Rider.den_out D C hN]
  have hp : ∀ s < C.a 2 - D.lW + D.lg + D.lT,
      C.zC 2 (fun _ => (0 : K)) (Cb.Rider.callIx (C.a 2 - D.lW) s) =
        Blocks.cubePt (C.a 2 - D.lW + D.lg + D.lT) 0 s := by
    intro s hs
    have e : C.zC 2 (fun _ => (0 : K)) (Cb.Rider.callIx (C.a 2 - D.lW) s) = 0 := by
      unfold Calls.zC
      split <;> rfl
    rw [e]
    simp [Blocks.cubePt, Blocks.nat, hs, Alg.corner, Alg.bits]
  rw [Blocks.ext_congr_point hp, Blocks.ext_cubePt _ _ (Nat.two_pow_pos _)]
  have : 0 < D.nb := hb
  simp [denVec, cells_at3, this]

/-- **The good cells**: all three kinds of identity hold everywhere; the guest is 0 at every point.
-/
theorem good_guest (D : Dim) (C : Calls) (z : ℕ → K) : denOut D C z (cellsAt false : Raw → K) = 0 := by
  unfold denOut rd2
  simp [cells_at3]

end Cells

/-- **The first joint refuses the bad cells and takes the good ones**, where LE is ZC's reading
alone; where LE accepts all it takes both. -/
theorem joint_bites (P : OwnPar K M X) (hM : ∀ s r m, P.LM s r m) (hD : ∀ s r m, P.LD s r m)
    (hE : ∀ s r m, P.LE s r m ↔ r P.iZC - P.msg m (P.kE P.iZC) = zcAt P s.1 m)
    (hN : P.D.nb ≤ 2 ^ (P.C.a 2 - P.D.lW)) (hb : 1 ≤ P.D.nb) (x : X) (m : M) :
    (P.zOf x = (fun _ => 0) → P.tOf m = cellsAt true → ¬ (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m) ∧
    (P.tOf m = cellsAt false → (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m) := by
  constructor
  · intro hz ht h
    have := ((todo_iff P hM hD hE x m).1 h).1
    rw [hz, ht, bad_guest P.D P.C hN hb] at this
    exact one_ne_zero this
  · intro ht
    rw [todo_iff P hM hD hE x m, ht]
    exact ⟨good_guest _ _ _, fun i Y _ => cells_fam2 _ _ _ _, fun i Y _ => cells_fam1 _ _ _ _⟩

theorem joint_free_takes_bad (P : OwnPar K M X) (hM : ∀ s r m, P.LM s r m) (hD : ∀ s r m, P.LD s r m)
    (hE : ∀ s r m, P.LE s r m) (x : X) (m : M) (ht : P.tOf m = cellsAt true) :
    (P.own (theMeans K P.D P.C P.kap)).ch.Todo x m := by
  rw [todo_iff_free P hM hD hE x m, ht]
  exact ⟨fun i Y _ => cells_fam2 _ _ _ _, fun i Y _ => cells_fam1 _ _ _ _⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.guest_at_point
#print axioms VerifiableInference.Desc.First.Att.P.todo_iff
#print axioms VerifiableInference.Desc.First.Att.P.todo_iff_free
#print axioms VerifiableInference.Desc.First.Att.P.bad_guest
#print axioms VerifiableInference.Desc.First.Att.P.good_guest
#print axioms VerifiableInference.Desc.First.Att.P.joint_bites
#print axioms VerifiableInference.Desc.First.Att.P.joint_free_takes_bad
