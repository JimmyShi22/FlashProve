-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailFour.lean.
The smallness test's four hand-made claims on its lookup are the last four of the flat list.

The byte-level routine objectsF (OnBytes/Model/Tail.lean) adds the lookup's claims on mask entries
by Forest.objects and then four claims by hand: linJoin9 adds the claim on the key vectors,
linBits9 the three claims on the planes. A sub-proof adds all its claims up, claim number c under
the c-th power of one drawn element (Fork.total). This file says by how much the two routines, run
one after the other, make that sum grow.

* same_total, paid_total: filling slots, and marking a claim as added, do not turn the sum.
* tail_four: the sum grows by claimJoin, claimLeaves, claimBits and countK of
  OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean, in this order, under four powers in a row, from the
  number of claims before the two runs on. The sums are read in the world (Fork.worldOf) of any
  state later than the one that linBits9 leaves. The flat list claimsOf ends with these four in the
  order claimLeaves, claimBits, countK, claimJoin (claims_last): the byte-level verifier adds the
  join first here.
  Under: both runs return, the second from what the first leaves; the record g is the smallness
  test's (tl.heard = some g) and its shape is tl.f9, is lawful (FoNums.ok) and has two calls;
  the record holds the end values endsOf (HeardIs) with a state F0, and the state F before the runs
  is later than F0, is Sized and has as many weights on slots as slots (F.LS.size = F.ns).
  It also says: the context is as before, the state behind is later and Sized, four claims more are
  counted, and the drawn element is the same.
The letters: kf is what the runs on the pieces' virtual rows read (kfRun,
OnBytes/Tie/Pv/Lookup/Ends/FoTailJoinVal.lean); bit0, bit1, pin are any letters that meet the three
premises of bits9_claim (OnBytes/Tie/Pv/Lookup/Ends/FoTailBits.lean): planesK of bit0 and of bit1
are the sums of the runs on virtual rows 0 and 1 of BZ, and countK of pin is the sum of the run on
row 2 less the number of keys that are not padding. That kfRun is a key form's value, and that the
columns' sums of the lookup's cells are such letters, is not shown here.

Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailJoinVal
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsTail

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo.PlaneClaims Cb.Fo

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- What the sum of the claims reads is not under the slots. -/
theorem same_total {F G : Fork} (h : Same F G) :
    G.total ρ W = F.total ρ W ∧ G.nClaim = F.nClaim ∧ G.theta = F.theta ∧ G.LS = F.LS ∧
      G.ns = F.ns := by
  have h' : G = { F with vp := G.vp, mf := G.mf, gotF := G.gotF } := h
  have e1 : G.trees = F.trees := by rw [h']
  have e2 : G.LS = F.LS := by rw [h']
  have e3 : G.c0 = F.c0 := by rw [h']
  refine ⟨?_, by rw [h'], by rw [h'], e2, by rw [h']⟩
  unfold Fork.total
  rw [e1, e2, e3]

/-- Marking a claim as added. -/
theorem paid_total {i : ℕ} {F G : Fork} {c c' : Ctx} (h : SubM.paid i F c = .ok (((), G), c')) :
    c' = c ∧ G.total ρ W = F.total ρ W ∧ G.nClaim = F.nClaim ∧ G.theta = F.theta ∧ G.LS = F.LS ∧
      G.ns = F.ns := by
  unfold SubM.paid at h
  obtain ⟨G', hG, e⟩ := (change_ok _ F c _).1 h
  have b0 : F.paid i = G' := Option.some.inj hG
  have b1 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
  have b2 : c' = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e
  rw [b1, ← b0]
  exact ⟨b2, rfl, rfl, rfl, rfl, rfl⟩

end

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The two routines, one after the other. F0: the state with which the record holds the end
values. -/
theorem tail_four (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Ctx)
    (hJ : tl.linJoin9 F c = .ok ((tl1, G1), c1)) (hB : tl1.linBits9 G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (lm jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (h2 : g.shape.NC = 2) (hF : Sized F)
    (hLS : F.LS.size = F.ns) :
    c2 = c ∧ Later F G2 ∧ Sized G2 ∧ G2.nClaim = F.nClaim + 4 ∧ G2.theta = F.theta ∧
      ∀ H, Later G2 H → ∀ (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K) (bit0 bit1 pin : ℕ → K),
        planesK g.shape lm (endsOf g.shape lm jLK rsK).zb0 bit0 =
          runK (H.worldOf ρ (fun j => ν (.mask j)) entry) tl 0
            (fun i => (eqTabK (exL (endsOf g.shape lm jLK rsK).zb0 5
              (5 + g.shape.kT + g.shape.cK))).getD i 0) →
        planesK g.shape lm (endsOf g.shape lm jLK rsK).zb1 bit1 =
          runK (H.worldOf ρ (fun j => ν (.mask j)) entry) tl 1
            (fun i => (eqTabK (exL (endsOf g.shape lm jLK rsK).zb1 5
              (5 + g.shape.kT + g.shape.cK))).getD i 0) →
        Pin.countK g.shape lm pin = -((2 ^ g.shape.v - g.shape.padding : ℕ) : K) +
          runK (H.worldOf ρ (fun j => ν (.mask j)) entry) tl 2
            (fun i => (rdL ρ (pinW tl)).getD i 0) →
        G2.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
          F.total ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
            ρ.val F.theta ^ F.nClaim * claimJoin g.shape lm jLK rsK ν
              (kfRun ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) tl g) +
            ρ.val F.theta ^ (F.nClaim + 1) * claimLeaves g.shape lm jLK rsK ν bit0 +
            ρ.val F.theta ^ (F.nClaim + 2) * claimBits g.shape lm jLK rsK ν bit1 +
            ρ.val F.theta ^ (F.nClaim + 3) * Pin.countK g.shape lm pin := by
  obtain ⟨lJ, sJ⟩ := keeps_Model_HTailF2_linJoin9 tl F c tl1 G1 c1 hJ hF
  obtain ⟨lB, sB⟩ := keeps_Model_HTailF2_linBits9 tl1 G1 c1 tl2 G2 c2 hB sJ
  -- the join
  obtain ⟨g', runs, A1, a1, j1, _, j3, j4, j5, j6⟩ := linJoin9_cut tl tl1 F G1 c c1 hJ
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans j1)
  -- the planes
  obtain ⟨g'', row, p', B1, B2, B3, B4, b1, b2, b3, b4, k1, k2, k3, k4, k5, k6, _⟩ :=
    linBits9_cut tl1 tl2 G1 G2 c1 c2 hB
  have hh : tl1.heard = tl.heard := by rw [j6]
  obtain rfl : g = g'' := Option.some.inj (hg.symm.trans (hh.symm.trans k1))
  have hf9 : tl1.f9 = tl.f9 := by rw [j6]
  have hrun : ∀ r co w, bzRun tl1 r co w = bzRun tl r co w := fun r co w => by rw [j6]; rfl
  have hpw : pinW tl1 = pinW tl := by rw [j6]; rfl
  rw [hrun, hf9] at k3 k4
  rw [hrun, hf9, hpw] at k5
  obtain ⟨q1, q2, q3, _, q5⟩ :=
    bits9_claim ρ tl g lm jLK rsK F0 G1 B1 c1 b1 row p' hs k2 hI (h0.trans lJ) hok sJ
  obtain ⟨_, _, _, _, _, r6, _, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ k2
  obtain ⟨sm, _⟩ := hideRun_filled sJ r6
  obtain ⟨l3, s3⟩ := keeps_Model_t2Lin _ _ B1 b1 () B2 b2 k3 q3
  obtain ⟨l4, s4⟩ := keeps_Model_t2Lin _ _ B2 b2 () B3 b3 k4 s3
  obtain ⟨l5, s5⟩ := keeps_Model_t2Lin _ _ B3 b3 () B4 b4 k5 s4
  obtain ⟨l6, _⟩ := Keeps.planesAdded g B4 b4 () G2 c2 k6 s5
  have key : ∀ W : World K,
      c2 = c ∧ G2.nClaim = F.nClaim + 4 ∧ G2.theta = F.theta ∧
      G2.total ρ W = F.total ρ W +
        ρ.val F.theta ^ F.nClaim * ((Aff.ofConst (joinConst tl g) - g.cEnd).value ρ W +
          ((joinRuns tl g).map (Run2.value ρ W)).sum) +
        ρ.val F.theta ^ (F.nClaim + 1) * (row.value ρ W + Run2.value ρ W
          (bzRun tl 0 (mulE g.leaves.eps g.leavesA)
            (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK))))) +
        ρ.val F.theta ^ (F.nClaim + 2) * ((Aff.slot g.sBit).value ρ W + Run2.value ρ W
          (bzRun tl 1 (subE zeroE oneE) (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK))))) +
        ρ.val F.theta ^ (F.nClaim + 3) *
          ((Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding)))).value ρ W +
            Run2.value ρ W (bzRun tl 2 oneE (pinW tl))) := by
    intro W
    obtain ⟨u1, u2, u3, u4, u5, u6, _⟩ := t2Lin_total ρ W _ _ F A1 c a1 hLS j4
    obtain ⟨v1, v2, v3, v4, v5, v6⟩ := paid_total ρ W j5
    obtain ⟨w2, w3, w4, w5, w6⟩ := same_total ρ W sm
    have hB1 : B1.LS.size = B1.ns := by rw [w5, w6, v5, v6]; exact u6
    obtain ⟨x1, x2, x3, x4, _, x6, _⟩ := t2Lin_total ρ W _ _ B1 B2 b1 b2 hB1 k3
    obtain ⟨y1, y2, y3, y4, _, y6, _⟩ := t2Lin_total ρ W _ _ B2 B3 b2 b3 x6 k4
    obtain ⟨z1, z2, z3, z4, _, _, _⟩ := t2Lin_total ρ W _ _ B3 B4 b3 b4 y6 k5
    obtain ⟨t1, t2, t3, t4, _, _⟩ := paid_total ρ W k6
    have n1 : B1.nClaim = F.nClaim + 1 := by rw [w3, v3, u3]
    have th1 : B1.theta = F.theta := by rw [w4, v4, u4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [t1, z1, y1, x1, q1, v1, u1]
    · rw [t3, z3, y3, x3, n1]
    · rw [t4, z4, y4, x4, th1]
    · rw [t2, z2, y2, x2, w2, v2, u2, j3]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        y4, x4, th1, y3, x3, n1]
  refine ⟨(key ⟨fun _ => 0, fun _ _ _ => 0⟩).1, lJ.trans lB, sB,
    (key ⟨fun _ => 0, fun _ _ _ => 0⟩).2.1, (key ⟨fun _ => 0, fun _ _ _ => 0⟩).2.2.1,
    fun H hH ν entry bit0 bit1 pin hb0 hb1 hpn => ?_⟩
  have hL1 : Later B1 H := (((l3.trans l4).trans l5).trans l6).trans hH
  have e3 := q5 H hL1 ν entry bit0 bit1 pin hb0 hb1 hpn
  have eJ := join9_claim ρ tl g lm jLK rsK F0 H hs hI ((h0.trans (lJ.trans lB)).trans hH) hok h2 ν
    entry
  rw [(key _).2.2.2, eJ]
  have a0 := congrArg (fun l : List K => l.getD 0 0) e3
  have a1' := congrArg (fun l : List K => l.getD 1 0) e3
  have a2' := congrArg (fun l : List K => l.getD 2 0) e3
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1' a2'
  rw [a0, a1', a2']

end
end Fo
