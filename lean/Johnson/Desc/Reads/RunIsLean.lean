-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RunIsLean.lean: fewer premises under Reads/RunIsAt.lean and
Reads/WeightsOfRunIs.lean.

Why. `runIs_at` names fourteen premises that no theorem pays. Two of them follow from the others.
And the weights' tie for the head's own five reads spends seven of the 22 fields of `RunIs`
(Johnson/Desc/Kinds/Law/TwelveOurs.lean): for these, six of the fourteen suffice.

What is here.
  `size_of_tail`: a tool: a key point of J + lt coordinates, with ls at most J, whose last ls + lt
    coordinates are those of the lookup's point: the lookup's point has ls + lt coordinates at
    least.
  `hz_at`: so the premise hz of `runIs_at` follows from the kind's own test on the key points, with
    hJ and hlsJ at one call.
  `hz_of_letters`: the same at the record, from the kind's letters.
  `tN_size`: the premise hsTN follows from a yes of the text that makes the tables.
  `runIs_at_twelve`: `runIs_at` without these two.
  `weights_of_seven`: a step: the weights' tie for the five reads, from seven facts by name in the
    place of `RunIs`.
  `weights_at`: **the weights' tie at the record**, for the five reads, under six of the fourteen:
    hX1, hX2, hqH, hsTH, and hJ and hlsJ at the one call x.qH.

Limits. The six are shown by no theorem here. `runIs_at_twelve` serves the twelve reads;
`weights_at` the head's five alone. The premises of `runIs_at_twelve` are met together at one toy
record of no run and no real layout (Johnson/Desc/Reads/ToyRecord.lean). Nothing on soundness.


-/
import Johnson.Desc.Reads.RunIsAt
import Johnson.Desc.Reads.WeightsOfRunIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open VerifiableInference.Desc.Kinds (Point)

/-- The lookup's point is as long as the tail that a key point shares with it. -/
theorem size_of_tail (zk zx : Point) {J ls lt : ℕ} (hs : zk.size = J + lt)
    (hl : zk.last (ls + lt) = zx.last (ls + lt)) (hJ : ls ≤ J) : ls + lt ≤ zx.size := by
  have h := congrArg Array.size hl
  unfold Point.last at h
  simp only [Array.size_extract] at h
  omega

end VerifiableInference.Reads

namespace VerifiableInference.Reads.AtSeat

open OnBytes (E zeroE mulE)
open OnBytes.Model (Reading eqTab longPhi longPoint)
open OnBytes.Model.Head (Shape HL Covered Run costWeights ztOf zjOf callNo)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables ReadsQuiet.bind_ok ReadsQuiet.named_ok
  ReadsQuiet.need_ok)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtHead

/-- The premise hz, from the kind's test on the key points at one call. -/
theorem hz_at (h : Shape) (L : HL) (G : OnBytes.Model.Forest.Heard) (floor : ℕ)
    (hP : @PointsOk (sizesOf h) floor G.zx fun c => G.zk.getD c #[]) {q : ℕ} (hq : q < 6)
    (hJ : (L.calls.getD q default).lJ = (letI := sizesOf h; lJ floor (callKeys q)))
    (hls : h.ls ≤ (L.calls.getD q default).lJ) : h.ls + h.lt ≤ G.zx.size := by
  obtain ⟨p1, p2⟩ := hP q _ (Came.call_get hq)
  exact size_of_tail (G.zk.getD q #[]) G.zx (J := (L.calls.getD q default).lJ)
    (by rw [hJ]; exact p1) p2 hls

/-- The premise hsTN, from a yes of the text that makes the tables. -/
theorem tN_size {h : Shape} {L : HL} {hp : OnBytes.Model.Head.HPlanH2} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : OnBytes.Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) : x.tN.r.size = h.lt := by
  unfold ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨lowN, p3, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, p4, _⟩ := ReadsQuiet.bind_ok e
  have c := ReadsQuiet.named_ok p3
  have j4 := ReadsQuiet.need_ok p4
  simp only [Bool.and_eq_true, beq_iff_eq] at j4
  unfold VerifiableInference.Desc.Own.cutTail at c
  split at c
  · cases c
  · rename_i hk
    have c' := (Option.some.inj c).symm
    subst c'
    have s1 := j4.1
    unfold longPoint at s1
    simp only [Array.size_append, Array.size_extract] at s1
    have s2 := j4.2
    omega

/-- The premise hz at the record: from the kind's letters, with hJ and hlsJ at the call x.qH. -/
theorem hz_of_letters (h : Shape) (L : HL) (iU3 work : ℕ) (s : S) (o : HeadOwn)
    (x : OnBytes.Model.Head.Heard) (here : s.here = .head o) (opened : o.opened = true)
    (hX1 : o.lookHeard = some x.g1) {g : Given} {bh : Behind} {pl : Places}
    (hl : lettersAt (parOf h work) (seatAt h iU3) s = .ok (g, bh, pl)) (hqH : x.qH < 6)
    (hJ : (L.calls.getD x.qH default).lJ =
      (letI := sizesOf h; lJ (OnBytes.Model.Head.keyFloor h) (callKeys x.qH)))
    (hlsJ : h.ls ≤ (L.calls.getD x.qH default).lJ) : h.ls + h.lt ≤ x.g1.zx.size := by
  obtain ⟨hg, -⟩ := lettersAt_ok hl
  obtain ⟨z, y, hz1, -, hP, -⟩ := Came.given_ok _ _ _ _ hg
  have hlook : s.lookHeard? = some x.g1 := by
    unfold S.lookHeard?
    rw [here]
    simp [opened, hX1]
  have hz2 : z = (x.g1.zx, fun c => x.g1.zk.getD c #[]) := by
    have e : (s.lookHeard?.map fun G => (G.zx, fun c => G.zk.getD c #[])) = some z := hz1
    rw [hlook] at e
    exact (Option.some.inj e).symm
  subst hz2
  exact hz_at h L x.g1 _ hP hqH hJ hlsJ

/-- runIs_at without the two premises that follow. -/
theorem runIs_at_twelve (h : Shape) (L : HL) (b : OnBytes.Model.Head.Border)
    (hp : OnBytes.Model.Head.HPlanH2) (iU3 work : ℕ) (s : S) (o : HeadOwn) (cov : Covered)
    (x : OnBytes.Model.Head.Heard) (t : OnBytes.Model.Head.Tables)
    (here : s.here = .head o) (opened : o.opened = true)
    (hcov : s.covered h.T h.V = .ok cov) (hx : o.x = some x)
    (made : ReadsQuiet.tables h L hp cov x = .ok t)
    (hX1 : o.lookHeard = some x.g1) (hX2 : x.Zl = Point.last x.g1.zx (h.ls + h.lt))
    [g : Given] [bh : Behind] {pl : Places}
    (hl : lettersAt (parOf h work) (seatAt h iU3) s = .ok (g, bh, pl))
    (hJ : ∀ q, q < 6 → (L.calls.getD q default).lJ =
      (letI := sizesOf h; lJ (OnBytes.Model.Head.keyFloor h) (callKeys q)))
    (hlsJ : ∀ q, q < 6 → h.ls ≤ (L.calls.getD q default).lJ)
    (hc6 : ∀ seg q, callNo L seg = some q → q < 6) (hqH : x.qH < 6) (hqN : x.qN < 6)
    (hsPV : x.PV.size = h.lt)
    (hsSq : x.wpl.r.size = (letI := sizesOf h; Norm.lNI + Norm.lPd) + h.lt)
    (hsTV : x.tV.r.size = h.lt) (hsTH : x.tH.r.size = h.lt)
    (hls : h.ls ≤ (letI := sizesOf h; Norm.lNI + Norm.lPd)) :
    RunIs ⟨h, L, b, hp, cov, x, t, iU3⟩ := by
  have hz : h.ls + h.lt ≤ x.g1.zx.size :=
    hz_of_letters h L iU3 work s o x here opened hX1 hl hqH (hJ _ hqH) (hlsJ _ hqH)
  exact runIs_at h L b hp iU3 work s o cov x t here opened hcov hx made hX1 hX2 hl hJ hlsJ hc6
    hqH hqN hz hsPV hsSq hsTV (tN_size made) hsTH hls

section Seven
variable [Sizes] [Request] [FinalNorm.In] [Heard]

/-- **The weights' tie for the five reads, from seven facts.** S: any seat. -/
theorem weights_of_seven (R : Run) (hZl : R.x.Zl = FinalNorm.zl ++ FinalNorm.zt)
    (szl : (FinalNorm.zl).size = Norm.ls) (szt : (FinalNorm.zt).size = Norm.lt)
    (ztH : ztOf R.h R.L R.x.g1 R.x.qH = FinalNorm.zt)
    (cov : ∀ t, t < Norm.T → R.cov.hOnC.getD t false = costed t) (tH : R.x.tH.r = rH)
    (stH : rH.size = Norm.lt) (hlt : R.h.lt = Norm.lt) (hls : R.h.ls = Norm.ls)
    (hla : R.h.la = Norm.ls + Norm.lt) (S : Seat) (ZV YN : Array E) (qFC qROW : ℕ)
    (b0 b1 : Array E) (r : Head.Read) (j : ℕ)
    (hj : j < (askOf (asksOfRun R ZV YN qFC qROW b0 b1) R.h r).2.2.1) :
    Reading.gl.val ((askOf (asksOfRun R ZV YN qFC qROW b0 b1) R.h r).2.2.2.1.getD j zeroE) =
      Reading.gl.val ((declOf S r).w j) := by
  have hT : R.h.T = Norm.T := by
    show 2 ^ R.h.lt = 2 ^ Norm.lt
    rw [hlt]
  have hTpos : 0 < Norm.T := Nat.two_pow_pos _
  have hZs : R.x.Zl.size = Norm.ls + Norm.lt := by
    rw [hZl, Array.size_append, szl, szt]
  have eZ1 : R.x.Zl.extract 0 Norm.ls = FinalNorm.zl := by
    rw [hZl, ← szl]
    exact Came.extract_left _ _
  have eZ2 : R.x.Zl.extract Norm.ls (Norm.ls + Norm.lt) = FinalNorm.zt := by
    rw [hZl, ← szl, ← szt]
    exact Came.extract_right _ _
  have hlong : ∀ {j : ℕ}, j < 2 ^ R.h.la →
      j / Norm.T < 2 ^ Norm.ls ∧ j % Norm.T < 2 ^ Norm.lt := by
    intro j hj
    rw [hla, Nat.pow_add] at hj
    exact ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj), Nat.mod_lt _ hTpos⟩
  have hshort : j < R.h.T → j < Norm.T := fun h0 => by
    rw [hT] at h0
    exact h0
  cases r
  · have hj' : j < 2 ^ R.h.la := hj
    obtain ⟨h1, h2⟩ := hlong hj'
    show rd ((longPhi R.x.Zl R.h.ls R.h.lt).getD j zeroE) =
      rd (eq FinalNorm.zl (j / Norm.T) * eq FinalNorm.zt (j % Norm.T))
    have e := Came.longPhi_cut R.x.Zl Norm.ls Norm.lt hZs h1 h2
    rw [eZ1, eZ2] at e
    have ej : j / Norm.T * 2 ^ Norm.lt + j % Norm.T = j := Nat.div_add_mod' j Norm.T
    rw [ej] at e
    rw [hls, hlt, e, rd_mul]
  · have hj' : j < 2 ^ R.h.la := hj
    obtain ⟨-, h2⟩ := hlong hj'
    show rd (((Array.range (2 ^ R.h.la)).map fun i =>
        (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (i % R.h.T) zeroE).getD j zeroE) =
      rd ((1 : E) * phiC (j % Norm.T))
    have e : ((Array.range (2 ^ R.h.la)).map fun i =>
        (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (i % R.h.T) zeroE).getD j zeroE =
        (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (j % R.h.T) zeroE := by
      simp [Array.getD, hj']
    rw [e, hT, ztH, Came.cost_phi szt cov _ h2, rd_mul, rd_one, one_mul]
  · show rd ((eqTab R.x.tH.r).getD j zeroE) = rd (eq rH j)
    rw [tH]
    exact Came.eqTab_reads rH j (by rw [stH]; exact hshort hj)
  · show rd ((costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD j zeroE) = rd (phiC j)
    rw [ztH]
    exact Came.cost_phi szt cov j (hshort hj)
  · show rd ((costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2.getD j zeroE) =
      rd (if costed j then (1 : E) else 0)
    rw [ztH]
    exact Came.cost_rho szt cov j (hshort hj)

end Seven

/-- **The weights' tie at the record, for the head's five reads, under six named premises.** -/
theorem weights_at (h : Shape) (L : HL) (b : OnBytes.Model.Head.Border)
    (hp : OnBytes.Model.Head.HPlanH2) (iU3 work : ℕ) (s : S) (o : HeadOwn) (cov : Covered)
    (x : OnBytes.Model.Head.Heard) (t : OnBytes.Model.Head.Tables)
    (here : s.here = .head o) (opened : o.opened = true)
    (hcov : s.covered h.T h.V = .ok cov) (hx : o.x = some x) (hla : h.la = h.ls + h.lt)
    (hX1 : o.lookHeard = some x.g1) (hX2 : x.Zl = Point.last x.g1.zx (h.ls + h.lt))
    [g : Given] [bh : Behind] {pl : Places}
    (hl : lettersAt (parOf h work) (seatAt h iU3) s = .ok (g, bh, pl)) (hqH : x.qH < 6)
    (hJ : (L.calls.getD x.qH default).lJ =
      (letI := sizesOf h; lJ (OnBytes.Model.Head.keyFloor h) (callKeys x.qH)))
    (hlsJ : h.ls ≤ (L.calls.getD x.qH default).lJ) (hsTH : x.tH.r.size = h.lt)
    (St : Seat) (ZV YN : Array E) (qFC qROW : ℕ) (b0 b1 : Array E) (r : Head.Read) (j : ℕ)
    (hj : j < (askOf (asksOfRun ⟨h, L, b, hp, cov, x, t, iU3⟩ ZV YN qFC qROW b0 b1) h r).2.2.1) :
    Reading.gl.val ((askOf (asksOfRun ⟨h, L, b, hp, cov, x, t, iU3⟩ ZV YN qFC qROW b0 b1)
        h r).2.2.2.1.getD j zeroE) = Reading.gl.val ((declOf St r).w j) := by
  obtain ⟨hg, H, hH, hb⟩ := lettersAt_ok hl
  obtain ⟨z, y, hz1, -, hP, hgE⟩ := Came.given_ok _ _ _ _ hg
  have hlook : s.lookHeard? = some x.g1 := by
    unfold S.lookHeard?
    rw [here]
    simp [opened, hX1]
  have hz2 : z = (x.g1.zx, fun c => x.g1.zk.getD c #[]) := by
    have e : (s.lookHeard?.map fun G => (G.zx, fun c => G.zk.getD c #[])) = some z := hz1
    rw [hlook] at e
    exact (Option.some.inj e).symm
  subst hz2
  have hz := hz_at h L x.g1 _ hP hqH hJ hlsJ
  have hall : ∃ q, allOf o.F x (some (keptOf q x.wpl.sL)) = some H := by
    have e : (match s.here with
      | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
        allOf o.F x (some (keptOf q x.wpl.sL))
      | _ => none) = some H := hH
    rw [here] at e
    obtain ⟨q, -, e⟩ := Option.bind_eq_some_iff.1 e
    rw [hx] at e
    exact ⟨q, e⟩
  obtain ⟨q, hall⟩ := hall
  obtain ⟨-, -, -, -, b5⟩ := back_points hall
  subst hb
  subst hgE
  have htH : x.tH.r = H.2.2.logits.r.extract 0 h.lt := by
    rw [b5]
    exact (take_append _ _ hsTH).symm
  exact @weights_of_seven (sizesOf h) (requestOf s)
    (@fromLookup (sizesOf h) (OnBytes.Model.Head.keyFloor h) x.g1.zx
      fun c => x.g1.zk.getD c #[]).norm H.2.2 ⟨h, L, b, hp, cov, x, t, iU3⟩
    (hX2.trans (Came.last_cut x.g1.zx h.ls h.lt hz).symm) (last_head_size x.g1.zx hz)
    (last_size x.g1.zx (n := h.lt) (Nat.le_trans (Nat.le_add_left _ _) hz))
    (zt_at h L x.g1 _ hP hqH hJ hlsJ hz) (cov_at h hcov) htH
    (by
      show (H.2.2.logits.r.extract 0 h.lt).size = h.lt
      rw [← htH]
      exact hsTH) rfl rfl
    hla St ZV YN qFC qROW b0 b1 r j hj

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.size_of_tail
#print axioms VerifiableInference.Reads.AtSeat.hz_at
#print axioms VerifiableInference.Reads.AtSeat.tN_size
#print axioms VerifiableInference.Reads.AtSeat.hz_of_letters
#print axioms VerifiableInference.Reads.AtSeat.runIs_at_twelve
#print axioms VerifiableInference.Reads.AtSeat.weights_of_seven
#print axioms VerifiableInference.Reads.AtSeat.weights_at
