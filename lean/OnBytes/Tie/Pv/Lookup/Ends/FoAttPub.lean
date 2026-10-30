-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttPub.lean: the attention sub-proof's key forms: the premises on
public numbers and values, cut in two: a test on the shape, and what depends on what was heard.

Fo.att_keys (OnBytes/Tie/Pv/Lookup/Ends/FoAttKeys.lean) stands under Fo.RuleA, whose first part
Fo.PubA gathers, call by call, the premises "on public numbers and values" of the theorem on the
call's kind. Some of them speak of the sub-proof's shape and of the lookup's record of public
numbers alone. The others speak of the record of what the verifier has heard: the lengths of the
calls' key points, the lists of units with their pieces' weights, points cut out of key points, and
two closed forms in such points.

 - callEq_of: two calls that callEqB passes are equal. pcsOK_of_test: pcsB gives PcsOK (the pieces
   are aligned and apart). The tests callEqB, pcsB, pubCallB, pubAB are defined in
   OnBytes/Tie/Pv/Lookup/Ends/FoAttBDefs.lean.
 - HeardKR, HeardKFD, HeardR16, HeardWH; HeardOf; HeardA h NC b': the rest of PubA, by kind.
 - pubA_of_test: pubAB at the record's own shape, lookup's record and call qWH, with HeardA, gives
   PubA.

Limits. HeardA is a hypothesis: it is shown of no record here. A call of kind WH that is not the
call qWH fails the test, as it fails PubA.
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that pubAB is true at
any shape (a test file that runs it at one is [not in this library]).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKeys
import OnBytes.Tie.Pv.Lookup.Ends.FoAttBDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Attention OnBytes.Ends OnBytes.Ends.A

theorem callEq_of {a b : Call} (h : callEqB a b = true) : a = b := by
  cases a
  cases b
  simp only [callEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

theorem pcsOK_of_test {n : ℕ} {ps : List Pc} (h : pcsB n ps = true) : PcsOK n ps := by
  simp only [pcsB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

/-! ### what hangs on what was heard -/

section
variable (h : Attention.Heard) (q : ℕ) (c : ACall)

/-- At a call of kind KR. -/
structure HeardKR : Prop where
  size : (h.g.zk.getD q #[]).size = c.call.n
  nodup : ((unitsKR h q).map fun pc => pc.seg).Nodup
  cover : ∀ p ∈ c.pcs.toList, p.seg ∈ (unitsKR h q).map fun pc => pc.seg
  segs : ∀ pc ∈ unitsKR h q, pc.seg = Attention.Seg.rm ∨ pc.seg = Attention.Seg.rd
  pw : ∀ pc ∈ unitsKR h q, pc.pw = pieces c (h.g.zk.getD q #[]) pc.seg

/-- At a call of kind KFD. -/
structure HeardKFD : Prop where
  size : (h.g.zk.getD q #[]).size = c.call.n
  nodup : ((unitsKFD h q).map fun k => k.seg).Nodup
  cover : ∀ p ∈ c.pcs.toList, p.seg ∈ (unitsKFD h q).map fun k => k.seg
  segs : ∀ k ∈ unitsKFD h q, k.seg = Attention.Seg.fm ∨ k.seg = Attention.Seg.fd
  pw : ∀ k ∈ unitsKFD h q, k.pw = pieces c (h.g.zk.getD q #[]) k.seg
  pub : ∀ k ∈ unitsKFD h q,
    (if k.seg == Attention.Seg.fm then
        ((h.S.shd c.sh).C : Cb.Gl.E) * readE (sumW k.pw) * readE (onesOf k.zs)
      else ((h.S.shd c.sh).Om : Cb.Gl.E) * readE (sumW k.pw) * (1 - readE (leOf k.zj k.zi))) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) k.seg
      fun _ => gcAt h.S c.sh (k.seg == Attention.Seg.fd)

/-- At a call of kind R16. -/
structure HeardR16 (b' : ℕ) : Prop where
  size : (h.g.zk.getD q #[]).size = c.call.n
  pw : h.d.pwW = pieces c (h.g.zk.getD q #[]) .wl
  zsl : readE h.d.zsl = readV (h.g.zk.getD q #[]) (c.call.n - (1 + b'))
  pub : readE (sumW h.d.pwX) * readE (idOf h.d.ziX) =
    ruleAt c.call.n c.pcs.toList (readV (h.g.zk.getD q #[])) .ix
      fun _ κ => ((κ % h.S.T : ℕ) : Cb.Gl.E)

/-- At the call of kind WH. -/
structure HeardWH : Prop where
  size : (h.g.zk.getD q #[]).size = c.call.n
  pw : h.d.pwH = pieces c (h.g.zk.getD q #[]) .wh

/-- By the call's kind. -/
def HeardOf (b' : ℕ) : Prop :=
  (h.d.qWH = q → HeardWH h q c) ∧ (h.d.qWH ≠ q → c.kind = .r16 → HeardR16 h q c b') ∧
    (h.d.qWH ≠ q → c.kind = .kfd → HeardKFD h q c) ∧ (h.d.qWH ≠ q → c.kind = .kr → HeardKR h q c)

end

/-- What of PubA hangs on what was heard. -/
def HeardA (h : Attention.Heard) (NC b' : ℕ) : Prop :=
  ∀ q < NC, ∀ c, h.S.calls[q]? = some c → HeardOf h q c b'

/-- **The test and the heard part give PubA.** -/
theorem pubA_of_test (h : Attention.Heard) (NC b' : ℕ)
    (hB : pubAB h.S h.g.shape NC h.d.qWH b' = true) (hH : HeardA h NC b') : PubA h NC b' := by
  intro q hq
  unfold pubAB at hB
  have h1 := List.all_eq_true.mp hB q (List.mem_range.mpr hq)
  obtain ⟨c, hc, h2⟩ : ∃ c, h.S.calls[q]? = some c ∧
      pubCallB h.S h.g.shape h.d.qWH b' q c = true := by
    cases e : h.S.calls[q]? with
    | none => rw [e] at h1; cases h1
    | some c => rw [e] at h1; exact ⟨c, rfl, h1⟩
  obtain ⟨w1, w2, w3, w4⟩ := hH q hq c hc
  refine ⟨c, hc, ?_⟩
  unfold pubCallB at h2
  rw [Bool.and_eq_true] at h2
  obtain ⟨hok, h2⟩ := h2
  have ok := pcsOK_of_test hok
  have cast0 : tauN h.g.shape q (t0N h.g.shape q) = 0 →
      (tauN h.g.shape q (t0N h.g.shape q) : Cb.Gl.E) = 0 := fun e => by rw [e, Nat.cast_zero]
  by_cases hw : h.d.qWH = q
  · rw [if_pos hw] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact Or.inl ⟨hw, ⟨ok, (w1 hw).size, cast0 h2.1, h2.2, (w1 hw).pw⟩⟩
  · rw [if_neg hw] at h2
    cases hk : c.kind with
    | r16 =>
      rw [hk] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h2
      have H := w2 hw hk
      exact Or.inr (Or.inl ⟨hw, hk,
        ⟨a1, a2, ok, H.size, cast0 a3, a4, a5, a6, H.pw, H.zsl, H.pub⟩⟩)
    | kfd =>
      rw [hk] at h2
      have H := w3 hw hk
      have hcall : h.g.shape.calls[q]? = some c.call := by
        cases e : h.g.shape.calls[q]? with
        | none => rw [e] at h2; cases h2
        | some k =>
          rw [e] at h2
          rw [callEq_of (a := k) (b := c.call) h2]
      exact Or.inr (Or.inr (Or.inl ⟨hw, hk,
        ⟨hcall, ok, H.size, H.nodup, H.cover, H.segs, H.pw, H.pub⟩⟩))
    | kr =>
      rw [hk] at h2
      simp only [decide_eq_true_eq] at h2
      have H := w4 hw hk
      exact Or.inr (Or.inr (Or.inr ⟨hw, hk,
        ⟨ok, H.size, cast0 h2, H.nodup, H.cover, H.segs, H.pw⟩⟩))
    | wh =>
      rw [hk] at h2
      cases h2

end Fo
