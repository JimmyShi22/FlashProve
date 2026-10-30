-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadPub.lean: four public conditions of the library's theorems on the output head, as
conclusions from the verifier's own tests on public numbers; and what the public part of a stage
has run for the head.

The library's theorems on the head ask that the final normalisation's three numbers are lawful
(NormPar.OK, Inst/Model/Program.lean) and that the policy's three words are bounded (AcceptancePolicy.OK,
Inst/Model/ProgramRPol.lean). The theorems on the policy's four claims
(Johnson/Road/HeadPolicyForms.lean) ask that the scale of the table of exponentials is 2^24 and that
the number of counted positions is the verifier's. This file shows these of the numbers that have
passed the verifier's tests.

Whose tests. Six of the seven clauses of NormPar.OK, two of the three of AcceptancePolicy.OK and the scale are
tests of the function policy (OnBytes/Model/HeadLayout.lean), which the head's layout runs. The
seventh clause, eps < 2^48, is no test of the head's: policy allows eps below 2^59. It is a test of
the layers' conditions against wrap-around (noWrapWith in OnBytes/Model/LayerLayout.lean, under five
limbs), which the public part of a stage runs (publicOf, OnBytes/Model/VerifyPublic.lean). The third
clause of AcceptancePolicy.OK, C < 2^40, is no test of the layout's either: its conditions give C < 2^42 at 1,024
positions. By the comments of the verifier the reader of the parameter file refuses a value of 2^32
or more; that is not shown here, and C < 2^40 stays a hypothesis.

Main definitions: PolicyHeld (what the function policy tests, as far as it is used).
Main theorems: policy_of_layout, policyHeld_of_policy; normOK_of_policy; true_of_need,
eps_of_noWrap; layerLayout_of_polLayout, pubOf_y, public_parts (publicOf taken apart: the lines on
the head's shape, layout and plan, with the caller's own arguments), layoutW_of_public;
normOK_of_public (NormPar.OK from publicOf, with five limbs); polOK_of_policy; famF_of_layout;
count_between, hRC_of_covered, nb_of_covered (the number of counted positions).

What is not claimed. That the functions return a value is a hypothesis throughout. Nothing on the
layers' two normalisations or on the file of scales. The program does not import this file.
-/
import Johnson.Road.HeadLaid
import Johnson.Road.HeadTabs
import Johnson.Road.FormsKeysCap

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

/-! ## The tests of the function policy -/

/-- The head's layout has run the function policy. -/
theorem policy_of_layout {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) : Model.Head.policy h = .ok () := by
  unfold Model.Head.layout at hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨u, hp, -⟩ := ok_of_bind hy
  exact hp

/-- What the function policy tests, as far as it is used here. -/
structure PolicyHeld (h : Model.Head.Shape) : Prop where
  MF24 : 24 ≤ h.MF
  MF47 : h.MF ≤ 47
  MK : h.MF ≤ h.KF + 14
  KF17 : 17 ≤ h.KF
  KF32 : h.KF ≤ 32
  eps1 : 1 ≤ h.epsF
  eps59 : h.epsF < 2 ^ 59
  theta : h.theta ≤ h.clipC
  capT : h.cap ≤ h.T
  cap16 : h.cap < 2 ^ 16
  famF : h.famF = 24

/-- The tests, one by one. -/
theorem policyHeld_of_policy {h : Model.Head.Shape} (hp : Model.Head.policy h = .ok ()) :
    PolicyHeld h := by
  unfold Model.Head.policy at hp
  obtain ⟨t1, hp⟩ := ok_of_needed hp
  obtain ⟨t2, hp⟩ := ok_of_needed hp
  obtain ⟨-, hp⟩ := ok_of_needed hp
  obtain ⟨t4, hp⟩ := ok_of_needed hp
  obtain ⟨t5, -⟩ := ok_of_needed hp
  obtain ⟨a1, a2⟩ := nor_true_split t1
  obtain ⟨a3, a4⟩ := or_false_split a1
  obtain ⟨b1, b2⟩ := nor_true_split t2
  obtain ⟨b3, b4⟩ := or_false_split b1
  obtain ⟨b5, b6⟩ := or_false_split b3
  obtain ⟨c1, c2⟩ := nor_true_split t4
  obtain ⟨c3, c4⟩ := or_false_split c1
  obtain ⟨d1, -⟩ := nor_true_split t5
  have k1 := of_decide_eq_false a3
  have k2 := of_decide_eq_false a4
  have k3 := of_decide_eq_false a2
  have k4 := of_decide_eq_false b5
  have k5 := of_decide_eq_false b6
  have k6 := of_decide_eq_false b4
  have k7 := of_decide_eq_false b2
  have k8 := of_decide_eq_false c3
  have k9 := of_decide_eq_false c4
  have k10 := of_decide_eq_false c2
  exact {
    MF24 := by omega
    MF47 := by omega
    MK := by omega
    KF17 := by omega
    KF32 := by omega
    eps1 := by omega
    eps59 := by omega
    theta := by omega
    capT := by omega
    cap16 := by omega
    famF := by simpa using d1 }

/-- **The scale of the table of exponentials is 2^24.** -/
theorem famF_of_layout {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) : h.famF = 24 :=
  (policyHeld_of_policy (policy_of_layout hy)).famF

/-! ## The final normalisation's numbers -/

/-- The final normalisation's numbers are lawful if they have passed policy and eps is below
2^48. -/
theorem normOK_of_policy {h : Model.Head.Shape} (hp : Model.Head.policy h = .ok ())
    (he : h.epsF < 2 ^ 48) : (npOf h).OK := by
  have P := policyHeld_of_policy hp
  have p1 := P.MF24
  have p2 := P.MF47
  have p3 := P.MK
  have p4 := P.KF17
  have p5 := P.KF32
  have p6 := P.eps1
  show (1 : ℤ) ≤ (h.epsF : ℤ) ∧ (h.epsF : ℤ) < 2 ^ 48 ∧ 24 ≤ h.MF ∧ h.MF ≤ 47 ∧ 17 ≤ h.KF ∧
    h.KF ≤ 32 ∧ h.MF - 14 ≤ h.KF
  refine ⟨by omega, by omega, p1, p2, p4, p5, by omega⟩

/-- A condition against wrap-around that goes on has found its condition true. -/
theorem true_of_need {b : Bool} {n : String} {a : Unit} (h : Model.Layer.need b n = .ok a) :
    b = true := by
  have k := false_of_refuseIf h
  cases b with
  | true => rfl
  | false => cases k

/-- With five limbs, the layers' conditions against wrap-around test that the final normalisation's
eps is below 2^48. -/
theorem eps_of_noWrap {h : Model.Layer.Shape} {s : Model.Layer.Scales} {dq : ℕ} {u : Unit}
    (hn : Model.Layer.noWrap h s dq = .ok u) (hx : h.xl = 5) : h.epsF < 2 ^ 48 := by
  unfold Model.Layer.noWrap Model.Layer.noWrapWith at hn
  dsimp only at hn
  repeat' first
    | (obtain ⟨_, _, hn⟩ := ok_of_bind hn)
    | (split at hn)
  all_goals first
    | exact of_decide_eq_true (true_of_need hn)
    | (rename_i hc
       exact absurd (by rw [hx]; rfl) hc)

/-! ## The public part of a stage, taken apart -/

/-- The layers' layout in what polLayout returns is what the layers' function layout returns for the
shape and the calls of the parameter file as read. -/
theorem layerLayout_of_polLayout {pol : ByteArray} {P : Model.PolScan} {y : Model.Layer.Lay}
    (hpl : Model.Verify.polLayout pol = .ok (P, y)) :
    Model.Layer.layout (Model.Verify.layerShape P) P.polCalls = .ok y := by
  unfold Model.Verify.polLayout at hpl
  obtain ⟨P0, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨y0, hy0, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hpl
  exact hy0

/-- The record of the layers' public numbers holds the layout from which it was made. -/
theorem pubOf_y {y : Model.Layer.Lay} {sc : Model.Layer.Scales} {rope : Array ℕ}
    {wsLay : Model.WsLay} {V : ℕ} {tokv : Array ℕ} {set : Model.Settings} {Z : Model.Layer.Pub}
    (h : Model.Layer.Pub.of y sc rope wsLay V tokv set = .ok Z) : Z.y = y := by
  unfold Model.Layer.Pub.of at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨rd, -, h⟩ := ok_of_bind h
  cases h
  rfl

/-- **What publicOf has run for the head, and what its value holds.** P, y: the parameter file as
read and the layers' layout, from polLayout. The value holds P, y and the head's shape made of them.
The layers' conditions against wrap-around have passed. The head's layout is what Head.layout
returns for that shape and the layers' table of the clamp. The head's plan is what planH2 returns
for the shape, the layout, the stream's matrix of y and the value's owner, but for its planned
state, which is trimmed: the plan of the smallness test is the same. -/
theorem public_parts {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) :
    ∃ P y, Model.Verify.polLayout pol = .ok (P, y) ∧ X.P = P ∧ X.y = y ∧
      X.hS = Model.Verify.headShape P y ∧
      (∃ sc u, Model.Layer.noWrap y.h sc y.dq = .ok u) ∧
      Model.Head.layout X.hS y.tauFC = .ok X.HLy ∧
      ∃ H, Model.Head.planH2 P.settings X.hS X.HLy (Model.Verify.borderOf y) X.owner y.NGr
        P.lkW = .ok H ∧ X.H.tl = H.tl := by
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_ite2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  refine ⟨P, y, hpl, rfl, pubOf_y (by assumption), rfl, ⟨_, _, by assumption⟩, by assumption,
    ⟨?H, ?h1, ?h2⟩⟩
  case h1 => assumption
  case h2 => rfl

/-- **The head's layout in the public part, at the clamp's table as
Johnson/Road/HeadTabs.lean writes it.** -/
theorem layoutW_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) :
    Model.Head.layout X.hS tauFCw = .ok X.HLy := by
  obtain ⟨P, y, hpl, -, -, -, -, hl, -⟩ := public_parts h
  rw [tauFC_of_layout (layerLayout_of_polLayout hpl)] at hl
  exact hl

/-- **The final normalisation's numbers are lawful**, for the head's shape in what the public part
of a stage returns, with five limbs. -/
theorem normOK_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) (h5 : X.hS.XL = 5) : (npOf X.hS).OK := by
  obtain ⟨P, y, hpl, -, -, eS, ⟨sc, u, hnw⟩, hl, -⟩ := public_parts h
  refine normOK_of_policy (policy_of_layout hl) ?_
  have hyh : y.h = Model.Verify.layerShape P := layout_shape (layerLayout_of_polLayout hpl)
  rw [eS] at h5 ⊢
  have h5' : P.XL = 5 := h5
  have k := eps_of_noWrap hnw (by rw [hyh]; exact h5')
  rw [hyh] at k
  exact k

/-! ## The policy's words -/

/-- The policy's three words are bounded as the library asks, if they have passed policy and the
clip is below 2^40. -/
theorem polOK_of_policy {h : Model.Head.Shape} (hp : Model.Head.policy h = .ok ())
    (hC : h.clipC < 2 ^ 40) : Inst.Model.AcceptancePolicy.OK ⟨h.clipC, h.theta, h.cap⟩ := by
  have P := policyHeld_of_policy hp
  exact ⟨hC, Nat.lt_of_le_of_lt P.theta hC, P.cap16⟩

/-! ## The number of counted positions -/

/-- Among the numbers below n, those from a on and below b are min b n - a. -/
theorem count_between (a b : ℕ) : ∀ n : ℕ,
    ((List.range n).filter fun t => decide (a ≤ t) && decide (t < b)).length = min b n - a
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, count_between a b n]
    by_cases h : a ≤ n ∧ n < b
    · have e : (decide (a ≤ n) && decide (n < b)) = true := by
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true h.1, decide_eq_true h.2⟩
      rw [List.filter_cons_of_pos (p := fun t => decide (a ≤ t) && decide (t < b)) e,
        List.filter_nil, List.length_singleton]
      omega
    · have e : ¬ (decide (a ≤ n) && decide (n < b)) = true := by
        rw [Bool.and_eq_true]
        intro k
        exact h ⟨of_decide_eq_true k.1, of_decide_eq_true k.2⟩
      rw [List.filter_cons_of_neg (p := fun t => decide (a ≤ t) && decide (t < b)) e,
        List.filter_nil, List.length_nil]
      omega

/-- The verifier's number of positions with a cost: min (e, T - 1) - r, with r and e for the two
words behind the tokens. -/
theorem hRC_of_covered {so : Model.Head.StOwn} {T V : ℕ} {cov : Model.Head.Covered}
    (h : Model.Head.coveredOf so T V = .ok cov) :
    cov.hRC = min (so.req.getD (T + 1) 0).toNat (T - 1) - (so.req.getD T 0).toNat := by
  unfold Model.Head.coveredOf at h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨-, h⟩ := ok_of_needed h
  cases h
  show ((List.range T).filter fun t =>
    (decide ((so.req.getD T 0).toNat ≤ t) && decide (t < (so.req.getD (T + 1) 0).toNat)) &&
      decide (t + 1 < T)).length = _
  have e : ((List.range T).filter fun t =>
      (decide ((so.req.getD T 0).toNat ≤ t) && decide (t < (so.req.getD (T + 1) 0).toNat)) &&
        decide (t + 1 < T)) =
      (List.range T).filter fun t => decide ((so.req.getD T 0).toNat ≤ t) &&
        decide (t < min (so.req.getD (T + 1) 0).toNat (T - 1)) := by
    refine List.filter_congr fun t _ => ?_
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro k
      omega
    · intro k
      omega
  rw [e, count_between]
  omega

/-- **The library's number of counted positions is the verifier's**, for a request with the r and e
of the request's words, at 1,024 positions. -/
theorem nb_of_covered {so : Model.Head.StOwn} {V : ℕ} {cov : Model.Head.Covered}
    (hc : Model.Head.coveredOf so 1024 V = .ok cov) {R : Model.Head.Run} (e1 : R.cov = cov)
    {y : Inst.Model.Head.Req} (hr : y.r = (so.req.getD 1024 0).toNat)
    (he : y.e = (so.req.getD (1024 + 1) 0).toNat) : y.NB = R.cov.hRC := by
  rw [e1, hRC_of_covered hc, ← hr, ← he]
  rfl

#print axioms public_parts
#print axioms layoutW_of_public
#print axioms normOK_of_public
#print axioms polOK_of_policy
#print axioms famF_of_layout
#print axioms nb_of_covered

end OnBytes.Road.Hd
