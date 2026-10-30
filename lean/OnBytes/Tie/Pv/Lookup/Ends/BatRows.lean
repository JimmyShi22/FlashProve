-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean.
The number of rows that a sub-proof's last round batches, as the planner is told it: the number of
the sub-proof's linear claims plus the number of indices of its smallness test's equations.

A sub-proof ends with one drawn element that batches all its claims; the equations of its smallness
test stand under further powers of that element. The planner lays that round by
Params.planBatSigma rows, and prices it by rows - 1 over the size of the field. This file says, for
each of the three kinds of sub-proof, on the verifier's own functions, which number rows is.
Statements and proofs.

Main names:
  `planG_rows` (layers): Layer.planG P g O = .ok hp gives
    hp.nBatched = hp.nLin + hp.tl.equationsF (Layer.readsCount P.y P.rd g).
  `planH2_rows` (the head): Head.planH2 .. = .ok hp gives
    hp.rows = hp.nLin + hp.tl.equationsF (Head.readsH h L b).
  `planA_rows` (attention): Attention.plan settings i cf = .ok P gives
    P.own.rows = P.nLin + P.seam.tl.equationsF (tableReads P.S (Counts.of P.S)).
    By `planA_rows0` (the same at the smallness test's shape before its list of arrays is made),
    `addTreesF_keeps`, `seamPlan_keeps` (the making of that list keeps the matrices and tau) and
    `equationsF_congr` (equationsF hangs on these two alone).
  `layer_last`, `attention_last`, `head_last`: where the rounds after moment 2, run from the state
    p, do not refuse and leave q: the calls of which they are made have returned one behind the
    other, the first from p, the last leaving q, each with its arguments written out; the last is
    Params.planBatSigma at that number.
  `link_layer`, `link_attention`, `link_head`: the same through Verify.linkRounds, the function
    from which the chain's plan is made. Under: the link's number is the head's (stepOf X * X.NGr),
    or is not and is a multiple of stepOf X (a layer's) or none (an attention's), and X.G or X.A has
    a plan at the number link / stepOf X.
Limits: what round planBatSigma adds, and its bound, is not said here. Nothing is said of a run on
a proof: that nLin is the number of claims that a run adds is a test of the run
(internal-g-claim-count and its like), no statement here, and that equationsF counts the indices of
the smallness test's equations is its name. In each maker the field for the rows is set to this
very sum, so the first three statements say what the maker writes. That the members of Public.G,
Public.A and Public.H come from planG, plan and planH2 is not stated here but in
OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean and FoPublicA.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.VerifySubproofs

set_option autoImplicit false

namespace Fo.BatRows
open OnBytes OnBytes.Model OnBytes.Params

theorem bindE_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ### The three plans -/

theorem planG_rows (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    hp.nBatched = hp.nLin + hp.tl.equationsF (Layer.readsCount P.y P.rd g) := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, _, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, _, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · repeat obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    rfl
  · split at h <;>
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      rfl

theorem planH2_rows (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    hp.rows = hp.nLin + hp.tl.equationsF (Head.readsH h L b) := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e <;>
  · repeat obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    rfl

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

theorem ite_ok {c : Prop} [Decidable c] {ε α : Type} {t f : Except ε α} {a : α}
    (h : (if c then t else f) = .ok a) : (c ∧ t = .ok a) ∨ (¬ c ∧ f = .ok a) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact .inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact .inr ⟨hc, h⟩

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

/-- The making of the list of arrays keeps the matrices and tau. -/
theorem addTreesF_keeps (tl : HTailF2) (F : Fork) (T : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat)
    (r : HTailF2 × Fork × Tail2) (e : tl.addTreesF F T nU aTX hb hbLine = .ok r) :
    r.1.mats = tl.mats ∧ r.1.tau = tl.tau := by
  unfold HTailF2.addTreesF at e
  dsimp only at e
  alive
  alive
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  cases e
  exact ⟨rfl, rfl⟩

theorem equationsF_congr {tl tl' : HTailF2} (hm : tl'.mats = tl.mats) (ht : tl'.tau = tl.tau)
    (n : Nat) : tl'.equationsF n = tl.equationsF n := by
  unfold HTailF2.equationsF HTailF2.stepF
  rw [hm, ht]

theorem seamPlan_keeps (s s' : Attention.Seam) (nU3 hb hbLine : Nat)
    (e : s.plan nU3 hb hbLine = .ok s') : s'.tl.mats = s.tl.mats ∧ s'.tl.tau = s.tl.tau := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨r, hr, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact addTreesF_keeps _ _ _ _ _ _ _ r hr

open Attention in
theorem planA_rows0 (settings : Settings) (i : In) (cf : Cfg) (P : Plan)
    (e : plan settings i cf = .ok P) :
    ∃ seam0, Seam.shape settings (matrices P.S i) settings.tau i.col0Q i.ktO i.aO = .ok seam0 ∧
      seam0.plan P.nW i.hb settings.hb = .ok P.seam ∧
      P.own.rows = P.nLin + seam0.tl.equationsF (tableReads P.S (Counts.of P.S)) := by
  unfold plan at e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam0, h0, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam, h1, e⟩ := bindE_ok e
  cases e
  exact ⟨seam0, h0, h1, rfl⟩

open Attention in
theorem planA_rows (settings : Settings) (i : In) (cf : Cfg) (P : Plan)
    (e : plan settings i cf = .ok P) :
    P.own.rows = P.nLin + P.seam.tl.equationsF (tableReads P.S (Counts.of P.S)) := by
  obtain ⟨seam0, _, h1, h2⟩ := planA_rows0 settings i cf P e
  obtain ⟨hm, ht⟩ := seamPlan_keeps seam0 P.seam _ _ _ h1
  rw [h2, equationsF_congr hm ht]

/-! ### The rounds after moment 2 -/

theorem bindP_ok {α β : Type} {x : Planning α} {f : α → Planning β} {p : PlanState}
    {r : β × PlanState} (h : (x >>= f) p = .ok r) : ∃ a p1, x p = .ok (a, p1) ∧ f a p1 = .ok r := by
  have h' : (x p >>= fun v => f v.1 v.2) = Except.ok r := h
  obtain ⟨v, hv, hf⟩ := bindE_ok h'
  exact ⟨v.1, v.2, hv, hf⟩

theorem layer_last (look : ForestSize) (x : LayerRounds) (small : SmallSize) (claims : Nat)
    (p q : PlanState) (h : layerRounds look x small claims 2 p = .ok ((), q)) :
    ∃ p1, planSmall small 1 p = .ok ((), p1) ∧ planBatSigma claims p1 = .ok ((), q) := by
  obtain ⟨_, p1, h1, h⟩ := bindP_ok (x := planSmall small 1) h
  exact ⟨p1, h1, h⟩

theorem attention_last (look : ForestSize) (x : AttentionRounds) (small : SmallSize)
    (p q : PlanState) (h : attentionRounds look x small 2 p = .ok ((), q)) :
    ∃ p1, planSmall small 1 p = .ok ((), p1) ∧ planBatSigma x.rows p1 = .ok ((), q) := by
  obtain ⟨_, p0, h0, h⟩ := bindP_ok (x := pure PUnit.unit) h
  obtain rfl : p = p0 := congrArg Prod.snd (Except.ok.inj h0)
  obtain ⟨_, p1, h1, h⟩ := bindP_ok (x := planSmall small 1) h
  exact ⟨p1, h1, h⟩

theorem head_last (look : ForestSize) (x : HeadRounds) (small : SmallSize)
    (p q : PlanState) (h : headRounds look x small 2 p = .ok ((), q)) :
    ∃ p1 p2 p3, planSmall small 1 p = .ok ((), p1) ∧ planBatSigma 1 p1 = .ok ((), p2) ∧
      planPsc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 } p2 = .ok ((), p3) ∧
      planBatSigma x.rows p3 = .ok ((), q) := by
  obtain ⟨_, p0, h0, h⟩ := bindP_ok (x := pure PUnit.unit) h
  obtain rfl : p = p0 := congrArg Prod.snd (Except.ok.inj h0)
  obtain ⟨_, p1, h1, h⟩ := bindP_ok (x := planSmall small 1) h
  obtain ⟨_, p2, h2, h⟩ := bindP_ok (x := planBatSigma 1) h
  obtain ⟨_, p3, h3, h⟩ := bindP_ok h
  exact ⟨p1, p2, p3, h1, h2, h3, h⟩

/-! ### Through the function from which the chain's plan is made -/

/-- The number of links of a group: an attention sub-proof follows each layer sub-proof or not. -/
def stepOf (X : Verify.Public) : Nat := if X.p4 then 2 else 1

theorem link_head (X : Verify.Public) (link : Nat) (h1 : link = stepOf X * X.NGr)
    (p q : PlanState) (h : Verify.linkRounds X link 2 p = .ok ((), q)) :
    ∃ p1 p2 p3, planSmall (smallSize X.H.tl) 1 p = .ok ((), p1) ∧
      planBatSigma 1 p1 = .ok ((), p2) ∧
      planPsc { degree := List.replicate X.H.lkW 3, degreeY := 1, values := 1 } p2 =
        .ok ((), p3) ∧
      planBatSigma X.H.rows p3 = .ok ((), q) := by
  unfold Verify.linkRounds at h
  have e : (link == (if X.p4 = true then 2 else 1) * X.NGr) = true := by
    rw [h1]
    exact beq_self_eq_true _
  simp only [e, if_true] at h
  exact head_last _ (X.H.own X.hS) _ p q h

theorem link_layer (X : Verify.Public) (link : Nat) (hp : Layer.HPlan2)
    (h1 : link ≠ stepOf X * X.NGr) (h2 : link % stepOf X = 0)
    (hG : X.G[link / stepOf X]? = some hp) (p q : PlanState)
    (h : Verify.linkRounds X link 2 p = .ok ((), q)) :
    ∃ p1, planSmall (smallSize hp.tl) 1 p = .ok ((), p1) ∧
      planBatSigma hp.nBatched p1 = .ok ((), q) := by
  unfold Verify.linkRounds at h
  have e1 : (link == (if X.p4 = true then 2 else 1) * X.NGr) = false := beq_false_of_ne h1
  have e2 : (link % (if X.p4 = true then 2 else 1) == 0) = true := by
    rw [show link % (if X.p4 = true then 2 else 1) = 0 from h2]
    rfl
  have e3 : X.G[link / (if X.p4 = true then 2 else 1)]? = some hp := hG
  simp only [e1, e2, e3, if_true, Bool.false_eq_true, if_false] at h
  exact layer_last _ _ _ _ p q h

theorem link_attention (X : Verify.Public) (link : Nat) (a : Attention.Plan)
    (h1 : link ≠ stepOf X * X.NGr) (h2 : link % stepOf X ≠ 0)
    (hA : X.A[link / stepOf X]? = some a) (p q : PlanState)
    (h : Verify.linkRounds X link 2 p = .ok ((), q)) :
    ∃ p1, planSmall (smallSize a.seam.tl) 1 p = .ok ((), p1) ∧
      planBatSigma a.own.rows p1 = .ok ((), q) := by
  unfold Verify.linkRounds at h
  have e1 : (link == (if X.p4 = true then 2 else 1) * X.NGr) = false := beq_false_of_ne h1
  have e2 : (link % (if X.p4 = true then 2 else 1) == 0) = false := beq_false_of_ne h2
  have e3 : X.A[link / (if X.p4 = true then 2 else 1)]? = some a := hA
  simp only [e1, e2, e3, Bool.false_eq_true, if_false] at h
  exact attention_last _ _ _ p q h

end Fo.BatRows
