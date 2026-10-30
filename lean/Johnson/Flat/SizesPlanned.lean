-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/SizesPlanned.lean: the sizes that `sizesAt` reads off a parameter file are those of
what the verifier program plans at the same file.

Laws only. The laws on the links' block at an instance (Johnson/Flat/LinksAt.lean and what stands on
it) ask that P.T is p's window, that P.V is p's vocabulary, that P.T < 2 ^ 32 and P.V ≤ 2 ^ 32. Here
P is what `sizesAt` (Johnson/Flat/Instance.lean) returns at a parameter file, and p what
`Model.Verify.planned` (OnBytes/Model/Verify.lean) returns at that file with any scale file and any
layout file. No run of a proof is asked.

Main names:
  `layoutBase_window`, `layoutLook_window`, `layout_window`: the layout of a layer sub-proof has the
    window 2 ^ lt, and lt is at most 16.
  `pub_layout`: the layers' public numbers hold the layout from which they were made.
  `publicOf_window`: in the public part that the planner makes, the window is 2 ^ lt of the
    parameter file as scanned, lt is at most 16, and the vocabulary is at most 2 ^ 24.
  `sizesAt_planned`: the four premises, from `sizesAt policy = .ok P` and `planned policy KL layout
    = .ok p`. `sizesAt_iff_exact`: where `planned` returns p, `sizesAt policy = .ok P` says exactly:
    the scanned file's acceptance policy is exact match, and P is `sizesOf` of p's own scan.
Limits: `sizesAt policy = .ok P` IS A PREMISE ON THE ACCEPTANCE POLICY: `sizesAt` refuses every
parameter file that is not exact match, also one that the program admits. Nothing where one of the
two refuses. P is not the file's parameters: ten sizes are the file's, the other fields the
reference numbers'. Nothing on the other eight sizes, which, by reading, no step of the links' block
reads.

-/
import Johnson.Flat.Instance
import OnBytes.Model.VerifyDerives

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- A refusal that did not happen. -/
theorem refuseIf_ok {b : Bool} {name : String} {u : Unit} (h : refuseIf b name = .ok u) :
    b = false := by
  unfold refuseIf at h
  cases b with
  | false => rfl
  | true => cases h

/-- The first half of a layer sub-proof's layout: the window is 2 ^ lt, and lt is at most 16. -/
theorem layoutBase_window {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layoutBase h pc = .ok y) : y.T = 2 ^ h.lt ∧ h.lt ≤ 16 := by
  unfold Layer.layoutBase at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := exc_bind e
  obtain ⟨_, e2, e⟩ := exc_bind e
  have hb := refuseIf_ok e2
  have hlt : h.lt ≤ 16 := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    omega
  refine ⟨?_, hlt⟩
  repeat' first
    | (obtain ⟨_, _, e⟩ := exc_bind e)
    | (split at e)
  all_goals (cases e; rfl)

/-- The second half keeps the window. -/
theorem layoutLook_window {y0 y : Layer.Lay} (e : Layer.layoutLook y0 = .ok y) : y.T = y0.T := by
  unfold Layer.layoutLook at e
  dsimp only at e
  repeat' first
    | (obtain ⟨_, _, e⟩ := exc_bind e)
    | (split at e)
  all_goals (cases e; rfl)

/-- The layout of a layer sub-proof: the window is 2 ^ lt, and lt is at most 16. -/
theorem layout_window {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layout h pc = .ok y) : y.T = 2 ^ h.lt ∧ h.lt ≤ 16 := by
  unfold Layer.layout at e
  obtain ⟨y0, e0, e⟩ := exc_bind e
  obtain ⟨a, b⟩ := layoutBase_window e0
  exact ⟨(layoutLook_window e).trans a, b⟩

/-- The layers' public numbers hold the layout from which they were made. -/
theorem pub_layout {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (e : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.y = y := by
  unfold Layer.Pub.of at e
  obtain ⟨_, _, e⟩ := exc_bind e
  obtain ⟨_, _, e⟩ := exc_bind e
  cases e
  rfl

/-- The scan and the layout: the layout's window is 2 ^ lt of the scan, and lt is at most 16. -/
theorem polLayout_window {pol : ByteArray} {P : PolScan} {y : Layer.Lay}
    (e : polLayout pol = .ok (P, y)) : y.T = 2 ^ P.h.lt ∧ P.h.lt ≤ 16 := by
  unfold polLayout at e
  obtain ⟨P0, _, e⟩ := exc_bind e
  obtain ⟨_, _, e⟩ := exc_bind e
  obtain ⟨y0, hy, e⟩ := exc_bind e
  obtain ⟨_, _, e⟩ := exc_bind e
  obtain ⟨_, _, e⟩ := exc_bind e
  obtain ⟨_, _, e⟩ := exc_bind e
  cases e
  exact layout_window hy

/-- The test on the vocabulary's size. -/
theorem vocabulary_le {h : Head.Shape} {u : Unit} (e : Head.vocabulary h = .ok u) :
    h.V ≤ 2 ^ 24 := by
  unfold Head.vocabulary at e
  obtain ⟨_, e1, _⟩ := exc_bind e
  unfold Head.needed at e1
  split at e1
  · rename_i hb
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    omega
  · cases e1

/-- **In the public part that the planner makes**: the window is 2 ^ lt of the parameter file as
scanned, lt is at most 16, and the vocabulary is at most 2 ^ 24. -/
theorem publicOf_window {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) :
    X.T = 2 ^ X.P.h.lt ∧ X.P.h.lt ≤ 16 ∧ X.P.h.V ≤ 2 ^ 24 := by
  unfold publicOf at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  obtain ⟨hT, hlt⟩ := polLayout_window h0
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals
    cases h
    have eL := pub_layout (by assumption)
    have eV : (headShape P y).V ≤ 2 ^ 24 := vocabulary_le (by assumption)
    exact ⟨(congrArg Layer.Lay.T eL).trans hT, hlt, eV⟩

/-- What `planned` holds as the public part is what `publicOf` returns. -/
theorem planned_publicOf {policy KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (hp : planned policy KL layout = .ok p) : publicOf policy KL layout = .ok p.X := by
  unfold planned at hp
  obtain ⟨X, h0, hp⟩ := exc_bind hp
  dsimp only at hp
  obtain ⟨_, _, hp⟩ := exc_bind hp
  obtain ⟨_, _, hp⟩ := exc_bind hp
  cases hp
  exact h0

/-- **Who pays `sizesAt policy = .ok P`**: where `planned` returns p, `sizesAt` returns exactly if
the scanned file's acceptance policy is exact match, and then it returns the sizes of p's own scan.
-/
theorem sizesAt_iff_exact {policy KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (hp : planned policy KL layout = .ok p) (P : Params) :
    sizesAt policy = .ok P ↔ exactPolicy p.X.P.h = true ∧ P = sizesOf p.X.P.h := by
  have hs := publicOf_scan (planned_publicOf hp)
  have e : sizesAt policy =
      if exactPolicy p.X.P.h then pure (sizesOf p.X.P.h) else throw "policy-not-exact-match" := by
    unfold sizesAt
    rw [hs]
    rfl
  rw [e]
  cases hb : exactPolicy p.X.P.h with
  | false =>
    constructor
    · intro h
      cases h
    · intro h
      cases h.1
  | true =>
    constructor
    · intro h
      exact ⟨rfl, (Except.ok.inj h).symm⟩
    · intro h
      rw [h.2]
      rfl

/-- **The four premises of the laws on the links' block**, from the two calls on one parameter
file. -/
theorem sizesAt_planned {policy KL : ByteArray} {layout : Option ByteArray} {P : Params}
    {p : Planned} (hP : sizesAt policy = .ok P) (hp : planned policy KL layout = .ok p) :
    P.T = p.X.T ∧ P.V = p.X.P.h.V ∧ P.T < 2 ^ 32 ∧ P.V ≤ 2 ^ 32 := by
  have hX := planned_publicOf hp
  obtain ⟨hT, hlt, hV⟩ := publicOf_window hX
  have hs := publicOf_scan hX
  unfold sizesAt at hP
  obtain ⟨S, h0, hP⟩ := exc_bind hP
  have e0 : S = p.X.P := Except.ok.inj (h0.symm.trans hs)
  subst e0
  split at hP
  · cases hP
    have hpow : (2 : Nat) ^ p.X.P.h.lt ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hlt
    refine ⟨hT.symm, rfl, ?_, ?_⟩
    · show 2 ^ p.X.P.h.lt < 2 ^ 32
      exact Nat.lt_of_le_of_lt hpow (by decide)
    · show p.X.P.h.V ≤ 2 ^ 32
      exact Nat.le_trans hV (by decide)
  · cases hP

end OnBytes.Flat
