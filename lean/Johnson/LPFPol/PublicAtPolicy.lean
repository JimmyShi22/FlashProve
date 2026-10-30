-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/PublicAtPolicy.lean: if the public part of a stage is made at one parameter file, it
is made at every parameter file whose strict scan differs from the first one's only in the numbers
of the lines C, theta and cap, provided that the new numbers pass the tests that read them.

Why. OnBytes/Tie/PlanAtPolicy.lean compares the public parts at two such files, and takes both
returns as hypotheses (`publicOf_withPol`). This file pays the other half: the return at the second
file follows from the return at the first.

Main names.
* `publicOfO_returns_withPol`: THE LAW, of `publicOfO secondHashFunction`
  (Johnson/Desc/Ok/PlanWritten/PublicAt.lean). `publicOf_returns_withPol`: the same of `publicOf`
  (OnBytes/Model/VerifyPublic.lean); the two texts are one at `secondHashFunction` (`publicOfO_older`,
  Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean).
* `polLayout_returns`, `policy_returns`, `h9_returns`, `layout_returns`: the law's steps, of
  `polLayout`, `Head.policy`, `Head.h9` and `Head.layout`.
* `callSizes_withPol`: `Head.callSizes` does not read the three numbers.
* `publicOf_lt`: the line lt in `X.hS` is that in `X.P.h`. `lt_of_admitted`: `Head.admitted` bounds
  lt by 16.

Premises of the law. h: `publicOfO secondHashFunction` returns X at pol, KL, layout. hs: the strict scan of pol'
is `X.P.withPol C theta cap`. h1: theta ≤ C. h2: cap ≤ T, the number of positions. h3: cap < 2^16.
h4: C < 2^32. hl: pol' has fewer than 2^32 bytes. Then `publicOfO secondHashFunction` returns
`X.withPol C theta cap` at pol', KL, layout.

Where the premises are used. h1, h2, h3: the fourth line of `Head.policy`, which is these three
tests. h1, h3, h4 and T ≤ 2^16: the three lines of `Head.h9` that read the three numbers
(no-wrap-H-E2, -E3, -E4; their bound is 2^60). T ≤ 2^16 is no premise: `Head.layout` tests lt ≤ 16
at the first file (`Head.admitted`). hl: `textTH` refuses a text of 2^32 bytes or more.

Limits.
* The return at the first file is a premise. Nothing here shows that `publicOf` returns at any file.
* hs is a premise. Nothing here shows it of any two files. No byte of a file is read here.
* The law speaks of the public part alone: not of the chains, of the links, of a plan, or of any
  test on a key file or a proof file.
* The premises h1 to h4 are sufficient. They are not shown to be necessary.
* Nothing on soundness, on hiding or on a security level.

Hash functions. `publicOf` calls the format's second hash function (`secondHashFunction`, `secondHashFunctionTree`,
OnBytes/Hash/SecondHashFunction.lean). Of that hash this file uses only that its values have 32 bytes
(Johnson/LPFPol/HashReturns.lean).

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.HashReturns
import OnBytes.Tie.PlanAtPolicy
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open OnBytes.Tie (layerShape_withPol)

/-- One step that is the same term, up to unfolding, in the hypothesis k and in the goal: its value
is carried into the goal. -/
local macro "step " k:ident : tactic =>
  `(tactic| (obtain ⟨a, ha, $k:ident⟩ := exc_bind $k
             refine (bind_ok ha).trans ?_
             clear ha
             try dsimp only at $k:ident
             try dsimp only))

/-! ### the tests -/

/-- `needed` at true returns. -/
theorem needed_yes {b : Bool} {n : String} (h : b = true) : Head.needed b n = .ok () := by
  subst h
  rfl

/-- What `needed` lets pass is true. -/
theorem needed_inv {b : Bool} {n : String} {u : Unit} (h : Head.needed b n = .ok u) :
    b = true := by
  unfold Head.needed at h
  split at h
  · assumption
  · cases h

/-- `Head.admitted` bounds lt by 16. -/
theorem lt_of_admitted {h : Head.Shape} (k : Head.admitted h = true) : h.lt ≤ 16 := by
  by_cases c : h.lt ≤ 16
  · exact c
  · exfalso
    have e : decide (h.lt ≤ 16) = false := decide_eq_false c
    unfold Head.admitted at k
    rw [e] at k
    simp at k

/-! ### the scan and the layers' layout -/

/-- Premises: `polLayout` returns (P, y) at pol; the strict scan of pol' is P with the three numbers
replaced. Then `polLayout` returns at pol': that scan, and y. -/
theorem polLayout_returns {pol pol' : ByteArray} {P : PolScan} {y : Layer.Lay} {C theta cap : Nat}
    (h : polLayout pol = .ok (P, y)) (hs : polScan pol' = .ok (P.withPol C theta cap)) :
    polLayout pol' = .ok (P.withPol C theta cap, y) := by
  unfold polLayout at h ⊢
  obtain ⟨P0, _, h⟩ := exc_bind h
  obtain ⟨_, a1, h⟩ := exc_bind h
  obtain ⟨y0, hy, h⟩ := exc_bind h
  obtain ⟨_, a2, h⟩ := exc_bind h
  obtain ⟨_, a3, h⟩ := exc_bind h
  obtain ⟨_, a4, h⟩ := exc_bind h
  cases h
  refine (bind_ok hs).trans ?_
  refine (bind_ok a1).trans ?_
  refine (bind_ok (a := y) ?_).trans ?_
  · rw [layerShape_withPol]
    exact hy
  refine (bind_ok a2).trans ?_
  refine (bind_ok a3).trans ?_
  refine (bind_ok a4).trans ?_
  rfl

/-! ### the head's layout -/

/-- `Head.callSizes` does not read the three numbers. -/
theorem callSizes_withPol (h : Head.Shape) (C theta cap : Nat) :
    ∀ cs : List CallD, Head.callSizes (h.withPol C theta cap) cs = Head.callSizes h cs
  | [] => rfl
  | c :: cs => by
    unfold Head.callSizes
    rw [callSizes_withPol h C theta cap cs]
    rfl

/-- Premises: `Head.policy` passes at h; theta ≤ C, cap ≤ T, cap < 2^16. Then it passes at h with
the three numbers replaced. -/
theorem policy_returns (h : Head.Shape) {C theta cap : Nat} {u : Unit} (k : Head.policy h = .ok u)
    (h1 : theta ≤ C) (h2 : cap ≤ h.T) (h3 : cap < 2 ^ 16) :
    Head.policy (h.withPol C theta cap) = .ok u := by
  unfold Head.policy at k ⊢
  step k
  step k
  step k
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes ?_)).trans ?_
  · show (!(decide (theta > C) || decide (cap > h.T) || decide (cap ≥ 2 ^ 16))) = true
    have e1 : decide (theta > C) = false := decide_eq_false (by omega)
    have e2 : decide (cap > h.T) = false := decide_eq_false (by omega)
    have e3 : decide (cap ≥ 2 ^ 16) = false := decide_eq_false (by omega)
    rw [e1, e2, e3]
    rfl
  step k
  exact k

/-- The bound of the line no-wrap-H-E2. -/
theorem e2_bound {T C theta : Nat} (hT : T ≤ 2 ^ 16) (hC : C < 2 ^ 32) (ht : theta ≤ C) :
    T * (2 ^ 40 + 2 ^ 8 * C + 2 ^ 40) + theta * T < 2 ^ 60 := by
  have a : T * (2 ^ 40 + 2 ^ 8 * C + 2 ^ 40) ≤ 2 ^ 16 * (2 ^ 40 + 2 ^ 8 * 2 ^ 32 + 2 ^ 40) :=
    Nat.mul_le_mul hT (by omega)
  have b : theta * T ≤ 2 ^ 32 * 2 ^ 16 := Nat.mul_le_mul (by omega) hT
  exact Nat.lt_of_le_of_lt (Nat.add_le_add a b) (by decide)

/-- Premises: `Head.h9` passes at h; theta ≤ C, cap < 2^16, C < 2^32, T ≤ 2^16. Then it passes at h
with the three numbers replaced. -/
theorem h9_returns (h : Head.Shape) (L : Head.HL) (Ty : Nat) {C theta cap : Nat} {u : Unit}
    (k : Head.h9 h L Ty = .ok u) (h1 : theta ≤ C) (h3 : cap < 2 ^ 16) (h4 : C < 2 ^ 32)
    (h5 : h.T ≤ 2 ^ 16) : Head.h9 (h.withPol C theta cap) L Ty = .ok u := by
  unfold Head.h9 at k ⊢
  dsimp only at k ⊢
  step k
  step k
  step k
  step k
  step k
  step k
  step k
  step k
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes ?_)).trans ?_
  · show decide (h.T * (2 ^ 40 + 2 ^ 8 * C + 2 ^ 40) + theta * h.T < 2 ^ 60) = true
    exact decide_eq_true (e2_bound h5 h4 h1)
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes ?_)).trans ?_
  · show decide (h.T * (2 ^ 8 + 2 ^ 16) + cap < 2 ^ 60) = true
    exact decide_eq_true (by omega)
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes ?_)).trans ?_
  · show decide (2 ^ 40 + 2 ^ 40 + C < 2 ^ 60) = true
    exact decide_eq_true (by omega)
  step k
  exact k

/-- Premises: `Head.layout` returns L at h; theta ≤ C, cap ≤ T, cap < 2^16, C < 2^32. Then it
returns L at h with the three numbers replaced. -/
theorem layout_returns (h : Head.Shape) {C theta cap : Nat} (t : Array F) {L : Head.HL}
    (k : Head.layout h t = .ok L) (h1 : theta ≤ C) (h2 : cap ≤ h.T) (h3 : cap < 2 ^ 16)
    (h4 : C < 2 ^ 32) : Head.layout (h.withPol C theta cap) t = .ok L := by
  unfold Head.layout at k ⊢
  -- admitted
  obtain ⟨_, a0, k⟩ := exc_bind k
  have h5 : h.T ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (lt_of_admitted (needed_inv a0))
  refine (bind_ok a0).trans ?_
  -- policy
  obtain ⟨_, a1, k⟩ := exc_bind k
  refine (bind_ok (policy_returns h a1 h1 h2 h3)).trans ?_
  try dsimp only at k
  try dsimp only
  step k -- numbers
  step k -- callsOf
  step k -- the table's size
  -- callSizes
  obtain ⟨_, a6, k⟩ := exc_bind k
  refine (bind_ok ((callSizes_withPol h C theta cap _).trans a6)).trans ?_
  try dsimp only at k
  try dsimp only
  step k -- Forest.shape
  step k -- the forest's depth
  step k -- planeCols
  step k -- the lines iotaH
  step k -- pubOf
  step k -- pubAsk
  step k -- the absent calls
  -- h9
  obtain ⟨_, a14, k⟩ := exc_bind k
  refine (bind_ok (h9_returns h _ _ a14 h1 h3 h4 h5)).trans ?_
  exact k

/-! ### the public part -/

/-- The line lt in the head's shape is the scan's. Premise: `publicOf` returns X. -/
theorem publicOf_lt {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) : X.hS.lt = X.P.h.lt := by
  unfold publicOf at h
  obtain ⟨⟨P, y⟩, _, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals
    cases h
    rfl

/-- The steps of `publicOf` behind the branch on attention. -/
local macro "rest4 " k:ident : tactic =>
  `(tactic| (step $k; step $k; step $k; step $k; step $k; step $k; step $k; cases $k:ident; rfl))

/-- The steps of `publicOf` behind the branch on the sigmoid's table. -/
local macro "rest3 " k:ident y:ident hl:ident h1:ident h2:ident h3:ident h4:ident : tactic =>
  `(tactic| (
    step $k
    obtain ⟨x, hx, $k:ident⟩ := exc_bind $k
    obtain ⟨x', hx'⟩ := hPar_returns hx $hl
    refine (bind_ok hx').trans ?_
    clear hx hx'
    try dsimp only at $k:ident
    try dsimp only
    step $k; step $k; step $k; step $k; step $k
    obtain ⟨HLy, hL, $k:ident⟩ := exc_bind $k
    refine (bind_ok (layout_returns _ _ hL $h1 $h2 $h3 $h4)).trans ?_
    clear hL
    try dsimp only at $k:ident
    try dsimp only
    by_cases c4 : ($y).h.p4 = true
    · rw [if_pos c4] at $k:ident ⊢
      step $k
      rest4 $k
    · rw [if_neg c4] at $k:ident ⊢
      rest4 $k))

/-- **The public part returns at the second file.** The law of this file's head, of `publicOf`. -/
theorem publicOf_returns_withPol {pol pol' KL : ByteArray} {layout : Option ByteArray} {X : Public}
    {C theta cap : Nat} (h : publicOf pol KL layout = .ok X)
    (hs : polScan pol' = .ok (X.P.withPol C theta cap))
    (h1 : theta ≤ C) (h2 : cap ≤ X.hS.T) (h3 : cap < 2 ^ 16) (h4 : C < 2 ^ 32)
    (hl : pol'.size < 2 ^ 32) : publicOf pol' KL layout = .ok (X.withPol C theta cap) := by
  have hP := publicOf_scan h
  have hlt := publicOf_lt h
  unfold publicOf at h ⊢
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  have eP : X.P = P := Except.ok.inj (hP.symm.trans (polLayout_scan h0))
  rw [eP] at hs hlt
  have h2' : cap ≤ (headShape P y).T := by
    have e : X.hS.T = (headShape P y).T := congrArg (fun n => 2 ^ n) hlt
    rw [← e]
    exact h2
  clear h2 hlt hP eP
  refine (bind_ok (polLayout_returns h0 hs)).trans ?_
  clear h0 hs
  dsimp only at h ⊢
  step h
  step h
  step h
  by_cases c3 : y.h.p3 = true
  · rw [if_pos c3] at h ⊢
    step h
    rest3 h y hl h1 h2' h3 h4
  · rw [if_neg c3] at h ⊢
    step h
    rest3 h y hl h1 h2' h3 h4

/-- **THE LAW.** Premises: h, `publicOfO secondHashFunction` returns X at pol, KL, layout; hs, the strict scan
of pol' is `X.P.withPol C theta cap`; h1 to h4, the new numbers pass the tests that read them; hl,
pol' has fewer than 2^32 bytes. Then `publicOfO secondHashFunction` returns `X.withPol C theta cap` at pol', KL,
layout. -/
theorem publicOfO_returns_withPol {pol pol' KL : ByteArray} {layout : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} {C theta cap : Nat}
    (h : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction pol KL layout = .ok X)
    (hs : OnBytes.Model.polScan pol' = .ok (X.P.withPol C theta cap))
    (h1 : theta ≤ C) (h2 : cap ≤ X.hS.T) (h3 : cap < 2 ^ 16) (h4 : C < 2 ^ 32)
    (hl : pol'.size < 2 ^ 32) :
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction pol' KL layout =
      .ok (X.withPol C theta cap) := by
  rw [VerifiableInference.PlanWritten.publicOfO_older] at h ⊢
  exact publicOf_returns_withPol h hs h1 h2 h3 h4 hl

end LPFPol

#print axioms LPFPol.publicOf_returns_withPol
#print axioms LPFPol.publicOfO_returns_withPol
