-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ClaimReturns.lean: the kind "lookup" (K3): when the
routine that makes the head's claim on the weights returns (the library's `weightsClaim`,
Johnson/Desc/First/Look/LookQuiet.lean): where the public test `layoutOk`
(Honest/K3/Law/Thread/ClaimSizes.lean) accepts and the checked token of every covered position is an
entry of the vocabulary. This is the converse of the library's `weightsClaim_is`
(Johnson/Top/H0/K11Caller/HeadClaim.lean). Also: the two calls of the step without a round behind
the lookup on the head's digits that can refuse on what was heard, as one test with code on the
state. One definition and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the step without a round behind the lookup on the head's
digits is `quietHead` (Johnson/Desc/First/Look/K3Whole.lean).

What is shown.
  `forIn_list_ok`, `forIn_range_ok`: a loop in Except returns if every step returns and goes on.
  `layoutOk_parts`: where the public test accepts: the call, its segment, the last unit's sort.
  `weightsClaim_returns`: the routine returns, under the two conditions above.
  `headVals`: the test on values, with code: the two calls of `quietHead` return, at the structure
    that `quietHead` itself hands them, field for field.
  `headVals_gives`: where that test accepts: the two returns, in the form of the hypothesis `hRest`
    of `headReturns_of_thr` (Honest/K3/Law/Thread/HeadReturnsOf.lean).

Hypotheses that remain.
  `hL`: (in `weightsClaim_returns`; named `h` in `layoutOk_parts`) the public test `layoutOk`
    accepts.
  `hw`: (in `weightsClaim_returns`) a fact on what the head heard: the checked token of every
    covered position is below the size of the vocabulary.
  `h`, `ha`, `hx`, `ht`: (in `headVals_gives`) `headVals` accepts at the state; the state stands in
    the head's link, whose own part holds what was heard and the tables.
  In `forIn_range_ok` (`hf`) and in `forIn_list_ok` (without a name, in front of an arrow): every
    step of the loop returns and goes on.

Users. `weightsClaim_returns` is called in Honest/K3/Law/Thread/HeadValsOf.lean; `headVals_gives` in
Honest/K3/Law/Thread/CarriesHeadDigits.lean; `headVals` stands in statements of both and of
Honest/K3/Law/Thread/HeadDigitsAtLink.lean.

Limits. `weightsClaim_returns` is conditional on the public test and on one fact on what the head
heard. Neither test is evaluated in this file. Both are evaluated in
Honest/K3/Law/Thread/CarriesGuardsHead.lean [not in this library], at states that the test makes up:
they accept at one of three small synthetic
public parts and reject at the two others. No instance of these hypotheses is exhibited in this
file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ClaimSizes
import Johnson.Desc.First.Look.K3Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E)
open OnBytes.Model (WsLay WsClaim WsGrp)
open OnBytes.Model.Head (callNo)
open VerifiableInference.Desc.First.Look (weightsClaim)

local notation "FS" => VerifiableInference.Desc.First.S

/-- A loop over a list in Except returns if every step returns and goes on. -/
theorem forIn_list_ok {β ε : Type} (f : Nat → β → Except ε (ForInStep β)) :
    ∀ (l : List Nat), (∀ x ∈ l, ∀ b, ∃ b', f x b = .ok (.yield b')) → ∀ b : β,
      ∃ b', forIn l b f = .ok b'
  | [], _, b => ⟨b, rfl⟩
  | x :: l, hf, b => by
    obtain ⟨b1, h1⟩ := hf x (List.mem_cons_self) b
    obtain ⟨b2, h2⟩ := forIn_list_ok f l (fun y hy => hf y (List.mem_cons_of_mem _ hy)) b1
    refine ⟨b2, ?_⟩
    rw [List.forIn_cons, h1]
    exact h2

/-- The same over the numbers below n. -/
theorem forIn_range_ok {β ε : Type} (n : Nat) (f : Nat → β → Except ε (ForInStep β))
    (hf : ∀ x, x < n → ∀ b, ∃ b', f x b = .ok (.yield b')) (b : β) :
    ∃ b', forIn [:n] b f = .ok b' := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have e : List.range' ([:n] : Std.Legacy.Range).start ([:n] : Std.Legacy.Range).size
      ([:n] : Std.Legacy.Range).step = List.range' 0 n := by
    simp [Std.Legacy.Range.size]
  rw [e]
  refine forIn_list_ok f _ (fun x hx => hf x ?_) b
  have := (List.mem_range'_1.1 hx).2
  omega

/-- Where the public test accepts: the call, its segment, the last unit's sort. -/
theorem layoutOk_parts {L : OnBytes.Model.Head.HL} {lay : WsLay} (h : layoutOk L lay = true) :
    (∃ q g, callNo L "HD0" = some q ∧ (L.calls.getD q default).seg? "HD0" = some g) ∧
      lay.U.back?.map (·.X) = some 13 := by
  unfold layoutOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, _⟩ := h
  refine ⟨?_, by simpa using h2⟩
  cases hq : callNo L "HD0" with
  | none =>
    rw [hq] at h1
    exact nomatch h1
  | some q =>
    rw [hq] at h1
    have h3 : ((L.calls.getD q default).seg? "HD0").isSome = true := h1
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h3
    exact ⟨q, g, rfl, hg⟩

/-- **The routine returns** where the public test accepts and the checked token of every covered
position is an entry of the vocabulary. Conditional on these two. -/
theorem weightsClaim_returns {R : OnBytes.Model.Head.Run} {lay : WsLay}
    (hL : layoutOk R.L lay = true)
    (hw : ∀ t, t < R.h.T → R.cov.hOn.getD t false = true → R.x.win.getD t 0 < R.h.V) :
    ∃ cl, weightsClaim R lay = .ok cl := by
  obtain ⟨⟨q, g, hq, hs⟩, h13⟩ := layoutOk_parts hL
  obtain ⟨gx, gk, hg, hx, hkk⟩ := layoutOk_groups hL
  unfold weightsClaim
  dsimp only
  rw [hq]
  dsimp only
  rw [pure_bind, hs]
  dsimp only
  rw [pure_bind]
  split
  · rename_i hc
    rw [h13] at hc
    exact absurd hc (by decide)
  · rw [pure_bind, hg]
    have e1 : (gx.name == "x") = true := by rw [hx]; rfl
    have e2 : (gk.name == "x") = false := by rw [hkk]; decide
    have e3 : (gk.name == "kk") = true := by rw [hkk]; rfl
    simp only [List.forIn_cons, List.forIn_nil, e1, e2, e3, if_true, Bool.false_eq_true, if_false]
    generalize hF : (forIn [:R.h.T] _ _ : Except String (Array E)) = F
    have hok : ∃ AV, F = .ok AV := by
      rw [← hF]
      refine forIn_range_ok R.h.T _ ?_ _
      intro x hx' b
      by_cases hon : R.cov.hOn.getD x false = true
      · rw [if_pos hon]
        have hd : (!decide (R.x.win.getD x 0 < R.h.V)) = false := by
          rw [decide_eq_true (hw x hx' hon)]
          rfl
        rw [if_neg (by rw [hd]; exact Bool.false_ne_true)]
        exact ⟨_, rfl⟩
      · rw [if_neg hon]
        exact ⟨_, rfl⟩
    obtain ⟨AV, rfl⟩ := hok
    exact ⟨_, rfl⟩

/-- **The test on values, with code**: the two calls of `quietHead` that can refuse on what was
heard return, at the structure that `quietHead` itself hands them. -/
def headVals (X : OnBytes.Model.Verify.Public) (s : FS) : Bool :=
  match s.here with
  | .head a =>
    match a.x, a.t, s.covered X.T X.P.h.V with
    | some x, some tt, .ok cov =>
      (weightsClaim
        { h := X.hS, L := X.HLy, b := OnBytes.Model.Verify.borderOf X.y, hp := X.H, cov := cov,
          x := x, t := tt, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 }
        X.layers.wsLay).isOk
    | _, _, _ => false
  | _ => false

/-- Where the test accepts: the two returns. -/
theorem headVals_gives {X : OnBytes.Model.Verify.Public} {s : FS}
    {a : VerifiableInference.Desc.First.HeadOwn} {x : OnBytes.Model.Head.Heard}
    {tt : OnBytes.Model.Head.Tables} (h : headVals X s = true) (ha : s.here = .head a)
    (hx : a.x = some x) (ht : a.t = some tt) :
    ∃ cov claim, s.covered X.T X.P.h.V = .ok cov ∧ weightsClaim
      { h := X.hS, L := X.HLy, b := OnBytes.Model.Verify.borderOf X.y, hp := X.H, cov := cov,
        x := x, t := tt, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 } X.layers.wsLay = .ok claim := by
  unfold headVals at h
  rw [ha] at h
  dsimp only at h
  rw [hx, ht] at h
  cases hc : s.covered X.T X.P.h.V with
  | error e =>
    rw [hc] at h
    exact nomatch h
  | ok cov =>
    rw [hc] at h
    dsimp only at h
    refine ⟨cov, ?_⟩
    cases hwc : weightsClaim
        { h := X.hS, L := X.HLy, b := OnBytes.Model.Verify.borderOf X.y, hp := X.H, cov := cov,
          x := x, t := tt, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 }
        X.layers.wsLay with
    | error e =>
      rw [hwc] at h
      exact nomatch h
    | ok claim => exact ⟨claim, rfl, rfl⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.forIn_list_ok
#print axioms ProofFile.Honest.K3.Law.AtThr.forIn_range_ok
#print axioms ProofFile.Honest.K3.Law.AtThr.layoutOk_parts
#print axioms ProofFile.Honest.K3.Law.AtThr.weightsClaim_returns
#print axioms ProofFile.Honest.K3.Law.AtThr.headVals_gives
