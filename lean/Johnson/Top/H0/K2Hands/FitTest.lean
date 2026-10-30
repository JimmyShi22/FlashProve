-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FitTest.lean: `Johnson.Top.H.Fit` (Johnson/Top/H/SwitchMapsFit.lean) from a
test with code on public numbers.
`Fit cs l s W mem row pl` has fifteen clauses. Twelve speak of the codes, the list l of the messages
that are sent, the stage s and the frame W alone; three run over the kept slots through the readings
mem, row and pl.
`fitHead`: the eight clauses at the first message of l. `fitKeptAt`: what the three clauses ask at a
place of W.kept, at every row below the place's number of rows. `fitB`: THE TEST: all of it.
`fit_of_test`: the test's yes gives `Fit` at every three readings that meet `SlotsAll`
(Numbering.lean): of that structure the fields member and rowIn alone are spent.
`fitAt`, `fit_made`: at a place's numbers r and the caller as it is made (CallerMade.lean).
`callerAt_of_tests`: so `CallerAt` hangs on three tests: `SwRow.keptAt`, `codesAt`, `fitAt`.
Limits. An implication: the test may say no where `Fit` holds (it asks a kept member's rows to be at
most its new message's main rows, at every row). That the tests say yes at any r and frame is
not shown here. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.CallerMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First.K2Caller

section
variable (cs : Codes) (l : List (OracleShape × ℕ)) (s : Sg) (W : SwitchFrame)

/-- The clauses at the first message that is sent. -/
def fitHead (x : OracleShape × ℕ) : Bool :=
  decide (W.rowBits = ceilLog2 x.1.mainRows) &&
  decide (W.mainCut.firstRow + 2 ^ W.mainCut.bits ≤ 2 ^ W.rowBits) &&
  decide (W.mainCut.firstRow + 2 ^ W.mainCut.bits ≤ x.1.mainRows) &&
  decide (s.C.l ≤ (pMain cs x.1).ell * 2 ^ W.mainCut.bits) &&
  decide (W.places.rowBits = ceilLog2 (x.1.rows W.restPart)) &&
  decide (W.places.cut.firstRow + 2 ^ W.places.cut.bits ≤ 2 ^ W.places.rowBits) &&
  decide (W.places.cut.firstRow + 2 ^ W.places.cut.bits ≤ x.1.rows W.restPart) &&
  decide (W.parts.length ≤ ellOf cs x.1 W.restPart * 2 ^ W.places.cut.bits - W.places.pad.length)

/-- What is asked at the place a of the frame's kept members: k its entry, x its new message. -/
def fitKeptAt (a : ℕ) (k : KeptPlace) (x : OracleShape × ℕ) : Bool :=
  decide (k.oldPadAt + k.pad.length ≤ W.parts.length) &&
  decide (k.rowBits = ceilLog2 x.1.mainRows) && decide (k.rows ≤ x.1.mainRows) &&
  decide (s.C.l ≤ (pMain cs x.1).ell) &&
  (List.range k.rows).all fun b =>
    decide (W.parts.keptTailAt.getD (keptNo W a b) 0 + s.C.r ≤ W.parts.length)

/-- **The test.** -/
def fitB : Bool :=
  (match l[0]? with
    | some x => fitHead cs s W x
    | none => false) &&
  decide (W.parts.maskAt.getD 0 0 + s.Z.l ≤ W.parts.length) &&
  decide (W.parts.maskAt.getD 1 0 + s.Z.l ≤ W.parts.length) &&
  decide (W.parts.mainTailAt + s.C.r ≤ W.parts.length) &&
  decide (W.parts.maskTailAt.getD 0 0 + s.Z.r ≤ W.parts.length) &&
  decide (W.parts.maskTailAt.getD 1 0 + s.Z.r ≤ W.parts.length) &&
  (List.range W.kept.length).all fun a =>
    match W.kept[a]?, l[1 + a]? with
    | some k, some x => fitKeptAt cs s W a k x
    | _, _ => false

variable {cs l s W}

/-- What the test says at a slot. -/
theorem fitB_kept {K : Type} {mem row : K → ℕ} {pl : K → KeptPlace}
    (A : SlotsAll K W mem row pl) (h : fitB cs l s W = true) (k : K) :
    ∃ hl : 1 + mem k < l.length,
      fitKeptAt cs s W (mem k) (pl k) (l.get ⟨1 + mem k, hl⟩) = true := by
  unfold fitB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hm : mem k < W.kept.length := (List.getElem?_eq_some_iff.1 (A.member k)).1
  have t := h.2 (mem k) hm
  rw [A.member k] at t
  cases hx : l[1 + mem k]? with
  | none =>
    rw [hx] at t
    exact absurd t (by simp)
  | some x =>
    rw [hx] at t
    obtain ⟨hl, e⟩ := List.getElem?_eq_some_iff.1 hx
    exact ⟨hl, by rw [show l.get ⟨1 + mem k, hl⟩ = x from e]; exact t⟩

/-- **The test's yes gives `Fit`.** -/
theorem fit_of_test {K : Type} {mem row : K → ℕ} {pl : K → KeptPlace}
    (A : SlotsAll K W mem row pl) (h : fitB cs l s W = true) : Fit cs l s W mem row pl := by
  have hk := fitB_kept A h
  unfold fitB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, m0⟩, m1⟩, mt⟩, z0⟩, z1⟩, -⟩ := h
  cases hx : l[0]? with
  | none =>
    rw [hx] at h0
    exact absurd h0 (by simp)
  | some x =>
    rw [hx] at h0
    obtain ⟨g, e⟩ := List.getElem?_eq_some_iff.1 hx
    have e' : l.get ⟨0, g⟩ = x := e
    unfold fitHead at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
    obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := h0
    have kk : ∀ k, ∃ hl : 1 + mem k < l.length,
        ((pl k).oldPadAt + (pl k).pad.length ≤ W.parts.length) ∧
        ((pl k).rowBits = ceilLog2 (l.get ⟨1 + mem k, hl⟩).1.mainRows) ∧
        ((pl k).rows ≤ (l.get ⟨1 + mem k, hl⟩).1.mainRows) ∧
        (s.C.l ≤ (pMain cs (l.get ⟨1 + mem k, hl⟩).1).ell) ∧
        ∀ b, b < (pl k).rows →
          W.parts.keptTailAt.getD (keptNo W (mem k) b) 0 + s.C.r ≤ W.parts.length := fun k => by
      obtain ⟨hl, t⟩ := hk k
      unfold fitKeptAt at t
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at t
      exact ⟨hl, t.1.1.1.1, t.1.1.1.2, t.1.1.2, t.1.2, t.2⟩
    exact
      { g := g
        mainBits := by rw [e']; exact a1
        mainFits := a2
        mainRows := by rw [e']; exact a3
        mainLen := by rw [e']; exact a4
        restBits := by rw [e']; exact a5
        restFits := a6
        restRows := by rw [e']; exact a7
        room := by rw [e']; exact a8
        mask := fun j hj => by
          interval_cases j
          · exact m0
          · exact m1
        mainTail := mt
        keptTail := fun k => by
          obtain ⟨_, _, _, _, _, t⟩ := kk k
          exact t (row k) (A.rowIn k)
        maskTail := fun j hj => by
          interval_cases j
          · exact z0
          · exact z1
        oldPad := fun k => by
          obtain ⟨_, t, _⟩ := kk k
          exact t
        keptMsg := fun k => by
          obtain ⟨hl, _, t2, t3, t4, _⟩ := kk k
          exact ⟨hl, t2, Nat.lt_of_lt_of_le (A.rowIn k) t3, t4⟩ }

end

/-- **The test at a place's numbers.** -/
def fitAt (r : SwRow) (W : SwitchFrame) : Bool := fitB r.cs r.l (stageOf r.g 0) W

variable {r : SwRow} (H : r.OK) {W₀ : SwitchFrame} (h : r.keptAt W₀ = true)
  (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)

/-- `Fit` at the caller as it is made. -/
theorem fit_made (hf : fitAt r W₀ = true) :
    Fit r.cs r.l (stageOf r.g t₀) W₀ (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ)
      (plAt H h t₀ oM oZ) :=
  fit_of_test (s := stageOf r.g t₀) (slots_made H h t₀ oM oZ) hf

/-- **`CallerAt` on three tests.** -/
theorem callerAt_of_tests (hc : codesAt r W₀ = true) (hf : fitAt r W₀ = true) :
    CallerAt ((rowsAt r H t₀ oM oZ).keep r.kp) r.cs r.l
      (Johnson.Top.H.iJ (stageOf r.g t₀) W₀ (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ)
        (plAt H h t₀ oM oZ) r.cs r.l (fit_made H h t₀ oM oZ hf).nameJ)
      (Johnson.Top.H.iQ (stageOf r.g t₀) W₀ (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ) r.cs r.l
        (fit_made H h t₀ oM oZ hf).nameQ)
      (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ) (plAt H h t₀ oM oZ) W₀ :=
  callerAt_made H h t₀ oM oZ hc (fit_made H h t₀ oM oZ hf)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.fit_of_test
#print axioms VerifiableInference.Desc.First.K2Hands.fit_made
#print axioms VerifiableInference.Desc.First.K2Hands.callerAt_of_tests
