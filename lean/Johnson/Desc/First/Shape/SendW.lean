-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SendW.lean: THE SENDING BEHIND THE LINKS (the kind K1, at the memory) AS A
MEMBER OF THE FIRST CHAIN, ON THE CHAIN's SHAPE: one step, and its two laws at the block's own
decision (K1.sendAtS, Johnson/Desc/K1/AtS.lean). General laws; nothing is evaluated.

  `wStepG`, **`sendW_sq`**: where the sending returns its written record, the member's decision and
    its step on the chain's shape commute.
  **`wG`**: the sending's Bool (sendB, SendCore.lean), then the step. `sendW_inv`: a yes has the
    sending's return in it. **`sendW_carries`**, **`sendW_returns`**.

Limits. The bare block, as in Commit.lean: in the description it is the first half of a member whose
second half is another kind's. The two premises on the rounds stand as in SendCore.lean. No state is
shown at which wG returns. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Commit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState)

/-- K1.sendAtS behind its sending's guards, on the chain's shape. -/
def wStepG (P : K1.Par) (a : ChainSh) : Option ChainSh :=
  match a.atEnd with
  | some e =>
    if e.1 == P.sent then
      some (((a.setCore (sendCore P a.core)).setRowsOwed none).setEnd
        (e.1, idsAt P a.core.st.oracles.length, e.2.2))
    else none
  | none => none

/-- **Where the sending returns, the decision and the step commute.** -/
theorem sendW_sq (P : K1.Par) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (x : Array Nat × DState (Array Nat))
    (hs : K1.decideSend P (K1.owedOf s) (K1.stateOf s (#[] : Array Nat)) rs = .ok x) :
    ((K1.sendAtS (Cl := Unit) P).decide s rs gs).toOption.map chainSh = wStepG P (chainSh s) := by
  obtain ⟨ids, d₁⟩ := x
  obtain ⟨hi, hcore, -, -⟩ := send_core hs
  have hi' : ids = idsAt P s.st.oracles.size := hi
  subst hi'
  have hcore' : Ground.Sh.coreSh (Ground.coreOf d₁) = sendCore P (chainSh s).core := hcore
  have hz : (chainSh s).core.st.oracles.length = s.st.oracles.size := Ground.Sh.orc_size s.st
  unfold wStepG
  rw [hz, ← hcore']
  show _ = (match endSh s.here with
    | some e =>
      if e.1 == P.sent then
        some ((((chainSh s).setCore (Ground.Sh.coreSh (Ground.coreOf d₁))).setRowsOwed none).setEnd
          (e.1, idsAt P s.st.oracles.size, e.2.2))
      else none
    | none => none)
  unfold K1.sendAtS
  simp only []
  cases hh : s.here with
  | mem a =>
    show _ = (if a.msg == P.sent then
      some ((((chainSh s).setCore (Ground.Sh.coreSh (Ground.coreOf d₁))).setRowsOwed none).setEnd
        (a.msg, idsAt P s.st.oracles.size, a.lin.map K13.Honest.laidSh)) else none)
    by_cases g : (a.msg == P.sent) = true
    · simp only [g, if_true]
      show (Except.toOption (((K1.decideSend P (K1.owedOf s) (K1.stateOf s #[]) rs).map fun x =>
        (⟨none, { x.2 with loc := x.1 }⟩ : K1.Owing (DState (Array Nat)))).map fun y =>
          { K1.laid s y.held with here := .mem { a with ids := y.held.loc } })).map chainSh = _
      rw [hs]
      show some (chainSh { K1.laid s d₁ with
        here := .mem { a with ids := idsAt P s.st.oracles.size } }) = _
      have e2 : chainSh { K1.laid s d₁ with
          here := .mem { a with ids := idsAt P s.st.oracles.size } } =
          (chainSh (K1.laid s d₁)).setEnd
            (a.msg, idsAt P s.st.oracles.size, a.lin.map K13.Honest.laidSh) := by
        obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
        subst hh
        rfl
      rw [e2, chainSh_laid]
    · simp only [g, Bool.false_eq_true, if_false]
      rfl
  | between => rfl
  | lay a => rfl
  | att a => rfl
  | head a => rfl
  | fin a => rfl

/-- **K1's sending behind the links on the chain's shape.** -/
def wG (P : K1.Par) (a : ChainSh) : Option ChainSh :=
  if sendB P a.rowsOwed a.core then wStepG P a else none

theorem sendW_inv {P : K1.Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.sendAtS (Cl := Unit) P).decide s rs gs = .ok s') :
    ∃ x, K1.decideSend P (K1.owedOf s) (K1.stateOf s (#[] : Array Nat)) rs = .ok x := by
  simp only [K1.sendAtS] at h
  split at h
  · split at h
    · cases hd : K1.decideSend P (K1.owedOf s) (K1.stateOf s (#[] : Array Nat)) rs with
      | error e => simp [K1.sendOwn, hd, Except.map] at h
      | ok x => exact ⟨x, rfl⟩
    · cases h
  · cases h

/-- **"Carries" at the member.** -/
theorem sendW_carries {P : K1.Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {t : ChainSh}
    (h : (K1.sendAtS (Cl := Unit) P).decide s rs gs = .ok s') (hg : wG P (chainSh s) = some t) :
    t = chainSh s' := by
  obtain ⟨x, hx⟩ := sendW_inv h
  have hq := sendW_sq P s rs gs x hx
  rw [h] at hq
  unfold wG at hg
  split at hg
  · rw [← hq] at hg
    exact (Option.some.inj hg).symm
  · cases hg

/-- **"Returns" at the member.** -/
theorem sendW_returns {P : K1.Par} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {t : ChainSh} (hg : wG P (chainSh s) = some t)
    (hz : ∀ x ∈ K1.seedsOf P r₁, isZeroE x.2 = false)
    (hn : (K1.answersIn r₂).length = P.answers) :
    ∃ s', (K1.sendAtS (Cl := Unit) P).decide s [r₁, r₂] gs = .ok s' ∧ chainSh s' = t := by
  unfold wG at hg
  split at hg
  · rename_i hB
    obtain ⟨x, hs⟩ := send_returns P s.rowsOwed (K1.stateOf s (#[] : Array Nat)) r₁ r₂ hB hz hn
    have hq := sendW_sq P s [r₁, r₂] gs x hs
    rw [hg] at hq
    cases hd : (K1.sendAtS (Cl := Unit) P).decide s [r₁, r₂] gs with
    | error e => rw [hd] at hq; cases hq
    | ok s' =>
      rw [hd] at hq
      exact ⟨s', rfl, Option.some.inj hq⟩
  · cases hg

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.sendW_sq
#print axioms VerifiableInference.Desc.First.Shape.sendW_inv
#print axioms VerifiableInference.Desc.First.Shape.sendW_carries
#print axioms VerifiableInference.Desc.First.Shape.sendW_returns
