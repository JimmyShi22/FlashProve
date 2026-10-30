-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeepsOwed.lean: THE OUTPUT HEAD's DECISION LEAVES THE LEDGER's LIST OF OWED
CLAIMS AS IT IS: it fills slots. Statements and proofs.
A NEAR TWIN, ON PURPOSE: Law/KeepsTrees.lean's text with "the list of arrays" turned into "the list
of owed claims", line by line (as that file goes by the pattern of Law/KeepsHear.lean).
  hide_owed, hideRun_owed   the program's own two steps that fill slots.
  KeepsO x          wherever the hearing x returns, its ledger owes what the ledger in front owes.
  keepsO_*          closed under bind; each part of the hearings; keepsO_hear: the head's whole.
  blockAt_owed, blockOf_owed   so of the sub-protocol's decision, at the verifier's state.
WHAT IT IS NOT. The decision alone: nothing on the four runs of claims. Nothing on soundness.
USER. Law/SilentAnswers.lean: the lookup's debts are unpaid behind the head's accept.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.Kinds.Law.SeatedBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

theorem hide_owed {F G : Fork} {j : Nat} {y k : E} (h : F.hide j y k = some G) :
    G.owed = F.owed := by
  unfold Fork.hide at h
  split at h
  · rw [← Option.some.inj h]
  · cases h

theorem hideSteps_owed (k : E) : ∀ (l : List E) (j : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep k) (j, F) = some x → x.2.owed = F.owed
  | [], j, F, x, h => by
    obtain rfl : (j, F) = x := Option.some.inj h
    rfl
  | y :: l, j, F, x, h => by
    rw [List.foldlM_cons] at h
    cases h1 : Fork.hideStep k (j, F) y with
    | none =>
      rw [h1] at h
      exact absurd h (by simp)
    | some z =>
      rw [h1] at h
      have hz : z.2.owed = F.owed := by
        unfold Fork.hideStep at h1
        obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact hide_owed hH
      obtain ⟨j', F'⟩ := z
      exact (hideSteps_owed k l j' F' x h).trans hz

theorem hideRun_owed {F G : Fork} {first : Nat} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : G.owed = F.owed := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideSteps_owed k _ _ _ _ hx
  · simp at h

/-- Wherever the hearing returns, its ledger has the owed claims of the ledger in front. -/
def KeepsO {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, x F rs = some (a, G, left) → G.owed = F.owed

theorem keepsO_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : KeepsO x)
    (hf : ∀ a, KeepsO (f a)) : KeepsO (x >>= f) := by
  intro F rs b G left h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  exact (hf a _ _ _ _ _ h2).trans (hx _ _ _ _ _ h1)

theorem keepsO_pure {α : Type} (a : α) : KeepsO (pure a : Hear α) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := pure_some h
  rfl

theorem keepsO_need {α : Type} (x : Option α) : KeepsO (Hear.need x) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := need_some h
  rfl

theorem keepsO_round (n k : Nat) : KeepsO (Hear.round n k) := by
  intro F rs b G left h
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some v =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]

theorem keepsO_hide (v : List E) : KeepsO (hide v) := by
  intro F rs b G left h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray
      OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    have e := hideRun_owed hr
    exact e

theorem keepsO_drawPoint (n : Nat) : KeepsO (drawPoint n) :=
  keepsO_bind (keepsO_round 0 n) fun _ => keepsO_pure _

theorem keepsO_sendThenBatch (n rows : Nat) : KeepsO (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine keepsO_bind (keepsO_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact keepsO_bind (keepsO_hide v) fun _ => keepsO_bind (keepsO_need _) fun _ => keepsO_pure _

/-- The part's hearing of a sumcheck. -/
theorem keepsO_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    KeepsO (heardBy lead C z ends) := by
  intro F0 t b F1 left h
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hFx : F0 = Fx := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact h1.2.1
  subst hFx
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨_, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  have L1 : Fa.owed = F0.owed := keepsO_hide ld _ _ _ _ _ h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have L2 : G.owed = Fa.owed := by
    have e := hideRun_owed hrun2
    exact e
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 : Fr.owed = G.owed := hideRun_owed e6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact (L3.trans L2).trans L1

theorem keepsO_sumcheck (z : Point) (ends : Nat) : KeepsO (sumcheck z ends) := by
  unfold sumcheck
  refine keepsO_bind (keepsO_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact keepsO_pure _

theorem keepsO_level (z : Point) (start : Form) : KeepsO (level z start) := by
  unfold level
  refine keepsO_bind (keepsO_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine keepsO_bind (keepsO_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact keepsO_bind (keepsO_need _) fun _ => keepsO_pure _

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

theorem keepsO_normRest (pV : Point) : KeepsO (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine keepsO_bind (keepsO_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine keepsO_bind ?_ fun rhoI => ?_
  · exact keepsO_pure _
  refine keepsO_bind (keepsO_level _ _) fun sq => ?_
  refine keepsO_bind (keepsO_sendThenBatch _ _) fun y => ?_
  obtain ⟨P, om⟩ := y
  exact keepsO_bind (keepsO_sumcheck _ _) fun _ => keepsO_pure _

theorem keepsO_norm : KeepsO Norm.hear :=
  keepsO_bind (keepsO_drawPoint _) fun pV => keepsO_normRest pV

theorem keepsO_final : KeepsO FinalNorm.hear :=
  keepsO_bind (keepsO_sumcheck _ _) fun _ => keepsO_pure _

/-- **The head's whole hearing.** -/
theorem keepsO_hear : KeepsO hear :=
  keepsO_bind keepsO_norm fun _ => keepsO_bind keepsO_final fun _ =>
    keepsO_bind (keepsO_sumcheck _ _) fun _ => keepsO_pure _

end Classes

/-- **The decision of K6's block at S leaves the ledger's list of owed claims.** -/
theorem blockAt_owed (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ((seatAt h iU3).ledger s').owed = ((seatAt h iU3).ledger s).owed := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, hh, e1, e2, hs⟩ := decideBy_spec hd'
  rw [hs, seatAt_fit h iU3 s F H w s1 s2 e1 e2]
  exact keepsO_hear _ _ _ _ _ hh

/-- The same for blockOf. -/
theorem blockOf_owed (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide s rs gs = .ok s') :
    (s'.fork?.getD {}).owed = (s.fork?.getD {}).owed := by
  unfold blockOf at hb
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact blockAt_owed _ _ _ _ s s' rs gs hd

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockOf_owed
