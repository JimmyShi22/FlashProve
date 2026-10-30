-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeepsHear.lean: THE HEARINGS KEEP THE LEDGER. `Keeps x`: wherever the hearing x
returns, its ledger is LATER than the ledger in front (OnBytes/Tie/Pv/Psc/PscLater.lean: `Later`: what
lies under a slot that is filled is kept); closed under bind; shown of each part of HeadParts.lean's
hearings (from hideRun_keeps, which asks nothing of the arrays' sizes) and so of Norm.hear,
FinalNorm.hear and the head's `hear`.
ALSO `hear_last`: THE HEAD's OWN SUMCHECK IS THE LAST THING THAT `hear` HEARS: the ledger behind it IS
the ledger that `hear` returns.
CUT OUT OF Law/Keeps.lean, not a line of a proof turned, so that a file on the hearings alone
need not import the kind: THIS FILE IMPORTS NO Block.lean, State.lean OR Tape.lean. What speaks of the
block's decision stays in Law/Keeps.lean, which imports this file.
Nothing on soundness.
-/
import Mathlib
import OnBytes.Tie.Pv.Psc.PscLater
import Johnson.Desc.Kinds.Head
import Johnson.Desc.Kinds.Law.Sum2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Later took took_later hideRun_keeps)

/-- Raising the next slot leads to a later state. -/
theorem later_next (F : Fork) (n : Nat) (h : F.next ≤ n) : Later F { F with next := n } :=
  ⟨h, rfl, id, fun _ hj => ⟨hj, rfl, rfl⟩⟩

/-- Wherever the hearing returns, its ledger is later. -/
def Keeps {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, x F rs = some (a, G, left) → Later F G

theorem keeps_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : Keeps x)
    (hf : ∀ a, Keeps (f a)) : Keeps (x >>= f) := by
  intro F rs b G left h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  exact (hx _ _ _ _ _ h1).trans (hf a _ _ _ _ _ h2)

theorem keeps_pure {α : Type} (a : α) : Keeps (pure a : Hear α) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := pure_some h
  exact Later.refl _

theorem keeps_need {α : Type} (x : Option α) : Keeps (Hear.need x) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := need_some h
  exact Later.refl _

theorem keeps_round (n k : Nat) : Keeps (Hear.round n k) := by
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
      rw [← h.2.1]; exact Later.refl _

theorem keeps_hide (v : List E) : Keeps (hide v) := by
  intro F rs b G left h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact (later_next F _ (Nat.le_add_right _ _)).trans (hideRun_keeps hr)

theorem keeps_drawPoint (n : Nat) : Keeps (drawPoint n) :=
  keeps_bind (keeps_round 0 n) fun _ => keeps_pure _

theorem keeps_sendThenBatch (n rows : Nat) : Keeps (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine keeps_bind (keeps_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact keeps_bind (keeps_hide v) fun _ => keeps_bind (keeps_need _) fun _ => keeps_pure _

/-- The part's hearing of a sumcheck. -/
theorem keeps_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    Keeps (heardBy lead C z ends) := by
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
  have L1 : Later F0 Fa := keeps_hide ld _ _ _ _ _ h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have L2 : Later Fa G := (later_next Fa _ (by omega)).trans (hideRun_keeps hrun2)
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 : Later G Fr := hideRun_keeps e6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact (L1.trans L2).trans L3

theorem keeps_sumcheck (z : Point) (ends : Nat) : Keeps (sumcheck z ends) := by
  unfold sumcheck
  refine keeps_bind (keeps_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact keeps_pure _

theorem keeps_level (z : Point) (start : Form) : Keeps (level z start) := by
  unfold level
  refine keeps_bind (keeps_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine keeps_bind (keeps_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact keeps_bind (keeps_need _) fun _ => keeps_pure _

/-! ## The place's three hearings -/

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

theorem keeps_normRest (pV : Point) : Keeps (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine keeps_bind (keeps_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine keeps_bind ?_ fun rhoI => ?_
  · exact keeps_pure _
  refine keeps_bind (keeps_level _ _) fun sq => ?_
  refine keeps_bind (keeps_sendThenBatch _ _) fun y => ?_
  obtain ⟨P, om⟩ := y
  exact keeps_bind (keeps_sumcheck _ _) fun _ => keeps_pure _

theorem keeps_norm : Keeps Norm.hear :=
  keeps_bind (keeps_drawPoint _) fun pV => keeps_normRest pV

theorem keeps_final : Keeps FinalNorm.hear :=
  keeps_bind (keeps_sumcheck _ _) fun _ => keeps_pure _

/-- **The head's whole hearing.** -/
theorem keeps_hear : Keeps hear :=
  keeps_bind keeps_norm fun _ => keeps_bind keeps_final fun _ =>
    keeps_bind (keeps_sumcheck _ _) fun _ => keeps_pure _

/-- **The head's own sumcheck is the last thing that is heard**: where `hear` returns, there are the
ledger and the rounds behind the normalization's two hearings, and from these the sumcheck returns
what `hear` returns: the same ledger, the same rounds left. -/
theorem hear_last {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll}
    (h : hear F rs = some (H, G, left)) :
    ∃ (F0 : Fork) (t : List Fmt.RoundView), Later F F0 ∧
      sumcheck (FinalNorm.zt ++ halves Norm.lPd) 2 F0 t = some (H.2.2.logits, G, left) := by
  unfold hear at h
  obtain ⟨n, F1, l1, h1, k1⟩ := bind_some h
  obtain ⟨f, F2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨lg, F3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  exact ⟨F2, l2, (keeps_norm _ _ _ _ _ h1).trans (keeps_final _ _ _ _ _ h2), h3⟩

end Classes

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.keeps_hear
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_last
