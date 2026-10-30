-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsK6Hear.lean: K6's HEARING.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
THE WALK IS THAT OF Johnson/Desc/Kinds/Law/KeepsTrees.lean ("the hearing leaves the
ledger's arrays"), CARRIED OVER BY PROGRAM to the two numbers (keepsT_… ↦ keepsSl_…).
Limits. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.KeepsTrees
import Johnson.Desc.First.Link.Law.SlotsAre

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (sl sl_core)

theorem hideRun_sl {F G : Fork} {first : Nat} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : sl G = sl F :=
  sl_core (OnBytes.Desc.First.K4.hideRun_core h)

/-- Wherever the hearing returns, its ledger has the two numbers of the ledger in front. -/
def KeepsSl {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, x F rs = some (a, G, left) → sl G = sl F

theorem keepsSl_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : KeepsSl x)
    (hf : ∀ a, KeepsSl (f a)) : KeepsSl (x >>= f) := by
  intro F rs b G left h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  exact (hf a _ _ _ _ _ h2).trans (hx _ _ _ _ _ h1)

theorem keepsSl_pure {α : Type} (a : α) : KeepsSl (pure a : Hear α) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := pure_some h
  rfl

theorem keepsSl_need {α : Type} (x : Option α) : KeepsSl (Hear.need x) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := need_some h
  rfl

theorem keepsSl_round (n k : Nat) : KeepsSl (Hear.round n k) := by
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

theorem keepsSl_hide (v : List E) : KeepsSl (hide v) := by
  intro F rs b G left h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray
      OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    have e := hideRun_sl hr
    exact e

theorem keepsSl_drawPoint (n : Nat) : KeepsSl (drawPoint n) :=
  keepsSl_bind (keepsSl_round 0 n) fun _ => keepsSl_pure _

theorem keepsSl_sendThenBatch (n rows : Nat) : KeepsSl (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine keepsSl_bind (keepsSl_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact keepsSl_bind (keepsSl_hide v) fun _ => keepsSl_bind (keepsSl_need _) fun _ => keepsSl_pure _

/-- The part's hearing of a sumcheck. -/
theorem keepsSl_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    KeepsSl (heardBy lead C z ends) := by
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
  have L1 : sl Fa = sl F0 := keepsSl_hide ld _ _ _ _ _ h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have L2 : sl G = sl Fa := by
    have e := hideRun_sl hrun2
    exact e
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 : sl Fr = sl G := hideRun_sl e6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact (L3.trans L2).trans L1

theorem keepsSl_sumcheck (z : Point) (ends : Nat) : KeepsSl (sumcheck z ends) := by
  unfold sumcheck
  refine keepsSl_bind (keepsSl_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact keepsSl_pure _

theorem keepsSl_level (z : Point) (start : Form) : KeepsSl (level z start) := by
  unfold level
  refine keepsSl_bind (keepsSl_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine keepsSl_bind (keepsSl_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact keepsSl_bind (keepsSl_need _) fun _ => keepsSl_pure _

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

theorem keepsSl_normRest (pV : Point) : KeepsSl (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine keepsSl_bind (keepsSl_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine keepsSl_bind ?_ fun rhoI => ?_
  · exact keepsSl_pure _
  refine keepsSl_bind (keepsSl_level _ _) fun sq => ?_
  refine keepsSl_bind (keepsSl_sendThenBatch _ _) fun y => ?_
  obtain ⟨P, om⟩ := y
  exact keepsSl_bind (keepsSl_sumcheck _ _) fun _ => keepsSl_pure _

theorem keepsSl_norm : KeepsSl Norm.hear :=
  keepsSl_bind (keepsSl_drawPoint _) fun pV => keepsSl_normRest pV

theorem keepsSl_final : KeepsSl FinalNorm.hear :=
  keepsSl_bind (keepsSl_sumcheck _ _) fun _ => keepsSl_pure _

/-- **The head's whole hearing.** -/
theorem keepsSl_hear : KeepsSl hear :=
  keepsSl_bind keepsSl_norm fun _ => keepsSl_bind keepsSl_final fun _ =>
    keepsSl_bind (keepsSl_sumcheck _ _) fun _ => keepsSl_pure _

end Classes

/-- **The decision of K6's block at S leaves the ledger's two numbers.** -/
theorem blockAt_sl (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    sl ((seatAt h iU3).ledger s') = sl ((seatAt h iU3).ledger s) := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, hh, e1, e2, hs⟩ := decideBy_spec hd'
  rw [hs, seatAt_fit h iU3 s F H w s1 s2 e1 e2]
  exact keepsSl_hear _ _ _ _ _ hh

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_sl
