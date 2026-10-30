-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeepsTrees.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing on the other blocks of the head's link, nor on this
block's four runs of claims: THE DECISION ALONE. That the ledger in front holds the plan's arrays:
not
here.
OBJECT. Desc/Kinds/Head.lean's hear; Stored/HeadSeatAt.lean's blockAt, blockOf; the seated block
(Stored/HeadAddsAtS.lean: seatedClaims).
USER. Whoever must know that the reads' array in the record's ledger has behind the output head's
block the rows and columns that it had in front (Law/HeadTabRows.lean's premise hK rides over it).
WHAT IT IS. THE OUTPUT HEAD's DECISION LEAVES THE LEDGER's LIST OF ARRAYS AS IT IS: it fills slots.
On the pattern of Law/KeepsHear.lean (whose "later" has no clause on the arrays).
  hide_trees, hideRun_trees   the program's own two steps that fill slots.
  KeepsT x          wherever the hearing x returns, its ledger has the arrays of the ledger in
  front.
  keepsT_*          closed under bind; each part of the hearings; keepsT_hear: the head's whole.
  blockAt_trees, blockOf_trees, seated_trees   so of the block's decision, at S.

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

theorem hide_trees {F G : Fork} {j : Nat} {y k : E} (h : F.hide j y k = some G) :
    G.trees = F.trees := by
  unfold Fork.hide at h
  split at h
  · rw [← Option.some.inj h]
  · cases h

theorem hideSteps_trees (k : E) : ∀ (l : List E) (j : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep k) (j, F) = some x → x.2.trees = F.trees
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
      have hz : z.2.trees = F.trees := by
        unfold Fork.hideStep at h1
        obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact hide_trees hH
      obtain ⟨j', F'⟩ := z
      exact (hideSteps_trees k l j' F' x h).trans hz

theorem hideRun_trees {F G : Fork} {first : Nat} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : G.trees = F.trees := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideSteps_trees k _ _ _ _ hx
  · simp at h

/-- Wherever the hearing returns, its ledger has the arrays of the ledger in front. -/
def KeepsT {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, x F rs = some (a, G, left) → G.trees = F.trees

theorem keepsT_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : KeepsT x)
    (hf : ∀ a, KeepsT (f a)) : KeepsT (x >>= f) := by
  intro F rs b G left h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  exact (hf a _ _ _ _ _ h2).trans (hx _ _ _ _ _ h1)

theorem keepsT_pure {α : Type} (a : α) : KeepsT (pure a : Hear α) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := pure_some h
  rfl

theorem keepsT_need {α : Type} (x : Option α) : KeepsT (Hear.need x) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := need_some h
  rfl

theorem keepsT_round (n k : Nat) : KeepsT (Hear.round n k) := by
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

theorem keepsT_hide (v : List E) : KeepsT (hide v) := by
  intro F rs b G left h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray
      OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    have e := hideRun_trees hr
    exact e

theorem keepsT_drawPoint (n : Nat) : KeepsT (drawPoint n) :=
  keepsT_bind (keepsT_round 0 n) fun _ => keepsT_pure _

theorem keepsT_sendThenBatch (n rows : Nat) : KeepsT (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine keepsT_bind (keepsT_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact keepsT_bind (keepsT_hide v) fun _ => keepsT_bind (keepsT_need _) fun _ => keepsT_pure _

/-- The part's hearing of a sumcheck. -/
theorem keepsT_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    KeepsT (heardBy lead C z ends) := by
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
  have L1 : Fa.trees = F0.trees := keepsT_hide ld _ _ _ _ _ h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have L2 : G.trees = Fa.trees := by
    have e := hideRun_trees hrun2
    exact e
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 : Fr.trees = G.trees := hideRun_trees e6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact (L3.trans L2).trans L1

theorem keepsT_sumcheck (z : Point) (ends : Nat) : KeepsT (sumcheck z ends) := by
  unfold sumcheck
  refine keepsT_bind (keepsT_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact keepsT_pure _

theorem keepsT_level (z : Point) (start : Form) : KeepsT (level z start) := by
  unfold level
  refine keepsT_bind (keepsT_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine keepsT_bind (keepsT_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact keepsT_bind (keepsT_need _) fun _ => keepsT_pure _

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

theorem keepsT_normRest (pV : Point) : KeepsT (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine keepsT_bind (keepsT_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine keepsT_bind ?_ fun rhoI => ?_
  · exact keepsT_pure _
  refine keepsT_bind (keepsT_level _ _) fun sq => ?_
  refine keepsT_bind (keepsT_sendThenBatch _ _) fun y => ?_
  obtain ⟨P, om⟩ := y
  exact keepsT_bind (keepsT_sumcheck _ _) fun _ => keepsT_pure _

theorem keepsT_norm : KeepsT Norm.hear :=
  keepsT_bind (keepsT_drawPoint _) fun pV => keepsT_normRest pV

theorem keepsT_final : KeepsT FinalNorm.hear :=
  keepsT_bind (keepsT_sumcheck _ _) fun _ => keepsT_pure _

/-- **The head's whole hearing.** -/
theorem keepsT_hear : KeepsT hear :=
  keepsT_bind keepsT_norm fun _ => keepsT_bind keepsT_final fun _ =>
    keepsT_bind (keepsT_sumcheck _ _) fun _ => keepsT_pure _

end Classes

/-- **The decision of K6's block at S leaves the ledger's arrays.** -/
theorem blockAt_trees (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ((seatAt h iU3).ledger s').trees = ((seatAt h iU3).ledger s).trees := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, hh, e1, e2, hs⟩ := decideBy_spec hd'
  rw [hs, seatAt_fit h iU3 s F H w s1 s2 e1 e2]
  exact keepsT_hear _ _ _ _ _ hh

/-- The same for blockOf. -/
theorem blockOf_trees (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide s rs gs = .ok s') :
    (s'.fork?.getD {}).trees = (s.fork?.getD {}).trees := by
  unfold blockOf at hb
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact blockAt_trees _ _ _ _ s s' rs gs hd

/-- **The same for the block as a lot seats it.** -/
theorem seated_trees {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide s rs gs = .ok s') :
    (s'.fork?.getD {}).trees = (s.fork?.getD {}).trees := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  have h1 := ((tested_decide _ _ _ _ _ _ _ _).1 hd).1
  exact blockAt_trees W.hS i _ l s s' rs gs h1

end VerifiableInference.Desc.Kinds.Head.Law
