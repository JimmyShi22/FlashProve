-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/KeepsBare.lean: the hearing of the sub-protocol "the output head's own
rounds" (K6) turns no field of the ledger but four: the next free number and the three arrays on
slots. Over the library alone.

  `bare_run`     one run of the ledger's own writer, by the library's law on it (`hideRun_ok`,
                 OnBytes/Tie/Pv/Psc/PscFork.lean: its clause `Same`)
  `KeepsB`       wherever a hearing returns from a ledger with its sizes: the ledger behind has its
                 sizes, and is the one in front but for these four fields (`bare`,
                 Johnson/Desc/First/Att/K05HearBelow.lean)
  `keepsB_…`     the hearings, one by one; `keepsB_hear`: the head's whole hearing
  `blockAt_bare` CONDITIONAL: at a yes of the bare block's decision, from a ledger with its sizes

Why it is typed. The library walks through the same hearings at least five times: for "a later
ledger" (Johnson/Desc/Kinds/Law/KeepsHear.lean), "it grows" (Law/GrowsHear.lean), "the arrays stay"
(Law/KeepsTrees.lean), "the list of debts stays" (Law/KeepsOwed.lean) and "just so many slots are
taken" (Law/Takes.lean). For the ledger's eight other fields (the coefficients and the constant of
the one equation; the counter of claims; the element of the weights and its mark; the plan's number
of claims and its marks; the mark of the shut door) a search over four folders of the library found
no such walk: A SEARCH, NOT A PROOF THAT THERE IS NONE. Here all fields but four at once. THE WALK
FOLLOWS Law/GrowsHear.lean's, STEP FOR STEP, with another sentence; each run of the writer is paid
by a call.

Limits. Every theorem is conditional on the hearing's return and on the sizes of the ledger in
front. The sizes are asked because the library's law on the writer asks them; that no other field
turns does not hang on them, by the writer's own text (`Fork.hide`, OnBytes/Model/Hide.lean: it lays
three arrays and nothing else): no theorem here says so. Nothing on what lies under a slot. Nothing
on any property.

-/
import Johnson.Desc.Kinds.Law.GrowsHear
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.First.Att.K05HearBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes (E)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Sized hideRun_ok)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (bare)
open VerifiableInference.Desc.Kinds.Head.Law

/-- One run of the ledger's own writer, from a ledger whose next free number was moved. -/
theorem bare_run {F G : Fork} {n first : Nat} {v : Array E} {factor : E} (hF : Sized F)
    (h : ({ F with next := n } : Fork).hideRun first v factor = some G) :
    Sized G ∧ bare G = bare F := by
  obtain ⟨a1, a2, _, _⟩ :=
    hideRun_ok _ G first v factor (show Sized { F with next := n } from hF) h
  exact ⟨a2, (congrArg bare a1).trans rfl⟩

/-- Wherever the hearing returns from a ledger with its sizes: the ledger behind has its sizes, and
is the ledger in front but for the next free number and the three arrays on slots. -/
def KeepsB {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, Sized F → x F rs = some (a, G, left) → Sized G ∧ bare G = bare F

theorem keepsB_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : KeepsB x)
    (hf : ∀ a, KeepsB (f a)) : KeepsB (x >>= f) := by
  intro F rs b G left hF h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  have g1 := hx _ _ _ _ _ hF h1
  have g2 := hf a _ _ _ _ _ g1.1 h2
  exact ⟨g2.1, g2.2.trans g1.2⟩

theorem keepsB_pure {α : Type} (a : α) : KeepsB (pure a : Hear α) := by
  intro F rs b G left hF h
  obtain ⟨_, rfl, _⟩ := pure_some h
  exact ⟨hF, rfl⟩

theorem keepsB_need {α : Type} (x : Option α) : KeepsB (Hear.need x) := by
  intro F rs b G left hF h
  obtain ⟨_, rfl, _⟩ := need_some h
  exact ⟨hF, rfl⟩

theorem keepsB_round (n k : Nat) : KeepsB (Hear.round n k) := by
  intro F rs b G left hF h
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
      rw [← h.2.1]; exact ⟨hF, rfl⟩

theorem keepsB_hide (v : List E) : KeepsB (hide v) := by
  intro F rs b G left hF h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray
      OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact bare_run hF hr

theorem keepsB_drawPoint (n : Nat) : KeepsB (drawPoint n) :=
  keepsB_bind (keepsB_round 0 n) fun _ => keepsB_pure _

theorem keepsB_sendThenBatch (n rows : Nat) : KeepsB (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine keepsB_bind (keepsB_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact keepsB_bind (keepsB_hide v) fun _ => keepsB_bind (keepsB_need _) fun _ => keepsB_pure _

/-- The part's hearing of a sumcheck. -/
theorem keepsB_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    KeepsB (heardBy lead C z ends) := by
  intro F0 t b F1 left hF h
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
  have L1 := keepsB_hide ld _ _ _ _ _ hF h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have L2 := bare_run L1.1 hrun2
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 := bare_run (n := G.next) L2.1 e6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact ⟨L3.1, (L3.2.trans L2.2).trans L1.2⟩

theorem keepsB_sumcheck (z : Point) (ends : Nat) : KeepsB (sumcheck z ends) := by
  unfold sumcheck
  refine keepsB_bind (keepsB_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact keepsB_pure _

theorem keepsB_level (z : Point) (start : Form) : KeepsB (level z start) := by
  unfold level
  refine keepsB_bind (keepsB_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine keepsB_bind (keepsB_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact keepsB_bind (keepsB_need _) fun _ => keepsB_pure _

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

theorem keepsB_normRest (pV : Point) : KeepsB (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine keepsB_bind (keepsB_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine keepsB_bind ?_ fun rhoI => ?_
  -- one norm: lNI = 0, so this step is pure
  · exact keepsB_pure _
  refine keepsB_bind (keepsB_level _ _) fun sq => ?_
  refine keepsB_bind (keepsB_sendThenBatch _ _) fun y => ?_
  obtain ⟨P, om⟩ := y
  exact keepsB_bind (keepsB_sumcheck _ _) fun _ => keepsB_pure _

theorem keepsB_norm : KeepsB Norm.hear :=
  keepsB_bind (keepsB_drawPoint _) fun pV => keepsB_normRest pV

theorem keepsB_final : KeepsB FinalNorm.hear :=
  keepsB_bind (keepsB_sumcheck _ _) fun _ => keepsB_pure _

/-- **The head's whole hearing.** -/
theorem keepsB_hear : KeepsB hear :=
  keepsB_bind keepsB_norm fun _ => keepsB_bind keepsB_final fun _ =>
    keepsB_bind (keepsB_sumcheck _ _) fun _ => keepsB_pure _

end Classes

/-- **The decision of the sub-protocol's block at the first chain's state.** -/
theorem blockAt_bare (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hS : Sized ((seatAt h iU3).ledger s))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    bare ((seatAt h iU3).ledger s') = bare ((seatAt h iU3).ledger s) := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, hh, e1, e2, hs⟩ := decideBy_spec hd'
  rw [hs, seatAt_fit h iU3 s F H w s1 s2 e1 e2]
  exact (keepsB_hear _ _ _ _ _ hS hh).2

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.bare_run
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_bind
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_pure
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_need
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_round
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_hide
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_drawPoint
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_sendThenBatch
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_heardBy
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_sumcheck
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_level
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_normRest
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_norm
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_final
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.keepsB_hear
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.blockAt_bare
