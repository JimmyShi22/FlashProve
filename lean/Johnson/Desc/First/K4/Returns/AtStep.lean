-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/AtStep.lean: THE LAYERS' OWN ROUNDS (K4): ITS HEARING MEMBER: ONE STEP
ON THE CHAIN's SHAPE WITH BOTH LAWS, at the block at the state that the first chain carries
(blockAtC, Johnson/Desc/First/K4/AtC.lean). General laws: nothing is evaluated.

  **k4Step p**    THE STEP: three guards with code, then the hearing on shapes (k4G,
                  Johnson/Desc/First/K4/Returns/AtShape.lean). The guards: the test on the plan
                  (k4PlanB); the host's count of the padding keys is the layout's own; the guard on
                  the shape in front (k4FrontB at no slot left over); all three from
                  Johnson/Desc/First/K4/Returns/AtChainPays.lean.
  K4Vals p s rs   THE MEMBER's TESTS ON VALUES AND ON ITS ROUNDS, by name: the stretch fits K4's
                  table and no count of rows waits (stretchB); the request's tokens; the merged
                  point; the coin.
  **k4Step_carries**   a yes of the block, and the step returns at the state's shape: then it has
                  returned the shape of the state behind. No premise on a value.
  **k4Step_returns**   the step returns at the state's shape, and K4Vals: then the block says yes.
  k4Step_follows  both together.

Why the guards. The hearing on shapes returns where the hearing at blanks does. The law that gives a
yes at a state (k4_returns) asks tests with code that are sufficient, not necessary: among them two
sizes of the ledger's arrays which the hearing itself never tests. So they do not follow from the
blank run's return, and stand in the step as guards of their own.

Limits. THAT THE STEP RETURNS AT A SHAPE WHICH THE CHAIN REACHES IS NOT SHOWN. The step is as dear
as the hearing, and the test on the plan is dear too. Who pays K4Vals is not said. k4Step_returns
spends of the step's return its three guards alone: that k4G itself returned, and what, plays no
part there. The step does not read rowsOwed (see AtShape.lean's Limits): "no count of rows waits"
stands in K4Vals, through stretchB. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.AtShape
import Johnson.Desc.First.K4.Returns.AtChainPays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-- **THE STEP.** -/
def k4Step (p : Par) (a : ChainSh) : Option ChainSh :=
  if (k4PlanB p &&
      (VerifiableInference.Desc.First.Look.laidLayers p.P == some p.P.y.fo.pub) &&
      k4FrontB p 0 a) = true then k4G p a
  else none

/-- **The member's tests on values and on its rounds.** -/
structure K4Vals (p : Par) (s : S) (rs : List Fmt.RoundView) : Prop where
  stretch : stretchB p s rs = true
  tokens : tokensFit { p.P with tokv := s.tokv } p.g = true
  merged : ∀ fo, s.look? = some fo → MergedAt p.P fo
  coin : coinB p.P p.g (paired rs (entries p.P p.hp p.g)) = true

theorem k4Step_carries {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (blockAtC p).decide s rs gs = .ok s')
    {t : ChainSh} (hg : k4Step p (chainSh s) = some t) : t = chainSh s' := by
  unfold k4Step at hg
  split at hg
  · exact k4_carries h hg
  · cases hg

theorem k4Step_returns {p : Par} {s : S} {rs : List Fmt.RoundView}
    (gs : List (List (Nat × List UInt64))) {t : ChainSh} (hg : k4Step p (chainSh s) = some t)
    (hv : K4Vals p s rs) : ∃ s', (blockAtC p).decide s rs gs = .ok s' := by
  unfold k4Step at hg
  split at hg
  case isFalse => cases hg
  case isTrue hb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨⟨hP, hL⟩, hF⟩ := hb
    obtain ⟨o, G, -, e, -⟩ := k4_returns p 0 s rs gs hP hL hF hv.stretch hv.tokens hv.merged hv.coin
    cases hd : (blockAtC p).decide s rs gs with
    | ok s' => exact ⟨s', rfl⟩
    | error m =>
      rw [hd] at e
      cases e

theorem k4Step_follows {p : Par} {s : S} {rs : List Fmt.RoundView}
    (gs : List (List (Nat × List UInt64))) {t : ChainSh} (hg : k4Step p (chainSh s) = some t)
    (hv : K4Vals p s rs) : ∃ s', (blockAtC p).decide s rs gs = .ok s' ∧ chainSh s' = t := by
  obtain ⟨s', h⟩ := k4Step_returns gs hg hv
  exact ⟨s', h, (k4Step_carries h hg).symm⟩

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.k4Step_carries
#print axioms OnBytes.Desc.First.K4.Rt.k4Step_returns
#print axioms OnBytes.Desc.First.K4.Rt.k4Step_follows
#print axioms OnBytes.Desc.First.K4.Rt.k4Step
#print axioms OnBytes.Desc.First.K4.Rt.K4Vals
