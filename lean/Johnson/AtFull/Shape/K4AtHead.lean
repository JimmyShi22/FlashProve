-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K4AtHead.lean: THE LAYERS' OWN ROUNDS (K4) AT THEIR SEAT IN THE PROOF FILE's
OWN FIRST CHAIN, AT ALL TWELVE LAYERS' LINKS: the member of the flat list has one step on the
chain's shape, with both laws at the seated block's own decision. Under the head P5J.AtMgA; nothing
is evaluated.

  mergedB, merged_of_B   the test on the merged point, with code.
  k4ValsB, vals_of_B     THE MEMBER's TESTS ON VALUES AND ON ITS ROUNDS AS ONE Bool of the state and
                  the rounds (K4Vals, Johnson/Desc/First/K4/Returns/AtStep.lean).
  k4StepS         THE STEP AT THE SEAT: no mark of failure, then k4Step.
  k4StepS_reads, k4ValsB_reads   the step and the Bool read three fields of a place's record alone:
                  the public record, the plan, the group's number.
  **k4_at**       for g < 12: with Bs what the maker's own ProofFile.baseOf returns at the public part
                  (one value: baseOf is a function), the member b at number 28 g + 4 of cF.blocksInOrder, and
                  a record y of K4's own list of places: WHAT THE STEP READS OF y IS TIED: y.2.P is
                  the public part's layers' record; y.2.g = g; y.2.hp is the public part's plan
                  number g. Then: where b says yes and the step returns, it has returned the shape
                  behind, and b has left the statement as it was; and where the step returns and
                  k4ValsB is true, b says yes.

By IM.k4_of and IM.k4_yes (Johnson/IMR/K4Seat.lean: the seat holds K4's own block alone; the seated
yes is the block's yes, no mark, the reply as it was), IM.hear_at_flat and IM.flatIx_scope (the
number in the flat list).

Limits. y stands under "there is": of its fields the step and the Bool read P, hp and g alone
(k4StepS_reads, k4ValsB_reads), and these three are tied. Of the head the proof spends h.scope,
h.reads and h.laid.opened alone. "b has left the statement as it was" stands under the step's
return, though the proof draws it from the yes alone. merged_of_B and vals_of_B go one way. NO STATE
IS SHOWN AT WHICH THE STEP RETURNS. Who pays k4ValsB is not said; the part of it on the rounds (the
stretch fits K4's table) is not drawn from the fit of the member's declared rounds. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.AtStep
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatScope
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First.K4 (Par blockAtC blockAtS entries)
open OnBytes.Desc.First.K4.Rt (k4Step K4Vals k4Step_carries k4Step_returns decide_lays MergedAt
  stretchB coinB k4PlanB k4FrontB k4G ownOf)
open OnBytes.Desc.First.K4.RtPub (tokensFit)

/-! ## 1 The tests on values, as one Bool -/

/-- The test on the merged point, with code: where both readings are there, every call's point ends
as the lookup's own. -/
def mergedB (P : Layer.Pub) (fo : Forest.Heard) : Bool :=
  match (lastOf fo.zx P.y.h.la).toOption, fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption with
  | some Z, some ends => ends.all (· == Z)
  | _, _ => true

theorem merged_of_B {P : Layer.Pub} {fo : Forest.Heard} (h : mergedB P fo = true) :
    MergedAt P fo := by
  intro Z ends hZ hE
  unfold mergedB at h
  rw [hZ, hE] at h
  exact h

/-- **The member's tests on values and on its rounds, as one Bool.** Where the state has no lookup's
record (s.look? = none) the clause on the merged point says yes. -/
def k4ValsB (p : Par) (s : S) (rs : List Fmt.RoundView) : Bool :=
  stretchB p s rs && tokensFit { p.P with tokv := s.tokv } p.g &&
    (s.look?.all fun fo => mergedB p.P fo) && coinB p.P p.g (paired rs (entries p.P p.hp p.g))

theorem vals_of_B {p : Par} {s : S} {rs : List Fmt.RoundView} (h : k4ValsB p s rs = true) :
    K4Vals p s rs := by
  unfold k4ValsB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun fo hfo => merged_of_B ?_, h4⟩
  rw [hfo] at h3
  exact h3

/-! ## 2 The seat -/

/-- **The step at the seat.** -/
def k4StepS (p : Par) (a : ChainSh) : Option ChainSh :=
  if a.marked then none else k4Step p a

/-- **The step reads three fields of the place's record alone**: the public record, the plan, the
group's number. -/
theorem k4StepS_reads {p q : Par} (h1 : p.P = q.P) (h2 : p.hp = q.hp) (h3 : p.g = q.g) :
    k4StepS p = k4StepS q := by
  funext a
  unfold k4StepS k4Step k4PlanB k4FrontB k4G ownOf
  rw [h1, h2, h3]

/-- So does the Bool of the tests on values and rounds. -/
theorem k4ValsB_reads {p q : Par} (h1 : p.P = q.P) (h2 : p.hp = q.hp) (h3 : p.g = q.g) :
    k4ValsB p = k4ValsB q := by
  funext s rs
  unfold k4ValsB stretchB
  rw [h1, h2, h3]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k4_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (y : Bool × Par) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      y ∈ ProofFile.k4From Zp Bs.G₀ Bs.G₀.built.toList 0 none ∧
      y.2.P = Bs.G₀.W.layers ∧ y.2.g = g ∧ Bs.G₀.W.G[g]? = some y.2.hp ∧
      cF.blocksInOrder[28 * g + 4]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        k4StepS { y.2 with k3Runs := true } (chainSh s) = some u → u = chainSh t ∧ t.st = s.st) ∧
      ∀ s rs gs u, k4StepS { y.2 with k3Runs := true } (chainSh s) = some u →
        k4ValsB { y.2 with k3Runs := true } s rs = true → ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, eL, eb, hy, la, -, eg, eP, ehp, -, -⟩ := IM.k4_of h.scope h.reads O g hg
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g ≤ 24) 2] at q
  have en : 14 * (2 * g) + 2 + 2 = 28 * g + 4 := by omega
  rw [en] at q
  refine ⟨Bs, y, b, O.made, hy, eP, eg, ehp, q, fun s rs gs t u hd hu => ?_,
    fun s rs gs u hu hv => ?_⟩
  · have hd' : (blockAtC { y.2 with k3Runs := true }).decide s rs gs = .ok t :=
      ((IM.k4_yes la s t rs gs).1 hd).1
    unfold k4StepS at hu
    split at hu
    · cases hu
    · refine ⟨k4Step_carries hd' hu, ?_⟩
      obtain ⟨a, o, G, -, -, rfl⟩ := decide_lays hd'
      rfl
  · unfold k4StepS at hu
    split at hu
    · cases hu
    · rename_i hm
      obtain ⟨t, ht⟩ := k4Step_returns gs hu (vals_of_B hv)
      have hf : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      obtain ⟨a, o, G, -, -, et⟩ := decide_lays ht
      refine ⟨t, (IM.k4_yes la s t rs gs).2 ⟨ht, ?_, ?_⟩⟩
      · rw [et]
        exact hf
      · rw [et]
        unfold ProofFile.sameReply
        exact beq_self_eq_true _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.merged_of_B
#print axioms Johnson.AtFull.Shape.vals_of_B
#print axioms Johnson.AtFull.Shape.k4StepS_reads
#print axioms Johnson.AtFull.Shape.k4ValsB_reads
#print axioms Johnson.AtFull.Shape.k4_at
#print axioms Johnson.AtFull.Shape.mergedB
#print axioms Johnson.AtFull.Shape.k4ValsB
#print axioms Johnson.AtFull.Shape.k4StepS
