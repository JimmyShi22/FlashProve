-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowK6.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, WITH THE 17 ROW FORMS (idn · the two sums · keys and rider in our own words; planes on neither side; join not among the outs), FROM THE BLOCK's OWN DECISION, UNDER ONE RULE WHOSE CEILING IS A
PUBLIC NUMBER BY THE ROUND's NUMBER, AT EVERY FRONT: STATED AND PROVED, general in the seat. This is the form that the bridge
from a kind's rule to a block's errors asks of a kind: rule (record in front) (cells, mask row) : front → list, with
(rule …  g).length ≤ ceil (g.length - 1) at every g; no bad event beside the rule.
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE YET; whoever
may pick mask behind the draws makes every hidden scalar what they like. rs IS WHAT decide IS SHOWN (no sealed digest): that these are the rounds of the written reading is another file's equation (Johnson/Desc/Sound/ShownRounds.lean).
That the 35 forms are 0 and the claim on the weights true (Opened: what the block opens: later blocks'
laws). How probable a bad draw is: no written challenge is counted; no sum of errors is taken. SeatBack
(Law/RowAtDecide.lean) IS A PREMISE ON THE SEAT THAT IS NOT PAID HERE AT THE REAL SEAT (see the head of Law/RowAtSeat.lean). hasFeatures (0 < d) is a premise on the
plan's public numbers. That an honest run meets the premises: not shown.
  ceilAt p j     one more than the scalars that round number j of the kind's table of rounds sends (Law/SentFits.lean: sentAt).
  ruleCutAt      Law/RowCut.lean's rowRuleC at the letters that given returns at the record in front, at its ledger.
  ruleK6         ruleCutAt CUT AT ceilAt of the front's last round's number. ruleK6_length: the ceiling, at every front, every
                 record: by the cut.
  cut_takes_nothing   on the rounds on which the decision went on, at a WellLaid ledger, the cut takes nothing away: each round
                 sends as many scalars as the table says (decide_shape), and rowRuleC's list has at most that and one.
  RowK6Statement the decision goes on from s to s' · SeatBack · WellLaid · the tests on the plan and the request · 0 < d ·
                 y < V · the rounds canonical · Sound.NoBad (ruleK6 …): Opened at s' gives ClosedWhole at s'.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowWholeAtDecide
import Johnson.Desc.Kinds.Law.RowCut
import Johnson.Desc.Kinds.Law.SentFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Sound (cutTo strikeLast)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)

variable {S : Type}

/-- The ceiling at round number j: a number of the plan alone. -/
def ceilAt (p : Par) (j : Nat) : Nat := sentAt p j + 1

/-- The block's one rule, the point with it, at a record in front. -/
noncomputable def ruleCutAt (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E) :
    List Fmt.RoundView → List E :=
  match given p L s with
  | .ok g => Came.rowRuleC c mask (L.ledger s)
  | .error _ => fun _ => []

/-- **K6's RULE**: cut at the public ceiling of the front's last round's number. -/
noncomputable def ruleK6 (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (g : List Fmt.RoundView) : List E :=
  (ruleCutAt p L s c mask g).take (ceilAt p (g.length - 1))

/-- **K6's ROW.** -/
def RowK6Statement : Prop :=
  ∀ (S Cl : Type) (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par) (s : S)
    (c : NCells) (mask : Nat → E) (s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (kind cl L link piece p).decide s rs gs = .ok s' → SeatBack p L s → WellLaid (L.ledger s) →
    p.ok = true → hasFeatures p → p.okStart (L.request s) = true →
    (∀ y, Reply.token L.toSeat s = some y → y < p.sizes.V) →
    Canonical rs → Sound.NoBad (ruleK6 p L s c mask) rs →
    Opened p L s' c mask → ClosedWhole p L s' c mask

namespace Came

/-- **The ceiling, at every front and every record.** -/
theorem ruleK6_length (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (g : List Fmt.RoundView) : (ruleK6 p L s c mask g).length ≤ ceilAt p (g.length - 1) :=
  List.length_take_le _ _

theorem ruleCutAt_length (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (hW : WellLaid (L.ledger s)) (h : List Fmt.RoundView) : (ruleCutAt p L s c mask h).length
      ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold ruleCutAt
  cases given p L s with
  | ok g => exact rowRuleC_length c mask _ hW h
  | error _ => simp

/-- **On the rounds on which the decision went on the cut takes nothing away.** -/
theorem cut_takes_nothing {Cl : Type} (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (c : NCells)
    (mask : Nat → E) (hd : (kind cl L link piece p).decide s rs gs = .ok s')
    (hW : WellLaid (L.ledger s)) (hnb : Sound.NoBad (ruleK6 p L s c mask) rs) :
    Sound.NoBad (ruleCutAt p L s c mask) rs := by
  intro i r hi j x hj hm
  refine hnb i r hi j x hj ?_
  show E.ofTriple x ∈ ruleK6 p L s c mask (rs.take i ++ [cutTo r j])
  have hil : i < rs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen : (rs.take i ++ [cutTo r j]).length - 1 = i := by
    rw [List.length_append, List.length_take, List.length_singleton]
    omega
  have hle := ruleCutAt_length p L s c mask hW (rs.take i ++ [cutTo r j])
  have hlast : (((rs.take i ++ [cutTo r j]).getLast?.map fun r => r.vals.length).getD 0)
      = r.vals.length := by simp [cutTo]
  rw [hlast, decide_shape cl L link piece p hd i r hi] at hle
  have hle' : (ruleCutAt p L s c mask (rs.take i ++ [cutTo r j])).length ≤ ceilAt p i := hle
  unfold ruleK6
  rw [hlen, List.take_of_length_le hle']
  exact hm

theorem rowK6 : RowK6Statement := by
  intro S Cl cl L link piece p s c mask s' rs gs hd hback hWL hplan hd0 hreq hy hcan hnb hopen
  have hnb1 := cut_takes_nothing cl L link piece p c mask hd hWL hnb
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) p L s rs
      = .ok s' := hd
  obtain ⟨g, H, F1, w, s1, s2, hg, hh, e1, e2, rfl⟩ := decide_hears hd'
  obtain ⟨bL, bH, bG, bZ⟩ := hback g rs [] F1 H w s1 s2 hg hWL hcan hh e1 e2
  obtain ⟨g', H', hg', hH', hO⟩ := hopen
  rw [bG, hg] at hg'
  obtain rfl : g = g' := Except.ok.inj hg'
  rw [bH] at hH'
  obtain rfl : H = H' := Option.some.inj hH'
  rw [bL] at hO
  have hnb' : Sound.NoBad (rowRuleC c mask (L.ledger s)) rs := by
    unfold ruleCutAt at hnb1
    rw [hg] at hnb1
    exact hnb1
  obtain ⟨z, y, hz, hty, hP, rfl⟩ := given_ok p L s g hg
  have main := @rowCut p.sizes p.policy (L.request s) ⟨y⟩ (@fromLookup p.sizes p.floor z.1 z.2).norm
    (@fromLookup p.sizes p.floor z.1 z.2).head p.sT p.floor z.1 z.2 c mask (L.ledger s) hplan hd0 hreq
    (hy y hty) hWL hP rfl rfl rs H F1 F1 hcan hh (Later.refl _) hnb' hO.1 hO.2
  refine ⟨⟨_, bG.trans hg, main.1⟩, _, H, z, bG.trans hg, bH, bZ.trans hz, ?_⟩
  rw [bL]
  exact main.2

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ruleK6_length
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.cut_takes_nothing
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowK6
