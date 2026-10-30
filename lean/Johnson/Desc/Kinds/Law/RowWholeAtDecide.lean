-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowWholeAtDecide.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, WITH THE 17 ROW FORMS (idn · the two sums · keys and rider in our own words; planes on neither side; join not among the outs), FROM THE BLOCK's OWN DECISION: STATED AND
PROVED, general in the seat: Law/RowWhole.lean's law said of (kind cl L link piece p).decide, the decision of the block
that runs (HeadKind.lean), at any carried record.
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE YET; whoever
may pick mask behind the draws makes every hidden scalar what they like. rs IS WHAT decide IS SHOWN (no sealed digest): that these are the rounds of the written reading is another file's equation (Johnson/Desc/Sound/ShownRounds.lean).
That the 35 forms are 0 and the claim on the weights true (Opened: what the block opens: later blocks'
laws). How probable a bad draw is. SeatBack (Law/RowAtDecide.lean) IS A PREMISE ON THE SEAT THAT IS NOT PAID HERE AT THE REAL
SEAT (at `seatAt`: see `seatBack_at`, Law/HeardBack.lean). GoodPointAt IS A PREMISE OF ITS OWN, NO RULE: the point on the positions, which the block's first round draws whole,
is not one of the bridge's bad points (BadP). Par.hasFeatures (0 < d) is a premise on the plan's public numbers, which
the program's test on the plan does not ask. That an honest run meets the premises: not shown.
  ruleWholeAt    the block's one rule at a record in front: rowRule at the letters that given returns there and at the
                 record's ledger; empty where given refuses. ruleWholeAt_length: its ceiling, at a WellLaid ledger.
  GoodPointAt    at the record in front and the rounds: the point that the first round draws is good.
  ClosedWhole    at every position's corner the row's 17 forms are 0 (the clause "rows" of CellRelN), and Closed.
  RowWholeAtDecideStatement   the decision goes on from s to s' · SeatBack · WellLaid · the tests on the plan and the
                 request · 0 < d · y < V · the rounds canonical · no bad draw under the one rule · the point good:
                 Opened at s' gives ClosedWhole at s'.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowAtDecide
import Johnson.Desc.Kinds.Law.RowCeil

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)

variable {S : Type}

/-- The plan has a feature. -/
def hasFeatures (p : Par) : Prop :=
  let _ := p.sizes
  0 < d

/-- The block's one rule at a record in front. -/
noncomputable def ruleWholeAt (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E) :
    List Fmt.RoundView → List E :=
  match given p L s with
  | .ok g => Came.rowRule c mask (L.ledger s)
  | .error _ => fun _ => []

/-- The point that the block's first round draws is good. -/
def GoodPointAt (p : Par) (L : Seat S) (s : S) (c : NCells) (rs : List Fmt.RoundView) : Prop :=
  ∀ (g : Given) (pV : Point) (G : Fork) (left : List Fmt.RoundView), given p L s = .ok g →
    drawPoint lt (L.ledger s) rs = some (pV, G, left) → GoodPoint c pV

/-- What the block closes, whole. -/
def ClosedWhole (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E) : Prop :=
  (∃ g : Given, given p L s = .ok g ∧ ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) ∧
    Closed p L s c mask

/-- **THE ROW, WITH THE 17 ROW FORMS, FROM THE BLOCK's DECISION.** -/
def RowWholeAtDecideStatement : Prop :=
  ∀ (S Cl : Type) (cl : Form → Cl) (L : Seat S) (link piece : Nat) (p : Par) (s : S)
    (c : NCells) (mask : Nat → E) (s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (kind cl L link piece p).decide s rs gs = .ok s' → SeatBack p L s → WellLaid (L.ledger s) →
    p.ok = true → hasFeatures p → p.okStart (L.request s) = true →
    (∀ y, Reply.token L.toSeat s = some y → y < p.sizes.V) →
    Canonical rs → NoBad (ruleWholeAt p L s c mask) rs → GoodPointAt p L s c rs →
    Opened p L s' c mask → ClosedWhole p L s' c mask

namespace Came

theorem ruleWholeAt_length (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    (hW : WellLaid (L.ledger s)) (h : List Fmt.RoundView) : (ruleWholeAt p L s c mask h).length
      ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold ruleWholeAt
  cases given p L s with
  | ok g => exact rowRule_length c mask _ hW h
  | error _ => simp

theorem rowWholeAtDecide : RowWholeAtDecideStatement := by
  intro S Cl cl L link piece p s c mask s' rs gs hd hback hWL hplan hd0 hreq hy hcan hnb hgood hopen
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
  have hnb' : NoBad (rowRule c mask (L.ledger s)) rs := by
    unfold ruleWholeAt at hnb
    rw [hg] at hnb
    exact hnb
  -- the point
  have hpt : GoodPoint c H.1.pV := by
    obtain ⟨Fa, Fb, l1, hNorm, _⟩ := hear_parts hWL hh
    obtain ⟨p0, p1, tS, p2, tP, _, _, _, hrs, h0, _⟩ := norm_parts hWL hNorm
    obtain ⟨q, hq, cq⟩ := consumes_drawPoint _ _ _ _ _ _ h0
    rw [List.append_nil] at hq
    subst hq
    exact hgood g H.1.pV _ _ hg (by rw [hrs]; exact cq _)
  obtain ⟨z, y, hz, hty, hP, rfl⟩ := given_ok p L s g hg
  have main := @rowWhole p.sizes p.policy (L.request s) ⟨y⟩ (@fromLookup p.sizes p.floor z.1 z.2).norm
    (@fromLookup p.sizes p.floor z.1 z.2).head p.sT p.floor z.1 z.2 c mask (L.ledger s) hplan hd0 hreq
    (hy y hty) hWL hP rfl rfl rs H F1 F1 hcan hh (Later.refl _) hnb' hpt hO.1 hO.2
  refine ⟨⟨_, bG.trans hg, main.1⟩, _, H, z, bG.trans hg, bH, bZ.trans hz, ?_⟩
  rw [bL]
  exact main.2

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ruleWholeAt_length
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowWholeAtDecide
