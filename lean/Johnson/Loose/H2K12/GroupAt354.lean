-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/GroupAt354.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST
CHAIN: A FACT ALONG "REACHED" AT THE BORDER IN FRONT OF THE TEST: where the verifier's state stands
at the chain's finish, the group that the finish's own frame names is the one that the last code
switch's numbers name. Definitions, statements and proofs.

Why it holds. "Reached" (Reach, Johnson/Top/H0/Walk/Reach.lean) is an inductive family: what is
reached by k + 1 sub-protocols stands behind an accepting step of sub-protocol number k. The place
of the last code switch (finishPlace, Johnson/Top/H0/Tw/K2C/Finish.lean) is a quiet step in front,
the switch's own decision, a quiet step behind. THE SWITCH's OWN DECISION TESTS THE EQUATION
(FinIs.hGrp by finish_inv, Johnson/Top/H0/Tw/K2C/Closed.lean), and neither it nor the quiet step
behind (finishBehindQ_iff, Johnson/Top/H0/Tw/K2C/Asks.lean) turns the frame. No count of groups is
spent.
Main names:
  reach_last      the case split on "reached".
  finishPlace_cut   an accept of the place's decision, cut into its three.
  fin_group_place   behind such an accept: the state stands at the finish, with the equation.
  SeatF1 B p      the sub-protocol B sits at that place with the numbers p: an accept of B's
                  decision is one of the place's. No state is read.
  seat_yes        an accepting step of "below B" (Johnson/Desc/Sound/ChainRule.lean): every word
                  shown is below the prime, and the place's decision accepts.
  group_of_reach  THE FACT, at every state that is reached by k + 1 sub-protocols, marked or not,
                  where number k is such a B.
Limits. (1) SeatF1 is a premise here. (2) That p.grp is the table's number of the last group is not
said here. (3) Nothing is said of a state that does not stand at the finish. No soundness statement.
Nothing on hiding.

-/
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.Tw.K2C.Finish
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 finishPlace)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-- What is reached by k + 1 sub-protocols stands behind an accepting step of sub-protocol number k,
from a state that is reached by k. -/
theorem reach_last {St Cl P : Type} {ft : ℕ} {bs : List (Block St Cl)} {start : P → St} {k : ℕ}
    {z : P} {s' : St} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩

private theorem bind_ok' {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The place of the last code switch, cut into its three: the quiet step in front, the switch's own
decision, the quiet step behind. -/
theorem finishPlace_cut (p : P2) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (finishPlace p : Block S Unit).decide s rs gs = .ok s') :
    ∃ t t' rs' gs', VerifiableInference.Desc.First.K2.finishFrontQ s = .ok t ∧
      VerifiableInference.Desc.First.K2.decideWith _root_.Tw.K2.sendByL8 p t rs' gs' = .ok t' ∧
      VerifiableInference.Desc.First.K2.finishBehindQ t' = .ok s' ∧ (∀ r ∈ rs', r ∈ rs) := by
  obtain ⟨m₂, h12, h3⟩ := bind_ok' h
  obtain ⟨m₁, h1, h2⟩ := bind_ok' h12
  exact ⟨m₁, m₂, _, _, h1, h2, h3, fun r hr => List.mem_of_mem_take (List.mem_of_mem_drop hr)⟩

/-- **Behind an accept at the place of the last code switch the state stands at the finish, and the
group that the finish's own frame names is the one that the switch's numbers name**: the switch's
own decision tests it, and neither it nor the quiet step behind turns the frame. -/
theorem fin_group_place (p : P2) (hp : p.stands = .finish) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (finishPlace p : Block S Unit).decide s rs gs = .ok s') :
    ∃ o, s'.here = .fin o ∧ o.fr.group = p.grp := by
  obtain ⟨t, t', rs', gs', -, h2, h3, -⟩ := finishPlace_cut p h
  obtain ⟨r₁, r₂, a, G, w, roots, -, F⟩ := VerifiableInference.Desc.First.K2.finish_inv hp h2
  obtain ⟨a', m, ha', -, rfl⟩ := (VerifiableInference.Desc.First.K2.finishBehindQ_iff t' s').1 h3
  rw [F.hOut] at ha'
  obtain rfl : { a with sw := w.out } = a' := by
    have e : VerifiableInference.Desc.First.Here.fin { a with sw := w.out } = .fin a' := ha'
    injection e
  exact ⟨_, rfl, F.hGrp⟩

/-- **The sub-protocol B sits at the place of the last code switch with the numbers p**: an accept
of its decision is one of that place's. -/
def SeatF1 {Cl : Type} (B : Block S Cl) (p : P2) : Prop :=
  p.stands = .finish ∧ ∀ s rs gs t, B.decide s rs gs = .ok t →
    (finishPlace p : Block S Unit).decide s rs gs = .ok t

/-- An accepting step of "below B" at such a B: every word shown is below the prime, and the place's
own decision accepts. -/
theorem seat_yes {Cl : Type} {B : Block S Cl} {p : P2} (hK : SeatF1 B p) {ft : ℕ} {s s' : S}
    (h : StepYes ft (VerifiableInference.Desc.Sound.below B) s s') :
    ∃ rs gs,
      VerifiableInference.Desc.viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true ∧
        (finishPlace p : Block S Unit).decide s rs gs = .ok s' := by
  obtain ⟨R, c, -, e⟩ := h
  obtain ⟨-, -, -, h4⟩ := (VerifiableInference.Desc.Sound.step_ok_iff ft
    (VerifiableInference.Desc.Sound.below B) s s' R c c.length).1 e
  obtain ⟨hv, hd⟩ := VerifiableInference.Desc.Sound.below_yes B _ _ _ _ h4
  exact ⟨_, _, hv, hK.2 _ _ _ _ hd⟩

/-- **THE GROUP AT THE FINISH, ALONG "REACHED".** -/
theorem group_of_reach {Cl P : Type} (bs : List (Block S Cl)) (start : P → S) (k : ℕ)
    (B : Block S Cl) (hB : bs[k]? = some B) (p : P2) (hK : SeatF1 B p) {z : P} {s' : S}
    (h : Reach 0 (bs.map VerifiableInference.Desc.Sound.below) start (k + 1) (z, s')) :
    ∀ o, s'.here = .fin o → o.fr.group = p.grp := by
  obtain ⟨s, b, -, hb, hy⟩ := reach_last h
  rw [List.getElem?_map, hB] at hb
  obtain rfl : VerifiableInference.Desc.Sound.below B = b := Option.some.inj hb
  obtain ⟨rs, gs, -, hd⟩ := seat_yes hK hy
  obtain ⟨o', ho', hg⟩ := fin_group_place p hK.1 hd
  intro o ho
  rw [ho'] at ho
  obtain rfl : o' = o := by injection ho
  exact hg

end H2K12

#print axioms H2K12.reach_last
#print axioms H2K12.finishPlace_cut
#print axioms H2K12.fin_group_place
#print axioms H2K12.seat_yes
#print axioms H2K12.group_of_reach
