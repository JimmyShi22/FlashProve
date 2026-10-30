-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SeatYes.lean: AT THE SWITCH INTO A LATER GROUP (the links 1 to 23):
THE SUB-PROTOCOL THAT THE DESCRIPTION SEATS AT NUMBER 14 l + 2 OF ITS FIRST CHAIN's FLAT LIST: ITS
PLACE, ITS ROUNDS AND ITS STATED ORACLE MESSAGES ARE THE KIND's OWN AT THE PLAN's NUMBERS; AND UNDER
THE HEAD, AT A STATE THAT IS REACHED THERE, ITS OWN DECISION SAYS YES AT ALL TWO ROUNDS AND COLUMNS
THAT PASS THE TWO TESTS WHICH `Block.step` RUNS. Two statements with their proofs: joins; no
definition.

  `link_seat_shape`   the place, the rounds, the stated oracle messages: in the goals' scope, at an
                      opening, under the plan's own test and the written cut
  `link_seat_yes`     THE SEATED DECISION's YES

By: the library's `IM.k2_link_sits`, `IM.hear_at_flat`, `IM.flatIx_scope`, `IM.Joined.rounds`,
`IM.Joined.planOk` (Johnson/IMR/) · the first pen's `link_dress`, `link_seat_reached`
(Returns/SeatAtLinks.lean: the seated decision both ways; the way out returns behind every yes at a
reached state), `six_at_head` (Returns/TiedReached.lean) · `link_yes_reached`
(Returns/YesReached.lean). The first lines of `link_seat_shape`'s proof walk the road of the first
pen's `link_seat_decides` anew: that law hands out the decision and neither the place nor the
rounds.

THE PREMISES OF `link_seat_yes`, ALL OF THEM: the head `P5J.AtMgA` and the opening · m < 23. What it
hands out stands under: the state is reached, OVER THE LIST OF THE WRAPPED SUB-PROTOCOLS (`below`,
Johnson/Desc/Sound/ChainRule.lean: narrower than over the description's own list) · hrf, hcols: the
two rounds and the columns pass the two tests · hp: the decision is shown the second round's
positions as `Block.step` reads them.

WHAT IT DOES NOT SAY: Returns/YesReached.lean's five points but the fourth, AT THE LINKS: THAT ANY
STATE IS REACHED THERE IS NOT SAID: where none is, it says nothing · THE YES HOLDS AT ALL TWO ROUNDS
AND COLUMNS OF THE RIGHT SHAPE AND IS NO SIGN THAT A MESSAGE IS HONEST · that the head has a member
together with a reached state is not said here · that `leafOk` bites is not said.

Limits. THE LINKS ALONE: nothing at the two other sorts of place. Of a sub-protocol's decision: not
of a verifier's program. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. What lies beneath is
graded in Returns/YesReached.lean's and Returns/SeatAtLinks.lean's heads. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.YesReached
import Johnson.Desc.K2.Honest.Returns.SeatAtLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit groupsOf Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (codeSwitchKind rounds)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P under)
open _root_.Tw.K2 (Col)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The seated sub-protocol's place, rounds and stated oracle messages.** -/
theorem link_seat_shape (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∃ b : Block S Cl, c.blocksInOrder[14 * l + 2]? = some b ∧ b.place = switchPlaceAt l ∧
      ∀ (nm : String) (Pp : Prep) (n : Nums), prepOf Z Bs.G₀ = some Pp →
        numsAt Pp (some l) = some n →
        b.rounds = rounds (k2P Z (switchPlaceAt l) nm .link n) ∧
          b.oracles = [(k2P Z (switchPlaceAt l) nm .link n).sent, []] := by
  obtain ⟨Lk, b, x, e1, e2, hx, J, hi⟩ := IM.k2_link_sits hS hR O l h1 h24
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  obtain ⟨fs, f, hfs, hff, ep⟩ := J.planOk
  rw [hb] at ep
  obtain ⟨hq, -⟩ := Bool.and_eq_true_iff.1 ep.symm
  have hxp := (IM.retype_planOk x hq).1
  have hpc : x.place = (switchPlaceAt l) := by
    obtain ⟨_, _, -, -, arms⟩ := hi.live hxp
    rcases arms with ⟨-, e⟩ | ⟨_, _, -, -, e⟩ | ⟨_, -, e⟩ <;> rw [e] <;> rfl
  obtain ⟨Pp₀, n₀, hP₀, hn₀, ex⟩ := link_dress hS hR O hpl hcut h24 hx hxp hpc
  have hro := J.rounds
  obtain ⟨fs', f', -, -, e⟩ := J
  refine ⟨b, by simpa using hf, ?_, fun nm Pp n hP hn => ?_⟩
  · rw [e]
    rfl
  · obtain rfl : Pp₀ = Pp := Option.some.inj (hP₀.symm.trans hP)
    obtain rfl : n₀ = n := Option.some.inj (hn₀.symm.trans hn)
    constructor
    · rw [hro, ex]
      rfl
    · rw [e]
      show (x.retype : Block S Cl).oracles ++ [] = _
      rw [List.append_nil, ex]
      rfl

end

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE SEATED DECISION's YES.** -/
theorem link_seat_yes (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) :
    ∃ (b : Block S Cl) (nm : String) (Pp : Prep) (n : Nums),
      cF.blocksInOrder[14 * (m + 1) + 2]? = some b ∧ b.place = switchPlaceAt (m + 1) ∧
      prepOf Zp Bs.G₀ = some Pp ∧ numsAt Pp (some (m + 1)) = some n ∧
      b.rounds = rounds (k2P Zp (switchPlaceAt (m + 1)) nm .link n) ∧
      b.oracles = [(k2P Zp (switchPlaceAt (m + 1)) nm .link n).sent, []] ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s) →
        ∀ (r₁ r₂ : Fmt.RoundView) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn),
          d₂.poss = r₂.drawn.poss →
          roundsFit (rounds (k2P Zp (switchPlaceAt (m + 1)) nm .link n)) [r₁, r₂] = true →
          cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
            (groupsOf ft (rounds (k2P Zp (switchPlaceAt (m + 1)) nm .link n)) [d₁, d₂]).flatMap
              id →
          ∃ t, b.decide s [r₁, r₂]
            (laidGroups (k2P Zp (switchPlaceAt (m + 1)) nm .link n) ft d₁ d₂ cols) = .ok t := by
  obtain ⟨hpl, hcut, -⟩ := six_at_head h.toAtMg O
  obtain ⟨b, nm, -, -, Pp, n, hb, -, -, -, hP, hn, -, hy⟩ :=
    link_seat_reached h.scope h.reads O hpl hcut (l := m + 1) (by omega) (by omega)
  obtain ⟨b', hb', hpc, hsh⟩ :=
    link_seat_shape h.scope h.reads O hpl hcut (l := m + 1) (by omega) (by omega)
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hro, hor⟩ := hsh nm Pp n hP hn
  refine ⟨b, nm, Pp, n, hb, hpc, hP, hn, hro, hor,
    fun z s hr r₁ r₂ ft d₁ d₂ cols hp hrf hcols => ?_⟩
  obtain ⟨u, hu⟩ := link_yes_reached h O h23 hP hn hr (switchPlaceAt (m + 1)) nm r₁ r₂ ft d₁ d₂
    cols hp hrf hcols
  exact hy z s hr _ _ u rfl
    (groups_give (k2P Zp (switchPlaceAt (m + 1)) nm .link n) ft d₁ d₂ cols) hu

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_seat_shape
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_seat_yes
