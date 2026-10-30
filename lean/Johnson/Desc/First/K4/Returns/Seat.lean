-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Seat.lean: THE LAYERS' OWN ROUNDS (K4): hearAt RETURNS (the hearing at
a seat, Johnson/Desc/First/K4/Block.lean; the block's decision stands over it). A seat
(the structure Seat, OnBytes/Desc/First/K4/Steps.lean) says where in a state lie the things that
K4's steps read and write. General laws: nothing is evaluated.

  leading_all     a message of field elements alone is taken whole.
  tape_of_fits    the view's rounds under the table's own entries have the table's shape, where K4's
                  two tests on the stretch pass (fitsAll, OnBytes/Desc/First/K4/Steps.lean;
                  plainStretchWith, OnBytes/Desc/First/FlStep.lean).
  **hearAt_returns**   nothing is owed in front; the two tests on the stretch; what the lookup
                  returned is there; and the premises of hear_returns
                  (Johnson/Desc/First/K4/Returns/Whole.lean) but the one on the tape's shape, which
                  tape_of_fits gives: at the plan (covers, shapeFits, PlanNums), at the state's
                  ledger (room, K3Hands), at the plan with the state's tokens laid in (HearPub), and
                  its two tests on values: hearAt returns the state with the ledger, what was heard
                  and "nothing owed" laid; the ledger still has room for the k slots that the
                  premise asked beyond k4Takes; nothing below its old next slot has turned; the next
                  slot stands k4Takes further; and HearLeft.

Limits. Those of Johnson/Desc/First/K4/Returns/Whole.lean stand here too. That the test which every
block's step makes on its rounds (roundsFit, Johnson/Desc/Block.lean) gives K4's two tests on the
stretch is not shown. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.Whole
import Johnson.Desc.First.K4.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 TableAt TableAsk)
open OnBytes.PscRun (Sized Filled)

/-- A message of field elements alone is taken whole. -/
theorem leading_all : ∀ l : List Fmt.ItemValue,
    (l.all fun x => match x with | .e _ => true | _ => false) = true →
      (leading l).length = l.length
  | [], _ => rfl
  | .e x :: l, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    show (E.ofTriple x :: leading l).length = _
    rw [List.length_cons, List.length_cons, leading_all l h.2]
  | .root _ :: _, h => by simp at h
  -- At the heads .f, .word and .answer the premise is false by its own text, as at .root. Lean
  -- takes the match without an alternative for them.

/-- **The view's rounds under the table's own entries have the table's shape**, where K4's two tests
on the stretch pass. -/
theorem tape_of_fits : ∀ (ds : List Rd) (rs : List Fmt.RoundView),
    fitsAll ds (ds.map entryOf) rs = true →
    Kit.plainStretchWith rowsTabled (ds.map entryOf) rs = true →
      TapeOf ds (paired rs (ds.map entryOf))
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | d :: ds, r :: rs, h, hp => by
    have h' : (d.fits (entryOf d) r && fitsAll ds (ds.map entryOf) rs) = true := h
    have hp' : (Kit.plainRoundWith rowsTabled (ds.map entryOf).isEmpty (entryOf d) r &&
      Kit.plainStretchWith rowsTabled (ds.map entryOf) rs) = true := hp
    rw [Bool.and_eq_true] at h' hp'
    refine ⟨⟨rfl, rfl, rfl, ?_, ?_⟩, tape_of_fits ds rs h'.2 hp'.2⟩
    · have a := h'.1
      have b := hp'.1
      unfold Rd.fits at a
      unfold Kit.plainRoundWith at b
      simp only [Bool.and_eq_true, beq_iff_eq] at a b
      show (leading r.vals).length = d.sent
      rw [leading_all _ b.2]
      exact a.1.1.1.1.2
    · have a := h'.1
      unfold Rd.fits at a
      simp only [Bool.and_eq_true, beq_iff_eq] at a
      show (r.drawn.elems.map E.ofTriple).length = d.drawn
      rw [List.length_map]
      exact a.1.1.2

variable {S : Type} (L : Seat S)

/-- **hearAt returns**: nothing is owed in front; the stretch passes K4's two
tests; what the lookup returned is there; and the premises of hear_returns at the state's own
parts, but the one on the tape's shape. Then hearAt returns the state with a ledger G, what was
heard and "nothing owed" laid; G has room for k more slots; nothing below the old next slot has
turned; the next slot stands k4Takes further; and HearLeft holds. -/
theorem hearAt_returns (p : Par) (s : S) (rs : List Fmt.RoundView) {fo : Forest.Heard} {k : Nat}
    {Z ztF : Array E} {ends : Array (Array E)} {iU3 : Nat} {tab : List TableAt}
    {laid : List (TableAsk × List (Nat × Nat))}
    (h0 : (L.owed s).isNone = true)
    (h1 : fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs = true)
    (h2 : Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs = true)
    (h3 : L.look s = some fo)
    (hc : covers p.P = true) (hs : shapeFits p.P fo = true)
    (hR : Room (L.fork s) (k4Takes p.P p.hp p.g + k)) (hN : PlanNums p.P p.hp p.g)
    (hK : K3Hands p.P fo (L.fork s) Z ztF ends)
    (hP : HearPub { p.P with tokv := L.tokv s } p.hp p.g fo ztF iU3 tab laid)
    (vM : ends.all (· == Z) = true)
    (vE : ∀ t₁ s0 eps t₂, TapeOf (rowsNorms p.P p.g) t₁ →
      paired rs (entries p.P p.hp p.g) =
        t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ → isZeroE eps = false) :
    ∃ o G, hearAt L p s rs = .ok (L.setOwed (L.setOwn (L.setFork s G) o) none) ∧ Room G k ∧
      Below (L.fork s) G ∧ G.next = (L.fork s).next + k4Takes p.P p.hp p.g ∧
      HearLeft { p.P with tokv := L.tokv s } p.hp p.g fo iU3 tab (L.fork s) G o := by
  obtain ⟨o, G, e, a1, a2, a3, a4⟩ := hear_returns { p.P with tokv := L.tokv s } p.hp p.g fo
    (F := L.fork s) (k := k) (t := paired rs (entries p.P p.hp p.g)) hc hs hR
    (tape_of_fits (rounds p.P p.hp p.g) rs h1 h2)
    ⟨hN.ns, hN.np, hN.no, hN.muV, hN.endT, hN.muH9, hN.muH29, hN.muH, hN.muH2, hN.ncl⟩
    ⟨hK.depth, hK.z, hK.ends, hK.zt, hK.ztSize, hK.cEnd⟩ hP vM vE
  refine ⟨o, G, ?_, a1, a2, a3, a4⟩
  unfold hearAt
  simp only [test, VerifiableInference.Desc.need, VerifiableInference.Desc.named, h0, h1, h2, h3, e,
    bind, Except.bind, pure, Except.pure, if_true]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.leading_all
#print axioms OnBytes.Desc.First.K4.Rt.tape_of_fits
#print axioms OnBytes.Desc.First.K4.Rt.hearAt_returns
