-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05LeftOn.lean: kind K5: WHAT THE LOOKUP ON THE CALLS LEFT, CARRIED OVER THE
HEARING's LAY: from the lookups' sharp promise at the record in front (K3LeftAt: the ledger in hand
IS the one behind the lookup's hearing) to their promise in the form that stands at every later
record (K3LeftOn: the ledger in hand is LATER than that one, and sized) at the record behind the
lay. Both: Johnson/Top/H/K3LeftStatement.lean.

Why. The table of joints' row of a caller's block drops the public item left m and makes leftOn m;
what the two say is a Prop (Meaning.pubP). K5Fill.leftOn (Johnson/Desc/First/Att/K05T2.lean) asks
that step of the meaning's filling. Here it is paid where the two are filled by the lookups' two
promises.

Main names:
  `later_behind`: the ledger behind the kind's hearing is later than the one in front, in the
    lookups' sense (Fo.Later), and sized: from hear_below (Johnson/Desc/First/Att/K05HearBelow.lean)
    and hear_law_paid (Johnson/Desc/First/Att/K05Paid.lean).
  `leftOn_behind`: **K3LeftAt at s gives K3LeftOn at the record behind the lay**, at the seat of the
    lookup on the calls, at every shape, lm, first slot and condition Q on the ledger in front.
  `fill_leftOn`: so K5Fill's field holds at a meaning whose pubP at left m gives K3LeftAt and whose
    pubP at leftOn m follows from K3LeftOn.
Beside it: Johnson/Road/K4/LeftOnKept.lean [not seen by this
file's author] is said to hold the general half (leftOn_of_kept: kept by whatever leaves a later
ledger and turns nothing of what was heard): when it is in the library leftOn_behind is to be had
from it and later_behind.
Limits. That any block makes K3LeftAt true in front is not shown. No member is shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftStatement
import Johnson.Desc.First.Att.K05BehindLay
import Johnson.Desc.First.Att.K05Paid
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.OnPublicFiles (K3LeftAt K3LeftOn)
open VerifiableInference.Desc.K3 (sizedB seatCalls)

section
variable {s : First.S} {a : First.AttOwn} {own : Params.AttentionRounds} {rs : List Fmt.RoundView}
  {h : Heard} {G : Fork}

/-- **The ledger behind the kind's hearing is a later one, and sized.** -/
theorem later_behind (hh : hear own (a.F, rs, 0) = some (h, G, [], 0)) (hz : Sized a.F) :
    _root_.Fo.Later a.F G ∧ Sized G := by
  obtain ⟨zG, bl⟩ := hear_below hh hz
  obtain ⟨_, _, _, _, st, _⟩ := hear_law_paid hh hz
  refine ⟨⟨bl.1, bl.ns, fun j hj => ?_⟩, zG⟩
  obtain ⟨c1, c2, c3⟩ := st j _ _ ⟨hj, rfl, rfl⟩
  exact ⟨c1, c2, c3⟩

/-- **What the lookup on the calls left, behind the lay.** -/
theorem leftOn_behind {Cl : Type} (claim : Aff → Cl) (hS : Forest.Shape) (lm first : ℕ)
    (Qf : Fork → Prop) (e : s.here = .att a) (hh : hear own (a.F, rs, 0) = some (h, G, [], 0))
    (hz : s.fork?.any sizedB = true)
    (hL : K3LeftAt (seatCalls claim).fork (seatCalls claim).heard hS lm first Qf s) :
    K3LeftOn (seatCalls claim).fork (seatCalls claim).heard hS lm first Qf (behind s a h G) := by
  obtain ⟨F, F', g, rs', q, hn, K, hheard, hfork⟩ := hL
  have e1 : s.fork? = some F' := hfork
  rw [fork_front e] at e1 hz
  obtain rfl : a.F = F' := Option.some.inj e1
  have e2 : s.lookHeard? = some g := hheard
  rw [lookHeard_front e] at e2
  obtain ⟨hl, zG⟩ := later_behind hh (sized_of_B hz)
  exact ⟨F, a.F, G, g, rs', q, hn, K, e2, rfl, hl, zG.vp, zG.mf, zG.got⟩

end

/-- **K5Fill's field leftOn, at the lookups' two promises.** -/
theorem fill_leftOn {Pp W Cl : Type} (Mg : First.Meaning Pp W) (π : Pp) (m : ℕ) (claim : Aff → Cl)
    (own : Params.AttentionRounds) (hS : Forest.Shape) (lm first : ℕ) (Qf : Fork → Prop)
    (h1 : ∀ s, Mg.pubP (.left m) (π, s) →
      K3LeftAt (seatCalls claim).fork (seatCalls claim).heard hS lm first Qf s)
    (h2 : ∀ s, K3LeftOn (seatCalls claim).fork (seatCalls claim).heard hS lm first Qf s →
      Mg.pubP (.leftOn m) (π, s)) :
    ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) →
      s.fork?.any sizedB = true → Mg.pubP (.left m) (π, s) →
      Mg.pubP (.leftOn m) (π, behind s a h G) :=
  fun s _ _ _ _ e hh hz hp => h2 _ (leftOn_behind claim hS lm first Qf e hh hz (h1 s hp))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.later_behind
#print axioms VerifiableInference.Desc.First.Att.P.leftOn_behind
#print axioms VerifiableInference.Desc.First.Att.P.fill_leftOn
