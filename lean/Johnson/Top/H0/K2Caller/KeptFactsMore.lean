-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptFactsMore.lean: the code switch: TWO MORE PREMISES OF
KeptFactsOf.lean's keptFacts_of, FROM WHAT LIES.
  hT_of_next   the premise hT (the typed new list has the target's kept shape at the member's place)
               from the field «next» of the law's public clauses in front (K2Hands/TieLight.lean's
               FrontAtL; the same words in TopAt.lean's Pub12), which binds its two bounds in
               the other order. The bound that is wanted first comes from the program's test on the
               public sizes: the target has as many kept shapes as the old group has kept members
               (Johnson/Top/H/SwitchMapsCheck.lean's check_facts)
  shown_of_promise   the premise hshown (every leaf of the typed kept member is shown) from the
               table's own «shown» at the seat (Johnson/Desc/Sound/MeaningSig.lean's shownJT), along
               Alike. By shown_move (Sound/PinMove.lean)
ALSO, BY A CALL AND NO LEMMA: «the carried rows have two mask rows» (a premise of slot_word and of
all that stands on it) is check_facts' first clause.
LIMITS. Two short carriages. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.KeptFactsOf
import Johnson.Top.H.SwitchMapsCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (ShownAt Mem Alike SitsAt shownJT shown_move)

variable {r : SwRow}

theorem hT_of_next (fx : _root_.Tw.K2.Front)
    (hchk : switchTargetCheck (K2.skelOf fx) fx.f.rows fx.T = true) (a : ℕ)
    (hi : a < (switchKept fx.f.rows).size)
    (next : ∀ i (hi : i < fx.T.kept.size), ∃ h : 1 + i < r.l.length,
      (r.l.get ⟨1 + i, h⟩).1 = fx.T.kept[i].shape)
    (ho : 1 + a < r.l.length) :
    ∃ h2 : a < fx.T.kept.size, (r.l.get ⟨_, ho⟩).1 = fx.T.kept[a].shape := by
  have h2 : a < fx.T.kept.size := by
    rw [(check_facts hchk).2.2.2.2.2.2.1]
    exact hi
  obtain ⟨_, e⟩ := next a h2
  exact ⟨h2, e⟩

theorem shown_of_promise {Xi : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
    (ms : List Mem) (q : ℕ × ℕ) (y : Strs) (hs : shownJT r.cs G ms q.1 q.2 y) (x : Mem)
    (hx : x ∈ ms) (hq : SitsAt x q.1 q.2) (i : Fin r.lo.length)
    (hA : Alike x ⟨⟨r.lo, seat⟩, i⟩) : ShownAt G r.cs r.lo seat y i :=
  (shown_move r.cs G x ⟨⟨r.lo, seat⟩, i⟩ hA y).1 (hs.2 x hx hq)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hT_of_next
#print axioms VerifiableInference.Desc.First.K2Caller.shown_of_promise
