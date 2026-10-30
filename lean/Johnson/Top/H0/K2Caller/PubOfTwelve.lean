-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PubOfTwelve.lean: the twelve public clauses that the code switch's law at a
place takes as one structure (`Pub12`, TopAt.lean), at the written frame with the place's own
numbers (`placeFrame`, K2Hands/FrontB2.lean), from the one test on the front. One
theorem; it calls `front_twelve` and orders its clauses.

  `pub12_of_twelve`: premises: the frame at a written front x₀ is W₀; x₀'s codes are the typed
     entry r's; `frontPubB` says yes at x₀; the place's numbers of the kept old messages differ;
     `Tied` holds at x's own announcements; `frontB2` says yes at x.
  `nums_of_twelve`: from the same: how many messages stand in front of x, the number of the group
     that the switch leads into, and how many rows that group has.
Limits: those of FrontB2.lean. Nothing on soundness.

-/
import Johnson.Top.H0.K2Caller.TopAt
import Johnson.Top.H0.K2Hands.FrontB2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes
open VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

theorem pub12_of_twelve {r : SwRow} {W₀ : SwitchFrame} {x₀ x : _root_.Tw.K2.Front}
    {grp rows n0 : ℕ} {olds : List ℕ} (h0 : K2.frameAt x₀ = some W₀) (hcs : x₀.st.codes = r.cs)
    (hb : frontPubB r.l.length x₀ = true) (hnd : olds.Nodup)
    (ht : Tied r.l (switchNotices x.T x.others))
    (h : frontB2 x₀ W₀ grp rows n0 olds x = true) :
    Pub12 (r := r) (placeFrame W₀ n0 olds) x := by
  obtain ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩, -⟩ :=
    front_twelve h0 hcs hb hnd ht h
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩

theorem nums_of_twelve {r : SwRow} {W₀ : SwitchFrame} {x₀ x : _root_.Tw.K2.Front}
    {grp rows n0 : ℕ} {olds : List ℕ} (h0 : K2.frameAt x₀ = some W₀) (hcs : x₀.st.codes = r.cs)
    (hb : frontPubB r.l.length x₀ = true) (hnd : olds.Nodup)
    (ht : Tied r.l (switchNotices x.T x.others))
    (h : frontB2 x₀ W₀ grp rows n0 olds x = true) :
    x.st.oracles.size = n0 ∧ x.f.group = grp ∧
      ∃ G, x.st.groups[grp]? = some G ∧ G.rows.size = rows :=
  (front_twelve h0 hcs hb hnd ht h).2

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.pub12_of_twelve
