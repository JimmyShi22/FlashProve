-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/K3/SiteOfView.lean: the kind "lookup" (K3): what a site of `lookSites`
(Honest/K3/Lot.lean) holds of the public record's place at its link and sort; and, where the
library's six statements hold at that link (`SixAt`, Johnson/AtFull/K3X/SixAt.lean), that its first
scalar and the two numbers of its shape are those of the library's written view. Two theorems; no
definition; nothing is evaluated.

Why. Three public tests on the frame's book (`bookFits`, `startsFit`, `placeFits`) read of a site
its place, five numbers of its face and its first scalar. That these tests accept at fifty written
records is `k3Fits_written` (AtFullSide/K14/RawK3Fits.lean; not imported here).
That the sites have the written numbers
is shown from here on.

What is shown.
  `site_at_record`: at every public part: where `lookAt` returns x at the site's link and sort:
  s.p.first is x.F.next; the pair (v, d) of the site's shape is that of what `shapeOwn` makes of
  x.calls at x.lid, and also of what it makes of these calls with their tables taken out.
  `site_of_view`: under `SixAt Z.p.X s.link`: s.p.first is `firstW`, and the pair is that of
  `shapeOwn` at the written calls `callsW` and the cap 28.

Hypotheses that remain. `hs`: the site. `hx`: the return of `lookAt`. `h6`: the six statements at
the site's link. No instance of these hypotheses is exhibited in this file; SixAtHead.lean beside it
has `h6` under the library's head at one named set of public files.

How the proof goes. `site_facts` (Honest/K3/Law/MemberSite.lean) gives the returns of `placeAt` and
`P.shape`; these unfold (Johnson/Desc/First/Look/LookKind.lean). `Shape.v` and `Shape.d` read
neither the calls nor the padding counts. With the tables taken out: the library's `all_of_shapeOwn`
(Johnson/AtFull/ProofRows/K3CallsOkHead.lean) and `shapeOwn_strip` (K3HeadRow.lean).

Why here. It stands over files under Johnson/AtFull/ and serves closed facts at the full size.

Users. ViewNumbers.lean beside it.

Limits. Numbers on public data. Nothing on a book, a sender, a run or a coin.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.AtFull.K3X.SixAt
import Johnson.AtFull.ProofRows.K3HeadRow
import Johnson.AtFull.ProofRows.K3CallsOkHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open OnBytes.Model (Call)
open VerifiableInference.Desc.First.Look (lookAt shapeOwn)
open Johnson.AtFull.ProofRows.K3 (strip stripS shapeOwn_strip all_of_shapeOwn)
open Johnson.AtFull.Lots.K3 (sortOf callsW firstW)
open Johnson.AtFull.K3X (SixAt)

/-- **What a site holds of the public record's place**: its first scalar is the ledger's next slot
there; the two numbers of its shape are those of what `shapeOwn` makes of the place's calls, with or
without their tables. -/
theorem site_at_record (Z : Pub) (s : Site) (hs : s ∈ lookSites Z)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : lookAt Z.p.X s.link s.digits = some x) :
    s.p.first = x.F.next ∧
      (shapeOwn x.calls x.lid).map (fun h => (h.v, h.d)) = some (s.shape.v, s.shape.d) ∧
      (shapeOwn (x.calls.map strip) x.lid).map (fun h => (h.v, h.d)) = some (s.shape.v, s.shape.d)
      := by
  unfold lookSites at hs
  obtain ⟨a, _, ha⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, f2, f3, f4, _⟩ := site_facts _ _ a s ha
  rw [← f3, ← f4] at f1
  unfold VerifiableInference.Desc.First.Look.placeAt at f1
  rw [hx] at f1
  have hp := (Option.some.inj f1).symm
  have h2 := f2
  rw [hp] at h2
  unfold VerifiableInference.Desc.First.Look.P.shape at h2
  obtain ⟨h0, e0, e1⟩ := Option.bind_eq_some_iff.1 h2
  have e0' : shapeOwn x.calls x.lid = some h0 := e0
  have hv : s.shape.v = h0.v ∧ s.shape.d = h0.d := by
    split at e1
    · rw [← Option.some.inj e1]
      exact ⟨rfl, rfl⟩
    · cases e1
  refine ⟨by rw [hp]; rfl, ?_, ?_⟩
  · rw [e0', hv.1, hv.2]
    rfl
  · rw [shapeOwn_strip (all_of_shapeOwn e0') x.lid, e0', hv.1, hv.2]
    rfl

/-- **Under the library's six statements at the site's link (`SixAt`): a site's first scalar and its
shape's two numbers are those of the written view at its link and sort.** -/
theorem site_of_view (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (h6 : SixAt Z.p.X s.link) :
    s.p.first = firstW (sortOf s.link) s.digits ∧
      (shapeOwn (callsW (sortOf s.link) s.digits) 28).map (fun h => (h.v, h.d)) =
        some (s.shape.v, s.shape.d) := by
  cases hd : s.digits with
  | false =>
    obtain ⟨x, hx, hw⟩ := h6.calls
    obtain ⟨g1, _, g3⟩ := site_at_record Z s hs x (by rw [hd]; exact hx)
    have e3 : x.calls.map strip = callsW (sortOf s.link) false := congrArg (·.2.2.1) hw
    have e5 : x.lid = 28 := congrArg (·.2.2.2.2.1) hw
    have e6 : x.F.next = firstW (sortOf s.link) false := congrArg (·.2.2.2.2.2.1) hw
    exact ⟨g1.trans e6, by rw [← e3, ← e5]; exact g3⟩
  | true =>
    obtain ⟨x, hx, hw⟩ := h6.digits
    obtain ⟨g1, g2, _⟩ := site_at_record Z s hs x (by rw [hd]; exact hx)
    have e3 : x.calls = callsW (sortOf s.link) true := congrArg (·.2.2.1) hw
    have e5 : x.lid = 28 := congrArg (·.2.2.2.2.1) hw
    have e6 : x.F.next = firstW (sortOf s.link) true := congrArg (·.2.2.2.2.2.1) hw
    exact ⟨g1.trans e6, by rw [← e3, ← e5]; exact g2⟩

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.site_at_record
#print axioms AtFullSide.Honest.K3.site_of_view
