-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TableAtConst.lean: THE TABLE's TESTS THAT LEAN's KERNEL HAS EVALUATED AT THE 25
    NUMBERS OF THE CODE SWITCH, CARRIED TO "EVERY PLACE OF THE KIND IN THE WRITTEN FULL LIST". Seven
    theorems. A law file: no sub-protocol imports it.

Why. The closed facts on the table stand as one Boolean over a written list of 25 pairs (`switches
    24`, Johnson/Top/H0/K2Ties/Table.lean) or as three theorems by the sort of place
    (Johnson/P1K2R/PinsBehind.lean). What is owed at a place is asked at "a number i at which the
    list of places has a place of the kind K2", with the carried claim's segment `mOf i`
    (Johnson/P1K2R/SitsAtConst.lean).

What is said, for i, a with (flatPlacesOf linksFull true)[i]? = some a and a.kind = K2.
  `mem_switches`: (i, mOf i + 1) is one of the 25 pairs.
  `said_at`: the field said of the shorter list (`said_full`, Johnson/Top/H0/K2Ties/PubBehind.lean).
      `pinOpen_at`: the index masks' pin is open in front (`pinOpen_full`, FenceOf.lean).
      `riders_at`: four sorts alone stay open across the place, the parts from mOf i + 1 on
      (`riders_full`, Table.lean).
  `pins_atB`: the pins that are open in front and behind (`pins_at`, `pins_head`, `pins_finish`).
  `hsam_at`, `hidx_at`: THE FIELDS hsam AND hidx of what is owed at a place, at any numbers N, at
      the written full list: by `sampled_behind`, `sampled_front` and
      `HashBuild.linksW_full`, `placesW_full` (Johnson/Desc/AtSeats/HearAtFifty.lean: one written
      list under two names).

Limits. Closed facts on the written table: they say nothing of a run. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.SitsAtConst
import Johnson.P1K2R.PinsBehind
import Johnson.Desc.AtSeats.HearAtFifty
import Johnson.Top.H0.K2Ties.PubBehind
import Johnson.Top.H0.K2Ties.FenceOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (Numbers Item flatPlacesOf sampledIn)
open VerifiableInference.Desc.First.K2Ties (switches saidBehindB said_full pinOpenB pinOpen_full
    ridersB riders_full)
open IM (openAt linksW placesW)

variable {i : ℕ} {a : Place}

theorem mem_switches (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind = KindName.K2) :
    (i, mOf i + 1) ∈ switches 24 := by
  unfold switches
  rcases k2_spots i a ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · rw [mOf_link l a1 a24]
    refine List.mem_append_left _ (List.mem_map.2 ⟨l - 1, List.mem_range.2 (by omega), ?_⟩)
    exact Prod.ext (by show 14 * (l - 1 + 1) + 2 = 14 * l + 0 + 2; omega) rfl
  · exact List.mem_append_right _ (List.mem_cons_self ..)
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem said_at (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind = KindName.K2) :
    saidBehindB linksFull (flatPlacesOf linksFull true) i = true :=
  List.all_eq_true.1 said_full _ (mem_switches ha hk)

theorem pinOpen_at (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind = KindName.K2) :
    pinOpenB linksFull (flatPlacesOf linksFull true) i = true :=
  List.all_eq_true.1 pinOpen_full _ (mem_switches ha hk)

theorem riders_at (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind = KindName.K2) :
    ridersB linksFull (flatPlacesOf linksFull true) i (mOf i + 1) = true :=
  List.all_eq_true.1 riders_full _ (mem_switches ha hk)

theorem pins_atB (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind = KindName.K2) :
    pinsB i [.pinI, .pinKept (mOf i)] [.pinI, .pin (mOf i + 1) 0] = true := by
  rcases k2_spots i a ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · rw [mOf_link l a1 a24, show l - 1 + 1 = l by omega]
    exact pins_at a1 a24
  · exact pins_head
  · exact pins_finish

/-- **The field hsam.** -/
theorem hsam_at (N : Numbers) (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind =
    KindName.K2) : sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (i + 1)) = N.index ::
    N.sent (mOf i + 1) 0 := by
  have h := sampled_behind N (pins_atB ha hk)
  rwa [HashBuild.linksW_full, HashBuild.placesW_full] at h

/-- **The field hidx.** -/
theorem hidx_at (N : Numbers) (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind =
    KindName.K2) : N.index ∈ sampledIn N (openAt linksFull (flatPlacesOf linksFull true) i) := by
  have h := sampled_front N (pins_atB ha hk)
  rw [HashBuild.linksW_full, HashBuild.placesW_full] at h
  rw [h]
  exact List.mem_cons_self ..

end P1K2

#print axioms P1K2.mem_switches
#print axioms P1K2.said_at
#print axioms P1K2.pinOpen_at
#print axioms P1K2.riders_at
#print axioms P1K2.pins_atB
#print axioms P1K2.hsam_at
#print axioms P1K2.hidx_at
