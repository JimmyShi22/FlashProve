-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K2R/PinsBehind.lean (over Johnson/IMR/TableW.lean):
code switching (K2): WHICH PINS ARE OPEN
AROUND A SWITCH, AT THE WRITTEN LIST OF PLACES: closed facts by Lean's kernel; and so which
tenants the table of joints' promise speaks of there. NO BLOCK IMPORTS THIS FILE.
  pinsB k front behind   the open pins at border k are «front», at border k + 1 «behind»
  pins_links     at all 23 links' first places (k = 14 l + 2, 1 ≤ l < 24): in front [pinI, pinKept
                 (l - 1)], behind [pinI, pin l 0]
  pins_head · pins_finish   at 339: [pinI, pinKept 23] and [pinI, pin 24 0] · at 353: [pinI,
                            pinKept 24] and [pinI, pin 25 0]
  pins_wrong     a negative test: with the kept pin left out in front the test rejects
  pins_at        the test at one link
  sampled_front · sampled_behind   so sampledIn N ‹open in front› = N.index :: N.keptOf (m - 1)
                                   and sampledIn N ‹open behind› = N.index :: N.sent m 0 (by
                                   sampledIn_of_filter)
On the table and the written list alone. No soundness is claimed.
-/
import Johnson.IMR.TableW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open VerifiableInference.Desc.First (Numbers Item sampledIn sampledIn_of_filter)
open IM (openAt linksW placesW)

/-- The open pins at the two borders of the sub-protocol number k. -/
def pinsB (k : Nat) (front behind : List Item) : Bool :=
  decide ((openAt linksW placesW k).filter Item.isPin = front) &&
    decide ((openAt linksW placesW (k + 1)).filter Item.isPin = behind)

set_option maxRecDepth 1000000 in
theorem pins_links : ((List.range' 1 23).all fun l =>
    pinsB (14 * l + 2) [.pinI, .pinKept (l - 1)] [.pinI, .pin l 0]) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pins_head : pinsB 339 [.pinI, .pinKept 23] [.pinI, .pin 24 0] = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pins_finish : pinsB 353 [.pinI, .pinKept 24] [.pinI, .pin 25 0] = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pins_wrong : pinsB 339 [.pinI] [.pinI, .pin 24 0] = false := by decide +kernel

theorem pins_at {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    pinsB (14 * l + 2) [.pinI, .pinKept (l - 1)] [.pinI, .pin l 0] = true :=
  List.all_eq_true.1 pins_links l (List.mem_range'_1.2 ⟨h1, by omega⟩)

theorem sampled_front (N : Numbers) {k m : Nat} {behind : List Item}
    (h : pinsB k [.pinI, .pinKept m] behind = true) :
    sampledIn N (openAt linksW placesW k) = N.index :: N.keptOf m := by
  unfold pinsB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [sampledIn_of_filter N [.pinI, .pinKept m] _ (by rw [h.1]; rfl)]
  simp [sampledIn]

theorem sampled_behind (N : Numbers) {k m : Nat} {front : List Item}
    (h : pinsB k front [.pinI, .pin m 0] = true) :
    sampledIn N (openAt linksW placesW (k + 1)) = N.index :: N.sent m 0 := by
  unfold pinsB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rw [sampledIn_of_filter N [.pinI, .pin m 0] _ (by rw [h.2]; rfl)]
  simp [sampledIn]

end P1K2

#print axioms P1K2.pins_links
#print axioms P1K2.pins_head
#print axioms P1K2.pins_finish
#print axioms P1K2.sampled_front
#print axioms P1K2.sampled_behind
