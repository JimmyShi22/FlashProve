-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FirstCall.lean: a segment that the first line of the head's list of lookup
calls names belongs to call number 0.

What the file holds.
  callsFrom_head   the first call that callsFrom returns is placed from the first line's segments.
  callNo_first     **where the head's layout has the calls that callsOf returns, and the first line
                   in use names the segment n: Head.callNo L n = some 0.**
Why. The program `verify-on-bytes` takes the numbers of two calls by their segments' names, "NF" and
"HD0" (OnBytes/Model/HeadHeard.lean: hear). The head's seat lays both numbers 0
(Johnson/Stored/HeadSeat.lean: heardOf). The two agree where the first line names both segments.

On what it rests. Johnson/Road/HeadFound.lean: lineSegs_names (what lineSegs returns for a line has
the line's names, in order) and place_names (a placed call's segments have the names that were to
be placed). That file shows that every segment is found under its name at its own call
(found_of_layout); it does not say which line makes which call: that is what is added here, for the
first line.

What it does not give. Nothing on soundness. Which lines are in use is a premise here: for the
goals' scope see Johnson/Goal/Meaning/HeadCallsScope.lean.

-/
import OnBytes.Model.HeadHeard
import Johnson.Road.HeadFound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.FirstCall

open OnBytes.Model (SegAsk CallD place)
open OnBytes.Model.Head (Shape HL lineSegs callsFrom callsOf callLines callNo segments keyFloor)

theorem callsFrom_head {sd : List (String × String × Nat)} {fl : Nat} {name kind s : String}
    {ss : List String} {rest : List (List String)} {names seen : List String} {cs : List CallD}
    {seen' : List String}
    (h : callsFrom sd fl ((name :: kind :: s :: ss) :: rest) names seen = some (cs, seen')) :
    ∃ asks r, cs = place name kind asks fl :: r ∧ asks.map (·.1) = s :: ss := by
  rw [callsFrom] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i asks seen2 hl
      obtain ⟨r, -, e⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact ⟨asks, r.1, rfl,
        (OnBytes.Road.Hd.lineSegs_names sd kind (s :: ss) seen (asks, seen2) hl).1⟩

/-- **A segment of the first line belongs to call number 0.** -/
theorem callNo_first {h : Shape} {L : HL} {cs : List CallD} (hc : callsOf h L = .ok cs)
    (hL : L.calls = cs.toArray) {name kind s : String} {ss : List String}
    {rest : List (List String)} (hl : callLines h = (name :: kind :: s :: ss) :: rest) {n : String}
    (hn : n ∈ s :: ss) : callNo L n = some 0 := by
  unfold callsOf at hc
  rw [hl] at hc
  obtain ⟨-, hc⟩ := OnBytes.Road.Hd.ok_of_needed hc
  dsimp only at hc
  split at hc
  · cases hc
  · rename_i calls seen hf
    obtain ⟨-, hc⟩ := OnBytes.Road.Hd.ok_of_needed hc
    cases hc
    obtain ⟨asks, r, rfl, ha⟩ := callsFrom_head hf
    have hm : n ∈ (place name kind asks (keyFloor h - h.lt)).segs.map (·.name) := by
      rw [OnBytes.Road.Hd.place_names, ha]
      exact hn
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
    have hp : ((place name kind asks (keyFloor h - h.lt)).seg? g.name).isSome = true := by
      unfold CallD.seg?
      rw [List.find?_isSome]
      exact ⟨g, hg, by simp⟩
    unfold callNo
    rw [hL]
    simp [List.findIdx?_cons, hp]

end VerifiableInference.Desc.Kinds.Head.Law.FirstCall

#print axioms VerifiableInference.Desc.Kinds.Head.Law.FirstCall.callNo_first
