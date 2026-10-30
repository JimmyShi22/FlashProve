-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlaceOf.lean: kind K5: the record PlaceIs
(Johnson/Desc/First/Att/Claims/Place.lean), paid: a shape that shapeHid returns at the usual call
list has the four calls' kinds of table and lists.

Main names:
  `layCall_segs`: what layCall returns holds the lists that it was given.
  `place_of_hid`: shapeHid lid cf = ok (S, fs) and UsualCalls cf (Johnson/Road/Lane5AttLaid.lean)
    give PlaceIs S (callAt S 0) (callAt S 1) (callAt S 2) (callAt S 3). The proof's first half
    follows that of four_of_list (same file), which reads the kinds and the pieces and not the
    lists.
Limit: UsualCalls is no test of the verifier (Johnson/Road/Lane5AttLaid.lean says so of itself): the
verifier takes other call lists, and groups with two shifts; at another list this file says nothing.
So the limit "no test of the verifier asks it" of Johnson/Desc/First/Att/Claims/Place.lean has moved
from PlaceIs to UsualCalls; it has not gone.
Used of OnBytes and Johnson/Road: hid_calls, calls_of_shape, shsOf_one, mapM_cons_ok, layCall_parts,
callAt_of_list, refuse_ok; plain records and the planner's pure functions shape, layCall,
expandLine.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5AttLaid
import Johnson.Desc.First.Att.Claims.Place

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road
open OnBytes.Road.L5 (callAt UsualCalls)

/-- What layCall returns holds the lists that it was given. -/
theorem layCall_segs {cf : Cfg} {HA Sm : ℕ} {Tt : Array ℕ} {name : String} {kind : Table} {sh : ℕ}
    {segs : List Attention.Seg} {k : ACall} (h : layCall cf HA Sm Tt (name, kind, sh, segs) = Except.ok k) :
    k.segs = segs := by
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  have e := Except.ok.inj h
  subst e
  rfl

/-- **PlaceIs, paid**: at a shape that shapeHid returns at the usual call list. -/
theorem place_of_hid {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) (U : UsualCalls cf) :
    PlaceIs S (callAt S 0) (callAt S 1) (callAt S 2) (callAt S 3) := by
  obtain ⟨A, io, kbA, hA, eS, -⟩ := L5.hid_calls h
  obtain ⟨calls, hM, hc, -, hsz⟩ := L5.calls_of_shape hA
  obtain ⟨n0, n1, n2, n3, hL⟩ := U.lines
  rw [L5.shsOf_one hsz U.one, hL] at hM
  have hx : ([⟨n0, .kr, [.rm, .rd]⟩, ⟨n1, .kfd, [.fm, .fd]⟩, ⟨n2, .r16, [.wl, .ix]⟩,
      ⟨n3, .wh, [.wh]⟩] : List Line).flatMap (expandLine [cf.sh.getD 0 0]) =
      [(n0 ++ "", .kr, cf.sh.getD 0 0, [.rm, .rd]), (n1 ++ "", .kfd, cf.sh.getD 0 0, [.fm, .fd]),
        (n2, .r16, 0, [.wl, .ix]), (n3, .wh, 0, [.wh])] := rfl
  rw [hx] at hM
  obtain ⟨k0, r0, h0, hM0, rfl⟩ := L5.mapM_cons_ok hM
  obtain ⟨k1, r1, h1, hM1, rfl⟩ := L5.mapM_cons_ok hM0
  obtain ⟨k2, r2, h2, hM2, rfl⟩ := L5.mapM_cons_ok hM1
  obtain ⟨k3, r3, h3, hM3, rfl⟩ := L5.mapM_cons_ok hM2
  have hr : r3 = [] := by
    rw [List.mapM_nil] at hM3
    exact (Except.ok.inj hM3).symm
  subst hr
  have hT : S.calls.toList =
      [{ k0 with call := { k0.call with iota := io 0 } }, { k1 with call := { k1.call with iota := io 1 } },
        { k2 with call := { k2.call with iota := io 2 } },
        { k3 with call := { k3.call with iota := io 3 } }] := by
    rw [eS]
    show (A.calls.mapIdx _).toList = _
    rw [Array.toList_mapIdx, hc]
    simp [List.mapIdx_cons]
  have c0 : callAt S 0 = { k0 with call := { k0.call with iota := io 0 } } := by
    rw [L5.callAt_of_list hT]; rfl
  have c1 : callAt S 1 = { k1 with call := { k1.call with iota := io 1 } } := by
    rw [L5.callAt_of_list hT]; rfl
  have c2 : callAt S 2 = { k2 with call := { k2.call with iota := io 2 } } := by
    rw [L5.callAt_of_list hT]; rfl
  have c3 : callAt S 3 = { k3 with call := { k3.call with iota := io 3 } } := by
    rw [L5.callAt_of_list hT]; rfl
  have s0 : k0.segs = [.rm, .rd] := layCall_segs h0
  have s1 : k1.segs = [.fm, .fd] := layCall_segs h1
  have s2 : k2.segs = [.wl, .ix] := layCall_segs h2
  have s3 : k3.segs = [.wh] := layCall_segs h3
  rw [c0, c1, c2, c3]
  exact ⟨hT, (L5.layCall_parts h0).1, (L5.layCall_parts h1).1, (L5.layCall_parts h2).1,
    (L5.layCall_parts h3).1, s0, s1, s2, s3⟩

end K5Law
