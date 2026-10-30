-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoHearParts.lean: the attention sub-proof: what the routine that hears
the first messages lays into
its record.

Attention.hear runs the lookup's Forest.pad, then Attention.scores, Attention.divide and
Attention.attain, and returns a record of what these returned.

 - hear_parts: a run of hear that returns f from (F, c) is a run of these four, each from where the
   one before ended, the first from (F, c), the last to hear's own end; what they return are f's
   fields.
 - pcKey, unitKey: of a plane claim, of a unit (call, segment): the call's number, the segment, the
   segment's pieces with their weights at the call's key point.
 - planeUnit_ok, planeUnits_ok: the plane claims that planeUnits adds are the units', in order.
 - cutA, cutB (OnBytes/Tie/Pv/Lookup/Ends/FoAttBDefs.lean): where scoreUnit cuts the inner point.
 - ScoreIs S zk u k: what scoreUnit lays into the record k of the unit u: the call's number, the
   segment, the pieces; the inner point has the length that the cut needs; the parts zs, zi, zj are
   the named stretches of the inner point.
 - scoreUnit_ok, scoreUnits_ok: the same for scoreUnits: plane claims and records, in order.
 - scores_ok: so for Attention.scores, from the empty lists.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttPub
import OnBytes.Model.Attention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

/-- A run of hear, part by part. -/
theorem hear_parts (P : Attention.Plan) (F G : Fork) (c c' : Ctx) (f : Attention.First)
    (h : Attention.hear P F c = .ok ((f, G), c')) :
    ∃ (F1 F2 F3 : Fork) (c1 c2 c3 : Ctx),
      Forest.pad (P.S.calls.map (·.call)) P.fs.pub P.lid F c = .ok ((f.g, F1), c1) ∧
      Attention.scores P.S f.g.zk F1 c1 = .ok (((f.planes, f.scores), F2), c2) ∧
      Attention.divide P.S f.g.zk F2 c2 = .ok ((f.d, F3), c3) ∧
      Attention.attain P.S F3 c3 = .ok ((f.x, G), c') := by
  unfold Attention.hear at h
  rw [bind_ok] at h
  obtain ⟨g, F1, c1, h1, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨⟨planes, scores⟩, F2, c2, h2, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨d, F3, c3, h3, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨x, F4, c4, h4, h⟩ := h
  have e := (pure_ok _ _ _ _).1 h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨F1, F2, F3, c1, c2, c3, h1, h2, h3, h4⟩

/-- Of a plane claim: the call's number, the segment, the pieces. -/
def pcKey (p : PlaneClaim) : ℕ × Attention.Seg × Array PW := (p.call, p.seg, p.pw)

/-- Of a unit: the call's number, the segment, the segment's pieces at the call's key point. -/
def unitKey (zk : Array (Array E)) (u : ℕ × ACall × Attention.Seg) :
    ℕ × Attention.Seg × Array PW := (u.1, u.2.2, pieces u.2.1 (zk.getD u.1 #[]) u.2.2)

theorem planeUnit_ok (S : Attention.Shape) (zk : Array (Array E)) (u : ℕ × ACall × Attention.Seg)
    (F G : Fork) (c c' : Ctx) (p : PlaneClaim)
    (h : planeUnit S zk u F c = .ok ((p, G), c')) : pcKey p = unitKey zk u := by
  unfold planeUnit at h
  rw [bind_ok] at h
  obtain ⟨s0, F1, c1, _, h⟩ := h
  have e := congrArg (fun y : (PlaneClaim × Fork) × Ctx => y.1.1) ((pure_ok _ _ _ _).1 h)
  dsimp only at e
  rw [e]
  unfold pcKey unitKey
  rfl

theorem planeUnits_ok (S : Attention.Shape) (zk : Array (Array E)) :
    ∀ (us : List (ℕ × ACall × Attention.Seg)) (planes out : Array PlaneClaim) (F G : Fork)
      (c c' : Ctx), planeUnits S zk us planes F c = .ok ((out, G), c') →
      out.toList.map pcKey = planes.toList.map pcKey ++ us.map (unitKey zk)
  | [], planes, out, F, G, c, c', h => by
    unfold planeUnits at h
    have e := (pure_ok _ _ _ _).1 h
    obtain ⟨⟨rfl, _⟩, _⟩ := by simpa [Prod.ext_iff] using e
    simp
  | u :: us, planes, out, F, G, c, c', h => by
    unfold planeUnits at h
    rw [bind_ok] at h
    obtain ⟨p, F1, c1, h1, h⟩ := h
    rw [planeUnits_ok S zk us _ out F1 G c1 c' h, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, planeUnit_ok S zk u F F1 c c1 p h1, List.map_cons,
      List.append_assoc]
    rfl

/-- What scoreUnit lays into the record of a unit. -/
structure ScoreIs (S : Attention.Shape) (zk : Array (Array E)) (u : ℕ × ACall × Attention.Seg)
    (k : Score) : Prop where
  call : k.call = u.1
  seg : k.seg = u.2.2
  pw : k.pw = pieces u.2.1 (zk.getD u.1 #[]) u.2.2
  size : (inner S (zk.getD u.1 #[]) u.2.2).size = cutB S u.2.2 + 2 * S.cf.lB
  zs : k.zs = if u.2.2 == Attention.Seg.fm then
    (inner S (zk.getD u.1 #[]) u.2.2).extract (cutA S) (cutB S u.2.2) else #[]
  zi : k.zi = (inner S (zk.getD u.1 #[]) u.2.2).extract (cutB S u.2.2) (cutB S u.2.2 + S.cf.lB)
  zj : k.zj = (inner S (zk.getD u.1 #[]) u.2.2).extract (cutB S u.2.2 + S.cf.lB)
    (cutB S u.2.2 + 2 * S.cf.lB)

theorem scoreUnit_ok (S : Attention.Shape) (zk : Array (Array E)) (claim : ℕ)
    (u : ℕ × ACall × Attention.Seg) (F G : Fork) (c c' : Ctx) (x : PlaneClaim × Score)
    (h : scoreUnit S zk claim u F c = .ok ((x, G), c')) :
    pcKey x.1 = unitKey zk u ∧ ScoreIs S zk u x.2 := by
  unfold scoreUnit at h
  dsimp only at h
  rw [bind_ok] at h
  obtain ⟨_, F0, c0, h0, h⟩ := h
  obtain ⟨hm, _⟩ := (must_ok _ _ _ _).1 h0
  rw [bind_ok] at h
  obtain ⟨s0, F1, c1, _, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨sc, F2, c2, _, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨sc', F3, c3, _, h⟩ := h
  have e := congrArg (fun y : ((PlaneClaim × Score) × Fork) × Ctx => y.1.1) ((pure_ok _ _ _ _).1 h)
  dsimp only at e
  rw [e]
  refine ⟨by unfold pcKey unitKey; rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  exact beq_iff_eq.mp hm

theorem scoreUnits_ok (S : Attention.Shape) (zk : Array (Array E)) :
    ∀ (us : List (ℕ × ACall × Attention.Seg)) (planes : Array PlaneClaim) (stored : Array Score)
      (out : Array PlaneClaim × Array Score) (F G : Fork) (c c' : Ctx),
      scoreUnits S zk us planes stored F c = .ok ((out, G), c') →
      out.1.toList.map pcKey = planes.toList.map pcKey ++ us.map (unitKey zk) ∧
        ∃ ks, out.2.toList = stored.toList ++ ks ∧ List.Forall₂ (ScoreIs S zk) us ks
  | [], planes, stored, out, F, G, c, c', h => by
    unfold scoreUnits at h
    have e := congrArg (fun y : ((Array PlaneClaim × Array Score) × Fork) × Ctx => y.1.1)
      ((pure_ok _ _ _ _).1 h)
    dsimp only at e
    rw [e]
    exact ⟨by simp, [], by simp, List.Forall₂.nil⟩
  | u :: us, planes, stored, out, F, G, c, c', h => by
    unfold scoreUnits at h
    rw [bind_ok] at h
    obtain ⟨x, F1, c1, h1, h⟩ := h
    obtain ⟨a1, a2⟩ := scoreUnit_ok S zk _ u F F1 c c1 x h1
    obtain ⟨b1, ks, b2, b3⟩ := scoreUnits_ok S zk us _ _ out F1 G c1 c' h
    refine ⟨?_, x.2 :: ks, ?_, List.Forall₂.cons a2 b3⟩
    · rw [b1, Array.toList_push, List.map_append, List.map_cons, List.map_nil, a1, List.map_cons,
        List.append_assoc]
      rfl
    · rw [b2, Array.toList_push, List.append_assoc]
      rfl

/-- What Attention.scores returns. -/
theorem scores_ok (S : Attention.Shape) (zk : Array (Array E))
    (out : Array PlaneClaim × Array Score) (F G : Fork) (c c' : Ctx)
    (h : Attention.scores S zk F c = .ok ((out, G), c')) :
    out.1.toList.map pcKey =
      (unitsOf S Table.kr [Attention.Seg.rm, Attention.Seg.rd]).map (unitKey zk) ++
        (unitsOf S Table.kfd [Attention.Seg.fm, Attention.Seg.fd]).map (unitKey zk) ∧
      List.Forall₂ (ScoreIs S zk) (unitsOf S Table.kfd [Attention.Seg.fm, Attention.Seg.fd])
        out.2.toList := by
  unfold Attention.scores at h
  rw [bind_ok] at h
  obtain ⟨planes, F1, c1, h1, h⟩ := h
  have a := planeUnits_ok S zk _ _ planes F F1 c c1 h1
  obtain ⟨b1, ks, b2, b3⟩ := scoreUnits_ok S zk _ _ _ out F1 G c1 c' h
  refine ⟨by rw [b1, a]; simp, ?_⟩
  rw [b2]
  simpa using b3

end Fo
