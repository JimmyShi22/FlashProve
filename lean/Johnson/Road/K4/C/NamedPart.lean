-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/NamedPart.lean: CONDITIONAL.

Not shown here. THAT THE VALUES WHICH THE HONEST SIDE HAS HEARD ARE THE VERIFIER's: NamedTie is a
hypothesis: nine ties for the lists' ten names ("Y" and "rt" share one). That pointsOf returns. No
example is known. No property is claimed.

THE POINTS THAT THE HONEST SIDE LISTS UNDER THE VERIFIER's NAMES STAND IN THE VERIFIER's LIST. The
honest side of the sub-protocol K4 lists the points at which the tables of the reads are taken
(namedPts, Johnson/Desc/K4/Honest/Front.lean), leaving out a point that is not yet whole; the
verifier lists all (pointsOf, OnBytes/Model/Layer.lean). Johnson/Road/K4/C/Reads.lean and what
stands over it ask PtsPart of the two lists. Here: PtsPart from nine equations, each asked only
where the honest side lists the point.

  part_of_mem    PtsPart where each member of the first list is found in the second under its name.
  mem_last, mem_full   the members of the two sorts of stretch in namedPts.
  points_open    pointsOf's list, written out.
  NamedTie       the nine ties.
  named_part     PtsPart (namedPts Q p) pts.
-/
import Johnson.Road.K4.C.Cells
import Johnson.Desc.K4.Honest.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Heard pointsOf)
open OnBytes.Desc.First.K4.Honest (K4Pub Pts ztOf namedPts)

/-- PtsPart where each member of the first list is found in the second under its name. -/
theorem part_of_mem {l pts : List (String × Array E)}
    (h : ∀ q ∈ l, (pts.find? fun x => x.1 == q.1) = some q) : PtsPart l pts := by
  intro n q hq
  have hm := List.mem_of_find?_eq_some hq
  have hn : q.1 = n := by
    have h1 := List.find?_some hq
    simpa using h1
  rw [← hn]
  exact h q hm

/-- A member of a stretch «the last la coordinates of z, if z is not empty». -/
theorem mem_last {la : ℕ} {n : String} {z : Array E} {q : String × Array E}
    (h : q ∈ (match (lastOf z la).toOption with
      | some x => if z.isEmpty then [] else [(n, x)]
      | none => [])) :
    z.isEmpty = false ∧ ∃ x, (lastOf z la).toOption = some x ∧ q = (n, x) := by
  cases hx : (lastOf z la).toOption with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    cases he : z.isEmpty with
    | true =>
      simp [he] at h
    | false =>
      simp [he] at h
      exact ⟨rfl, x, rfl, h⟩

/-- A member of a stretch «z, if it has k coordinates and k is not 0». -/
theorem mem_full {n : String} {k : ℕ} {z : Array E} {q : String × Array E}
    (h : q ∈ (if (z.size == k && k != 0) = true then [(n, z)] else [])) :
    z.size = k ∧ k ≠ 0 ∧ q = (n, z) := by
  split at h
  · rename_i c
    rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at c
    exact ⟨c.1, c.2, List.mem_singleton.mp h⟩
  · cases h

/-- **pointsOf's list, written out.** -/
theorem points_open {y : Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) :
    ∃ Z zv za routed, (lastOf H.fo.zx y.h.la).toOption = some Z ∧
      (lastOf H.wpl.r y.h.la).toOption = some zv ∧ (lastOf hd.r y.h.la).toOption = some za ∧
      (match hd2 with
        | some o => ((lastOf o.r y.h.la).toOption).map fun z => [("Z_b", z)]
        | none => some []) = some routed ∧
      pts = ([("Z", Z), ("zt", H.ztF), ("Z_V", zv), ("P_V", H.PV), ("Z_E", H.ZE),
        ("r_tV", H.tV.r), ("Z_a", za)] ++
        (match H.tT with
          | some tT => [("Y", longPoint (Z.extract 0 y.ls) tT.r), ("rt", tT.r)]
          | none => [])) ++ routed := by
  unfold pointsOf at h
  dsimp only at h
  obtain ⟨Z, hZ, h⟩ := Option.bind_eq_some_iff.mp h
  cases hd2 with
  | none =>
    obtain ⟨routed, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨zv, hzv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨za, hza, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨Z, zv, za, routed, hZ, hzv, hza, hr, (Option.some.inj h).symm⟩
  | some o2 =>
    obtain ⟨routed, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨zv, hzv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨za, hza, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨Z, zv, za, routed, hZ, hzv, hza, hr, (Option.some.inj h).symm⟩

/-- **The nine ties**: each value that the honest side has heard is the verifier's, asked where the
honest side lists the point. This defines a hypothesis; the definition claims nothing. -/
structure NamedTie (Q : K4Pub) (p : Pts) (H : Heard) (hd : Level) (hd2 : Option Level) : Prop where
  /-- the lookup's point -/
  zx : p.fo.zx = H.fo.zx
  /-- the lookup's token point -/
  zt : (ztOf Q p).size = Q.P.y.h.lt → Q.P.y.h.lt ≠ 0 → ztOf Q p = H.ztF
  /-- the squares' point -/
  r6 : p.r6.isEmpty = false → p.r6 = H.wpl.r
  /-- the norms' token point -/
  PV : p.PV.size = Q.P.y.h.lt → Q.P.y.h.lt ≠ 0 → p.PV = H.PV
  /-- the embedding's point -/
  ZE : p.ZE.size = Q.P.y.h.la → Q.P.y.h.la ≠ 0 → p.ZE = H.ZE
  /-- the first token sumcheck's end point -/
  rtV : p.rtV.size = Q.P.y.h.lt → Q.P.y.h.lt ≠ 0 → p.rtV = H.tV.r
  /-- the first gated level's point -/
  r12 : p.r12.isEmpty = false → p.r12 = hd.r
  /-- the second token sumcheck's end point -/
  rt : p.rt.size = Q.P.y.h.lt → ∃ tT, H.tT = some tT ∧ p.rt = tT.r
  /-- the second gated level's point -/
  r14 : p.r14.isEmpty = false → ∃ o2, hd2 = some o2 ∧ p.r14 = o2.r

/-- **The points that the honest side lists stand in the verifier's list.** -/
theorem named_part {Q : K4Pub} {p : Pts} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf Q.P.y H hd hd2 = some pts)
    (N : NamedTie Q p H hd hd2) : PtsPart (namedPts Q p) pts := by
  obtain ⟨Z, zv, za, routed, hZ, hzv, hza, hr, rfl⟩ := points_open h
  refine part_of_mem fun q hq => ?_
  unfold namedPts at hq
  dsimp only at hq
  simp only [List.mem_append] at hq
  rcases hq with (((((((hq | hq) | hq) | hq) | hq) | hq) | hq) | hq) | hq
  · obtain ⟨-, x, hx, rfl⟩ := mem_last hq
    rw [N.zx, hZ] at hx
    obtain rfl := Option.some.inj hx
    rfl
  · obtain ⟨hs, h0, rfl⟩ := mem_full hq
    rw [N.zt hs h0]
    rfl
  · obtain ⟨he, x, hx, rfl⟩ := mem_last hq
    rw [N.r6 he, hzv] at hx
    obtain rfl := Option.some.inj hx
    rfl
  · obtain ⟨hs, h0, rfl⟩ := mem_full hq
    rw [N.PV hs h0]
    rfl
  · obtain ⟨hs, h0, rfl⟩ := mem_full hq
    rw [N.ZE hs h0]
    rfl
  · obtain ⟨hs, h0, rfl⟩ := mem_full hq
    rw [N.rtV hs h0]
    rfl
  · obtain ⟨he, x, hx, rfl⟩ := mem_last hq
    rw [N.r12 he, hza] at hx
    obtain rfl := Option.some.inj hx
    rfl
  · -- the two points of the second token sumcheck
    rw [N.zx, hZ] at hq
    cases hs : (p.rt.size == Q.P.y.h.lt) with
    | false =>
      rw [hs] at hq
      cases he : H.fo.zx.isEmpty <;> simp [he] at hq
    | true =>
      rw [hs] at hq
      obtain ⟨tT, hT, e⟩ := N.rt (beq_iff_eq.mp hs)
      rw [hT]
      cases he : H.fo.zx.isEmpty with
      | true => simp [he] at hq
      | false =>
        simp [he] at hq
        rcases hq with rfl | rfl
        · rw [e]
          rfl
        · rw [e]
          rfl
  · obtain ⟨he, x, hx, rfl⟩ := mem_last hq
    obtain ⟨o2, h2, e⟩ := N.r14 he
    rw [h2] at hr
    dsimp only at hr
    rw [e] at hx
    rw [hx] at hr
    obtain rfl := Option.some.inj hr
    cases H.tT <;> rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.part_of_mem
#print axioms OnBytes.Road.K4.C.mem_last
#print axioms OnBytes.Road.K4.C.mem_full
#print axioms OnBytes.Road.K4.C.points_open
#print axioms OnBytes.Road.K4.C.named_part
