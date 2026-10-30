-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/NumsAt.lean: THE NUMBERS THAT A LOT READS OFF THE PLANNER's RECORD OF A
GROUP ARE THE TYPED RECORD's: `P2At` (P2At.lean) at `rowOf` (Table.lean), from eight equations.

The law of the code switch speaks of the kind's block at a place's numbers p with `P2At r p`: the
two declared rounds' entries are those of the typed record r. A written description's lot makes p of
the planner's sizes z and its record n of the group (`FrameN`, OnBytes/Plan/ReqFrames.lean);
Table.lean makes r of the same two. Here the two meet, for all z and n: no number is evaluated.

Main names:
  `sampledOf`: the notices of a sending that have an answer. `reqSampled_length`, `reqSampled_cube`:
    the planner's samples of a sending (`reqSampled`) are as many, and their largest cube is the
    largest of these notices' cubes.
  `p2At_frame`: if `layTrees` lays the sending's trees, and p's eight numbers are: the work of a
    sample's round; the number of trees; samples × (the largest cube + 1); samples; the work of a
    query's round; samples × the number of sampled notices; `baseCount` at the group in front; that
    group's logN: then `P2At (rowOf z lo l kept n) p`, whatever lo, l and kept are.
Limits: one identity. That a lot's numbers are these eight is by unfolding the lot's own text, not
here. Nothing on r.ok, r.writtenOK or sizedB at `rowOf`: these stay tests on the plan. Nothing on
soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Table
import Johnson.Top.H0.K2Caller.P2At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Plan Johnson.Top.H OnBytes.Tie.Pv.Switch

theorem zip_filter_snd {α β : Type} (q : β → Bool) : ∀ (xs : List α) (ys : List β),
    xs.length = ys.length → ((xs.zip ys).filter fun x => q x.2).map (·.2) = ys.filter q
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
      have ih := zip_filter_snd q xs ys (Nat.succ.inj h)
      rw [List.zip_cons_cons, List.filter_cons, List.filter_cons]
      cases hq : q y
      · simpa using ih
      · simp only [if_true, List.map_cons, ih]

/-- The sampled notices of a sending. -/
def sampledOf (sent : List OracleNotice) : List OracleNotice :=
  sent.filter fun n => decide (0 < n.shape.answers)

theorem reqSampled_snd (codes : Codes) (sent : List OracleNotice) (g a : GroupSize) (r : ℕ) :
    (reqSampled codes sent g a r).map (·.cubeBits) =
      (sampledOf sent).map fun n => cubeBitsOf codes n.shape := by
  unfold reqSampled sampledOf
  rw [OnBytes.zipT_eq, List.map_map,
    ← zip_filter_snd (fun n : OracleNotice => decide (0 < n.shape.answers)) (List.range sent.length)
      sent List.length_range, List.map_map]
  rfl

theorem reqSampled_length (codes : Codes) (sent : List OracleNotice) (g a : GroupSize) (r : ℕ) :
    (reqSampled codes sent g a r).length = (sampledOf sent).length := by
  have h := congrArg List.length (reqSampled_snd codes sent g a r)
  rwa [List.length_map, List.length_map] at h

theorem reqSampled_cube (codes : Codes) (sent : List OracleNotice) (g a : GroupSize) (r : ℕ) :
    largestCube (reqSampled codes sent g a r) =
      (sampledOf sent).foldl (fun c n => max c (cubeBitsOf codes n.shape)) 0 := by
  have h := reqSampled_snd codes sent g a r
  have e1 : largestCube (reqSampled codes sent g a r) =
      ((reqSampled codes sent g a r).map (·.cubeBits)).foldl max 0 := by
    unfold largestCube
    rw [List.foldl_map]
  rw [e1, h, List.foldl_map]

/-- **The numbers that a lot reads off the planner's record of a group are the typed record's**: a
place's numbers p whose eight numbers of the two rounds are made of the sizes z and the record n as
written here meet `P2At` at `rowOf z lo l kept n`, whatever lo, l and kept are. -/
theorem p2At_frame (z : ProofSized) (n : FrameN) (lo l : List (OracleShape × ℕ)) (kept : List ℕ)
    (lay : TreeLay) (hlay : layTrees z.codes n.sent.toArray = some lay) (p : K2.P2)
    (h1 : p.work₁ = z.set.workOf .sample .request) (h2 : p.roots = lay.shapes.size)
    (h3 : p.seeds = z.set.samples *
      ((sampledOf n.sent).foldl (fun c x => max c (cubeBitsOf z.codes x.shape)) 0 + 1))
    (h4 : p.nonZero = z.set.samples) (h5 : p.work₂ = z.set.workOf .query .request)
    (h6 : p.answers = z.set.samples * (sampledOf n.sent).length)
    (h7 : p.positions = baseCount z.set .request n.before) (h8 : p.logN = n.before.main.logN) :
    P2At (rowOf z lo l kept n) p := by
  have e : (K2.rounds p).map (·.entry) =
      (K2.rounds (p2Of (rowOf z lo l kept n) p)).map (·.entry) := by
    have r2 : (rowOf z lo l kept n).roots = lay.shapes.size := by
      show ((treesOf z.codes n.sent.toArray).getD 0) = _
      unfold treesOf
      rw [hlay]
      rfl
    have r3 : largestCube (rowOf z lo l kept n).o =
        (sampledOf n.sent).foldl (fun c x => max c (cubeBitsOf z.codes x.shape)) 0 :=
      reqSampled_cube _ _ _ _ _
    have r6 : (rowOf z lo l kept n).o.length = (sampledOf n.sent).length :=
      reqSampled_length _ _ _ _ _
    unfold K2.rounds p2Of
    simp only [List.map_cons, List.map_nil, h1, h2, h3, h4, h5, h6, h7, h8, r2, r3, r6]
    rfl
  exact e.trans (p2Of_at _ _)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.p2At_frame
