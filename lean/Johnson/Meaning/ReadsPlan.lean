-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsPlan.lean: the premises of Johnson/Meaning/ReadsRecord.lean's
`k4_host_planes_closed` on the record, paid at the plan's own record of the smallness test.

`k4_host_planes_closed` asks of a record tl0: its matrices have the sizes of the group's list, and
each of the hearing's tables stands on one of its matrices. At tl0 := hp.tl, the record in the plan
of the group (Layer.planG), the first is the library's planG_sizes
(Johnson/Road/FormsKeysPlan.lean). The second follows from the text that lays the tables: a family's
parts stand on the matrices M0 to M0 + parts - 1, and every family of Layer.tableAsks ends inside
the group's list.

Main theorems (namespace `Meaning.Reads`).
  `asks_bound`: every family of tableAsks has M0 + parts at most parts[0] + parts[1] + 5.
  `layParts_bound`, `layTables_bound`: so every table that layTables lays stands on a matrix below
      that number. `tails_size`: it is the length of the group's list.
  `k4_mats_below`: every table that a run of the layers' plain hearing leaves stands on a matrix of
      the group's list.
  `sizes_of_map`: lists of matrices with the same pairs (rows, columns) have the same sizes at every
      number.
  `k4_host_planes_plan`: **`k4_host_planes_closed` at the plan's record**: without the premises on
      the record.

Limits. New premise: hp is the plan that Layer.planG returns for the group. The other premises of
`k4_host_planes_cells` stay: the relation in front of the draw; the two on the letters; the cells of
the planes' matrix. That the smallness test is seated at this closed record is not shown. Nothing on
soundness.
-/
import Johnson.Meaning.ReadsRecord
import Johnson.Road.FormsKeysPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf Lay Reads TableAsk TableAt tableAsks layParts
  layTables planG)
open OnBytes.K.Kc
open Meaning.Planes

/-- Every family of tables ends inside the group's list of matrices. -/
theorem asks_bound (y : Lay) (rd : Reads) (g : ℕ) :
    ∀ a ∈ tableAsks y rd g, a.M0 + a.parts ≤ y.parts.getD 0 0 + y.parts.getD 1 0 + 5 := by
  intro a ha
  unfold tableAsks at ha
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha
  casesm* _ ∨ _
  all_goals first
    | (obtain ⟨n, _, rfl⟩ := ha; show _ + _ ≤ _; simp only [matIx]; omega)
    | (split at ha
       · simp only [List.mem_map] at ha
         obtain ⟨n, _, rfl⟩ := ha
         show _ + _ ≤ _
         simp only [matIx]
         omega
       · cases ha)

/-- The parts of a family stand on matrices below M0 + parts. -/
theorem layParts_bound (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ (n p : ℕ), n ≤ a.parts →
    ∀ m ∈ (layParts mats a n p).1, m.1 < a.M0 + a.parts
  | 0, _, _, m, hm => by
    unfold layParts at hm
    cases hm
  | n + 1, p, hn, m, hm => by
    unfold layParts at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · show a.M0 + (a.parts - (n + 1)) < _
      omega
    · exact layParts_bound mats a n _ (Nat.le_of_succ_le hn) m hm

/-- Every table that layTables lays stands on a matrix below B, if every family ends at or below B.
-/
theorem layTables_bound (mats : Array (ℕ × ℕ)) (B : ℕ) : ∀ (asks : List TableAsk) (p : ℕ)
    (tab : List TableAt) (laid : List (TableAsk × List (ℕ × ℕ))) (n : ℕ),
    (∀ a ∈ asks, a.M0 + a.parts ≤ B) → layTables mats asks p = some (tab, laid, n) →
    ∀ T ∈ shapesOf laid, T.mat < B
  | [], p, tab, laid, n, _, h, T, hT => by
    unfold layTables at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    cases hT
  | a :: rest, p, tab, laid, n, hB, h, T, hT => by
    unfold layTables at h
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨_, rfl, _⟩ := e
      unfold shapesOf at hT
      rw [List.map_cons, List.flatten_cons] at hT
      rcases List.mem_append.mp hT with hT | hT
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hT
        exact lt_of_lt_of_le (layParts_bound mats a a.parts p (Nat.le_refl _) m hm)
          (hB a List.mem_cons_self)
      · exact layTables_bound mats B rest _ r.1 r.2.1 r.2.2
          (fun b hb => hB b (List.mem_cons_of_mem _ hb)) hr T hT

/-- The length of a group's list of matrices. -/
theorem tails_size (y : Lay) (g : ℕ) (hg : g < y.NGr) :
    ((tailsOf y).getD g {}).mats.size = y.parts.getD 0 0 + y.parts.getD 1 0 + 5 := by
  unfold tailsOf
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hg, if_true,
    Option.map_some, Option.getD_some, List.size_toArray, List.length_map, List.length_zipIdx,
    List.length_append, List.length_range, List.length_cons, List.length_nil]

/-- **Every table that the hearing leaves stands on a matrix of the group's list.** -/
theorem k4_mats_below {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr) :
    ∀ f ∈ o.funs.toList, f.mat < (P.tails.getD g {}).mats.size := by
  intro f hf
  obtain ⟨laid, hl, e⟩ := hear_shapes hh
  have hm : (⟨f.mat, f.len, f.start⟩ : Tab) ∈ shapesOf laid := by
    rw [← e]
    exact List.mem_map_of_mem hf
  rw [hT, tails_size P.y g hg]
  exact layTables_bound _ _ _ 0 _ laid _ (asks_bound P.y P.rd g) hl _ hm

/-- Lists of matrices with the same pairs (rows, columns) have the same sizes at every number. -/
theorem sizes_of_map {ms ms' : Array TMat}
    (h : (ms.map fun M => (M.m, M.k)) = ms'.map fun M => (M.m, M.k)) (μ : ℕ) :
    (ms.getD μ {}).m = (ms'.getD μ {}).m ∧ (ms.getD μ {}).k = (ms'.getD μ {}).k := by
  have e : ∀ xs : Array TMat, (xs.map fun M => (M.m, M.k)).getD μ (0, 0) =
      ((xs.getD μ {}).m, (xs.getD μ {}).k) := by
    intro xs
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases xs[μ]? <;> rfl
  have e2 := congrArg (fun a => a.getD μ (0, 0)) h
  simp only [e] at e2
  exact ⟨(Prod.mk.inj e2).1, (Prod.mk.inj e2).2⟩

/-- **The three clauses at the layers' forms, at the plan's record, closed with the public shapes.**
-/
theorem k4_host_planes_plan (ρ : Reading Cb.Gl.E) {P : Pub} {hp : HPlan2}
    {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr) {O : Option HPlan2}
    (hplan : planG P g O = .ok hp)
    (zb0 zb1 : List Cb.Gl.E) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf (Closed.closedAt hp.tl (Closed.layShapes P g))))
    {x : Θ.X} {msg : Θ.M} (h : relIn Θ.letters x msg)
    (hphi : ∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
      Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE))
    (W : World Cb.Gl.E)
    (hu : ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (hp.tl.mats.getD f.mat {}).k,
      ∀ sg < (hp.tl.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val W.entry o.v.iU3 o.v.K3
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN (Closed.closedAt hp.tl (Closed.layShapes P g)) Θ msg (matIx o.v.y).iB r c =
        ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨s1, s2⟩ := Road.planG_sizes hplan
  have hsz : hp.tl.mats.size = (P.tails.getD g {}).mats.size := by
    have := congrArg Array.size s1
    simpa using this
  exact k4_host_planes_closed ρ hh hq hT hg zb0 zb1 hz0 hz1 hp.tl Θ h (sizes_of_map s1)
    (fun f hf _ => by rw [s2, hsz]; exact k4_mats_below hh hT hg f hf) hphi W hu ν h4

#print axioms asks_bound
#print axioms k4_mats_below
#print axioms k4_host_planes_plan

end Meaning.Reads
