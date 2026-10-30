-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/OwnedOfInTab.lean: a place of the array of reads that lies inside one of the plan's
families of tables (inTab, Johnson/Road/K4/Reads/TermsEnts.lean) IS OWNED BY A TABLE of the list
that the hearing returns: the smallness test's numbering (HTailF2.tabAt) has that place for a
column and a run of a table of o.funs.

Why. The entries entryTrue (Johnson/Road/K4/EntryTrue.lean) are a table's sum at a place that a
table owns, and 0 elsewhere, which is true of nothing. Johnson/Road/K4/Reads/Covered.lean and
StackEnts.lean say of K4's claims that every entry that they name is inTab. With this file: at
every such entry entryTrue is a table's sum.

  `layTables_both`: beside each family's place layTables returns the family with its parts' first
    entries, and the family ends where its last part ends (layTables_laid and
    layTables_len at ONE family).
  `owned_aux`, `owned_of_place`: from the returns of layTables and funsOf.
  `plan_sizes`: htm and hNM, member by member and as a sum of the layout's parts.
  `owned_of_inTab`: at a hearing.
No new argument: layParts_eq, entry_split, entry_tabAt, funsOf_mem.
Limits. Premises at a hearing, in the letters of PubLines' fields (Johnson/Road/K4/PubAt.lean):
hmats (the plan's list of matrices has the rows and columns of tailsOf's), hg (g is a group of the
layout), htm (so has the smallness test's record tl), hNM (tl's number of matrices is its list's
length). Nothing on what a prover has committed, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.EntryTrue
import Johnson.Road.K4.ReadsAtPub
import Johnson.Road.K4.K4DeclsWhole
import Johnson.Road.K4.Reads.TermsEnts
import Johnson.Road.FormsKeysPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layParts layTables tableAsks phiOf funsOf Pub
  Own HPlan2 tailsOf)
open OnBytes.Desc.First.K4 (engFl hear)
open OnBytes.Desc.First.K4.Reads (inTab)
open OnBytes.Desc.First.P1 (gl)

/-- Beside each family's place: the family, its parts' first entries, and its end. -/
theorem layTables_both (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    ∀ x ∈ r.1, ∃ q ∈ r.2.1, q.1 ∈ asks ∧ q.2 = (layParts mats q.1 q.1.parts x.first).1 ∧
      x.first + x.len = (layParts mats q.1 q.1.parts x.first).2
  | [], p, r, h, x, hx => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    simp at hx
  | a :: rest, p, r, h, x, hx => by
    have hle := layParts_le mats a a.parts p
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      subst h2
      rcases List.mem_cons.mp hx with e | hx
      · subst e
        refine ⟨(a, (layParts mats a a.parts p).1), List.mem_cons_self, List.mem_cons_self, rfl,
          ?_⟩
        show p + ((layParts mats a a.parts p).2 - p) = (layParts mats a a.parts p).2
        omega
      · obtain ⟨q, q1, q2, q3, q4⟩ := layTables_both mats rest _ r' h1 x hx
        exact ⟨q, List.mem_cons_of_mem _ q1, List.mem_cons_of_mem _ q2, q3, q4⟩

/-- One family, at its numbers. -/
theorem owned_aux (tl : HTailF2) {M0 parts m k L b e : ℕ} (phi : Array E) (funs : Array HFun)
    (he : e < parts * (k * (m / L)))
    (htl : ∀ p, p < parts → M0 + p < tl.NM ∧ (tl.mats.getD (M0 + p) {}).m = m ∧
      (tl.mats.getD (M0 + p) {}).k = k)
    (hmem : ∀ s, s < parts →
      ({ mat := M0 + s, len := L, phi := phi, tree := 2, start := b + s * (k * (m / L)) } : HFun) ∈
        funs) :
    ∃ z : HFun × ℕ × ℕ, z.1 ∈ funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some (b + e) :=
  ⟨({ mat := M0 + e / (m / L) / k, len := L, phi := phi, tree := 2,
      start := b + e / (m / L) / k * (k * (m / L)) }, e / (m / L) % k, e % (m / L)),
    hmem _ (entry_split he).1, entry_tabAt tl phi he htl⟩

/-- **A place inside a family is owned by a table of the list.** -/
theorem owned_of_place {y : Lay} {fo : Forest.Heard} {pts : List (String × Array E)}
    {mats : Array (ℕ × ℕ)} {asks : List TableAsk} {p : ℕ}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {funs : Array HFun} (tl : HTailF2)
    (h : layTables mats asks p = some r) (hfu : funsOf y fo pts r.2.1 = some funs)
    (hf : ∀ a ∈ asks, ∀ q, q < a.parts → mats.getD (a.M0 + q) (0, 0) = mats.getD a.M0 (0, 0))
    (hN : ∀ a ∈ asks, a.M0 + a.parts ≤ tl.NM)
    (htl : ∀ i, mats.getD i (0, 0) = ((tl.mats.getD i {}).m, (tl.mats.getD i {}).k))
    {x : TableAt} (hx : x ∈ r.1) {pos : ℕ} (h1 : x.first ≤ pos) (h2 : pos < x.first + x.len) :
    ∃ z : HFun × ℕ × ℕ, z.1 ∈ funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some pos := by
  obtain ⟨q, hq, ha, e1, e2⟩ := layTables_both mats asks p r h x hx
  obtain ⟨phi, _, hm⟩ := funsOf_mem hfu hq
  have L := layParts_eq mats q.1 (mats.getD q.1.M0 (0, 0)).1 (mats.getD q.1.M0 (0, 0)).2
    (fun s hs => hf q.1 ha s hs) x.first
  rw [L] at e1 e2
  have e2' : x.first + x.len = x.first + q.1.parts *
      ((mats.getD q.1.M0 (0, 0)).2 * ((mats.getD q.1.M0 (0, 0)).1 / q.1.L)) := e2
  obtain ⟨e, rfl⟩ : ∃ e, pos = x.first + e := ⟨pos - x.first, by omega⟩
  have he : e < q.1.parts *
      ((mats.getD q.1.M0 (0, 0)).2 * ((mats.getD q.1.M0 (0, 0)).1 / q.1.L)) := by omega
  refine owned_aux tl (M0 := q.1.M0) phi funs he (fun s hs => ?_) (fun s hs =>
    hm (q.1.M0 + s, x.first + s *
      ((mats.getD q.1.M0 (0, 0)).2 * ((mats.getD q.1.M0 (0, 0)).1 / q.1.L))) ?_)
  · have a1 := hf q.1 ha s hs
    rw [htl (q.1.M0 + s)] at a1
    have a2 := hN q.1 ha
    exact ⟨by omega, congrArg Prod.fst a1, congrArg Prod.snd a1⟩
  · rw [e1]
    exact List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩

/-- The record's sizes, member by member; its number of matrices as a sum of the layout's parts. -/
theorem plan_sizes {y : Lay} {g : ℕ} {tl : HTailF2} (hg : g < y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR y g) (hNM : tl.NM = tl.mats.size) :
    (∀ i, (matsR y g).getD i (0, 0) = ((tl.mats.getD i {}).m, (tl.mats.getD i {}).k)) ∧
      tl.NM = y.parts.getD 0 0 + y.parts.getD 1 0 + 5 := by
  refine ⟨fun i => by rw [← htm, pair_getD], ?_⟩
  have e := congrArg Array.size htm
  rw [Array.size_map] at e
  rw [hNM, e]
  unfold matsR
  rw [Array.size_map]
  exact (tails_sizes y hg).1

/-- **At a hearing.** -/
theorem owned_of_inTab {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM' : tl.NM = tl.mats.size)
    {a r i : ℕ} (hi : inTab o.v a r i) :
    a = o.v.iU3 ∧ ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧
      tl.tabAt z.1 z.2.1 z.2.2 = some (r * o.v.K3 + i) := by
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, e3, _, ev, _, _, _, _, e10⟩ :=
    Desc.First.K4.hear_public h
  obtain ⟨htl, hNM⟩ := plan_sizes hg htm hNM'
  rw [hm] at e3
  obtain ⟨ha, x, hx, h1, h2⟩ := hi
  have hx' : x ∈ tab := by
    rw [ev] at hx
    exact hx
  refine ⟨ha, owned_of_place (r := (tab, laid, nU3)) tl e3 e10 (asks_fit P.y P.rd hg)
    (fun b hb => ?_) htl hx' h1 h2⟩
  exact (k4Decl_fit P.rd hg hb 0 #[] (OnBytes.Tie.Pv.Tail.sizeOf tl) htl hNM).1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.layTables_both
#print axioms OnBytes.Road.K4.owned_aux
#print axioms OnBytes.Road.K4.owned_of_place
#print axioms OnBytes.Road.K4.plan_sizes
#print axioms OnBytes.Road.K4.owned_of_inTab
