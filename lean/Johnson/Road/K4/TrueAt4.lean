-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TrueAt4.lean: the long tables of af at the points named Z_a and Z_b, which the
claims on the gated products' end values read, are true of the cells, if every table of the reads
holds what it says of the matrices.

Johnson/Road/FormsKeysTrue3.lean concludes the truth of five families of tables from that one
statement on the world, and says in its head: "Nothing on the tables of af at Z_a and Z_b, which the
claims on the gated products read: long_family serves them as it stands, but no record here names
them." Here they are named, after the pattern of trueAt3_of_holds.

Main names:
  `TrueAt4`: the two families are true in the world W.
  `readsOf_points4`: the list of af's points that readsOf returns has Z_a, and Z_b with routed
    experts.
  `two_numbers`: the numbers of the two families in the verifier's list of asks.
  `pointsOf_names4`: in the verifier's list of points by name, Z_a is the last la coordinates of
    the challenges of the first product layer of the gated products, Z_b those of the second's.
  `trueAt4_of_holds`: TrueAt4 as a conclusion, with a second product layer.
Limits. That every table holds is a premise (another kind's row). The public lines of the layout are
premises, as in trueAt3_of_holds. With routed experts and a second product layer alone. Nothing on a
draw, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysTrue3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World HFun HTailF2 Level lastOf)
open OnBytes.Model.Layer (Env Lay Shape Reads Heard TableAsk TableAt layout readsOf layTables
  tableAsks pointsOf funsOf)

/-- The long tables of af at the points named Z_a and Z_b are true in the world W. lowA, lowB: the
first ls coordinates of the two points; uA, uB: the others. -/
structure TrueAt4 {K : Type} [Field K] (ρ : Reading K) (W : World K) (v : Env) (lT : ℕ)
    (c : Cells K) (lowA uA lowB uB : ℕ → K) : Prop where
  /-- af at Z_a -/
  afA : ∀ b, v.tabAt ("af" ++ "@" ++ "Z_a") = some b → LongTrue ρ W v b 0 v.y.ls lT c lowA uA
  /-- af at Z_b -/
  afB : ∀ b, v.tabAt ("af" ++ "@" ++ "Z_b") = some b → LongTrue ρ W v b 0 v.y.ls lT c lowB uB

/-- The list of af's points has Z_a, and Z_b with routed experts. -/
theorem readsOf_points4 {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) (h3 : y.h.p3 = true) :
    "Z_a" ∈ rd.rdAF ∧ "Z_b" ∈ rd.rdAF := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  refine ⟨?_, ?_⟩
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))
  · refine List.mem_append_right _ (List.mem_append_right _ ?_)
    rw [h3]
    exact List.mem_singleton.mpr rfl

/-- The numbers of a family of af's long tables at a point of its list. -/
theorem af_numbers (y : Lay) (rd : Reads) (g : ℕ) {P : String} (hAF : P ∈ rd.rdAF) :
    ∃ a ∈ tableAsks y rd g, a.name = "af" ++ "@" ++ P ∧ a.M0 = firstM y 0 ∧
      a.parts = partsM y 0 ∧ a.L = 2 ^ y.h.la ∧ a.point = P ∧ a.lng = true :=
  ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.mpr ⟨P, hAF, rfl⟩)))))))),
      rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two points in the verifier's list of points by name. -/
theorem pointsOf_names4 {y : Lay} {H : Heard} {hd o : Level} {pts : List (String × Array E)}
    (h : pointsOf y H hd (some o) = some pts) :
    ∃ ZA ZB, lastOf hd.r y.h.la = .ok ZA ∧ lastOf o.r y.h.la = .ok ZB ∧
      pts.find? (fun p => p.1 == "Z_a") = some ("Z_a", ZA) ∧
      pts.find? (fun p => p.1 == "Z_b") = some ("Z_b", ZB) := by
  unfold pointsOf at h
  obtain ⟨Z, hZ, h⟩ := bind_some h
  obtain ⟨routed, hr, h⟩ := bind_some h
  obtain ⟨a, ha, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  obtain ⟨zb, hzb, rfl⟩ := map_some hr
  have e := Option.some.inj h
  subst e
  refine ⟨b, zb, ok_of_toOption hb, ok_of_toOption hzb, ?_, ?_⟩
  · cases H.tT <;> simp
  · cases H.tT <;> simp

section Run

variable {K : Type} [Field K] {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **TrueAt4 as a conclusion.** Under the hypotheses of trueAt3_of_holds, with a second product
layer o. -/
theorem trueAt4_of_holds (ρ : Reading K) (W : World K) (hy : layout h pc = .ok v.y)
    (S : Switches h) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd o : Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hp : pointsOf v.y H hd (some o) = some pts) (hfun : funsOf v.y H.fo pts r.2.1 = some funs)
    (M : Mats K) (Hd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) :
    ∃ ZA ZB, lastOf hd.r v.y.h.la = .ok ZA ∧ lastOf o.r v.y.h.la = .ok ZB ∧
      TrueAt4 ρ W v v.y.h.lt (cellsAt v.y M) (pt ρ ZA) (fun j => pt ρ ZA (v.y.ls + j))
        (pt ρ ZB) (fun j => pt ρ ZB (v.y.ls + j)) := by
  have h3 : v.y.h.p3 = true := by
    rw [(admitted_of_layout hy S.p3).shape]
    exact S.p3
  obtain ⟨p1, p2⟩ := readsOf_points4 hrd h3
  obtain ⟨ZA, ZB, hA, hB, fA, fB⟩ := pointsOf_names4 hp
  refine ⟨ZA, ZB, hA, hB, ?_⟩
  exact
    { afA := fun b hb => (long_family ρ W hy S hg hrd hl ht htm hNM hfun M Hd (by omega) (by simp)
        (by simp) (af_numbers v.y rd v.g p1) fA hb).2
      afB := fun b hb => (long_family ρ W hy S hg hrd hl ht htm hNM hfun M Hd (by omega) (by simp)
        (by simp) (af_numbers v.y rd v.g p2) fB hb).2 }

end Run

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.trueAt4_of_holds
