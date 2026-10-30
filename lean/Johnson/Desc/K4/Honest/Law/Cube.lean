-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/Cube.lean: CONDITIONAL. Statements with their proofs; no definition.

What is here. Laws on a sum over a cube as the program of Johnson/Desc/K4/Honest/Cube.lean computes
it.

`sumBy` is `CubeTest.sumBy` of Johnson/Desc/K4/Honest/Cube.lean, a definition among that file's
tests: of no coordinate and g it is g(0) + g(1); of a coordinate z and g, (1 - z) g(0) + z g(1).

THE SUMMAND. `termsAt_read` (CubeKitB.lean's `termsAt_rd` with that file's terms written out: one
  law), `summandAt_read`: at an entry of some tables; at all challenges.
0 THE TEST. `fits_sizes`: two cubes with the same number of variables, order, sizes of maps, maps
  named by the pairs and number of coordinates fit together or not at all. `fits_of`: from the
  sizes: the test accepts.
1 THE CHAIN. With val := `partK ρ c`:
  `round_length`   a round's polynomial has three coefficients
  `part_nil`   val [] is the reading of `Cube.total`
  `part_sum`   the round's polynomial behind rs, summed in the cube's way, reads as val rs
  `part_next`   that polynomial at a challenge r reads as val (rs ++ [r])
  `part_last`   behind all challenges val rs is the reading of `Cube.summandAt`
  `round_sum_plain`, `round_sum_point`   `part_sum` on the three coefficients: 2 g0 + g1 + g2, and
     g0 + z (g1 + g2)
2 THE SUM. `total_plain`, `total_point`, `total_ext`: the total is the sum over the corners of the
  summand, bare or under the library's equality table.
3 THE VALUES. `valuesAt_size`; `valuesAt_mle`: behind all challenges each map's value reads as
  `mle` of the map at `Cube.pointOf`; `pointOf_size`, `zip_facts`, `pointOf_mem`, `pointOf_at`,
  `pointOf_default`: which challenge lies where in that point; `mle_read`, `mle_ext`: `mle` reads
  as the sum under the library's kernel `Blocks.eqN`, which is the library's `Blocks.ext`.

Limits. Every law on a VALUE is an equation between READINGS of the program's elements in a
commutative ring (`OnBytes.Model.Reading`), not between machine words; `total_ext`, `mle_read` and
`mle_ext` at readings into a field alone, as the library's `eqTab_value` is; the laws on sizes and
lengths count, and `pointOf_mem`, `pointOf_at` and `pointOf_default` are on words. Every law on
rounds has the hypothesis `c.fits = true` (`zip_facts` and `pointOf_mem`: the lesser `FitsP c`); of
no cube of the layers is it shown here that the test holds (`fits_of`: from which sizes it does;
`fits_sizes`: it reads no entry of a table, no weight and no coordinate). `partK`
(Johnson/Desc/K4/Honest/Law/CubeTerms.lean) is made of the program's own bound tables: no law here
writes a partial sum in the middle of the rounds as a sum of products of multilinear extensions; the
two ends of the chain are tied to `Cube.total` and to `Cube.summandAt`, and each map's last value to
`mle`. `partK` READS NO MORE CHALLENGES THAN THE ORDER LISTS VARIABLES, n where the cube fits: it is
no partial sum for a further variable behind the cube's own. Nothing here ties a cube to a
verifier's text, to a committed table or to a model, and nothing here holds a `Job`'s `ends` and
`atEnds` against its cube.

Kin. Sisters of the chain at other definitions, no twins: another kind's, at its own sum
(`total_reads`, `round_sums`, `round_at`, `ends_reads`, Johnson/Desc/K6/Honest/PairLaw.lean); and,
on functions over a field, for a summand κ + A B under equality weights, the variables in any order:
`wsum_round`, `evalP_round`, `lvlSum_last`, `pj_lawful` (Johnson/HonestTrace/LookCube.lean). This
file builds on neither.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeKitD
import Blocks.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Desc.First.K4.Honest.CubeTest (sumBy)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## 0 The test -/

/-- **The test reads the number of variables, the order, which maps the pairs name, and sizes**: no
entry of a table, no weight and no coordinate. -/
theorem fits_sizes (c c' : Cube) (hn : c'.n = c.n) (ho : c'.order = c.order)
    (hm : c'.maps.map Array.size = c.maps.map Array.size)
    (hp : c'.pairs.map Prod.snd = c.pairs.map Prod.snd) (hw : wayLen c'.way = wayLen c.way) :
    c'.fits = c.fits := by
  have key : ∀ d : Cube, d.fits =
      (d.order.length == d.n && (List.range d.n).all (fun v => d.order.contains v) &&
        (d.maps.map Array.size).all (fun s => s == 2 ^ d.n) &&
        (d.pairs.map Prod.snd).all (fun x => decide (x.1 < (d.maps.map Array.size).size) &&
          decide (x.2 < (d.maps.map Array.size).size)) &&
        (match wayLen d.way with
         | none => true
         | some s => s == d.n)) := by
    intro d
    unfold Cube.fits
    rw [Array.all_map, List.all_map, Array.size_map]
    cases d.way <;> rfl
  rw [key c, key c', hn, ho, hm, hp, hw]

/-- **From the sizes: the test accepts.** -/
theorem fits_of (c : Cube) (h1 : c.order.length = c.n) (h2 : ∀ v, v < c.n → v ∈ c.order)
    (h3 : ∀ t ∈ c.maps.toList, t.size = 2 ^ c.n)
    (h4 : ∀ x ∈ c.pairs, x.2.1 < c.maps.size ∧ x.2.2 < c.maps.size)
    (h5 : ∀ rho, c.way = .point rho → rho.size = c.n) : c.fits = true := by
  have h3' : ∀ a (ha : a < c.maps.size), (c.maps[a]).size = 2 ^ c.n := fun a ha =>
    h3 _ (Array.getElem_mem_toList ha)
  simp only [Cube.fits, Bool.and_eq_true]
  refine ⟨⟨⟨⟨by simpa using h1, by simpa using h2⟩, by simpa [Array.all_eq_true] using h3'⟩,
    List.all_eq_true.mpr fun x hx => by simp [h4 x hx]⟩, ?_⟩
  cases hw : c.way with
  | plain => rfl
  | point rho => simpa using h5 rho hw

/-! ## The summand -/

/-- The summand at an entry of some tables. -/
theorem termsAt_read (pairs : List (E × Nat × Nat)) (ms : Array Tab) (j : ℕ) :
    ρ.val (termsAt pairs ms j) =
      (pairs.map fun x => ρ.val x.1 * (ρ.val ((ms.getD x.2.1 #[]).getD j zeroE) *
        ρ.val ((ms.getD x.2.2 #[]).getD j zeroE))).sum :=
  termsAt_rd ρ pairs ms j

/-- The summand at all challenges, on the maps' values there. -/
theorem summandAt_read (c : Cube) (rs : List E) :
    ρ.val (c.summandAt rs) =
      (c.pairs.map fun x => ρ.val x.1 * (ρ.val ((c.valuesAt rs).getD x.2.1 zeroE) *
        ρ.val ((c.valuesAt rs).getD x.2.2 zeroE))).sum := by
  have one : ∀ a, (((c.valuesAt rs).map fun x => #[x]).getD a #[]).getD 0 zeroE =
      (c.valuesAt rs).getD a zeroE := by
    intro a
    by_cases ha : a < (c.valuesAt rs).size
    · rw [OnBytes.Road.getD_map_lt _ _ ha #[] zeroE]
      rfl
    · have ha' : (c.valuesAt rs).size ≤ a := Nat.le_of_not_lt ha
      rw [OnBytes.Road.getD_ge _ (by rw [Array.size_map]; exact ha') #[],
        OnBytes.Road.getD_ge _ ha' zeroE, OnBytes.Road.getD_ge #[] (Nat.zero_le 0) zeroE]
  unfold Cube.summandAt
  rw [termsAt_rd]
  simp only [sumT, rdM, rdT, one]

/-! ## 1 The chain -/

/-- A round's polynomial has three coefficients. -/
theorem round_length (c : Cube) (h : c.fits = true) (rs : List E) (hr : rs.length < c.n) :
    (c.round rs).length = 3 := by
  obtain ⟨v, os, hd⟩ := next_var (fitsP c h) rs hr
  rw [round_eq hd]
  rfl

/-- In front of the first round the partial sum is the total. -/
theorem part_nil (c : Cube) : partK ρ c [] = ρ.val c.total := by
  have hw := weights_sum ρ ((List.range c.n).reverse.map (sidesOf c)) fun i =>
    ρ.val (termsAt c.pairs c.maps i)
  rw [List.length_map, List.length_reverse, List.length_range, List.map_map,
    ← List.map_reverse] at hw
  unfold partK
  rw [bound_nil]
  show _ = ρ.val ((List.range (2 ^ c.n)).foldl (fun t i => addE t (mulE
    ((weightsOf ((List.range c.n).reverse.map (sidesOf c))).getD i zeroE)
    (termsAt c.pairs c.maps i))) zeroE)
  rw [foldRange ρ (fun i => mulE
    ((weightsOf ((List.range c.n).reverse.map (sidesOf c))).getD i zeroE)
    (termsAt c.pairs c.maps i)) zeroE, ρ.zero, zero_add]
  simp only [ρ.mul]
  exact hw.symm

/-- **A round's polynomial, summed in the cube's way, is the partial sum in front of the round.** -/
theorem part_sum (c : Cube) (h : c.fits = true) (rs : List E) (hr : rs.length < c.n) :
    ρ.val (sumBy c.points[rs.length]? (c.round rs)) = partK ρ c rs := by
  obtain ⟨v, os, hd⟩ := next_var (fitsP c h) rs hr
  rw [sumBy_round ρ hd, roundAt_sum ρ hd (inv (fitsP c h) rs (Nat.le_of_lt hr))]

/-- **A round's polynomial at the round's challenge is the partial sum behind the round.** -/
theorem part_next (c : Cube) (h : c.fits = true) (rs : List E) (r : E) (hr : rs.length < c.n) :
    ρ.val (valueP (c.round rs) r) = partK ρ c (rs ++ [r]) := by
  obtain ⟨v, os, hd⟩ := next_var (fitsP c h) rs hr
  rw [round_value ρ hd, roundAt_next ρ hd (inv (fitsP c h) rs (Nat.le_of_lt hr)) r]

/-- Behind the last round the partial sum is the summand at the challenges. -/
theorem part_last (c : Cube) (h : c.fits = true) (rs : List E) (hr : rs.length = c.n) :
    partK ρ c rs = ρ.val (c.summandAt rs) := by
  have I := inv (fitsP c h) rs (Nat.le_of_eq hr)
  have hl : (c.bound rs).1 = [] := List.eq_nil_of_length_eq_zero (by have := I.len; omega)
  unfold partK
  rw [hl, summandAt_read]
  show ρ.val (termsAt c.pairs (c.bound rs).2 0) = _
  rw [termsAt_rd]
  simp only [sumT, rdM, rdT, valuesAt_getD]

/-- `part_sum` on the coefficients, where the sum is plain: 2 g0 + g1 + g2. -/
theorem round_sum_plain (c : Cube) (h : c.fits = true) (hw : c.way = .plain) (rs : List E)
    (hr : rs.length < c.n) :
    2 * ρ.val ((c.round rs).getD 0 zeroE) + ρ.val ((c.round rs).getD 1 zeroE) +
      ρ.val ((c.round rs).getD 2 zeroE) = partK ρ c rs := by
  obtain ⟨v, os, hd⟩ := next_var (fitsP c h) rs hr
  have hs := part_sum ρ c h rs hr
  have hp : c.points[rs.length]? = none := by simp [Cube.points, hw]
  rw [hp, round_eq hd] at hs
  rw [round_eq hd, ← hs]
  show _ = ρ.val (addE (valueP _ zeroE) (valueP _ oneE))
  rw [ρ.add, valueP_three, valueP_three, ρ.zero, ρ.one]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- `part_sum` on the coefficients, where the sum is at a point: g0 + z (g1 + g2), z the round's
member of `Cube.points`. -/
theorem round_sum_point (c : Cube) (h : c.fits = true) (rho : Array E) (hw : c.way = .point rho)
    (rs : List E) (hr : rs.length < c.n) :
    ρ.val ((c.round rs).getD 0 zeroE) + ρ.val (c.points.getD rs.length zeroE) *
      (ρ.val ((c.round rs).getD 1 zeroE) + ρ.val ((c.round rs).getD 2 zeroE)) = partK ρ c rs := by
  obtain ⟨v, os, hd⟩ := next_var (fitsP c h) rs hr
  have hs := part_sum ρ c h rs hr
  have hlen : rs.length < c.points.length := by
    simp [Cube.points, hw, (fitsP c h).len, hr]
  have hp : c.points[rs.length]? = some (c.points.getD rs.length zeroE) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rfl
  rw [hp, round_eq hd] at hs
  rw [round_eq hd, ← hs]
  show _ = ρ.val (addE (mulE (subE oneE _) (valueP _ zeroE)) (mulE _ (valueP _ oneE)))
  rw [ρ.add, ρ.mul, ρ.mul, ρ.sub, valueP_three, valueP_three, ρ.zero, ρ.one]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  ring

/-! ## 2 The sum -/

/-- Summed plainly, the total is the sum of the summand over the corners. -/
theorem total_plain (c : Cube) (hw : c.way = .plain) :
    ρ.val c.total = ∑ i ∈ Finset.range (2 ^ c.n), ρ.val (termsAt c.pairs c.maps i) := by
  rw [← part_nil ρ c]
  unfold partK
  rw [bound_nil, sumOver_ones _ _ (by
    intro w hw'
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw'
    simp [sidesK, sidesOf, hw, ρ.one])]
  simp

/-- Summed at a point, the total is the sum over the corners under the library's equality table. -/
theorem total_point (c : Cube) (rho : Array E) (hw : c.way = .point rho) (hs : rho.size = c.n) :
    ρ.val c.total = ∑ i ∈ Finset.range (2 ^ c.n),
      ρ.val ((eqTab rho).getD i zeroE) * ρ.val (termsAt c.pairs c.maps i) := by
  have hk : sidesK ρ c = fun v => (1 - ρ.val (rho.getD (c.n - 1 - v) zeroE),
      ρ.val (rho.getD (c.n - 1 - v) zeroE)) := by
    funext v
    simp [sidesK, sidesOf, hw, ρ.sub, ρ.one]
  have he := eqTab_sum ρ rho fun i => ρ.val (termsAt c.pairs c.maps i)
  rw [← toList_rev rho c.n hs, List.map_map, ← List.map_reverse, hs] at he
  rw [he, ← part_nil ρ c]
  unfold partK
  rw [bound_nil, hk]
  rfl

/-- The same in the library's letters: the multilinear extension, at the point, of the summand's
values at the corners. (The summand itself has degree 2 in each variable: this is not its value at
the point.) -/
theorem total_ext {K : Type} [Field K] (ρ : Reading K) (c : Cube) (rho : Array E)
    (hw : c.way = .point rho) (hs : rho.size = c.n) :
    ρ.val c.total =
      Blocks.ext c.n (fun i => ρ.val (termsAt c.pairs c.maps i)) (OnBytes.Road.pt ρ rho) := by
  rw [total_point ρ c rho hw hs]
  unfold Blocks.ext
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [OnBytes.Road.eqTab_value ρ rho i (by rw [hs]; exact Finset.mem_range.mp hi), hs]

/-! ## 3 The values -/

/-- There is a value for each map. -/
theorem valuesAt_size (c : Cube) (rs : List E) : (c.valuesAt rs).size = c.maps.size := by
  have key : ∀ (zs : List (ℕ × E)) (s : List ℕ × Array Tab),
      (zs.foldl boundStep s).2.size = s.2.size := by
    intro zs
    induction zs with
    | nil => intro s; rfl
    | cons x zs ih =>
      intro s
      rw [List.foldl_cons, ih]
      exact Array.size_map
  unfold Cube.valuesAt
  rw [Array.size_map, bound_eq, key]

/-- The challenges as a point: as many coordinates as variables. -/
theorem pointOf_size (c : Cube) (rs : List E) : (c.pointOf rs).size = c.n := by
  unfold Cube.pointOf
  rw [pointFold_size]
  simp

/-- The rounds' variables with their challenges: each variable once. -/
theorem zip_facts {c : Cube} (F : FitsP c) {rs : List E} (hr : rs.length = c.n) :
    ((c.order.zip rs).map Prod.fst).Nodup ∧ (∀ x ∈ c.order.zip rs, x.1 < c.n) ∧
      ∀ v, v < c.n → ∃ x ∈ c.order.zip rs, x.1 = v := by
  have e : (c.order.zip rs).map Prod.fst = c.order :=
    List.map_fst_zip (by rw [F.len, hr])
  refine ⟨by rw [e]; exact F.nodup, fun x hx => ?_, fun v hv => ?_⟩
  · exact (F.mem x.1).mp (by rw [← e]; exact List.mem_map_of_mem hx)
  · have hm : v ∈ (c.order.zip rs).map Prod.fst := by rw [e]; exact (F.mem v).mpr hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    exact ⟨x, hx, rfl⟩

/-- Each listed variable's challenge lies at the variable's place. -/
theorem pointOf_mem {c : Cube} (F : FitsP c) {rs : List E} (hr : rs.length = c.n) (x : ℕ × E)
    (hx : x ∈ c.order.zip rs) : (c.pointOf rs).getD (c.n - 1 - x.1) zeroE = x.2 := by
  obtain ⟨h1, h2, _⟩ := zip_facts F hr
  exact pointFold_at c.n (c.order.zip rs) (Array.replicate c.n zeroE) h1 h2 (by simp) x hx

/-- The challenge of round j lies at the place of the round's variable. An equation on words. -/
theorem pointOf_at (c : Cube) (h : c.fits = true) (rs : List E) (hr : rs.length = c.n) (j : ℕ)
    (hj : j < c.n) :
    (c.pointOf rs).getD (c.n - 1 - c.order.getD j 0) zeroE = rs.getD j zeroE := by
  have F := fitsP c h
  have hjo : j < c.order.length := by rw [F.len]; exact hj
  have hjr : j < rs.length := by rw [hr]; exact hj
  have hjz : j < (c.order.zip rs).length := by
    rw [List.length_zip]
    omega
  have hx : (c.order[j], rs[j]) ∈ c.order.zip rs := by
    have e : (c.order.zip rs)[j] = (c.order[j], rs[j]) := List.getElem_zip
    rw [← e]
    exact List.getElem_mem hjz
  have e1 : c.order.getD j 0 = c.order[j] := by simp [List.getD_eq_getElem?_getD, hjo]
  have e2 : rs.getD j zeroE = rs[j] := by simp [List.getD_eq_getElem?_getD, hjr]
  rw [e1, e2]
  exact pointOf_mem F hr _ hx

/-- In the order from the highest variable down the point is the list of the challenges. An
equation on words. -/
theorem pointOf_default (c : Cube) (h : c.fits = true)
    (ho : c.order = OnBytes.Model.orderDefault c.n) (rs : List E) (hr : rs.length = c.n) :
    c.pointOf rs = rs.toArray := by
  apply Array.ext
  · rw [pointOf_size]
    simp [hr]
  · intro j h1 h2
    have hj : j < c.n := by rwa [pointOf_size] at h1
    have hjr : j < rs.length := by rw [hr]; exact hj
    have e0 : c.order.getD j 0 = c.n - 1 - j := by
      rw [ho]
      simp [OnBytes.Model.orderDefault, List.getD_eq_getElem?_getD, hj]
    have hp := pointOf_at c h rs hr j hj
    rw [e0, show c.n - 1 - (c.n - 1 - j) = j by omega] at hp
    have e1 : (c.pointOf rs).getD j zeroE = (c.pointOf rs)[j] := by simp [Array.getD, h1]
    have e2 : rs.getD j zeroE = rs[j] := by simp [List.getD_eq_getElem?_getD, hjr]
    rw [e1, e2] at hp
    rw [hp]
    simp

/-- **Behind all challenges each map's value is its multilinear extension at the challenges.** -/
theorem valuesAt_mle (c : Cube) (h : c.fits = true) (rs : List E) (hr : rs.length = c.n) (m : ℕ) :
    ρ.val ((c.valuesAt rs).getD m zeroE) = ρ.val (mle (c.maps.getD m #[]) (c.pointOf rs)) := by
  have F := fitsP c h
  have I := inv F rs (Nat.le_of_eq hr)
  have hl : (c.bound rs).1 = [] := List.eq_nil_of_length_eq_zero (by have := I.len; omega)
  have hrep := rep ρ F m rs (Nat.le_of_eq hr) fun _ => 0
  rw [hl] at hrep
  have hlist : (List.range c.n).map (prK (setAll ρ (c.order.zip rs) fun _ => 0)) =
      ((c.pointOf rs).toList.map fun zv => (1 - ρ.val zv, ρ.val zv)).reverse := by
    rw [← toList_rev (c.pointOf rs) c.n (pointOf_size c rs), List.map_map, ← List.map_reverse,
      List.reverse_reverse]
    refine List.map_congr_left fun v hv => ?_
    obtain ⟨h1, _, h3⟩ := zip_facts F hr
    obtain ⟨x, hx, rfl⟩ := h3 v (List.mem_range.mp hv)
    show (1 - setAll ρ (c.order.zip rs) (fun _ => 0) x.1,
        setAll ρ (c.order.zip rs) (fun _ => 0) x.1) =
      (1 - ρ.val ((c.pointOf rs).getD (c.n - 1 - x.1) zeroE),
        ρ.val ((c.pointOf rs).getD (c.n - 1 - x.1) zeroE))
    rw [setAll_at ρ _ _ h1 x hx, pointOf_mem F hr x hx]
  rw [valuesAt_getD, mle_sum, eqTab_sum, ← hlist]
  exact hrep

/-- `mle` reads as the sum of the table's entries under the library's kernel. An entry beyond the
table counts as 0; the table's entries from number 2 ^ z.size on are not read. -/
theorem mle_read {K : Type} [Field K] (ρ : Reading K) (t : Tab) (z : Array E) :
    ρ.val (mle t z) = ∑ i ∈ Finset.range (2 ^ z.size),
      Blocks.eqN z.size 0 (OnBytes.Road.pt ρ z) i * ρ.val (t.getD i zeroE) := by
  rw [mle_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [OnBytes.Road.eqTab_value ρ z i (Finset.mem_range.mp hi)]
  rfl

/-- The same in the library's letters. -/
theorem mle_ext {K : Type} [Field K] (ρ : Reading K) (t : Tab) (z : Array E) :
    ρ.val (mle t z) =
      Blocks.ext z.size (fun i => ρ.val (t.getD i zeroE)) (OnBytes.Road.pt ρ z) :=
  mle_read ρ t z

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fits_sizes
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fits_of
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.termsAt_read
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.summandAt_read
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.round_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.part_nil
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.part_sum
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.part_next
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.part_last
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.round_sum_plain
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.round_sum_point
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.total_plain
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.total_point
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.total_ext
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.valuesAt_size
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.pointOf_size
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.zip_facts
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.pointOf_mem
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.pointOf_at
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.pointOf_default
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.valuesAt_mle
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.mle_read
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.mle_ext
