-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/UnitsSel.lean: CONDITIONAL.

What is here. An entry of the honest side's table of a unit's weights under a claim's factors, with
some groups left open (`fbFree`, Johnson/Desc/K4/Honest/Units.lean), reads as the library's sum that
the claim speaks of, with the open groups' indices picked (`sumSel`, Johnson/Road/FormsKeysWv.lean).

How. The loops leave in an entry the sum over the unit's cells whose numbers add to the entry's
(UnitsRead.lean). An open group with a picked index is the same group closed under the factor that
weighs that index alone (UnitsDelta.lean): on the library's side by the definition of its sums; on
the honest side cell by cell: the verifier's coefficients of that closed claim on a row and a column
are the honest weights where the cell's number is the entry's, and 0 elsewhere (UnitsRows.lean,
UnitsCols.lean, UnitsRadix.lean). The wholly closed claim's value is the library's `claim_cells`
(Johnson/Road/FormsKeysFac.lean).

  `selFree`   which index a choice picks in a group
  `fbFree_checks`, `fbFree_size`   what a return says; the table's size
  `find_name`, `extOf_at`, `strideOf_iff`, `selFree_eq`   a group by its name
  `pickT`, `prod_pick`   a number for the closed members, another for the open ones; a product of
     tests
  `rowNumT`, `colNumT`   what an open group adds to a row's and a column's number
  `cell_pick`   **a cell's number is the entry's just where every open group's two parts make the
     picked index**
  `kOf`, `ownCol`, `colWeight_pick`, `colNumber_pick`, `rnOf_pick`, `delta_cols`, `rowPick_eq`   the
     neighbours' laws in these letters
  `cell_eq`   one cell
  `fbFree_sel`   **THE LAW**
  Beside these, smaller steps: `rows_size`, `pickT_none`, `pickT_some`, `one_one`, `map_snd_zip'`.

Limits. At the reading `Reading.gl`. The matrix is any function of row and column to the program's
words, read word by word (`wmOf`). Premises: the layout has the claim's unit; the unit meets the
library's condition `UnitOK`; no two of its groups have one name; no name stands twice among the
open ones; the honest function returns; each open group's index lies below the group's extent.
Nothing on a commitment, a slot or a world.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsRead
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsRows
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsCols
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMergeStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE oneE mulE ofF)
open OnBytes.Model (Reading WsLay WsUnit WsGrp WsFac WsClaim wsClaimShape wsGamma wsRowPart wsEpsT
  wsDigits)
open OnBytes.Road (GrpOK UnitOK sumSel sumIdx wgtOf claim_cells wsGamma_eq gamOf colHalf rowHalf
  bitsOf gl_numerals)
open OnBytes.Desc.First.K4.Honest

/-- idx gives each group's name an index. In a group named in free: that index. In any other group:
none. -/
def selFree (free : List String) (idx : String → ℕ) (g : WsGrp) : Option ℕ :=
  if free.contains g.name then some (idx g.name) else none

/-! ## 1 What a return says -/

theorem fbFree_checks {lay : WsLay} {c : WsClaim} {u : WsUnit} {w : ℕ → ℕ → F}
    {free : List String} (hu : lay.U[c.ui]? = some u) {tab : Array E}
    (h : fbFree lay w c free = some tab) :
    c.f.length = u.g.length ∧ (∀ n ∈ free, n ∈ u.g.map (·.name)) ∧
      ∀ y ∈ c.f.zip u.g, strideOf (stridesOf u free).1 y.2 = none → y.1.fits y.2 = true := by
  unfold fbFree at h
  rw [hu] at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or, not_not,
      Bool.not_eq_false, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, h6⟩ := hc
    refine ⟨h1, fun n hn => ?_, fun y hy hs => ?_⟩
    · obtain ⟨g, hg, e⟩ := h2 n hn
      exact List.mem_map.mpr ⟨g, hg, e⟩
    · rcases h6 y hy with k | k
      · rw [hs] at k
        cases k
      · exact k

/-- The rows' loop keeps the table's size. -/
theorem rows_size (B : Array (Array (ℕ × E))) (rw : Array E) (rn : Array ℕ) (X : ℕ → ℕ → F) :
    ∀ (l : List ℕ) (out : Array E), (l.foldl (fun out y =>
      if OnBytes.isZeroE (rw.getD y zeroE) = true then out
      else (B.toList.zipIdx.filter fun b => !b.1.isEmpty).foldl
        (fun out b => out.modify (rn.getD y 0 + b.2) fun s =>
          OnBytes.maddE s (rw.getD y zeroE)
            (b.1.foldl (fun t x => OnBytes.maddS t (X y x.1) x.2) zeroE))
        out) out).size = out.size
  | [], _ => rfl
  | y :: l, out => by
    rw [List.foldl_cons, rows_size B rw rn X l]
    by_cases hz : OnBytes.isZeroE (rw.getD y zeroE) = true
    · rw [if_pos hz]
    · rw [if_neg hz, size_foldl_modify (fun b : Array (ℕ × E) × ℕ => rn.getD y 0 + b.2)
        (fun b s => OnBytes.maddE s (rw.getD y zeroE)
          (b.1.foldl (fun t x => OnBytes.maddS t (X y x.1) x.2) zeroE))]

/-- **The table has one entry for each choice of the open groups' indices.** -/
theorem fbFree_size {lay : WsLay} {c : WsClaim} {u : WsUnit} {w : ℕ → ℕ → F}
    {free : List String} (hu : lay.U[c.ui]? = some u) {tab : Array E}
    (h : fbFree lay w c free = some tab) : tab.size = (stridesOf u free).2 := by
  unfold fbFree at h
  rw [hu] at h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact (rows_size
      (bucketsOf (colWeight u (c.f.zip u.g) (stridesOf u free).1)
        (colNumber (c.f.zip u.g) (stridesOf u free).1) (2 ^ u.ncb) (stridesOf u free).2)
      (rowWeights u (c.f.zip u.g) (stridesOf u free).1)
      (rowNumbers u (c.f.zip u.g) (stridesOf u free).1) (fun y col => w (u.off + y) col)
      (List.range u.rows) (Array.replicate (stridesOf u free).2 zeroE)).trans
      Array.size_replicate

/-! ## 2 A group by its name -/

/-- Where no two groups have one name, a group is the first of its name. -/
theorem find_name : ∀ (G : List WsGrp), (G.map (·.name)).Nodup → ∀ g ∈ G,
    G.find? (fun x => x.name == g.name) = some g
  | [], _ => fun _ hg => absurd hg List.not_mem_nil
  | x :: G, hd => by
    rw [List.map_cons, List.nodup_cons] at hd
    intro g hg
    rw [List.find?_cons]
    rcases List.mem_cons.mp hg with rfl | hg'
    · rw [beq_self_eq_true]
    · have hne : (x.name == g.name) = false := by
        simpa using fun e : x.name = g.name => hd.1 (by rw [e]; exact List.mem_map_of_mem hg')
      rw [hne]
      exact find_name G hd.2 g hg'

theorem extOf_at {u : WsUnit} (hnd : (u.g.map (·.name)).Nodup) {g : WsGrp} (hg : g ∈ u.g) :
    extOf u g.name = g.R := by
  unfold extOf
  rw [find_name u.g hnd g hg]
  rfl

/-- A group has a stride just where its name is open. -/
theorem strideOf_iff (u : WsUnit) (free : List String) (g : WsGrp) :
    strideOf (stridesOf u free).1 g = none ↔ g.name ∉ free := by
  constructor
  · intro h hm
    obtain ⟨s, hs⟩ := strideOf_some g (stridesOf u free).1 (by rw [strides_names]; exact hm)
    rw [hs] at h
    cases h
  · intro h
    exact strideOf_none g _ (by rw [strides_names]; exact h)

/-- The two ways to pick: by the open names, by the strides. -/
theorem selFree_eq (u : WsUnit) (free : List String) (idx : String → ℕ) :
    selFree free idx = selSt (stridesOf u free).1 idx := by
  funext g
  unfold selFree selSt
  by_cases hm : g.name ∈ free
  · obtain ⟨s, hs⟩ := strideOf_some g (stridesOf u free).1 (by rw [strides_names]; exact hm)
    rw [if_pos (by simpa using hm), hs]
    rfl
  · rw [if_neg (by simpa using hm), (strideOf_iff u free g).mpr hm]
    rfl

/-! ## 3 A cell's number -/

/-- A number for the members without a stride, another for those with one. -/
def pickT {α : Type} (k : α → Option ℕ) (a t : α → Cb.Gl.E) (y : α) : Cb.Gl.E :=
  match k y with
  | none => a y
  | some _ => t y

theorem pickT_none {α : Type} {k : α → Option ℕ} (a t : α → Cb.Gl.E) {y : α} (h : k y = none) :
    pickT k a t y = a y := by
  unfold pickT
  rw [h]

theorem pickT_some {α : Type} {k : α → Option ℕ} (a t : α → Cb.Gl.E) {y : α} {s : ℕ}
    (h : k y = some s) : pickT k a t y = t y := by
  unfold pickT
  rw [h]

/-- A product, over a list, of a number for the members of one kind and a test for those of the
other: the product of the numbers where every test passes; 0 elsewhere. -/
theorem prod_pick {α : Type} (k : α → Option ℕ) (a : α → Cb.Gl.E) (p : α → Prop)
    [DecidablePred p] : ∀ l : List α,
    (l.map (pickT k a fun y => if p y then 1 else 0)).prod =
      if ∀ y ∈ l, k y ≠ none → p y then (l.map (pickT k a fun _ => 1)).prod else 0
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.prod_cons, prod_pick k a p l, List.map_cons, List.prod_cons]
    by_cases hl : ∀ y ∈ l, k y ≠ none → p y
    · rw [if_pos hl]
      cases hk : k x with
      | none =>
        rw [pickT_none _ _ hk, pickT_none _ _ hk,
          if_pos (show ∀ y ∈ x :: l, k y ≠ none → p y from fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact fun hn => absurd hk hn
            · exact hl y hy')]
      | some s =>
        rw [pickT_some _ _ hk, pickT_some _ _ hk]
        by_cases hp : p x
        · rw [if_pos hp, if_pos (show ∀ y ∈ x :: l, k y ≠ none → p y from fun y hy => by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact fun _ => hp
            · exact hl y hy')]
        · rw [if_neg hp, zero_mul, if_neg (show ¬ ∀ y ∈ x :: l, k y ≠ none → p y from fun H =>
            hp (H x List.mem_cons_self (by rw [hk]; exact Option.some_ne_none s)))]
    · rw [if_neg hl, mul_zero, if_neg (show ¬ ∀ y ∈ x :: l, k y ≠ none → p y from fun H =>
        hl fun y hy => H y (List.mem_cons_of_mem _ hy))]

/-- What an open group adds to a row's number. rp: the groups' row parts, by their names. -/
def rowNumT (st : List (String × ℕ)) (rp : String → ℕ) (g : WsGrp) : ℕ :=
  match strideOf st g with
  | none => 0
  | some s => s * grpIndex g 0 (rp g.name)

/-- What an open group adds to a column's number. cp: the groups' column parts. -/
def colNumT (st : List (String × ℕ)) (cp : WsGrp → ℕ) (g : WsGrp) : ℕ :=
  match strideOf st g with
  | none => 0
  | some s => s * grpIndex g (cp g) 0

/-- **A cell's number is the entry's just where every open group's two parts make the picked
index**, among the cells at which every open group's guard passes. -/
theorem cell_pick {u : WsUnit} (hnd : (u.g.map (·.name)).Nodup) (hok : ∀ g ∈ u.g, GrpOK g)
    {free : List String} (hfree : free.Nodup) (hin : ∀ n ∈ free, n ∈ u.g.map (·.name))
    (idx : String → ℕ) (hidx : ∀ g ∈ u.g, g.name ∈ free → idx g.name < g.R) (cp : WsGrp → ℕ)
    (rp : String → ℕ) (hcp : ∀ g ∈ u.g, cp g < 2 ^ g.t) (hrp : ∀ g ∈ u.g, rp g.name < g.left)
    (hgd : ∀ g ∈ u.g, g.name ∈ free → grpGuard g (cp g) = true) :
    ((u.g.map (rowNumT (stridesOf u free).1 rp)).sum +
      (u.g.map (colNumT (stridesOf u free).1 cp)).sum = numFree (stridesOf u free).1 idx) ↔
      ∀ g ∈ u.g, g.name ∈ free → grpIndex g (cp g) (rp g.name) = idx g.name := by
  -- the cell's indices, by the groups' names
  let A : String → ℕ := fun n =>
    match u.g.find? fun x => x.name == n with
    | some g => grpIndex g (cp g) (rp n)
    | none => 0
  have hA : ∀ g ∈ u.g, A g.name = grpIndex g (cp g) (rp g.name) := by
    intro g hg
    show (match u.g.find? fun x => x.name == g.name with
      | some g' => grpIndex g' (cp g') (rp g.name)
      | none => 0) = _
    rw [find_name u.g hnd g hg]
  have hsum : (u.g.map (rowNumT (stridesOf u free).1 rp)).sum +
      (u.g.map (colNumT (stridesOf u free).1 cp)).sum = numFree (stridesOf u free).1 A := by
    rw [← sum_groups u.g hnd A (stridesOf u free).1 (by rw [strides_names]; exact hfree)
      (fun x hx => hin x.1 (by rw [← strides_names u free]; exact List.mem_map_of_mem hx)),
      ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun g hg => ?_
    rw [hA g hg, ← grpIndex_add g (cp g) (rp g.name)]
    unfold rowNumT colNumT
    cases strideOf (stridesOf u free).1 g with
    | none => rfl
    | some s =>
      show s * _ + s * _ = s * (_ + _)
      ring
  have grp : ∀ n ∈ free, ∃ g ∈ u.g, g.name = n := fun n hn => by
    obtain ⟨g, hg, e⟩ := List.mem_map.mp (hin n hn)
    exact ⟨g, hg, e⟩
  have bA : ∀ n ∈ free, A n < extOf u n := by
    intro n hn
    obtain ⟨g, hg, rfl⟩ := grp n hn
    rw [hA g hg, extOf_at hnd hg]
    exact (grpIndex_split (hok g hg) (hcp g hg) (hrp g hg) (hgd g hg hn)).1
  have bI : ∀ n ∈ free, idx n < extOf u n := by
    intro n hn
    obtain ⟨g, hg, rfl⟩ := grp n hn
    rw [extOf_at hnd hg]
    exact hidx g hg hn
  rw [hsum]
  constructor
  · intro h g hg hn
    rw [← hA g hg]
    exact numFree_inj u A idx free bA bI h g.name hn
  · intro h
    unfold numFree
    congr 1
    refine List.map_congr_left fun x hx => ?_
    have hx1 : x.1 ∈ free := by
      rw [← strides_names u free]
      exact List.mem_map_of_mem hx
    obtain ⟨g, hg, e⟩ := grp x.1 hx1
    rw [← e, hA g hg, h g hg (by rw [e]; exact hx1)]

/-! ## 4 The law -/

/-- One times one, on words. -/
theorem one_one : OnBytes.mulE OnBytes.oneE OnBytes.oneE = OnBytes.oneE := by decide

/-- A list made of the pairs of factors and groups that reads the groups alone. -/
theorem map_snd_zip' {β : Type} {f : List WsFac} {G : List WsGrp} (h : f.length = G.length)
    (k : WsGrp → β) : ((f.zip G).map fun y => k y.2) = G.map k := by
  rw [show (fun y : WsFac × WsGrp => k y.2) = k ∘ Prod.snd from rfl, ← List.map_map,
    List.map_snd_zip (by omega)]

variable (st : List (String × ℕ))

/-- The stride of a pair's group. -/
abbrev kOf (z : WsFac × WsGrp) : Option ℕ := strideOf st z.2

/-- A closed group's own column half at the group's part of column C. -/
abbrev ownCol (C : ℕ) (z : WsFac × WsGrp) : Cb.Gl.E := colHalf Reading.gl z.1 z.2 (colPart z.2 C)

theorem colWeight_pick (u : WsUnit) (fs : List (WsFac × WsGrp)) (hok : ∀ y ∈ fs, GrpOK y.2)
    {C : ℕ} (hC : C < 2 ^ u.ncb) :
    Reading.gl.val (colWeight u fs st C) = (fs.map (pickT (kOf st) (ownCol C) fun z =>
      if grpGuard z.2 (colPart z.2 C) = true then 1 else 0)).prod := by
  exact (colWeight_read st u fs hok hC).trans rfl

theorem colNumber_pick (fs : List (WsFac × WsGrp)) (C : ℕ) :
    colNumber fs st C = (fs.map fun z => colNumT st (fun g => colPart g C) z.2).sum := by
  exact (colNumber_read st fs C).trans rfl

theorem rnOf_pick (l : List (WsFac × WsGrp)) (m j : ℕ) (hj : j < m * (l.map (·.2.left)).prod)
    (hd : (l.map (·.2.name)).Nodup) :
    (rnOf st l (Array.replicate m 0)).getD j 0 =
      (l.map fun z => rowNumT st (rowPart l j) z.2).sum := by
  exact (rnOf_at l m j hj hd).trans rfl

/-- The closed claim's column halves. -/
theorem delta_cols (tv : String → ℕ) (C : ℕ) (l : List (WsFac × WsGrp)) :
    ((deltaAt (selSt st tv) l).map fun z => colHalf Reading.gl z.1 z.2 (colPart z.2 C)) =
      l.map (pickT (kOf st) (ownCol C) fun z =>
        colHalf Reading.gl (deltaFac z.2 (tv z.2.name)) z.2 (colPart z.2 C)) := by
  unfold deltaAt
  rw [List.map_map]
  refine List.map_congr_left fun z _ => ?_
  show colHalf Reading.gl (pickFac (selSt st tv) z) z.2 (colPart z.2 C) = _
  cases hs : strideOf st z.2 with
  | none => rw [pickFac_none (selSt_none hs), pickT_none _ _ (show kOf st z = none from hs)]
  | some s => rw [pickFac_some (selSt_some hs), pickT_some _ _ (show kOf st z = some s from hs)]

/-- The open factors' row halves. -/
theorem rowPick_eq (tv : String → ℕ) (rp : String → ℕ) (z : WsFac × WsGrp) :
    rowPick st tv rp z = pickT (kOf st) (fun _ => 1) (fun z =>
      rowHalf Reading.gl (deltaFac z.2 (tv z.2.name)) z.2 (rp z.2.name)) z := by
  unfold rowPick pickT kOf
  cases strideOf st z.2 <;> rfl

/-- **ONE CELL**: the honest weights, where the cell's number is the entry's, are the verifier's
coefficients of the closed claim. a: the row's honest weight; X: the cell's word, read. -/
theorem cell_eq {c : WsClaim} {u : WsUnit} {lk : ℕ} (hlen : c.f.length = u.g.length)
    (hnd : (u.g.map (·.name)).Nodup) (U : UnitOK lk u) {free : List String} (hfree : free.Nodup)
    (hin : ∀ n ∈ free, n ∈ u.g.map (·.name)) (idx : String → ℕ)
    (hidx : ∀ g ∈ u.g, g.name ∈ free → idx g.name < g.R) (C y : ℕ)
    (hy : y < u.nlw * ((c.f.zip u.g).map (·.2.left)).prod) (a X : Cb.Gl.E) :
    (if ((c.f.zip u.g).map fun z =>
          rowNumT (stridesOf u free).1 (rowPart (c.f.zip u.g) y) z.2).sum +
        ((c.f.zip u.g).map fun z =>
          colNumT (stridesOf u free).1 (fun g => colPart g C) z.2).sum =
        numFree (stridesOf u free).1 idx then
      a * (X * ((c.f.zip u.g).map (pickT (kOf (stridesOf u free).1) (ownCol C) fun z =>
        if grpGuard z.2 (colPart z.2 C) = true then 1 else 0)).prod)
    else 0) =
      a * ((c.f.zip u.g).map
          (rowPick (stridesOf u free).1 idx (rowPart (c.f.zip u.g) y))).prod *
        ((deltaAt (selSt (stridesOf u free).1 idx) (c.f.zip u.g)).map fun z =>
          colHalf Reading.gl z.1 z.2 (colPart z.2 C)).prod * X := by
  have hnames : ((c.f.zip u.g).map (·.2.name)).Nodup := by
    rw [map_snd_zip' hlen fun g => g.name]
    exact hnd
  have hmem : ∀ z ∈ c.f.zip u.g, z.2 ∈ u.g := fun z hz => (List.of_mem_zip hz).2
  have hpair : ∀ g ∈ u.g, ∃ z ∈ c.f.zip u.g, z.2 = g := by
    intro g hg
    have : g ∈ (c.f.zip u.g).map Prod.snd := by
      rw [List.map_snd_zip (by omega)]
      exact hg
    obtain ⟨z, hz, e⟩ := List.mem_map.mp this
    exact ⟨z, hz, e⟩
  have hrp : ∀ g ∈ u.g, rowPart (c.f.zip u.g) y g.name < g.left := by
    intro g hg
    obtain ⟨z, hz, rfl⟩ := hpair g hg
    exact rowPart_lt (c.f.zip u.g) u.nlw y hy hnames z hz
  have hopen : ∀ z : WsFac × WsGrp, kOf (stridesOf u free).1 z ≠ none ↔ z.2.name ∈ free :=
    fun z => by
      show strideOf (stridesOf u free).1 z.2 ≠ none ↔ _
      rw [ne_eq, strideOf_iff, not_not]
  -- the right side's two products, joined, are a product of tests
  have eR : ((c.f.zip u.g).map
        (rowPick (stridesOf u free).1 idx (rowPart (c.f.zip u.g) y))).prod *
      ((deltaAt (selSt (stridesOf u free).1 idx) (c.f.zip u.g)).map fun z =>
        colHalf Reading.gl z.1 z.2 (colPart z.2 C)).prod =
      ((c.f.zip u.g).map (pickT (kOf (stridesOf u free).1) (ownCol C) fun z =>
        if grpGuard z.2 (colPart z.2 C) = true ∧
            grpIndex z.2 (colPart z.2 C) (rowPart (c.f.zip u.g) y z.2.name) = idx z.2.name
          then 1 else 0)).prod := by
    rw [delta_cols, ← List.prod_map_mul]
    congr 1
    refine List.map_congr_left fun z hz => ?_
    rw [rowPick_eq]
    cases hs : kOf (stridesOf u free).1 z with
    | none =>
      rw [pickT_none _ _ hs, pickT_none _ _ hs, pickT_none _ _ hs, one_mul]
    | some s =>
      rw [pickT_some _ _ hs, pickT_some _ _ hs, pickT_some _ _ hs, mul_comm,
        halves_delta Reading.gl (U.grp z.2 (hmem z hz)) _ (colPart_lt z.2 C)
          (hrp z.2 (hmem z hz))]
  rw [mul_assoc a, eR, prod_pick, prod_pick,
    map_snd_zip' hlen (rowNumT (stridesOf u free).1 (rowPart (c.f.zip u.g) y)),
    map_snd_zip' hlen (colNumT (stridesOf u free).1 fun g => colPart g C)]
  by_cases hgd : ∀ z ∈ c.f.zip u.g, kOf (stridesOf u free).1 z ≠ none →
      grpGuard z.2 (colPart z.2 C) = true
  · have hgd' : ∀ g ∈ u.g, g.name ∈ free → grpGuard g (colPart g C) = true := by
      intro g hg hn
      obtain ⟨z, hz, rfl⟩ := hpair g hg
      exact hgd z hz ((hopen z).mpr hn)
    have key := cell_pick hnd U.grp hfree hin idx hidx (fun g => colPart g C)
      (rowPart (c.f.zip u.g) y) (fun g _ => colPart_lt g C) hrp hgd'
    rw [if_pos hgd]
    by_cases hall : ∀ g ∈ u.g, g.name ∈ free →
        grpIndex g (colPart g C) (rowPart (c.f.zip u.g) y g.name) = idx g.name
    · rw [if_pos (key.mpr hall), if_pos (show ∀ z ∈ c.f.zip u.g,
          kOf (stridesOf u free).1 z ≠ none → grpGuard z.2 (colPart z.2 C) = true ∧
            grpIndex z.2 (colPart z.2 C) (rowPart (c.f.zip u.g) y z.2.name) = idx z.2.name from
        fun z hz hs => ⟨hgd z hz hs, hall z.2 (hmem z hz) ((hopen z).mp hs)⟩)]
      ring
    · rw [if_neg fun k => hall (key.mp k), if_neg (show ¬ ∀ z ∈ c.f.zip u.g,
          kOf (stridesOf u free).1 z ≠ none → grpGuard z.2 (colPart z.2 C) = true ∧
            grpIndex z.2 (colPart z.2 C) (rowPart (c.f.zip u.g) y z.2.name) = idx z.2.name from
        fun H => hall fun g hg hn => by
          obtain ⟨z, hz, rfl⟩ := hpair g hg
          exact (H z hz ((hopen z).mpr hn)).2)]
      ring
  · rw [if_neg hgd, if_neg (show ¬ ∀ z ∈ c.f.zip u.g,
        kOf (stridesOf u free).1 z ≠ none → grpGuard z.2 (colPart z.2 C) = true ∧
          grpIndex z.2 (colPart z.2 C) (rowPart (c.f.zip u.g) y z.2.name) = idx z.2.name from
      fun H => hgd fun z hz hs => (H z hz hs).1)]
    simp only [mul_zero, zero_mul, ite_self]

/-- **AN ENTRY OF THE TABLE WITH OPEN GROUPS IS THE LIBRARY's SUM WITH THESE GROUPS' INDICES
PICKED.** idx: an index below its extent for each open group. The entry's number is the sum of the
open groups' strides times their indices; the strides are `stridesOf`'s: the first name is the most
significant. -/
theorem fbFree_sel {lay : WsLay} {c : WsClaim} {u : WsUnit} (w : ℕ → ℕ → F) (free : List String)
    (hu : lay.U[c.ui]? = some u) (U : UnitOK lay.lk u) (hnd : (u.g.map (·.name)).Nodup)
    (hfree : free.Nodup) {tab : Array E} (h : fbFree lay w c free = some tab) (idx : String → ℕ)
    (hidx : ∀ g ∈ u.g, g.name ∈ free → idx g.name < g.R) :
    Reading.gl.val (tab.getD (numFree (stridesOf u free).1 idx) zeroE) =
      sumSel Reading.gl (selFree free idx) (c.f.zip u.g) (wgtOf u (wmOf w)) := by
  obtain ⟨hlen, hin, hfit⟩ := fbFree_checks hu h
  have hmem : ∀ y ∈ c.f.zip u.g, y.2 ∈ u.g := fun y hy => (List.of_mem_zip hy).2
  have hokG : ∀ y ∈ c.f.zip u.g, GrpOK y.2 := fun y hy => U.grp y.2 (hmem y hy)
  have hRows : RowsOK (stridesOf u free).1 (c.f.zip u.g) := fun y hy => ⟨hokG y hy, hfit y hy⟩
  have hnames : ((c.f.zip u.g).map (·.2.name)).Nodup := by
    rw [map_snd_zip' hlen fun g => g.name]
    exact hnd
  have hleft : ((c.f.zip u.g).map (·.2.left)).prod = (u.g.map (·.left)).prod := by
    rw [map_snd_zip' hlen fun g => g.left]
  have hbound : numFree (stridesOf u free).1 idx < (stridesOf u free).2 :=
    numFree_lt u idx free fun n hn => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (hin n hn)
      rw [extOf_at hnd hg]
      exact hidx g hg hn
  -- the closed claim
  let c' : WsClaim :=
    { c with f := (deltaAt (selSt (stridesOf u free).1 idx) (c.f.zip u.g)).map Prod.fst }
  have hu' : lay.U[c'.ui]? = some u := hu
  have hzip : c'.f.zip u.g = deltaAt (selSt (stridesOf u free).1 idx) (c.f.zip u.g) := by
    have e2 : (deltaAt (selSt (stridesOf u free).1 idx) (c.f.zip u.g)).map Prod.snd = u.g := by
      unfold deltaAt
      rw [List.map_map]
      exact List.map_snd_zip (by omega)
    exact (List.zip_of_prod rfl e2).symm
  have hlen' : c'.f.length = u.g.length := by
    show ((deltaAt _ (c.f.zip u.g)).map Prod.fst).length = _
    unfold deltaAt
    rw [List.length_map, List.length_map, List.length_zip, hlen, Nat.min_self]
  have hs' : wsClaimShape lay c' = .ok () := by
    unfold wsClaimShape
    rw [hu']
    have hall : (c'.f.length == u.g.length && ((c'.f.zip u.g).all fun y => y.1.fits y.2)) =
        true := by
      rw [hlen', beq_self_eq_true, Bool.true_and, hzip, List.all_eq_true]
      intro y hy
      exact (delta_ok idx hRows y hy).2
    show (if (c'.f.length == u.g.length && ((c'.f.zip u.g).all fun y => y.1.fits y.2)) = true
      then (pure () : Except String Unit) else throw "internal-claim-factors") = .ok ()
    rw [if_pos hall]
    rfl
  -- the library's side
  have hR : sumSel Reading.gl (selFree free idx) (c.f.zip u.g) (wgtOf u (wmOf w)) =
      OnBytes.Road.claimVal Reading.gl lay (wmOf w) c' := by
    unfold OnBytes.Road.claimVal
    rw [hu']
    show _ = sumIdx Reading.gl (c'.f.zip u.g) (wgtOf u (wmOf w))
    rw [hzip, sumIdx_delta Reading.gl _ _ hokG, selFree_eq u free idx]
  have hcells := claim_cells gl_numerals hu' hs' U (wmOf w) oneE oneE
  rw [Reading.gl.one, one_mul, one_mul] at hcells
  rw [hR, ← hcells, fbFree_read w free hu h _ hbound, Finset.sum_comm]
  -- the columns that the groups cannot spell count 0
  have hle : 2 ^ u.ncb ≤ 2 ^ lay.lk := Nat.pow_le_pow_right (by norm_num) U.le
  refine Eq.trans ?_ (Finset.sum_subset (Finset.range_subset_range.mpr hle) fun C hC hn => by
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [eps_corner hu' U (Finset.mem_range.mp hC),
      if_neg (fun k => hn (Finset.mem_range.mpr k)), mul_zero, mul_zero, zero_mul])
  refine Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun y hy => ?_
  have hC' := Finset.mem_range.mp hC
  have hy' : y < (wsDigits u.nlw oneE).toArray.size * ((c.f.zip u.g).map (·.2.left)).prod := by
    rw [hleft, List.size_toArray, OnBytes.Road.wsDigits_length, ← U.rows]
    exact Finset.mem_range.mp hy
  have hy'' : y < u.nlw * ((c.f.zip u.g).map (·.2.left)).prod := by
    rw [hleft, ← U.rows]
    exact Finset.mem_range.mp hy
  -- the four letters, in the library's halves
  rw [eps_corner hu' U (lt_of_lt_of_le hC' hle), if_pos hC', mul_one, hzip,
    wsGamma_eq hu' oneE oneE, hzip, one_one,
    gam_at idx _ (c.f.zip u.g) hRows hnames y hy', rowWeights_eq, rowNumbers_eq',
    rnOf_pick _ (c.f.zip u.g) u.nlw y hy'' hnames, colWeight_pick _ u _ hokG hC',
    colNumber_pick]
  exact cell_eq hlen hnd U hfree hin idx hidx C y hy'' _ _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.fbFree_checks
#print axioms ProofFile.Honest.K4.rows_size
#print axioms ProofFile.Honest.K4.fbFree_size
#print axioms ProofFile.Honest.K4.find_name
#print axioms ProofFile.Honest.K4.extOf_at
#print axioms ProofFile.Honest.K4.strideOf_iff
#print axioms ProofFile.Honest.K4.selFree_eq
#print axioms ProofFile.Honest.K4.pickT_none
#print axioms ProofFile.Honest.K4.pickT_some
#print axioms ProofFile.Honest.K4.prod_pick
#print axioms ProofFile.Honest.K4.cell_pick
#print axioms ProofFile.Honest.K4.one_one
#print axioms ProofFile.Honest.K4.map_snd_zip'
#print axioms ProofFile.Honest.K4.colWeight_pick
#print axioms ProofFile.Honest.K4.colNumber_pick
#print axioms ProofFile.Honest.K4.rnOf_pick
#print axioms ProofFile.Honest.K4.delta_cols
#print axioms ProofFile.Honest.K4.rowPick_eq
#print axioms ProofFile.Honest.K4.cell_eq
#print axioms ProofFile.Honest.K4.fbFree_sel
