-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPan.lean: on the panels of a layer sub-proof's batched sumcheck.

The keys of some lookup segments hold inner products. One sumcheck proves them all; a stretch of its
two long vectors, a panel, holds the inner products of one segment
(OnBytes/Model/LayerPanels.lean). The library writes the same panels as mathematics
(Inst/Model/FF/Objects.lean: Pan.A, Pan.B, Pan.wt, offP). This file has three statements:
 - where the verifier places the panels: each panel's first place is a multiple of its size (on the
   verifier's own list; the library's offP is not compared),
 - what the sides and weights of one panel, that of the segment V, are worth,
 - what a factor of a weight claim means, and that the factor which is made from a segment's
   columns weighs each index with that segment's own weight.

Main definition: facAt (what a factor of a weight claim weighs an index with).
Main theorems: placePanels_dvd; panelV_spec; eqTab_split, facEw_at.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. Nothing here is on the other panels, on the
sumcheck's end, on the other factors of a weight claim, or on how a claim is settled on the
committed matrix of weights. The program does not import this file.
-/
import Johnson.Road.FormsKeysEq
import OnBytes.Model.LayerPanels

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab Seg CallD WsGrp WsFac)
open OnBytes.Model.Layer (Env SBlk Panels PanelEnv placePanels panelA ClaimEnv)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell)

/-! ## Where the panels are placed -/

/-- The bits of a place in panel number i. -/
def wOf (bl : Array SBlk) (i : ℕ) : ℕ := (bl.getD i {}).w

/-- One step of the placing: panel i gets the first free place, and the places of its size are
taken. -/
def placeStep (bl : Array SBlk) (s : Array SBlk × ℕ) (i : ℕ) : Array SBlk × ℕ :=
  (s.1.modify i fun b => { b with off := s.2 }, s.2 + 2 ^ (bl.getD i {}).w)

/-- The order in which the panels are placed: the largest first. -/
def placeOrder (bl : Array SBlk) : List ℕ :=
  (List.range bl.size).mergeSort fun a b => decide ((bl.getD b {}).w ≤ (bl.getD a {}).w)

/-- What placePanels is, in these words. -/
theorem placePanels_eq (bl : Array SBlk) :
    placePanels bl = (placeOrder bl).foldl (placeStep bl) (bl, 0) := rfl

/-- The placing keeps the number of panels. -/
theorem place_size (bl : Array SBlk) : ∀ (l : List ℕ) (s : Array SBlk × ℕ),
    (l.foldl (placeStep bl) s).1.size = s.1.size
  | [], _ => rfl
  | a :: l, s => by
    rw [List.foldl_cons, place_size bl l]
    simp [placeStep]

/-- A panel that is not in the list is left as it is. -/
theorem place_other (bl : Array SBlk) : ∀ (l : List ℕ) (s : Array SBlk × ℕ) (i : ℕ), i ∉ l →
    (l.foldl (placeStep bl) s).1.getD i {} = s.1.getD i {}
  | [], _, _, _ => rfl
  | a :: l, s, i, h => by
    have h1 : i ≠ a := fun e => h (e ▸ List.mem_cons_self)
    have h2 : i ∉ l := fun e => h (List.mem_cons_of_mem _ e)
    rw [List.foldl_cons, place_other bl l _ i h2]
    simp [placeStep, Array.getD, Array.getElem_modify, Ne.symm h1]

/-- The panel that a step places gets the first free place and keeps its other fields. -/
theorem placeStep_self (bl : Array SBlk) (s : Array SBlk × ℕ) (a : ℕ) (h : a < s.1.size) :
    (placeStep bl s a).1.getD a {} = { s.1.getD a {} with off := s.2 } := by
  simp [placeStep, Array.getD, Array.getElem_modify, h]

/-- If the panels of a list are placed in an order of falling sizes, from a first free place that
every size in the list divides, then each panel's first place is a multiple of its size. -/
theorem place_dvd (bl : Array SBlk) : ∀ (l : List ℕ) (s : Array SBlk × ℕ),
    l.Pairwise (fun a b => wOf bl b ≤ wOf bl a) → l.Nodup → (∀ j ∈ l, 2 ^ wOf bl j ∣ s.2) →
    ∀ i ∈ l, i < s.1.size → 2 ^ wOf bl i ∣ ((l.foldl (placeStep bl) s).1.getD i {}).off
  | [], _, _, _, _, i, hi, _ => by simp at hi
  | a :: l, s, hp, hn, hd, i, hi, hs => by
    rw [List.foldl_cons]
    have hp' := List.pairwise_cons.mp hp
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hi with e | hil
    · subst e
      rw [place_other bl l _ i hn'.1, placeStep_self bl s i hs]
      exact hd i List.mem_cons_self
    · refine place_dvd bl l _ hp'.2 hn'.2 (fun j hj => ?_) i hil (by simpa [placeStep] using hs)
      exact Nat.dvd_add (hd j (List.mem_cons_of_mem _ hj)) (pow_dvd_pow 2 (hp'.1 j hj))

/-- The order of the placing lists every panel once, in an order of falling sizes. -/
theorem placeOrder_spec (bl : Array SBlk) :
    (placeOrder bl).Pairwise (fun a b => wOf bl b ≤ wOf bl a) ∧ (placeOrder bl).Nodup ∧
      ∀ i, i ∈ placeOrder bl ↔ i < bl.size := by
  have perm : (placeOrder bl).Perm (List.range bl.size) := List.mergeSort_perm _ _
  refine ⟨?_, perm.nodup_iff.mpr List.nodup_range, fun i => ?_⟩
  · have srt := List.pairwise_mergeSort
      (le := fun a b => decide ((bl.getD b {}).w ≤ (bl.getD a {}).w))
      (fun a b c h1 h2 => by
        simp only [decide_eq_true_eq] at h1 h2 ⊢
        omega)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega)
      (List.range bl.size)
    exact srt.imp fun h => by simpa [wOf] using h
  · rw [perm.mem_iff, List.mem_range]

/-- Each panel's first place is a multiple of the panel's size. -/
theorem placePanels_dvd (bl : Array SBlk) (i : ℕ) (hi : i < bl.size) :
    2 ^ wOf bl i ∣ ((placePanels bl).1.getD i {}).off := by
  obtain ⟨hp, hn, hm⟩ := placeOrder_spec bl
  rw [placePanels_eq]
  exact place_dvd bl _ _ hp hn (fun j _ => Nat.dvd_zero _) i ((hm i).mpr hi) hi

#print axioms placePanels_dvd

/-! ## The panel of the segment V -/

section PanelV

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K}

omit [Field K] scl in
/-- What panelA appends for the segment V. -/
theorem panelA_V_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelA p ec el "V" s = Model.Layer.plain p.v.y ec 0 false p.v.y.h.d
      (some fun lam k2 => p.v.shIn (p.v.tensorAt "a" "zt") lam k2) none
      (fun lam => mulE (el.getD lam zeroE) (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkv))
      none s := rfl

/-- The panel that the verifier appends for the segment V, against the library's panel Pan.V: as
many rows (Pan.nr) and columns (Pan.nc); the A side at (layer, channel) is worth Pan.A at any record
of reads whose a1 is the extension of the array a at the lookup's token point (rdTrue has that a1);
the weight of a row of the group is the layer's weight under the factor 2^max(0, 16 - kv), which is
the shape of Pan.wt, with the layer's weight left free; the B side is a weight matrix, with one
weight claim for each row. -/
theorem panelV_spec (F : Fits ρ W v D c t low u) (p : PanelEnv) (hp : p.v = v) (ec : E)
    (el : Array E) (s : Panels) :
    ∃ b : SBlk, (panelA p ec el "V" s).bl = s.bl.push b ∧
      (panelA p ec el "V" s).nextV = s.nextV + v.y.Lam ∧
      b.tri = false ∧ b.claim = 0 ∧ b.ec = ec ∧ b.ni = Inst.Model.FFSeg.Pan.V.nr D ∧
      b.ny = Inst.Model.FFSeg.Pan.V.nc D ∧
      b.v0 = some s.nextV ∧ b.virt = none ∧ b.B.isNone = true ∧
      (∃ A, b.A = some A ∧ ∀ (r : Inst.Model.FFSeg.Rd K),
        (∀ l j, r.a1 l j = Inst.Model.FFSeg.valU D t .a l j u) → ∀ lam k2 a, A lam k2 = some a →
          a.value ρ W = Inst.Model.FFSeg.Pan.V.A D r lam k2) ∧
      ∀ lam, lam < v.y.Lam → ρ.val (b.wt.getD lam zeroE) =
        Inst.Model.Site.scl (D.Pl lam).kv (ρ.val (el.getD lam zeroE)) := by
  subst hp
  rw [panelA_V_eq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, F.Lam, F.d, rfl, rfl, rfl, ⟨_, rfl, ?_⟩, ?_⟩
  · intro r hr lam k2 a ha
    have ha' : p.v.shA "a" "zt" lam k2 = some a := ha
    show _ = r.a1 lam k2
    rw [F.shA .a rfl ha', hr]
    unfold Inst.Model.FFSeg.valU
    congr 1
    funext i
    simp [raw, Inst.Model.FFSeg.Arr.off]
  · intro lam hlam
    have e : ((Array.range p.v.y.Lam).map fun i =>
        mulE (el.getD i zeroE) (Model.Layer.kT p.v.sc (p.v.lay i) Model.Layer.Lkv)).getD lam zeroE =
        mulE (el.getD lam zeroE) (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkv) := by
      simp [Array.getD, hlam]
    show ρ.val (((Array.range p.v.y.Lam).map fun i =>
        mulE (el.getD i zeroE)
          (Model.Layer.kT p.v.sc (p.v.lay i) Model.Layer.Lkv)).getD lam zeroE) = _
    rw [e, ρ.mul, Inst.Model.Site.scl_eq]
    unfold Model.Layer.kT Model.Layer.tOf Inst.Model.Site.dn
    rw [F.num.pw, F.kv lam (F.Lam ▸ hlam)]
    ring

#print axioms panelV_spec

end PanelV

/-! ## A factor of a weight claim -/

section Factor

variable {K : Type} [Field K] (ρ : Reading K)

/-- What a claim's factor for one index group weighs the index idx with. Class 'E': the index is
hi 2^z + lo; the weight is the element for hi times the equality weight of the factor's point at lo,
the point's first coordinate with the top bit of lo. Class 'A': the element that is written out for
the index. -/
def facAt (x : WsFac) (g : WsGrp) (idx : ℕ) : K :=
  if g.cls == 'E' then
    ρ.val (x.HV.getD (idx / 2 ^ g.z) zeroE) * Blocks.eqN g.z 0 (pt ρ x.pt) (idx % 2 ^ g.z)
  else ρ.val (x.AV.getD idx zeroE)

/-- The table of equality weights of a point, cut after its first lJ - ls coordinates: the entry at
2^ls Q + r is the entry at Q of the table of the first coordinates, times the equality weight of the
last ls at r. zh: the point's first lJ - ls coordinates. -/
theorem eqTab_split {ls lJ : ℕ} (z zh : Array E) (hz : z.size = lJ) (hls : ls ≤ lJ)
    (hzh : zh.size = lJ - ls) (hpre : ∀ j, j < lJ - ls → zh.getD j zeroE = z.getD j zeroE)
    {Q r : ℕ} (hQ : Q < 2 ^ (lJ - ls)) (hr : r < 2 ^ ls) :
    ρ.val ((eqTab z).getD (2 ^ ls * Q + r) zeroE) =
      ρ.val ((eqTab zh).getD Q zeroE) * Blocks.eqN ls 0 (fun j => pt ρ z (lJ - ls + j)) r := by
  have hsplit : lJ = lJ - ls + ls := by omega
  have hlt : 2 ^ ls * Q + r < 2 ^ z.size := by
    rw [hz, hsplit, pow_add]
    have h1 : Q + 1 ≤ 2 ^ (lJ - ls) := hQ
    have h2 : 2 ^ ls * (Q + 1) ≤ 2 ^ ls * 2 ^ (lJ - ls) := Nat.mul_le_mul_left _ h1
    have h3 : 2 ^ (lJ - ls) * 2 ^ ls = 2 ^ ls * 2 ^ (lJ - ls) := by ring
    have h4 : 2 ^ ls * (Q + 1) = 2 ^ ls * Q + 2 ^ ls := by ring
    omega
  rw [eqTab_value ρ z _ hlt, eqTab_value ρ zh _ (by rw [hzh]; exact hQ), hz, hzh, eqN_shift']
  have e := Blocks.eqN_append (lJ - ls) ls 0 (pt ρ z) Q hr
  rw [← hsplit, Nat.zero_add] at e
  rw [e]
  congr 1
  refine eqN_congr' _ _ (fun j hj => ?_) Q
  unfold pt
  rw [Nat.zero_add, hpre j hj]

/-- If a function that may refuse is run over a list and nothing is refused, the results are as many
as the list's members, and each is its member's. -/
theorem list_mapM_some {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.length = l.length ∧
      ∀ (i : ℕ) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ f a = some b
  | [], r, h => by
    have hr : r = [] := by simpa using h.symm
    subst hr
    exact ⟨rfl, fun i a ha => by simp at ha⟩
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    cases h1 : f x with
    | none => simp [h1] at h
    | some b =>
      cases h2 : l.mapM f with
      | none => simp [h1, h2] at h
      | some bs =>
        have hr : r = b :: bs := by simpa [h1, h2] using h.symm
        subst hr
        obtain ⟨hl, hi⟩ := list_mapM_some f l bs h2
        refine ⟨by simp [hl], fun i a ha => ?_⟩
        cases i with
        | zero =>
          have : x = a := by simpa using ha
          subst this
          exact ⟨b, by simp, h1⟩
        | succ i =>
          have ha' : l[i]? = some a := by simpa using ha
          obtain ⟨b', hb', hf⟩ := hi i a ha'
          exact ⟨b', by simpa using hb', hf⟩

/-- An entry that is there is what getD reads. -/
theorem getD_of_some {α : Type} {a : Array α} {i : ℕ} {x : α} (h : a[i]? = some x) (d : α) :
    a.getD i d = x := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- The factor that is made from the columns of segment sn, from its entry x0 on, weighs the index
idx of its group with the weight that the lookup's join gives to entry x0 + idx of the segment: the
equality weight of the column's point at that entry's column. Asked: the group has class 'E'; the
stretch of the segment from x0 on lies in runs of 2^z neighbouring columns, each from a multiple of
2^z on; the call's point is long enough. -/
theorem facEw_at (c : ClaimEnv) (G : WsGrp) (sn : String) (x0 q : ℕ) (cd : CallD) (s : Seg)
    (hcall : c.v.callOf sn = some (q, cd, s)) (hE : (G.cls == 'E') = true)
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size)
    (hrun : ∀ xh r, xh < G.o → r < 2 ^ G.z →
      s.pos.getD (x0 + xh * 2 ^ G.z + r) 0 = s.pos.getD (x0 + xh * 2 ^ G.z) 0 + r)
    (hstart : ∀ xh, xh < G.o → 2 ^ G.z ∣ s.pos.getD (x0 + xh * 2 ^ G.z) 0)
    (hin : ∀ x, x < x0 + G.o * 2 ^ G.z → x < s.pos.size ∧ s.pos.getD x 0 < 2 ^ cd.lJ)
    {X : WsFac} (h : c.facEw G sn x0 = some X) (idx : ℕ) (hidx : idx < G.o * 2 ^ G.z) :
    facAt ρ X G idx = ρ.val ((Env.ewFrom (eqTab (c.v.zj q cd.lJ)) s).getD (x0 + idx) zeroE) := by
  unfold ClaimEnv.facEw at h
  rw [hcall] at h
  have h' : (do
      if G.z > cd.lJ then none
      let HV ← (Array.range G.o).mapM fun xh => do
        (eqTab ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)))[(← s.pos[x0 + xh * 2 ^ G.z]?) / 2 ^ G.z]?
      pure ({ pt := (Array.range G.z).map fun i => (c.v.zj q cd.lJ).getD (cd.lJ - G.z + i) zeroE,
              HV := HV } : WsFac)) = some X := h
  have hz : G.z ≤ cd.lJ := by
    by_contra hc
    have hc' : G.z > cd.lJ := by omega
    simp only [hc', ↓reduceIte] at h'
    cases h'
  have hn : ¬ G.z > cd.lJ := by omega
  simp only [hn, ↓reduceIte] at h'
  obtain ⟨_, _, h2⟩ := bind_some h'
  obtain ⟨HV, hm, h3⟩ := bind_some h2
  cases h3
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hm
  obtain ⟨l, hl, hHV⟩ := map_some hm
  subst hHV
  have hpos : 0 < 2 ^ G.z := by positivity
  have hxh : idx / 2 ^ G.z < G.o := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hidx
  have hr : idx % 2 ^ G.z < 2 ^ G.z := Nat.mod_lt _ hpos
  have hsplit : idx = idx / 2 ^ G.z * 2 ^ G.z + idx % 2 ^ G.z := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod idx (2 ^ G.z)).symm
  obtain ⟨b, hb, hf⟩ := (list_mapM_some _ _ l hl).2 (idx / 2 ^ G.z) (idx / 2 ^ G.z)
    (by simp [hxh])
  obtain ⟨P, hP, hbe⟩ := bind_some hf
  have hP' := getD_of_some hP 0
  obtain ⟨Q, hQ⟩ := hstart _ hxh
  rw [hP'] at hQ
  have s1 : (c.v.zj q cd.lJ).size = cd.lJ := by
    unfold Env.zj
    rw [Array.size_extract]
    omega
  have s2 : ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)).size = cd.lJ - G.z := by
    rw [Array.size_extract, s1]
    omega
  have hlt0 : x0 + idx / 2 ^ G.z * 2 ^ G.z < x0 + G.o * 2 ^ G.z := by
    have h1 : idx / 2 ^ G.z * 2 ^ G.z ≤ idx := by omega
    omega
  have hPlt := (hin _ hlt0).2
  rw [hP', hQ] at hPlt
  have hQlt : Q < 2 ^ (cd.lJ - G.z) := by
    have e : cd.lJ = cd.lJ - G.z + G.z := by omega
    rw [e, pow_add] at hPlt
    by_contra hc
    have h1 : 2 ^ (cd.lJ - G.z) ≤ Q := Nat.le_of_not_lt hc
    have h2 : 2 ^ G.z * 2 ^ (cd.lJ - G.z) ≤ 2 ^ G.z * Q := Nat.mul_le_mul_left _ h1
    have h3 : 2 ^ (cd.lJ - G.z) * 2 ^ G.z = 2 ^ G.z * 2 ^ (cd.lJ - G.z) := by ring
    omega
  have hcol : s.pos.getD (x0 + idx) 0 = 2 ^ G.z * Q + idx % 2 ^ G.z := by
    have e : x0 + idx = x0 + idx / 2 ^ G.z * 2 ^ G.z + idx % 2 ^ G.z := by omega
    rw [e, hrun _ _ hxh hr, hP', hQ]
  have hHVb : (l.toArray).getD (idx / 2 ^ G.z) zeroE = b := getD_of_some (by simpa using hb) zeroE
  have hbe' := getD_of_some hbe zeroE
  rw [hQ, Nat.mul_div_cancel_left Q hpos] at hbe'
  unfold facAt Env.ewFrom
  rw [if_pos hE, getD_map_lt _ _ (hin _ (by omega)).1 zeroE 0, hcol,
    eqTab_split ρ _ _ s1 hz s2 (fun j hj => by
      have h1 : j < ((c.v.zj q cd.lJ).extract 0 (cd.lJ - G.z)).size := by rw [s2]; exact hj
      have h2 : j < (c.v.zj q cd.lJ).size := by rw [s1]; omega
      simp [Array.getD, h2, hj]) hQlt hr, hHVb, hbe']
  congr 1
  refine eqN_congr' _ _ (fun j hj => ?_) _
  unfold pt
  rw [Nat.zero_add, getD_map_lt _ _ (by simpa using hj) zeroE 0]
  simp [Array.getD, hj]

#print axioms facEw_at

end Factor

end OnBytes.Road
