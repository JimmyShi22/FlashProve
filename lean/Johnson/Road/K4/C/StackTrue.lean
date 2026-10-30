-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackTrue.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the batched sumcheck: ON
THE TRUE END VALUES THE VERIFIER's TWO NUMBERS ARE THE TWO LONG VECTORS' EXTENSIONS AT THE
CHALLENGES. The verifier's function stackEnd makes two numbers of the end values that it is shown
(sidesOn, Johnson/Desc/K4/Honest/Stack.lean). At the end values that the honest side computes
(endsAt) each is the sum over the panels of the panel's term (PanelTerm.lean), which is the
extension of the long vector (LongExt.lean). What one panel adds is the library's (stackEndOf_rd,
Johnson/Road/FormsKeysEnd.lean). A definition; statements and proofs.

  `readsWorld`          the world whose entries are the honest reads, with 0 under every slot.
  `reads_val`, `val_reads`   a form's value on the honest reads is its value in that world.
  `extract_at`, `ends_list`   a stretch of an array; the end values' list, member by member.
  `endsAt_all`          the honest side's end values, opened whole.
  `mapM_zipped`         what mapM returns, zipped with its list.
  `sum_one_three`, `sum_two_four`   two of the library's five numbers, summed over a list.
  `stack_tabs`          the maker's sides and long vectors.
  **`stack_ends_are`**    EndsAre at every panel in the job's data, at the honest end values.
  **`stack_sides_sum`**   the verifier's two numbers as sums over the panels.
  **`stack_sides_true`**  the same as the two extensions.

Not shown here. That the maker returns anywhere: no example is known. The maker's return, the
number of the challenges and the return of the honest side's end values are the premises.
No property is claimed.
-/
import Johnson.Road.K4.C.PanelTerm
import Johnson.Road.K4.C.PanelsFitOf
import Johnson.Road.K4.C.PanelsTri
import Johnson.Road.K4.C.EndsV
import Johnson.Road.K4.C.StackSides
import Johnson.Road.K4.C.TermsOpen
import Johnson.Desc.First.K4.Returns.Pub.End
import Johnson.Road.FormsKeysFac

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk Lay Env StackEnd stackEnd stackEndOf placePanels)
open OnBytes.Road.K4 (WalkL VirtOK virt_panels virt_placed panelsT_walked panelsA_walked
  walk_placed)
open OnBytes.Desc.First.K4.Honest

/-- The world whose entries are the honest reads, with 0 under every slot. -/
def readsWorld (v : Env) (R : OnBytes.Desc.First.K4.Honest.Reads) : World Cb.Gl.E where
  slot := fun _ => 0
  entry := fun _ row idx => Reading.gl.val (R.u3 (row * v.K3 + idx))

/-- A form's value on the honest reads is its value in that world. -/
theorem reads_val (v : Env) (R : OnBytes.Desc.First.K4.Honest.Reads) (f : Aff) (x : E)
    (h : valAff? v R (fun _ => zeroE) f = some x) :
    Reading.gl.val x = f.value Reading.gl (readsWorld v R) := by
  obtain ⟨hfit, rfl⟩ := (valAffQ_some v R _ f x).mp h
  exact valAff_value hfit (fun _ _ => rfl) fun _ _ => Reading.gl.zero.symm

/-- The same for the job's own function. -/
theorem val_reads (D : StackData) (f : Aff) (x : E) (h : D.val f = some x) :
    Reading.gl.val x = f.value Reading.gl (readsWorld D.S.v D.R) := by
  unfold StackData.val at h
  by_cases c : affFits D.S.v D.R f = true
  · rw [if_pos c] at h
    obtain rfl := Option.some.inj h
    rw [valAff_filter]
    exact valAff_value c (fun _ _ => rfl) fun _ _ => Reading.gl.zero.symm
  · rw [if_neg c] at h
    cases h

/-- An entry of a stretch of an array. -/
theorem extract_at (e : Array E) (a b k : ℕ) :
    (e.extract a b).getD k zeroE =
      if a + k < min b e.size then e.getD (a + k) zeroE else zeroE := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h : k < min b e.size - a
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
    rfl

/-- **The end values' list, member by member.** -/
theorem ends_list (A0 H1 B0 : E) (H2 Vl : List E) :
    ([A0, H1] ++ H2 ++ [B0] ++ Vl).length = 3 + H2.length + Vl.length ∧
      ([A0, H1] ++ H2 ++ [B0] ++ Vl).getD 0 zeroE = A0 ∧
      ([A0, H1] ++ H2 ++ [B0] ++ Vl).getD 1 zeroE = H1 ∧
      (∀ k, k < H2.length → ([A0, H1] ++ H2 ++ [B0] ++ Vl).getD (2 + k) zeroE = H2.getD k zeroE) ∧
      ([A0, H1] ++ H2 ++ [B0] ++ Vl).getD (2 + H2.length) zeroE = B0 ∧
      ∀ j, ([A0, H1] ++ H2 ++ [B0] ++ Vl).getD (3 + H2.length + j) zeroE = Vl.getD j zeroE := by
  have e : [A0, H1] ++ H2 ++ [B0] ++ Vl = A0 :: H1 :: (H2 ++ B0 :: Vl) := by simp
  rw [e]
  refine ⟨by simp; omega, rfl, rfl, fun k hk => ?_, ?_, fun j => ?_⟩
  · rw [Nat.add_comm 2 k, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_append_left hk]
  · rw [Nat.add_comm 2, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · have e3 : 3 + H2.length + j = (H2.length + (j + 1)) + 1 + 1 := by omega
    rw [e3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
      List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_cons_succ]

/-- **The honest side's end values, opened whole.** -/
theorem endsAt_all {D : StackData} {rs : Array E} {l : List E} (h : D.endsAt rs = some l) :
    ∃ fin A0 B0 dn, stackEnd D.S.v.y D.bl rs D.S.Q.hp.lamS D.om (Array.replicate D.nVirt zeroE)
        (Array.replicate D.S.opens.size zeroE) zeroE zeroE = some fin ∧
      D.val fin.Alin = some A0 ∧ D.val fin.Blin = some B0 ∧
      (D.bl.find? fun b => !b.tri && b.virt.isSome) = some dn ∧
      l = [A0, StackData.under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
          fun i yv => D.hZ.getD (i * D.S.v.y.Pf + yv) zeroE] ++
        ((List.range D.S.v.y.LamM).map fun lm =>
          StackData.under #[oneE] (eqLow rs 0 D.S.v.y.lfe) 1 D.S.v.y.h.fe
            fun _ yv => D.hR.getD (D.S.routedAt lm yv) zeroE) ++ [B0] ++
        (D.bl.foldl (vStep D rs) (Array.replicate D.S.opens.size zeroE)).toList := by
  unfold StackData.endsAt at h
  dsimp only at h
  obtain ⟨fin, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨A0, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨B0, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dn, h4, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨fin, A0, B0, dn, h1, h2, h3, h4, (Option.some.inj h).symm⟩

/-- What mapM returns, zipped with its list: each pair is an argument with its value. -/
theorem mapM_zipped {α β : Type} {f : α → Option β} : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ z ∈ l.zip r, f z.1 = some z.2
  | [], r, h, z, hz => by simp at hz
  | x :: l, r, h, z, hz => by
    rw [List.mapM_cons] at h
    obtain ⟨c, hc, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, hcs, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain rfl : c :: cs = r := Option.some.inj h2
    rw [List.zip_cons_cons] at hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hc
    · exact mapM_zipped l cs hcs z hz'

/-- The first and third numbers of a sum of the library's five. -/
theorem sum_one_three {α : Type} (f : α → Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × ℕ) :
    ∀ l : List α, (l.map f).sum.1 + (l.map f).sum.2.2.1 =
      (l.map fun x => (f x).1 + (f x).2.2.1).sum
  | [] => by
    show (0 : Cb.Gl.E) + 0 = 0
    rw [add_zero]
  | x :: l => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← sum_one_three f l]
    show (f x).1 + (l.map f).sum.1 + ((f x).2.2.1 + (l.map f).sum.2.2.1) = _
    ring

/-- The second and fourth. -/
theorem sum_two_four {α : Type} (f : α → Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × ℕ) :
    ∀ l : List α, (l.map f).sum.2.1 + (l.map f).sum.2.2.2.1 =
      (l.map fun x => (f x).2.1 + (f x).2.2.2.1).sum
  | [] => by
    show (0 : Cb.Gl.E) + 0 = 0
    rw [add_zero]
  | x :: l => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← sum_two_four f l]
    show (f x).2.1 + (l.map f).sum.2.1 + ((f x).2.2.2.1 + (l.map f).sum.2.2.2.1) = _
    ring

variable {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData} {rs : Array E}
  {l : List E}

/-- **The maker's sides and long vectors.** CONDITIONAL: on the maker's return. -/
theorem stack_tabs (h : stackData Q w p shownT = some SD) :
    ∃ sides, SD.bl.mapM (panelTabs SD.S (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a) SD.om
        SD.F SD.hZ SD.hR) = some sides ∧
      SD.SA = (longTabs SD.S.Q.hp.lamS SD.bl sides).1 ∧
      SD.SB = (longTabs SD.S.Q.hp.lamS SD.bl sides).2 := by
  unfold stackData at h
  obtain ⟨S, _, h⟩ := Option.bind_eq_some_iff.1 h
  unfold stackDataOn at h
  obtain ⟨R, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨bl, places⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  by_cases hc : (ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != S.Q.hp.NCL - (if (S.Q.g == 0) = true then 1 else 0)) = true
  · rw [if_pos hc] at h
    simp at h
  · rw [if_neg hc] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sides, hs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    exact ⟨sides, hs, rfl, rfl⟩

/-- **THE HONEST END VALUES ARE THE TRUE ONES AT EVERY PANEL.** CONDITIONAL: on h and he. -/
theorem stack_ends_are (h : stackData Q w p shownT = some SD) (he : SD.endsAt rs = some l) :
    ∀ b ∈ SD.bl.toList, EndsAre SD.S SD.F SD.hZ SD.hR SD.S.v.y rs
      (valsOf Reading.gl (l.toArray.extract 1 (1 + SD.nVirt)))
      (valsOf Reading.gl (l.toArray.extract (2 + SD.nVirt) l.toArray.size)) b := by
  obtain ⟨pans, hp, ebl, hnext⟩ := stack_panels_at h
  obtain ⟨fin, A0, B0, dn, hfin, _, _, hdn, rfl⟩ := endsAt_all he
  have hN : pans.nextV = SD.S.opens.size := by simpa using hnext
  have hVk : ∀ b ∈ SD.bl.toList, VirtOK SD.S.v.y b := by
    rw [ebl]
    exact virt_placed (virt_panels _ _ hp)
  have hDk : ∀ b ∈ SD.bl.toList, DownOK SD.S.v.y b := by
    rw [ebl]
    exact down_placed (down_panels _ _ hp)
  have hTk : ∀ b ∈ SD.bl.toList, TriOK SD.S.v.y b := by
    rw [ebl]
    exact triOK_placed (triOK_panels _ _ hp)
  have hW : WalkL 0 SD.bl.toList SD.S.opens.size := by
    rw [ebl, ← hN]
    exact walk_placed (placed_f2 pans.bl) (panelsT_walked hp (panelsA_walked rfl))
  obtain ⟨_, _, hV⟩ := walk_V SD rs SD.bl.toList 0 SD.S.opens.size
    (Array.replicate SD.S.opens.size zeroE) hW (by rw [Array.size_replicate])
  rw [← Array.foldl_toList] at *
  generalize hVl : (SD.bl.toList.foldl (vStep SD rs)
    (Array.replicate SD.S.opens.size zeroE)) = Va at hV ⊢
  generalize hH1 : StackData.under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
    (fun i yv => SD.hZ.getD (i * SD.S.v.y.Pf + yv) zeroE) = H1v
  obtain ⟨eLen, _, e1, e2, _, e5⟩ := ends_list A0 H1v B0
    ((List.range SD.S.v.y.LamM).map fun lm =>
      StackData.under #[oneE] (eqLow rs 0 SD.S.v.y.lfe) 1 SD.S.v.y.h.fe
        fun _ yv => SD.hR.getD (SD.S.routedAt lm yv) zeroE) Va.toList
  rw [List.length_map, List.length_range] at eLen e2 e5
  generalize hL : [A0, H1v] ++ ((List.range SD.S.v.y.LamM).map fun lm =>
      StackData.under #[oneE] (eqLow rs 0 SD.S.v.y.lfe) 1 SD.S.v.y.h.fe
        fun _ yv => SD.hR.getD (SD.S.routedAt lm yv) zeroE) ++ [B0] ++ Va.toList = L
    at eLen e1 e2 e5 ⊢
  have hnv : SD.nVirt = 1 + SD.S.v.y.LamM := rfl
  have vvAt : ∀ j, valsOf Reading.gl (L.toArray.extract (2 + SD.nVirt) L.toArray.size) j =
      Reading.gl.val (Va.getD j zeroE) := by
    intro j
    unfold valsOf
    rw [extract_at, List.size_toArray, Nat.min_self, toArray_getD, hnv]
    have e3 : 2 + (1 + SD.S.v.y.LamM) + j = 3 + SD.S.v.y.LamM + j := by omega
    rw [e3, e5 j, ← toArray_getD, Array.toArray_toList]
    by_cases c : 3 + SD.S.v.y.LamM + j < L.length
    · rw [if_pos c]
    · rw [if_neg c, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [← Array.length_toList]
        omega)]
      rfl
  have h1At : ∀ k, k < 1 + SD.S.v.y.LamM →
      valsOf Reading.gl (L.toArray.extract 1 (1 + SD.nVirt)) k =
        Reading.gl.val (L.getD (1 + k) zeroE) := by
    intro k hk
    unfold valsOf
    rw [extract_at, List.size_toArray, toArray_getD, hnv, if_pos (by omega)]
  have hdnM : dn ∈ SD.bl.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hdn)
  have hdnP : dn.tri = false ∧ ∃ k, dn.virt = some k := by
    have hp' := Array.find?_some hdn
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hp'
    exact ⟨hp'.1, Option.isSome_iff_exists.mp hp'.2⟩
  intro b hb
  refine ⟨fun ht => (hTk b hb ht).1, fun ht v0 h0 => ?_, fun ht v0 h0 i hi => ?_,
    fun ht k hk => ?_, fun ht k hk => ?_⟩
  · rw [vvAt, ((hV b hb v0 h0).1 ht)]
    unfold vTri
    rw [under_read]
    rfl
  · rw [vvAt, ((hV b hb v0 h0).2 ht i hi)]
    unfold vRow
    rw [under_one]
    rfl
  · obtain ⟨⟨lm, hlm, rfl⟩, _⟩ := (hVk b hb).tri ht k hk
    obtain ⟨s1, s2, hs⟩ := stackEnd_each hfin b hb
    obtain ⟨_, _, hwy, _⟩ := end_tri_virt (ρ := Reading.gl) (W := readsWorld SD.S.v SD.R) ht hk hs
    rw [h1At (1 + lm) (by omega)]
    have e4 : 1 + (1 + lm) = 2 + lm := by omega
    rw [e4, e2 lm hlm, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hlm, Option.map_some, Option.getD_some, under_one,
      ((hTk b hb ht).2 (1 + lm) hk), Nat.add_sub_cancel_left]
    unfold eyK
    rw [hwy]
  · obtain ⟨rfl, bwy, bw⟩ := (hVk b hb).plain ht k hk
    obtain ⟨bni, bny⟩ := hDk b hb ht 0 hk
    obtain ⟨kd, hkd⟩ := hdnP.2
    obtain ⟨_, dwy, dw⟩ := (hVk dn hdnM).plain hdnP.1 kd hkd
    obtain ⟨dni, dny⟩ := hDk dn hdnM hdnP.1 kd hkd
    rw [h1At 0 (by omega), e1, ← hH1, under_read, dni, dny, dwy, dw, bni, bny]
    unfold eiK eyK
    rw [bwy, bw]

/-- **THE VERIFIER's TWO NUMBERS ON THE HONEST END VALUES, AS SUMS OVER THE PANELS.** sides: the
panels' two sides, as the maker lays them. CONDITIONAL: on h, he and hs. -/
theorem stack_sides_sum (h : stackData Q w p shownT = some SD) (he : SD.endsAt rs = some l)
    {sides : Array (Array E × Array E)}
    (hs : SD.bl.mapM (panelTabs SD.S (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a) SD.om SD.F
      SD.hZ SD.hR) = some sides) :
    ∃ x, SD.sidesOn rs l.toArray = some x ∧
      Reading.gl.val x.1 =
        ((zipped SD.bl sides).map fun z => sideTerm rs SD.S.Q.hp.lamS z.1 z.2.1).sum ∧
      Reading.gl.val x.2 =
        ((zipped SD.bl sides).map fun z => sideTerm rs SD.S.Q.hp.lamS z.1 z.2.2).sum := by
  have T := stack_ends_are h he
  obtain ⟨fin0, A0, B0, dn, hfin0, hA0, hB0, _, hl⟩ := endsAt_all he
  have hsome : (stackEnd SD.S.v.y SD.bl rs SD.S.Q.hp.lamS SD.om
      (l.toArray.extract 1 (1 + SD.nVirt)) (l.toArray.extract (2 + SD.nVirt) l.toArray.size)
      (l.toArray.getD 0 zeroE) (l.toArray.getD (1 + SD.nVirt) zeroE)).isSome = true := by
    rw [OnBytes.Desc.First.K4.RtPub.stackEnd_rel SD.S.v.y SD.S.Q.hp.lamS SD.om _ _ SD.om
      (Array.replicate SD.nVirt zeroE) (Array.replicate SD.S.opens.size zeroE) _ _ zeroE zeroE
      (OnBytes.Flat.All2.refl OnBytes.Desc.First.K4.RtPub.BlkSkel.refl _) rfl, hfin0]
    rfl
  obtain ⟨fin, hfin⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨eAl, eBl⟩ := stackEnd_lin hfin hfin0
  have hrd := (stackEnd_rd (ρ := Reading.gl) (W := readsWorld SD.S.v SD.R) hfin).1
  have g0 : l.toArray.getD 0 zeroE = A0 := by
    rw [toArray_getD, hl]
    exact (ends_list _ _ _ _ _).2.1
  have g1 : l.toArray.getD (1 + SD.nVirt) zeroE = B0 := by
    have e := (ends_list A0 (StackData.under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
      fun i yv => SD.hZ.getD (i * SD.S.v.y.Pf + yv) zeroE) B0
      ((List.range SD.S.v.y.LamM).map fun lm =>
        StackData.under #[oneE] (eqLow rs 0 SD.S.v.y.lfe) 1 SD.S.v.y.h.fe
          fun _ yv => SD.hR.getD (SD.S.routedAt lm yv) zeroE)
      (SD.bl.foldl (vStep SD rs) (Array.replicate SD.S.opens.size zeroE)).toList).2.2.2.2.1
    rw [List.length_map, List.length_range] at e
    have e2 : 1 + SD.nVirt = 2 + SD.S.v.y.LamM := by
      show 1 + (1 + SD.S.v.y.LamM) = _
      omega
    rw [toArray_getD, hl, e2]
    exact e
  rw [g0, g1] at hrd
  have c1 : fin.Alin.value Reading.gl (readsWorld SD.S.v SD.R) = 0 + _ :=
    congrArg (fun m : Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × ℕ => m.1) hrd
  have c2 : fin.Blin.value Reading.gl (readsWorld SD.S.v SD.R) = 0 + _ :=
    congrArg (fun m : Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × ℕ => m.2.1) hrd
  have c3 : Reading.gl.val fin.As = Reading.gl.val A0 + _ :=
    congrArg (fun m : Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × ℕ => m.2.2.1) hrd
  have c4 : Reading.gl.val fin.Bs = Reading.gl.val B0 + _ :=
    congrArg (fun m : Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × Cb.Gl.E × ℕ => m.2.2.2.1) hrd
  rw [val_reads SD _ _ hA0, ← eAl, c1, zero_add, sum_one_three] at c3
  rw [val_reads SD _ _ hB0, ← eBl, c2, zero_add, sum_two_four] at c4
  rw [Array.mapM_eq_mapM_toList] at hs
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hsz : L.toArray.size = SD.bl.size := by
    rw [List.size_toArray, (list_mapM_some _ _ _ hL).1, Array.length_toList]
  have hz := zipped_panels hsz
  have hmem : ∀ z ∈ zipped SD.bl L.toArray,
      panelTabs SD.S (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a) SD.om SD.F SD.hZ SD.hR z.1 =
        some z.2 ∧ z.1 ∈ SD.bl.toList := fun z hzm =>
    ⟨mapM_zipped _ _ hL z hzm, (List.of_mem_zip hzm).1⟩
  refine ⟨(fin.As, fin.Bs), ?_, ?_, ?_⟩
  · unfold StackData.sidesOn
    dsimp only
    rw [hfin]
    rfl
  · rw [c3, ← hz, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun z hzm =>
      (panel_adds (a := z.2.1) (c := z.2.2) (hmem z hzm).1 (reads_val SD.S.v SD.R)
        (T z.1 (hmem z hzm).2)).1)
  · rw [c4, ← hz, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun z hzm =>
      (panel_adds (a := z.2.1) (c := z.2.2) (hmem z hzm).1 (reads_val SD.S.v SD.R)
        (T z.1 (hmem z hzm).2)).2)

/-- **ON THE HONEST END VALUES THE VERIFIER's TWO NUMBERS ARE THE TWO LONG VECTORS' EXTENSIONS AT
THE CHALLENGES.** rs: the challenges by bit. CONDITIONAL: on h, hr and he. -/
theorem stack_sides_true (h : stackData Q w p shownT = some SD)
    (hr : rs.size = SD.S.Q.hp.lamS) (he : SD.endsAt rs = some l) :
    ∃ x, SD.sidesOn rs l.toArray = some x ∧
      Reading.gl.val x.1 = Blocks.ext SD.S.Q.hp.lamS
        (fun n => Reading.gl.val (SD.SA.getD n zeroE)) (pt Reading.gl rs.reverse) ∧
      Reading.gl.val x.2 = Blocks.ext SD.S.Q.hp.lamS
        (fun n => Reading.gl.val (SD.SB.getD n zeroE)) (pt Reading.gl rs.reverse) := by
  obtain ⟨sides, hs, eA, eB⟩ := stack_tabs h
  obtain ⟨x, hx, h1, h2⟩ := stack_sides_sum h he hs
  obtain ⟨fin0, _, _, _, hfin0, _⟩ := endsAt_all he
  have hok : ∀ b ∈ SD.bl.toList,
      eqIndexOK (rs.extract b.w SD.S.Q.hp.lamS) (b.off / 2 ^ b.w) = true := fun b hb => by
    obtain ⟨s1, s2, e⟩ := stackEnd_each hfin0 b hb
    exact OnBytes.Road.stackEndOf_ok e
  have hP := stack_panelsFit h
  have hsz : sides.size = SD.bl.size := by
    have hs' := hs
    rw [Array.mapM_eq_mapM_toList] at hs'
    obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hs'
    rw [List.size_toArray, (list_mapM_some _ _ _ hL).1, Array.length_toList]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [h1, eA, long_under_fst hP hsz rs hr hok]
    rfl
  · rw [h2, eB, long_under_snd hP hsz rs hr hok]
    rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.reads_val
#print axioms OnBytes.Road.K4.C.val_reads
#print axioms OnBytes.Road.K4.C.extract_at
#print axioms OnBytes.Road.K4.C.ends_list
#print axioms OnBytes.Road.K4.C.endsAt_all
#print axioms OnBytes.Road.K4.C.mapM_zipped
#print axioms OnBytes.Road.K4.C.sum_one_three
#print axioms OnBytes.Road.K4.C.sum_two_four
#print axioms OnBytes.Road.K4.C.stack_tabs
#print axioms OnBytes.Road.K4.C.stack_ends_are
#print axioms OnBytes.Road.K4.C.stack_sides_sum
#print axioms OnBytes.Road.K4.C.stack_sides_true
