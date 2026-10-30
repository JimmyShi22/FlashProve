-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLeavesTop.lean: the claim on the leaves of a part's key tree holds exactly if the
pending row on the matrix holds.

OnBytes/Slice/KeyLeaves.lean states it (`Top`). This file proves it with one more hypothesis: for
each run of padding of the lookup the loop that cuts the run into cubes has steps enough
(OnBytes/Slice/KeyLeavesCubes.lean: `Covered`, a public test that can be evaluated). All else that
is asked is what the program tests itself: the matrix's size and the lookup pass `Wf.lookupOk` and
`Wf.fitsMatrix`, and the claim's point has one coordinate for each bit of a key's number; and two
conditions on the letters: there is a weight for each digit, and the table's row at the padding
key's number is what a place of padding holds.

The way. The map of the leaves at the point is alpha less the sum of the equality vector times the
keys (OnBytes/Slice/KeyLeavesEq.lean). That sum falls into the padding's share, the offset's share
and the value of the row's weights on the matrix (OnBytes/Slice/KeyLeavesRuns.lean). The program's
padding is the gaps between the runs, stretch by stretch, and what it takes out of the target for a
stretch is the padding's value times the equality vector's sum over the stretch
(OnBytes/Slice/KeyLeavesCubes.lean).

Main theorems.
 `paddingFrom_eq`    the program's padding of a part is the gaps between its runs, as stretches.
 `padding_filter`    the runs of padding of part i, out of the lookup's list.
 `keysOfF_target`    the target of the claim on the keys, written out.
 `runsOk_of`, `rowsIn_of`   what the program's public tests give for a part.
 `pad_sum`           what is taken out of the target is the padding's value times the equality
                    vector's sum over the gaps.
 `leaves_top`        the statement.
 `top_of_covered`    so `Top` holds if the loop's steps are always enough.

Not claimed. That the loop's steps are always enough (OnBytes/Slice/KeyLeavesFuel.lean shows it).
That the functions over the field are the readings of the program's. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeavesRuns
import OnBytes.Slice.KeyLeavesCubes

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)
open OnBytes.Slice.PscF (World scaleForm)

/-! ## The program's padding -/

/-- The program's padding of a part is the gaps between its runs, as stretches. -/
theorem paddingFrom_eq (kCol number row lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ)
    (acc : Array Lkp.Padding),
    (Wf.paddingFrom kCol number row lp u rs acc).toList =
      acc.toList ++ (gaps (2 ^ lp) u rs).flatMap fun g => Wf.stretch kCol number row g.1 g.2
  | [], u, acc => by simp [Wf.paddingFrom, gaps]
  | r :: rs, u, acc => by
    rw [Wf.paddingFrom, paddingFrom_eq kCol number row lp rs]
    simp [gaps]

/-- A stretch's runs of padding belong to its part. -/
theorem stretch_part {kCol number row lo hi : ℕ} {q : Lkp.Padding}
    (h : q ∈ Wf.stretch kCol number row lo hi) : q.part = number := by
  unfold Wf.stretch at h
  split at h
  · rw [List.mem_singleton.1 h]
  · cases h

/-- A filter that every member passes keeps the list. -/
theorem filter_all {α : Type} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x = true) :
    l.filter p = l := List.filter_eq_self.2 h

/-- A filter that no member passes leaves nothing. -/
theorem filter_none {α : Type} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x = false) :
    l.filter p = [] := List.filter_eq_nil_iff.2 fun x hx => by rw [h x hx]; decide

/-- Out of lists that are made for numbered members, each list's members marked with the number: the
members with the mark i are the list of member i. -/
theorem filter_numbered {α : Type} (f : α × ℕ → List Lkp.Padding)
    (hf : ∀ x, ∀ q ∈ f x, q.part = x.2) (i : ℕ) (a : α) :
    ∀ (xs : List α) (k : ℕ), k ≤ i → xs[i - k]? = some a →
      ((xs.zipIdx k).flatMap f).filter (·.part == i) = f (a, i)
  | [], _, _, h => by cases h
  | x :: xs, k, hk, h => by
    have later : ∀ (ys : List α) (j : ℕ), i < j →
        ((ys.zipIdx j).flatMap f).filter (·.part == i) = [] := by
      intro ys
      induction ys with
      | nil => intro j _; rfl
      | cons y ys ih =>
        intro j hj
        rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append, ih (j + 1) (by omega),
          List.append_nil]
        refine filter_none _ _ fun q hq => ?_
        rw [hf _ q hq]
        exact beq_false_of_ne (by show j ≠ i; omega)
    rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append]
    by_cases e : k = i
    · subst e
      rw [Nat.sub_self, List.getElem?_cons_zero] at h
      obtain rfl := Option.some.inj h
      rw [later xs (k + 1) (by omega), List.append_nil]
      refine filter_all _ _ fun q hq => ?_
      rw [hf _ q hq]
      exact beq_self_eq_true _
    · have h' : xs[i - (k + 1)]? = some a := by
        rw [show i - k = (i - (k + 1)) + 1 by omega, List.getElem?_cons_succ] at h
        exact h
      rw [filter_numbered f hf i a xs (k + 1) (by omega) h', filter_none, List.nil_append]
      intro q hq
      rw [hf _ q hq]
      exact beq_false_of_ne e

/-- The runs of padding of part i, out of the lookup's list. -/
theorem padding_filter (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (i : ℕ) (p : WfPart)
    (hp : l.parts[i]? = some p) :
    (Wf.lookupOf id m l).padding.filter (·.part == i) =
      (gaps (2 ^ p.logPlaces) 0 p.runs).flatMap fun g =>
        Wf.stretch m.kCol i l.paddingKey.toNat g.1 g.2 := by
  show ((l.parts.zipIdx 0).flatMap fun x =>
    (Wf.paddingFrom m.kCol x.2 l.paddingKey.toNat x.1.logPlaces 0 x.1.runs #[]).toList).filter
      (·.part == i) = _
  rw [filter_numbered _ (fun x q hq => ?_) i p l.parts 0 (Nat.zero_le _) hp, paddingFrom_eq]
  · rfl
  · rw [paddingFrom_eq] at hq
    rcases List.mem_append.1 hq with h | h
    · cases h
    · obtain ⟨g, _, hg⟩ := List.mem_flatMap.1 h
      exact stretch_part hg

/-! ## The target of the claim on the keys -/

/-- The target after the cubes of one run of padding are taken out. -/
theorem fold_takeOut (rowV : ℕ → GE) (pt : List GE) (row : ℕ) (blk : Option ℕ) :
    ∀ (cubes : List Lkp.Cube) (a : KeyAccF),
      (cubes.foldl (fun a c => takeOutF rowV pt a c row blk) a).target =
        a.target - (cubes.map fun c => cubeWeightF c pt).sum * rowV row
  | [], a => by simp
  | c :: cs, a => by
    rw [List.foldl_cons, fold_takeOut rowV pt row blk cs, List.map_cons, List.sum_cons]
    show a.target - cubeWeightF c pt * rowV row - _ = _
    ring

/-- The target after the cubes of all runs of padding are taken out. -/
theorem fold_padding (rowV : ℕ → GE) (pt : List GE) (blk : Lkp.Padding → ℕ) :
    ∀ (ps : List Lkp.Padding) (a : KeyAccF),
      (ps.foldl (fun a p =>
        (Lkp.cubesOf p pt.length).foldl (fun a c => takeOutF rowV pt a c p.row (some (blk p))) a)
        a).target =
        a.target - (ps.map fun p =>
          ((Lkp.cubesOf p pt.length).map fun c => cubeWeightF c pt).sum * rowV p.row).sum
  | [], a => by simp
  | p :: ps, a => by
    rw [List.foldl_cons, fold_padding rowV pt blk ps, fold_takeOut, List.map_cons, List.sum_cons]
    ring

/-- The target of the claim on the keys, where all keys belong to one block of tree numbers, of
the function 0. -/
theorem keysOfF_target (S : Lkp.Public) (k0 : Lkp.KeyBlock) (hk : S.keys = [k0])
    (hf : k0.function = some 0) (rowV natV : ℕ → GE) (θ α : GE) (part : ℕ)
    (c : PscF.PointClaim) :
    (keysOfF S rowV natV θ α part c).target =
      α - c.value - ((S.padding.filter (·.part == part)).map fun p =>
        ((Lkp.cubesOf p c.point.length).map fun x => cubeWeightF x c.point).sum *
          rowV p.row).sum := by
  unfold keysOfF
  simp only [hk]
  have hn : [k0].filter (·.function.isNone) = [] := by simp [hf]
  rw [hn, List.foldl_nil]
  have hz : ∀ F : GE → Lkp.KeyBlock × GE → GE, (∀ t x, F t (k0, x) = t) →
      ∀ (real : List GE) (t : GE), ([k0].zip real).foldl F t = t := by
    intro F hF real t
    cases real with
    | nil => rfl
    | cons x xs => exact hF t x
  rw [hz _ ?_, fold_padding rowV c.point fun p => [k0].findIdx fun k => k.holds S.g p.first]
  intro t x
  simp only [hf]
  rfl

/-! ## What the program's public tests give -/

/-- The number of a member of a numbered list is below the first number plus the list's length. -/
theorem snd_lt_of_mem_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ) (x : α × ℕ), x ∈ l.zipIdx k →
    x.2 < k + l.length
  | [], _, _, h => by cases h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with h | h
    · rw [h, List.length_cons]
      show k < _
      omega
    · have := snd_lt_of_mem_zipIdx l (k + 1) x h
      rw [List.length_cons]
      omega

/-- The runs of a part of a lookup that is in order rise without overlap inside the part. -/
theorem runsOk_of {l : WfLookup} {p : WfPart} (h : Wf.lookupOk Wf.fBits l = true)
    (hp : p ∈ l.parts) : Wf.runsOk p.logPlaces 0 p.runs = true := by
  simp only [Wf.lookupOk, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := (h.2 p hp).1
  simp only [Wf.partOk, Bool.and_eq_true] at h2
  exact h2.1.2

/-- What the program's test on a lookup and the matrix's size says of each run of each part. -/
theorem partsFit_mem (m : Wf.Matrix) (l : WfLookup) : ∀ (ps : List WfPart) (keys : ℕ),
    Wf.partsFit m l keys ps = true → ∀ p ∈ ps, ∀ r ∈ p.runs,
      r.firstRow < m.rows ∧ r.places ≤ m.rows - r.firstRow ∧
        (l.digitWeight.length - 1) * r.stride ≤ m.rows - r.firstRow - r.places
  | [], _, _, p, hp => by cases hp
  | q :: ps, keys, h, p, hp => by
    simp only [Wf.partsFit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hp with e | hp
    · subst e
      intro r hr
      have := h.1.1.2 r hr
      exact ⟨this.1.1.2, this.1.2, this.2⟩
    · exact partsFit_mem m l ps _ h.2 p hp

/-- Every row that a run of a part reads is a row of the matrix, if the lookup fits the matrix. -/
theorem rowsIn_of {m : Wf.Matrix} {l : WfLookup} {p : WfPart} (L : LkF)
    (hL : L.dw.length = l.digitWeight.length) (h : Wf.fitsMatrix m l = true) (hp : p ∈ l.parts) :
    RowsIn L m.rows p.runs := by
  intro r hr w hw
  obtain ⟨h1, h2, h3⟩ := partsFit_mem m l l.parts 0 h p hp r hr
  have hw' := snd_lt_of_mem_zipIdx L.dw 0 w hw
  rw [hL] at hw'
  have := Nat.mul_le_mul_right r.stride (by omega : w.2 ≤ l.digitWeight.length - 1)
  omega

/-! ## The padding's share -/

/-- What is taken out of the target is the padding's value times the equality vector's sum over
the gaps. -/
theorem pad_sum (z : List GE) (kCol lp number row : ℕ) (rowV : ℕ → GE)
    (hz : z.length = kCol + lp) : ∀ gs : List (ℕ × ℕ), (∀ g ∈ gs, g.2 ≤ 2 ^ lp) →
      (∀ q ∈ gs.flatMap (fun g => Wf.stretch kCol number row g.1 g.2), Covered q) →
      ((gs.flatMap fun g => Wf.stretch kCol number row g.1 g.2).map fun p =>
        ((Lkp.cubesOf p z.length).map fun x => cubeWeightF x z).sum * rowV p.row).sum =
      rowV row * (gs.map fun g => ∑ p ∈ Finset.Ico g.1 g.2, eqW (z.drop kCol) p).sum
  | [], _, _ => by simp
  | g :: gs, hle, hc => by
    have ih := pad_sum z kCol lp number row rowV hz gs
      (fun x hx => hle x (List.mem_cons_of_mem _ hx)) fun q hq => hc q (by
        rw [List.flatMap_cons]
        exact List.mem_append_right _ hq)
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      mul_add]
    refine congrArg (· + _) ?_
    by_cases h : g.1 < g.2
    · have hs : Wf.stretch kCol number row g.1 g.2 =
          [{ part := number, first := g.1 * 2 ^ kCol, logStep := 0,
             length := (g.2 - g.1) * 2 ^ kCol, row := row }] := by
        unfold Wf.stretch
        rw [if_pos h]
      have hcov := hc _ (by
        rw [List.flatMap_cons, hs]
        exact List.mem_append_left _ List.mem_cons_self)
      have hfit : g.1 * 2 ^ kCol + (g.2 - g.1) * 2 ^ kCol ≤ 2 ^ z.length := by
        rw [← Nat.add_mul, Nat.add_sub_cancel' (le_of_lt h), hz, Nat.add_comm kCol, pow_add]
        exact Nat.mul_le_mul_right _ (hle g List.mem_cons_self)
      rw [hs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        cubesOf_sum z _ rfl hcov hfit]
      show (∑ j ∈ Finset.Ico (g.1 * 2 ^ kCol) (g.1 * 2 ^ kCol + (g.2 - g.1) * 2 ^ kCol), eqW z j) *
        rowV row = _
      rw [stretch_sum z kCol g.1 g.2 (by omega) (le_of_lt h), mul_comm]
    · have hs : Wf.stretch kCol number row g.1 g.2 = [] := by
        unfold Wf.stretch
        rw [if_neg h]
      rw [hs, List.map_nil, List.sum_nil, Finset.Ico_eq_empty (by omega), Finset.sum_empty,
        mul_zero]

/-! ## The statement -/

/-- The claim on the leaves of a part's key tree holds exactly if the pending row on the matrix
holds, for every matrix, every world of mask entries, every alpha and every point with one
coordinate for each bit of a key's number. Asked: the program's public tests on the lookup and the
matrix's size; that the loop that cuts padding into cubes has steps enough for each run of padding
of the lookup; and of the letters: L has a weight for each digit, and the table's row at the padding
key's number is what L has for a place of padding. -/
theorem leaves_top (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (L : LkF)
    (rowV natV : ℕ → GE) (θ α : GE) (W : World) (M : ℕ → ℕ → GE) (c : PscF.PointClaim)
    (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true)
    (hp : l.parts[i]? = some p) (hL : L.dw.length = l.digitWeight.length)
    (hpad : rowV l.paddingKey.toNat = L.pad) (hz : c.point.length = m.kCol + p.logPlaces)
    (hc : ∀ q ∈ (Wf.lookupOf id m l).padding, Covered q) :
    c.Holds W (treeMap (m.kCol + p.logPlaces) (leafTab α (key L M m.kCol p.runs))) ↔
      (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
        (eqPlacesF m.kCol c.point)).Holds W M m.rows m.kCol := by
  have hmem : p ∈ l.parts := List.mem_of_getElem? hp
  have hr := runsOk_of hl hmem
  have hR := rowsIn_of L hL hm hmem
  have ht := keysOfF_target (Wf.lookupOf id m l) _ rfl rfl rowV natV θ α i c
  rw [padding_filter id m l i p hp,
    pad_sum c.point m.kCol p.logPlaces i l.paddingKey.toNat rowV hz _ (gaps_le _ _ _ hr)
      (fun q hq => hc q (by
        have := padding_filter id m l i p hp
        rw [← this] at hq
        exact (List.mem_filter.1 hq).1)), hpad] at ht
  have hs := keys_sum L M m.kCol p.logPlaces m.rows p.runs c.point hz hr hR
    (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
  unfold PscF.PointClaim.Holds TRowF.Holds
  rw [treeMap_leafTab α _ _ c.point hz, hs]
  show _ ↔ _ + W.form (scaleForm (-1) c.masks) =
    (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c).target -
      coveredSumF p.runs (eqPlacesF m.kCol c.point) * L.off
  have hpsi : (pendingRowF m.kCol L p.runs (keysOfF (Wf.lookupOf id m l) rowV natV θ α i c)
      (eqPlacesF m.kCol c.point)).psi = c.point.take m.kCol := rfl
  rw [ht, World.form_scale]
  simp only [hpsi]
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

/-- So the statement of OnBytes/Slice/KeyLeaves.lean holds if the loop's steps are always enough. -/
theorem top_of_covered
    (h : ∀ (m : Wf.Matrix) (l : WfLookup) (id : ℕ), m.ok = true → Wf.lookupOk Wf.fBits l = true →
      Wf.fitsMatrix m l = true → ∀ q ∈ (Wf.lookupOf id m l).padding, Covered q) : Top :=
  fun m l id i p L rowV natV θ α W M c hm0 hl hm hp hL hpad hz =>
    leaves_top m l id i p L rowV natV θ α W M c hl hm hp hL hpad hz (h m l id hm0 hl hm)

end OnBytes.Slice.Leaves
