-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Below.lean: CONDITIONAL.

Not shown here. That layTables returns, and that the structure which the forms read has its list of
places (hv): hypotheses; and that funsOf and termsForms return, and that the list of places has the
family "b-bits-0" (hf, h, hB: terms_off; hB: tabFront_of_lay too): hypotheses: who pays hf is not
known. OF THE VERIFIER's READERS ONLY THOSE ARE TREATED THAT MAKE THE CLAIMS ON THE SECOND TOKEN
SUMCHECK's END VALUES (rowR, shA) and what they are made of; the panels' forms and the rows' forms
are not treated here. No example is known. No property is claimed.

THE ENTRIES OF THE CLAIMS ON THE SECOND TOKEN SUMCHECK's END VALUES LIE IN FRONT OF THE FAMILY
"b-bits-0". OffPlanes.lean asks one inequality for each entry of a form (hG_of_lt's hlt). Each
entry of these claims' forms is made by Env.U3at t i (OnBytes/Model/LayerForms.lean), which tests
that i lies below the length of the family that begins at t. So the entry lies in front of
"b-bits-0" wherever that family does; and a family whose name does not begin with the letter b
does.

  Below          each entry that the form names lies in front of the place tB0. It is EntsIn
                 (Johnson/Road/K4/Reads/EntsIn.lean) at that test: so that file's rules for sums
                 hold.
  below_iff      it is hG_of_lt's hlt.
  TabFront       the list of places: a family that begins in front of tB0 ends there or earlier; a
                 family whose name does not begin with b begins in front of tB0.
  tab_of_lay, laid_split', named_ends, named_of_head, tabFront_of_lay   TabFront where layTables has
                 returned.
  below_U3at, below_foldlM, below_sumForms, below_limbs, head_or, mname_head, below_shA,
  below_rowCells,
  below_ledDig, below_digits, below_rowR   the readers.
  below_terms    every claim of termsForms.
  terms_off      so these claims' entries lie off the matrix of the lookup's planes.
-/
import Johnson.Road.K4.C.OffPlanes
import Johnson.Road.K4.Reads.TermsEnts
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model.Layer (Lay Env Heard Ten TableAsk TableAt layParts layTables tableAsks funsOf
  matIx sumForms aff0)
open OnBytes.Desc.First.K4 (termsForms)
open OnBytes.Desc.First.K4.Reads (EntsIn entsIn_ofConst entsIn_slot entsIn_ent entsIn_addMul
  entsIn_scale entsIn_add entsIn_sub entsIn_foldl all_mapM)
open OnBytes.Desc.First.K4.Honest (K4Pub matsOf)

/-- Each entry that the form names lies in front of the place tB0 of the array of the reads. -/
abbrev Below (v : Env) (tB0 : ℕ) (a : Aff) : Prop := EntsIn (fun _ r i => r * v.K3 + i < tB0) a

/-- It is hG_of_lt's hypothesis hlt. -/
theorem below_iff (v : Env) (tB0 : ℕ) (a : Aff) :
    Below v tB0 a ↔ ∀ x ∈ a.ents.toList, x.row * v.K3 + x.idx < tB0 := Iff.rfl

/-- The list of places, seen from the place tB0. This defines a hypothesis; the definition claims
nothing. -/
structure TabFront (v : Env) (tB0 : ℕ) : Prop where
  /-- a family that begins in front of tB0 ends there or earlier -/
  ends : ∀ x ∈ v.tab, x.first < tB0 → x.first + x.len ≤ tB0
  /-- a family whose name does not begin with the letter b begins in front of tB0 -/
  front : ∀ n t, v.tabAt n = some t → n.toList.head? ≠ some 'b' → t < tB0

/-! ## The list of places that layTables returns -/

/-- Each place of the list is a family's: its name, its first entry, its end. -/
theorem tab_of_lay (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    ∀ x ∈ r.1, ∃ q ∈ r.2.1, x.name = q.1.name ∧ x.first = famFirst q ∧
      x.first + x.len = famFirst q + famLen mats q
  | [], p, r, h, x, hx => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    cases hx
  | a :: rest, p, r, h, x, hx => by
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
      have hne : (layParts mats a a.parts p).2 ≠ p := fun e =>
        hq (by rw [e]; exact beq_self_eq_true _)
      have hge := parts_end mats a a.parts p
      have hlt : p < (layParts mats a a.parts p).2 := by omega
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨(a, (layParts mats a a.parts p).1), List.mem_cons_self, rfl, ?_, ?_⟩
        · exact (parts_first mats a a.parts p hlt).symm
        · have f1 : famFirst (a, (layParts mats a a.parts p).1) = p :=
            parts_first mats a a.parts p hlt
          have f2 : famLen mats (a, (layParts mats a a.parts p).1) + p =
              0 + (layParts mats a a.parts p).2 := parts_len mats a a.parts p 0
          rw [f1]
          show p + ((layParts mats a a.parts p).2 - p) = _
          omega
      · obtain ⟨q, q1, q2⟩ := tab_of_lay mats rest _ r' h1 x hx
        exact ⟨q, List.mem_cons_of_mem _ q1, q2⟩

/-- The hind part of a list of families that lie one behind the other, and where the fore part ends.
-/
theorem laid_split' (mats : Array (ℕ × ℕ)) : ∀ (l1 l2 : List (TableAsk × List (ℕ × ℕ))) (p : ℕ),
    Laid mats (l1 ++ l2) p → ∃ p2, Laid mats l2 p2 ∧ p ≤ p2 ∧
      ∀ q ∈ l1, famFirst q < p2 ∧ famFirst q + famLen mats q ≤ p2
  | [], _, p, h => ⟨p, h, Nat.le_refl _, fun q hq => by cases hq⟩
  | x :: l1, l2, p, h => by
    obtain ⟨e1, e2, e3⟩ := h
    obtain ⟨p2, L, g1, g2⟩ := laid_split' mats l1 l2 _ e3
    have f1 : famFirst x = p := by
      unfold famFirst
      rw [e1]
      exact parts_first mats x.1 x.1.parts p e2
    have f2 : famLen mats x + p = 0 + (layParts mats x.1 x.1.parts p).2 := by
      have := parts_len mats x.1 x.1.parts p 0
      unfold famLen
      rw [e1]
      exact this
    refine ⟨p2, L, by omega, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨by omega, by omega⟩
    · exact g2 q hq

variable {Q : K4Pub} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **A family with none of the three names ends where a family with one of them begins, or
earlier.** -/
theorem named_ends (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {q0 : TableAsk × List (ℕ × ℕ)} (h0 : q0 ∈ r.2.1) (hn0 : ¬ Named q0.1) :
    ∀ q ∈ r.2.1, Named q.1 →
      famFirst q < famFirst q0 ∧ famFirst q + famLen (matsOf Q) q ≤ famFirst q0 := by
  obtain ⟨L1, L2⟩ := laid_of_layTables _ _ _ _ hl
  rw [Fo.tableAsks_eq] at L2
  obtain ⟨l1, l2, e, m1, m2⟩ := List.map_eq_append_iff.mp L2
  rw [e] at L1
  obtain ⟨p2, L3, -, g⟩ := laid_split' _ l1 l2 0 L1
  have pre : ∀ q ∈ l1, Named q.1 := by
    intro q h
    have hp : q.1 ∈ Fo.preAsks Q.P.y Q.P.rd Q.g := by
      rw [← m1]
      exact List.mem_map.mpr ⟨q, h, rfl⟩
    exact ⟨beq_eq_false_iff_ne.mpr (Fo.ask_ne hp _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne hp _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne hp _ (by decide))⟩
  have hind : ∀ q ∈ l2, ¬ Named q.1 := by
    intro q h hn
    have hp : q.1 ∈ [Fo.planeAsk Q.P.y "b-bits-0", Fo.planeAsk Q.P.y "b-bits-1",
        Fo.planeAsk Q.P.y "b-pin"] := by
      rw [← m2]
      exact List.mem_map.mpr ⟨q, h, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with e' | e' | e'
    · exact absurd (e' ▸ hn.1) (by simp [Fo.planeAsk])
    · exact absurd (e' ▸ hn.2.1) (by simp [Fo.planeAsk])
    · exact absurd (e' ▸ hn.2.2) (by simp [Fo.planeAsk])
  have h02 : q0 ∈ l2 := by
    rw [e] at h0
    rcases List.mem_append.mp h0 with h | h
    · exact absurd (pre q0 h) hn0
    · exact h
  have hp2 := laid_first_ge _ _ _ L3 q0 h02
  intro q hq hn
  rw [e] at hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨a1, a2⟩ := g q h
    exact ⟨by omega, by omega⟩
  · exact absurd hn (hind q h)

/-- A name that does not begin with the letter b is none of the three. -/
theorem named_of_head {a : TableAsk} (h : a.name.toList.head? ≠ some 'b') : Named a := by
  refine ⟨beq_eq_false_iff_ne.mpr fun e => h ?_, beq_eq_false_iff_ne.mpr fun e => h ?_,
    beq_eq_false_iff_ne.mpr fun e => h ?_⟩ <;>
  · rw [e]
    decide

/-- **TabFront where layTables has returned**, at the first place of the family "b-bits-0". -/
theorem tabFront_of_lay (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {v : Env} (hv : v.tab = r.1) {tB0 : ℕ} (hB : v.tabAt "b-bits-0" = some tB0) :
    TabFront v tB0 := by
  have hl' : layTables (matsOf Q) (Fo.preAsks Q.P.y Q.P.rd Q.g ++ Fo.planeAsk Q.P.y "b-bits-0" ::
      [Fo.planeAsk Q.P.y "b-bits-1", Fo.planeAsk Q.P.y "b-pin"]) 0 = some (r.1, r.2.1, r.2.2) := hl
  obtain ⟨p0, hp0, hmem⟩ := Fo.lay_find (matsOf Q) (Fo.planeAsk Q.P.y "b-bits-0") rfl _ _ 0 _ _ _
    (fun b hb => Fo.ask_ne hb "b-bits-0" (by decide)) hl'
  have hB' : (r.1.find? fun t => t.name == "b-bits-0").map (·.first) = some tB0 := by
    rw [← hv]
    exact hB
  obtain rfl : tB0 = p0 := Option.some.inj (hB'.symm.trans hp0)
  have hn0 : ¬ Named (Fo.planeAsk Q.P.y "b-bits-0") := fun hn =>
    absurd hn.1 (by simp [Fo.planeAsk])
  have low := planes_last hl hmem rfl
  have high := named_ends hl hmem hn0
  refine ⟨fun x hx hlt => ?_, fun n t hn hh => ?_⟩
  · rw [hv] at hx
    obtain ⟨q, hq, -, a2, a3⟩ := tab_of_lay _ _ _ _ hl x hx
    by_cases c : Named q.1
    · have := (high q hq c).2
      have e0 : famFirst (Fo.planeAsk Q.P.y "b-bits-0",
          [((Fo.planeAsk Q.P.y "b-bits-0").M0, tB0)]) = tB0 := rfl
      omega
    · have := low q hq c
      have e0 : famFirst (Fo.planeAsk Q.P.y "b-bits-0",
          [((Fo.planeAsk Q.P.y "b-bits-0").M0, tB0)]) = tB0 := rfl
      omega
  · unfold Env.tabAt at hn
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hn
    have hm : x ∈ r.1 := by
      rw [← hv]
      exact List.mem_of_find?_eq_some hx
    have hname : x.name = n := by
      have h1 := List.find?_some hx
      simpa using h1
    obtain ⟨q, hq, a1, a2, -⟩ := tab_of_lay _ _ _ _ hl x hm
    have c : Named q.1 := named_of_head (by rw [← a1, hname]; exact hh)
    have := (high q hq c).1
    have e0 : famFirst (Fo.planeAsk Q.P.y "b-bits-0",
        [((Fo.planeAsk Q.P.y "b-bits-0").M0, tB0)]) = tB0 := rfl
    omega

/-! ## The readers -/

variable {v : Env} {tB0 : ℕ}

/-- **One entry.** -/
theorem below_U3at (F : TabFront v tB0) {t i : ℕ} (ht : t < tB0) {f : Aff}
    (h : v.U3at t i = some f) : Below v tB0 f := by
  unfold Env.U3at at h
  split at h
  · cases h
  · rename_i x hx
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      have hm : x ∈ v.tab := List.mem_of_find?_eq_some hx
      have hf : x.first = t := by
        have h1 := List.find?_some hx
        simpa using h1
      have hi : i < x.len := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1.1
      have e : (t + i) / v.K3 * v.K3 + (t + i) % v.K3 = t + i := Nat.div_add_mod' _ _
      have he := F.ends x hm (by rw [hf]; exact ht)
      exact entsIn_ent (by rw [e]; omega)
    · cases h

/-- A sum made by a loop that may return nothing. -/
theorem below_foldlM {g : ℕ → Option (Aff × E)} (hg : ∀ x p, g x = some p → Below v tB0 p.1) :
    ∀ (l : List ℕ) (a s : Aff), Below v tB0 a →
      l.foldlM (fun a x => (g x).map fun t => a.addMul t.1 t.2) a = some s → Below v tB0 s
  | [], a, s, ha, h => by
    cases h
    exact ha
  | x :: l, a, s, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact below_foldlM hg l _ s (entsIn_addMul _ ha (hg x p hp)) h

/-- The verifier's sum of forms. -/
theorem below_sumForms {n : ℕ} {g : ℕ → Option (Aff × E)} {s : Aff}
    (hg : ∀ x p, g x = some p → Below v tB0 p.1) (h : sumForms n g = some s) : Below v tB0 s :=
  below_foldlM hg _ _ s (entsIn_ofConst _) h

/-- A sum over limbs. -/
theorem below_limbs (F : TabFront v tB0) {t : ℕ} (ht : t < tB0) {nl : ℕ} {cell : ℕ → ℕ} {s : Aff}
    (h : v.limbs t nl cell = some s) : Below v tB0 s :=
  below_sumForms (fun _ p hp => by
    obtain ⟨a, ha, e⟩ := map_some hp
    subst e
    exact below_U3at F ht ha) h

/-- A list of signs that begins with a sign other than b, with any list behind it. -/
theorem head_or {l m : List Char} {c : Char} (h : l.head? = some c) (hc : c ≠ 'b') :
    (l ++ m).head? ≠ some 'b' := by
  cases l with
  | nil => cases h
  | cons x t =>
    have e : x = c := Option.some.inj h
    rw [List.cons_append, List.head?_cons, e]
    exact fun e' => hc (Option.some.inj e')

/-- The name of a matrix's family at a point does not begin with the letter b. -/
theorem mname_head (mat : ℕ) (Z : String) :
    (Env.mname mat ++ "@" ++ Z).toList.head? ≠ some 'b' := by
  rw [String.toList_append, String.toList_append]
  show ((Env.mname mat).toList ++ ['@'] ++ Z.toList).head? ≠ _
  match mat with
  | 0 => exact head_or (c := 'a') (by decide) (by decide)
  | 1 => exact head_or (c := 'a') (by decide) (by decide)
  | 2 => exact head_or (c := 'a') (by decide) (by decide)
  | 3 => exact head_or (c := 'q') (by decide) (by decide)
  | n + 4 =>
    have e : Env.mname (n + 4) = "" := by simp [Env.mname]
    rw [e]
    exact head_or (c := '@') (by decide) (by decide)

/-- **An entry of a tensor at a token point.** -/
theorem below_shA (F : TabFront v tB0) {X P : String} {i j : ℕ} {s : Aff}
    (h : v.shA X P i j = some s) : Below v tB0 s := by
  obtain ⟨x, hx, h⟩ := bind_some h
  unfold Env.tensorAt at hx
  obtain ⟨t, -, hx⟩ := bind_some hx
  obtain ⟨tb, htb, hx⟩ := bind_some hx
  obtain rfl := Option.some.inj hx
  exact below_limbs F (F.front _ _ htb (mname_head _ _)) h

/-- The cells of a norm's row. -/
theorem below_rowCells (F : TabFront v tB0) {P : String} {i n : ℕ} {cells : Array Aff}
    (h : v.rowCells P i n = some cells) (j : ℕ) : Below v tB0 (cells.getD j aff0) := by
  unfold Env.rowCells at h
  obtain ⟨t, ht, h⟩ := bind_some h
  obtain ⟨tr, -, h⟩ := bind_some h
  have hlt : t < tB0 := F.front _ _ ht (by
    rw [String.toList_append]
    exact head_or (c := 'a') (by decide) (by decide))
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : j < ys.length
  · have e : ys.toArray.getD j aff0 = ys[j] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := Below v tB0) (fun _ _ hb => below_U3at F hlt hb) _ ys hys _
      (List.getElem_mem hj)
  · have e : ys.toArray.getD j aff0 = aff0 := by simp [Array.getD, hj]
    rw [e]
    exact entsIn_ofConst _

/-- The number that digits spell, in the row of five limbs. -/
theorem below_ledDig {Dg : Array Aff} (hD : ∀ j, Below v tB0 (Dg.getD j (LedK.c zeroE)))
    (first n : ℕ) : Below v tB0 (ledDig Dg first n) :=
  entsIn_foldl _ (fun _ _ hf => entsIn_add hf (entsIn_scale _ (hD _))) _ _ (entsIn_ofConst _)

/-- The same in the row of four limbs. -/
theorem below_digits {Dg : Array Aff} (hD : ∀ j, Below v tB0 (Dg.getD j aff0)) (a n : ℕ) :
    Below v tB0 (Env.digits Dg a n) :=
  entsIn_foldl _ (fun _ _ hf => entsIn_addMul _ hf (hD _)) _ _ (entsIn_ofConst _)

/-- **The reciprocal of a norm's row.** The proof follows the library's inTab_rowR
(Johnson/Road/K4/Reads/TermsEnts.lean), with Below in place of its predicate. -/
theorem below_rowR (F : TabFront v tB0) {P : String} {i : ℕ} {f : Aff}
    (h : v.rowR P i = some f) : Below v tB0 f := by
  unfold Env.rowR at h
  split at h
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.row5At at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    obtain rfl : row5 (fun j => cells.getD j aff0) = r := Option.some.inj hr
    have hD : ∀ j, Below v tB0 ((Array.ofFn (n := 99) fun j : Fin 99 =>
        (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE)) := by
      intro j
      by_cases hj : j < 99
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.add (cells.getD j aff0) (LedK.c (ofNat 128)) := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_add (below_rowCells F hc j) (entsIn_ofConst _)
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.c zeroE := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_ofConst _
    exact entsIn_add (below_ledDig hD 80 3) (entsIn_scale _ (below_ledDig hD 83 3))
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.rowAt at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    have hr' := Option.some.inj hr
    subst hr'
    have hD : ∀ j, Below v tB0 ((cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0) := by
      intro j
      by_cases hj : j < cells.size
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 =
            cells.getD j aff0 + Aff.ofConst (ofNat 128) := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_add (below_rowCells F hc j) (entsIn_ofConst _)
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 = aff0 := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_ofConst _
    exact entsIn_add (below_digits hD 57 3) (entsIn_scale _ (below_digits hD 60 3))

/-- **Every claim on the second token sumcheck's end values.** -/
theorem below_terms (F : TabFront v tB0) {H : Heard} {l : List Aff}
    (h : termsForms v H = some l) : ∀ a ∈ l, Below v tB0 a := by
  unfold termsForms at h
  obtain ⟨tT, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : a ++ b ++ c = l := Option.some.inj h
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · refine all_mapM (Pr := Below v tB0) (fun i y hy => ?_) _ a a1 f hf
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
      exact entsIn_sub (entsIn_slot _) (below_rowR F hx)
    · refine all_mapM (Pr := Below v tB0) (fun i y hy => ?_) _ b a2 f hf
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
      exact entsIn_sub (entsIn_slot _) (below_shA F hx)
  · refine all_mapM (Pr := Below v tB0) (fun i y hy => ?_) _ c a3 f hf
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact entsIn_sub (entsIn_slot _) (below_shA F hx)

/-- **The claims' entries lie off the matrix of the lookup's planes**: what TermsField.lean's
TermsAt asks under the name off, at G := off that matrix. -/
theorem terms_off (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {fo' : Forest.Heard} {pts : List (String × Array E)} {tl : HTailF2} {funs : Array HFun}
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hv : v.tab = r.1)
    (hB : v.tabAt "b-bits-0" = some tB0) {H : Heard} {l : List Aff}
    (h : termsForms v H = some l) :
    ∀ a ∈ l, ∀ y ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (y.row * v.K3 + y.idx) → z.1.mat ≠ (matIx Q.P.y).iB :=
  fun a ha => hG_of_lt hl hf hv hB (below_terms (tabFront_of_lay hl hv hB) h a ha)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.below_iff
#print axioms OnBytes.Road.K4.C.tab_of_lay
#print axioms OnBytes.Road.K4.C.laid_split'
#print axioms OnBytes.Road.K4.C.named_ends
#print axioms OnBytes.Road.K4.C.named_of_head
#print axioms OnBytes.Road.K4.C.tabFront_of_lay
#print axioms OnBytes.Road.K4.C.below_U3at
#print axioms OnBytes.Road.K4.C.below_foldlM
#print axioms OnBytes.Road.K4.C.below_sumForms
#print axioms OnBytes.Road.K4.C.below_limbs
#print axioms OnBytes.Road.K4.C.head_or
#print axioms OnBytes.Road.K4.C.mname_head
#print axioms OnBytes.Road.K4.C.below_shA
#print axioms OnBytes.Road.K4.C.below_rowCells
#print axioms OnBytes.Road.K4.C.below_ledDig
#print axioms OnBytes.Road.K4.C.below_digits
#print axioms OnBytes.Road.K4.C.below_rowR
#print axioms OnBytes.Road.K4.C.below_terms
#print axioms OnBytes.Road.K4.C.terms_off
