-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TripsOf.lean: CONDITIONAL.

What is here. THE PRODUCTS OF ONE PANEL OF THE SECOND TOKEN SUMCHECK's SUMMAND (`tripsOf`,
Johnson/Desc/K4/Honest/Sides.lean), AT A POINT AND AT N CORNERS. Where the panel is one panel with
open places (PanelsShown.lean), filled at the point and at each corner with the values given there,
and under the hypothesis `Kinds` on what its factors are made of (three kinds of thing: a form's
value; a weights' table's entry; a never-sent vector's entry: are each, at the point, the
combination of the same at the corners under given coefficients; a constant form is worth its
constant, at the point and at EVERY corner's number; the coefficients sum to 1; of the given values
nothing is asked), the panel's products at the point and at the corners stand in the relation
`LinAt` (TripsKit.lean). Statements and proofs.

  `Kinds`   **the hypothesis**
  `amapM_range_get`, `amapM_range_size`, `getD_map_range`, `LinAt.ofRange`   tools
  `ixOf`   for each product of a panel the number of the given value that its first factor is
  `sl_at_some`, `sl_at_none`, `tri_lin`   a panel whose rows carry the selector
  `elemOfP`, `elem_lin`, `plain_lin`   a panel with two factors
  `tripsOf_lin`   **one panel**

Limits. At the reading `Reading.gl`. `Kinds` IS A HYPOTHESIS: nothing here shows it. FOR A PANEL
WHOSE ROWS CARRY THE SELECTOR ONE HYPOTHESIS MORE: ITS WEIGHTS' TABLE IS THE SAME WORDS AT THE POINT
AND AT EVERY CORNER: its second factor is a sum of products of a column factor, which moves with the
point, and an entry of that table: were both to move, the sum would be no such combination. From
returns: that `tripsOf` returns anywhere is not said. These are hypotheses of statements on what an
honest sum is worth; where they are false nothing is said. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelsShown
import Johnson.Desc.ProofFile.Honest.K4.Law.TripsKit
import Johnson.Road.K4.C.StackEnds
import OnBytes.Desc.First.K4.RowsLaws
import OnBytes.Maker.TablesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE maddE)
open OnBytes.Model (Reading Aff)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Road.K4.C (gl_foldl_maddE range_sum)
open OnBytes.Desc.First.K4 (mapM_range_get)
open OnBytes.Desc.First.K4.Honest

/-- **What a product's factors are made of, at the point and at the corners**: three kinds of thing
are combinations; a constant form is worth its constant; the coefficients sum to 1. valz, Fz, hhz: a
form's value, the weights' tables, the never-sent vectors' entries at the point; valt t, Ft t, hht
t: at corner t. This defines a hypothesis; the definition claims nothing. -/
structure Kinds (N : ℕ) (q : ℕ → Cb.Gl.E) (valz : Aff → Option E) (valt : ℕ → Aff → Option E)
    (Fz : Array (Array E)) (Ft : ℕ → Array (Array E)) (hhz : ℕ → ℕ → E)
    (hht : ℕ → ℕ → ℕ → E) : Prop where
  form : ∀ (a : Aff) (x : E) (xt : ℕ → E), valz a = some x →
    (∀ t, t < N → valt t a = some (xt t)) →
    Reading.gl.val x = ∑ t ∈ Finset.range N, q t * Reading.gl.val (xt t)
  constz : ∀ c x, valz (Aff.ofConst c) = some x → x = c
  constt : ∀ t c x, valt t (Aff.ofConst c) = some x → x = c
  tab : ∀ a kk hi yv, Reading.gl.val (at2 (Fz.getD a #[]) kk hi yv) =
    ∑ t ∈ Finset.range N, q t * Reading.gl.val (at2 ((Ft t).getD a #[]) kk hi yv)
  gated : ∀ lm yv, Reading.gl.val (hhz lm yv) =
    ∑ t ∈ Finset.range N, q t * Reading.gl.val (hht t lm yv)
  one : ∑ t ∈ Finset.range N, q t = 1

/-! ## 1 Tools -/

/-- A loop over the first n numbers that answers: its member number i. -/
theorem amapM_range_get {β : Type} (g : ℕ → Option β) {n : ℕ} {L : Array β}
    (h : (Array.range n).mapM g = some L) {i : ℕ} (hi : i < n) (d : β) :
    g i = some (L.getD i d) := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at h
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨b, hb, hb'⟩ := mapM_range_get g hl hi
  rw [hb, ← e, Array.getD_eq_getD_getElem?, List.getElem?_toArray, hb']
  rfl

/-- It has n members. -/
theorem amapM_range_size {β : Type} (g : ℕ → Option β) {n : ℕ} {L : Array β}
    (h : (Array.range n).mapM g = some L) : L.size = n := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at h
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp h
  rw [← e, List.size_toArray, OnBytes.Maker.mapM_length _ _ _ hl, List.length_range]

theorem getD_map_range {β : Type} (f : ℕ → β) (n k : ℕ) (hk : k < n) (d : β) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

variable {N : ℕ} {q : ℕ → Cb.Gl.E} {e : Array E} {shs : ℕ → Array E}

/-- Lists that are made number by number. -/
theorem LinAt.ofRange (n : ℕ) (φz : ℕ → Trip) (φt : ℕ → ℕ → Trip) (o : ℕ → Option ℕ)
    (h : ∀ k, k < n → TripLin N q e shs (φz k) (fun t => φt t k) (o k)) :
    LinAt N q e shs ((List.range n).map φz) (fun t => (List.range n).map (φt t))
      ((List.range n).map o) := by
  refine ⟨fun t _ => by simp, by simp, fun k hk => ?_⟩
  have hk' : k < n := by simpa using hk
  rw [getD_map_range φz n k hk', getD_map_range o n k hk']
  exact (h k hk').congr fun t _ => getD_map_range (φt t) n k hk' _

/-! ## 2 Which given value a product's first factor is -/

/-- For each product of a panel with open places, in the products' order. -/
def ixOf (s : SymBlk) : List (Option ℕ) :=
  if s.b.tri then
    (List.range s.b.ni).map fun k => s.gS.bind fun x => if k < x.1 then some (x.2 k) else none
  else
    (List.range s.b.ni).flatMap fun i => (List.range s.b.ny).map fun yv => s.fA.map fun f => f i yv

/-! ## 3 A panel whose rows carry the selector -/

/-- The selector's entry number k of a panel whose selector has open places. -/
theorem sl_at_some (s : SymBlk) (sh : Array E) (k : ℕ) {x : ℕ × (ℕ → ℕ)} (hg : s.gS = some x) :
    (s.at sh).sl.getD k zeroE = if k < x.1 then sh.getD (x.2 k) zeroE else zeroE := by
  have e : (s.at sh).sl = (Array.range x.1).map fun e => sh.getD (x.2 e) zeroE := by
    unfold SymBlk.at
    rw [hg]
  rw [e, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  by_cases hk : k < x.1
  · rw [if_pos hk, if_pos hk]
    rfl
  · rw [if_neg hk, if_neg hk]
    rfl

/-- The same of a panel whose selector has none. -/
theorem sl_at_none (s : SymBlk) (sh : Array E) (k : ℕ) (hg : s.gS = none) :
    (s.at sh).sl.getD k zeroE = s.b.sl.getD k zeroE := by
  have e : (s.at sh).sl = s.b.sl := by
    unfold SymBlk.at
    rw [hg]
  rw [e]

variable {S : Sides} {valz : Aff → Option E} {valt : ℕ → Aff → Option E}
  {Fz : Array (Array E)} {Ft : ℕ → Array (Array E)} {hhz : ℕ → ℕ → E} {hht : ℕ → ℕ → ℕ → E}

/-- **A panel whose rows carry the selector.** hpl: its weights' table is the same words at the
point and at every corner. -/
theorem tri_lin (K : Kinds N q valz valt Fz Ft hhz hht) (s : SymBlk) (htri : s.b.tri = true)
    (hpl : ∀ v0, s.b.v0 = some v0 → ∀ t, t < N → (Ft t).getD v0 #[] = Fz.getD v0 #[])
    (bz : Array Trip) (bt : ℕ → Array Trip)
    (hz : tripsOf S valz Fz hhz (s.at e) = some bz)
    (ht : ∀ t, t < N → tripsOf S (valt t) (Ft t) (hht t) (s.at (shs t)) = some (bt t)) :
    LinAt N q e shs bz.toList (fun t => (bt t).toList) (ixOf s) := by
  have hb : ∀ sh, (s.at sh).tri = true := fun _ => htri
  -- the point
  unfold tripsOf at hz
  simp only [hb e, ↓reduceIte] at hz
  obtain ⟨v0, hv0, hz⟩ := Option.bind_eq_some_iff.mp hz
  obtain ⟨cz, hcz, hz⟩ := Option.bind_eq_some_iff.mp hz
  have ez := (Option.some.inj hz).symm
  have hv0' : s.b.v0 = some v0 := hv0
  -- the corners
  have hc : ∀ t, t < N → ∃ ct : Array E,
      ((Array.range s.b.ny).mapM fun yv =>
        match s.b.virt with
        | some k => some (hht t (k - 1) yv)
        | none => valt t (s.b.xx.getD yv {})) = some ct ∧
      bt t = (Array.range s.b.ni).map fun k =>
        (mulE s.b.ec (s.b.wt.getD 0 zeroE), (s.at (shs t)).sl.getD k zeroE,
          (List.range s.b.ny).foldl
            (fun a yv => maddE a (ct.getD yv zeroE) (at2 ((Ft t).getD v0 #[]) (S.kkOf v0) k yv))
            zeroE) := by
    intro t htN
    have h := ht t htN
    unfold tripsOf at h
    simp only [hb (shs t), ↓reduceIte] at h
    obtain ⟨v0', hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ct, hct, h⟩ := Option.bind_eq_some_iff.mp h
    have ev : v0' = v0 := Option.some.inj ((show s.b.v0 = some v0' from hv).symm.trans hv0')
    subst ev
    exact ⟨ct, hct, (Option.some.inj h).symm⟩
  classical
  let ct : ℕ → Array E := fun t => if h : t < N then (hc t h).choose else #[]
  have hct1 : ∀ t, t < N → ((Array.range s.b.ny).mapM fun yv =>
      match s.b.virt with
      | some k => some (hht t (k - 1) yv)
      | none => valt t (s.b.xx.getD yv {})) = some (ct t) := fun t h => by
    have := (hc t h).choose_spec.1
    simpa only [ct, dif_pos h] using this
  have hct2 : ∀ t, t < N → bt t = (Array.range s.b.ni).map fun k =>
      (mulE s.b.ec (s.b.wt.getD 0 zeroE), (s.at (shs t)).sl.getD k zeroE,
        (List.range s.b.ny).foldl
          (fun a yv => maddE a ((ct t).getD yv zeroE)
            (at2 ((Ft t).getD v0 #[]) (S.kkOf v0) k yv)) zeroE) := fun t h => by
    have := (hc t h).choose_spec.2
    simpa only [ct, dif_pos h] using this
  have hcz' : ((Array.range s.b.ny).mapM fun yv =>
      match s.b.virt with
      | some k => some (hhz (k - 1) yv)
      | none => valz (s.b.xx.getD yv {})) = some cz := hcz
  -- a column factor at the point is the combination of the corners'
  have hcol : ∀ yv, yv < s.b.ny → Reading.gl.val (cz.getD yv zeroE) =
      ∑ t ∈ Finset.range N, q t * Reading.gl.val ((ct t).getD yv zeroE) := by
    intro yv hyv
    have gz := amapM_range_get _ hcz' hyv zeroE
    have gt := fun t (h : t < N) => amapM_range_get _ (hct1 t h) hyv zeroE
    cases hv : s.b.virt with
    | some k =>
      simp only [hv] at gz gt
      rw [← Option.some.inj gz, K.gated]
      exact Finset.sum_congr rfl fun t h => by
        rw [← Option.some.inj (gt t (Finset.mem_range.mp h))]
    | none =>
      simp only [hv] at gz gt
      exact K.form _ _ (fun t => (ct t).getD yv zeroE) gz gt
  have ezl : bz.toList = (List.range s.b.ni).map fun k =>
      ((mulE s.b.ec (s.b.wt.getD 0 zeroE), (s.at e).sl.getD k zeroE,
        (List.range s.b.ny).foldl
          (fun a yv => maddE a (cz.getD yv zeroE) (at2 (Fz.getD v0 #[]) (S.kkOf v0) k yv))
          zeroE) : Trip) := by
    rw [ez, Array.toList_map, Array.toList_range]
    rfl
  unfold ixOf
  rw [if_pos htri, ezl]
  refine (LinAt.ofRange s.b.ni _ (fun t k =>
    ((mulE s.b.ec (s.b.wt.getD 0 zeroE), (s.at (shs t)).sl.getD k zeroE,
      (List.range s.b.ny).foldl
        (fun a yv => maddE a ((ct t).getD yv zeroE)
          (at2 ((Ft t).getD v0 #[]) (S.kkOf v0) k yv)) zeroE) : Trip)) _ fun k _ => ?_).congr
    fun t h => by rw [hct2 t h, Array.toList_map, Array.toList_range]
  refine ⟨fun _ _ => rfl, fun i hi => ?_, fun ho => ?_, ?_⟩
  · -- the first factor is a given value
    show (s.at e).sl.getD k zeroE = e.getD i zeroE ∧
      ∀ t, t < N → (s.at (shs t)).sl.getD k zeroE = (shs t).getD i zeroE
    cases hg : s.gS with
    | none =>
      rw [hg] at hi
      cases hi
    | some x =>
      rw [hg] at hi
      have hi' : (if k < x.1 then some (x.2 k) else none) = some i := hi
      by_cases hk : k < x.1
      · rw [if_pos hk] at hi'
        obtain rfl := Option.some.inj hi'
        exact ⟨by rw [sl_at_some s e k hg, if_pos hk],
          fun t _ => by rw [sl_at_some s (shs t) k hg, if_pos hk]⟩
      · rw [if_neg hk] at hi'
        cases hi'
  · -- the first factor is none of them: it is the same word everywhere
    show Reading.gl.val ((s.at e).sl.getD k zeroE) =
      ∑ t ∈ Finset.range N, q t * Reading.gl.val ((s.at (shs t)).sl.getD k zeroE)
    have hc : ∃ c : E, ∀ sh, (s.at sh).sl.getD k zeroE = c := by
      cases hg : s.gS with
      | none => exact ⟨_, fun sh => sl_at_none s sh k hg⟩
      | some x =>
        rw [hg] at ho
        have ho' : (if k < x.1 then some (x.2 k) else none) = none := ho
        by_cases hk : k < x.1
        · rw [if_pos hk] at ho'
          cases ho'
        · exact ⟨zeroE, fun sh => by rw [sl_at_some s sh k hg, if_neg hk]⟩
    obtain ⟨c, hc⟩ := hc
    simp only [hc]
    rw [← Finset.sum_mul, K.one, one_mul]
  · -- the second factor
    show Reading.gl.val ((List.range s.b.ny).foldl
        (fun a yv => maddE a (cz.getD yv zeroE) (at2 (Fz.getD v0 #[]) (S.kkOf v0) k yv)) zeroE) =
      ∑ t ∈ Finset.range N, q t * Reading.gl.val ((List.range s.b.ny).foldl
        (fun a yv => maddE a ((ct t).getD yv zeroE)
          (at2 ((Ft t).getD v0 #[]) (S.kkOf v0) k yv)) zeroE)
    rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum]
    have er : ∀ t ∈ Finset.range N, q t * Reading.gl.val ((List.range s.b.ny).foldl
        (fun a yv => maddE a ((ct t).getD yv zeroE)
          (at2 ((Ft t).getD v0 #[]) (S.kkOf v0) k yv)) zeroE) =
        ∑ yv ∈ Finset.range s.b.ny, q t * Reading.gl.val ((ct t).getD yv zeroE) *
          Reading.gl.val (at2 (Fz.getD v0 #[]) (S.kkOf v0) k yv) := by
      intro t h
      rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum, Finset.mul_sum,
        hpl v0 hv0' t (Finset.mem_range.mp h)]
      exact Finset.sum_congr rfl fun yv _ => by ring
    rw [Finset.sum_congr rfl er, Finset.sum_comm]
    refine Finset.sum_congr rfl fun yv hyv => ?_
    rw [hcol yv (Finset.mem_range.mp hyv), Finset.sum_mul]

/-! ## 4 A panel with two factors; one panel -/

/-- The product at row i and column yv of a panel with two factors, as `tripsOf` makes it. A: the
panel's side A. -/
def elemOfP (S : Sides) (val : Aff → Option E) (Fx : Array (Array E)) (s : SymBlk)
    (A : ℕ → ℕ → Option Aff) (i yv : ℕ) : Option Trip := do
  let a ← val (← A i yv)
  let c ← match s.b.v0, s.b.B with
    | none, some B => do val (← B i yv)
    | some v0, _ => some (at2 (Fx.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
    | none, none => none
  pure ((mulE s.b.ec (s.b.wt.getD i zeroE), a, c) : Trip)

/-- **One product of a panel with two factors.** -/
theorem elem_lin (K : Kinds N q valz valt Fz Ft hhz hht) (s : SymBlk) (i yv : ℕ)
    {Az : ℕ → ℕ → Option Aff} {At : ℕ → ℕ → ℕ → Option Aff} (hAz : (s.at e).A = some Az)
    (hAt : ∀ t, t < N → (s.at (shs t)).A = some (At t)) {x : Trip} {xs : ℕ → Trip}
    (gz : elemOfP S valz Fz s Az i yv = some x)
    (gt : ∀ t, t < N → elemOfP S (valt t) (Ft t) s (At t) i yv = some (xs t)) :
    TripLin N q e shs x xs (s.fA.map fun f => f i yv) := by
  -- the text, opened
  have open_ : ∀ (val : Aff → Option E) (Fx : Array (Array E)) (A : ℕ → ℕ → Option Aff) (y : Trip),
      elemOfP S val Fx s A i yv = some y → ∃ f a c, A i yv = some f ∧ val f = some a ∧
        (match s.b.v0, s.b.B with
          | none, some B => (B i yv).bind val
          | some v0, _ => some (at2 (Fx.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
          | none, none => none) = some c ∧
        y = (mulE s.b.ec (s.b.wt.getD i zeroE), a, c) := by
    intro val Fx A y h
    unfold elemOfP at h
    obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    refine ⟨f, a, ?_⟩
    revert h
    cases s.b.v0 with
    | some v0 =>
      intro h
      exact ⟨_, hf, ha, rfl, (Option.some.inj h).symm⟩
    | none =>
      cases s.b.B with
      | none =>
        intro h
        cases h
      | some B =>
        intro h
        obtain ⟨g, hg, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨c, hf, ha, by
          show (B i yv).bind val = some c
          rw [hg]
          exact hc, (Option.some.inj h).symm⟩
  obtain ⟨fz, az, cz, h1, h2, h3, rfl⟩ := open_ valz Fz Az x gz
  have hc := fun t (h : t < N) => open_ (valt t) (Ft t) (At t) (xs t) (gt t h)
  refine ⟨fun t h => ?_, fun ix hix => ?_, fun ho => ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, e1⟩ := hc t h
    rw [e1]
  · -- the first factor is a given value
    cases hf : s.fA with
    | none =>
      rw [hf] at hix
      cases hix
    | some f0 =>
      rw [hf] at hix
      obtain rfl : f0 i yv = ix := Option.some.inj hix
      have eAz : Az = fun i yv => some (Aff.ofConst (e.getD (f0 i yv) zeroE)) := by
        have : (s.at e).A = some fun i yv => some (Aff.ofConst (e.getD (f0 i yv) zeroE)) := by
          unfold SymBlk.at
          rw [hf]
        exact Option.some.inj (hAz.symm.trans this)
      refine ⟨?_, fun t h => ?_⟩
      · rw [eAz] at h1
        rw [← Option.some.inj h1] at h2
        exact K.constz _ _ h2
      · obtain ⟨ft, at_, ct, k1, k2, _, e1⟩ := hc t h
        have eAt : At t = fun i yv => some (Aff.ofConst ((shs t).getD (f0 i yv) zeroE)) := by
          have : (s.at (shs t)).A =
              some fun i yv => some (Aff.ofConst ((shs t).getD (f0 i yv) zeroE)) := by
            unfold SymBlk.at
            rw [hf]
          exact Option.some.inj ((hAt t h).symm.trans this)
        rw [eAt] at k1
        rw [← Option.some.inj k1] at k2
        rw [e1]
        exact K.constt t _ _ k2
  · -- the first factor is a form's value
    cases hf : s.fA with
    | some f0 =>
      rw [hf] at ho
      cases ho
    | none =>
      have eA : ∀ sh, (s.at sh).A = s.b.A := fun sh => by
        unfold SymBlk.at
        rw [hf]
      have e0 : s.b.A = some Az := (eA e).symm.trans hAz
      refine K.form fz az (fun t => (xs t).2.1) h2 fun t h => ?_
      obtain ⟨ft, at_, ct, k1, k2, _, e1⟩ := hc t h
      have e2 : At t = Az := Option.some.inj ((hAt t h).symm.trans ((eA _).trans e0))
      rw [e2, h1] at k1
      show valt t fz = some (xs t).2.1
      rw [Option.some.inj k1, e1]
      exact k2
  · -- the second factor
    cases hv : s.b.v0 with
    | some v0 =>
      simp only [hv] at h3
      show Reading.gl.val cz = _
      rw [← Option.some.inj h3, K.tab]
      refine Finset.sum_congr rfl fun t h => ?_
      obtain ⟨_, _, ct, _, _, k3, e1⟩ := hc t (Finset.mem_range.mp h)
      simp only [hv] at k3
      rw [e1, ← Option.some.inj k3]
    | none =>
      cases hB : s.b.B with
      | none =>
        simp only [hv, hB] at h3
        cases h3
      | some B =>
        simp only [hv, hB] at h3
        obtain ⟨g, hg, h4⟩ := Option.bind_eq_some_iff.mp h3
        refine K.form g cz (fun t => (xs t).2.2) h4 fun t h => ?_
        obtain ⟨_, _, ct, _, _, k3, e1⟩ := hc t h
        simp only [hv, hB] at k3
        obtain ⟨g', hg', k4⟩ := Option.bind_eq_some_iff.mp k3
        rw [hg] at hg'
        show valt t g = some (xs t).2.2
        rw [Option.some.inj hg', e1]
        exact k4

/-- **A panel with two factors.** -/
theorem plain_lin (K : Kinds N q valz valt Fz Ft hhz hht) (s : SymBlk) (htri : s.b.tri = false)
    (bz : Array Trip) (bt : ℕ → Array Trip)
    (hz : tripsOf S valz Fz hhz (s.at e) = some bz)
    (ht : ∀ t, t < N → tripsOf S (valt t) (Ft t) (hht t) (s.at (shs t)) = some (bt t)) :
    LinAt N q e shs bz.toList (fun t => (bt t).toList) (ixOf s) := by
  -- the maker's text at any of the arguments, opened
  have open_ : ∀ (val : Aff → Option E) (Fx : Array (Array E)) (hh : ℕ → ℕ → E) (sh : Array E)
      (b : Array Trip), tripsOf S val Fx hh (s.at sh) = some b →
      ∃ (A : ℕ → ℕ → Option Aff) (Lr : List (Array Trip)), (s.at sh).A = some A ∧
        (List.range s.b.ni).mapM (fun i => (Array.range s.b.ny).mapM (elemOfP S val Fx s A i)) =
          some Lr ∧ b.toList = Lr.flatMap Array.toList := by
    intro val Fx hh sh b h
    unfold tripsOf at h
    have hb : (s.at sh).tri = false := htri
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hv : (s.at sh).virt.isSome = true
    · rw [if_pos hv] at h
      cases h
    · rw [if_neg hv] at h
      obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rows, hr, h⟩ := Option.bind_eq_some_iff.mp h
      have hr' : (Array.range s.b.ni).mapM
          (fun i => (Array.range s.b.ny).mapM (elemOfP S val Fx s A i)) = some rows := hr
      rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hr'
      obtain ⟨Lr, hL, eL⟩ := Option.map_eq_some_iff.mp hr'
      refine ⟨A, Lr, hA, hL, ?_⟩
      rw [← Option.some.inj h, ← eL, Array.toList_flatMap]
      rfl
  obtain ⟨Az, Lz, hAz, hLz, ez⟩ := open_ valz Fz hhz e bz hz
  have hc := fun t (h : t < N) => open_ (valt t) (Ft t) (hht t) (shs t) (bt t) (ht t h)
  classical
  let At : ℕ → ℕ → ℕ → Option Aff := fun t => if h : t < N then (hc t h).choose else Az
  let Lt : ℕ → List (Array Trip) := fun t =>
    if h : t < N then (hc t h).choose_spec.choose else []
  have hAt : ∀ t, t < N → (s.at (shs t)).A = some (At t) := fun t h => by
    have := (hc t h).choose_spec.choose_spec.1
    simpa only [At, dif_pos h] using this
  have hLt : ∀ t, t < N → (List.range s.b.ni).mapM
      (fun i => (Array.range s.b.ny).mapM (elemOfP S (valt t) (Ft t) s (At t) i)) =
        some (Lt t) := fun t h => by
    have := (hc t h).choose_spec.choose_spec.2.1
    simpa only [At, Lt, dif_pos h] using this
  have et : ∀ t, t < N → (bt t).toList = (Lt t).flatMap Array.toList := fun t h => by
    have := (hc t h).choose_spec.choose_spec.2.2
    simpa only [Lt, dif_pos h] using this
  unfold ixOf
  rw [if_neg (by rw [htri]; exact Bool.false_ne_true), ez]
  refine (LinAt.mapM Array.toList
    (fun i => (Array.range s.b.ny).mapM (elemOfP S valz Fz s Az i))
    (fun t i => (Array.range s.b.ny).mapM (elemOfP S (valt t) (Ft t) s (At t) i))
    (fun i => (List.range s.b.ny).map fun yv => s.fA.map fun f => f i yv) (List.range s.b.ni)
    (fun i _ rz rt hrz hrt => ?_) Lz Lt hLz hLt).congr et
  -- one row
  have sz : rz.size = s.b.ny := amapM_range_size _ hrz
  refine ⟨fun t h => by
      rw [Array.length_toList, Array.length_toList, sz, amapM_range_size _ (hrt t h)],
    by rw [List.length_map, List.length_range, Array.length_toList, sz], fun yv hyv => ?_⟩
  have hyv' : yv < s.b.ny := by
    rw [Array.length_toList, sz] at hyv
    exact hyv
  have gz := amapM_range_get _ hrz hyv' trip0
  have gt := fun t (h : t < N) => amapM_range_get _ (hrt t h) hyv' trip0
  have tl : ∀ a : Array Trip, a.toList.getD yv trip0 = a.getD yv trip0 := fun a => by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [tl, getD_map_range _ _ _ hyv']
  refine TripLin.congr (xs := fun t => (rt t).getD yv trip0) ?_ fun t _ => tl _
  exact elem_lin K s i yv hAz hAt gz gt

/-- **One panel.** -/
theorem tripsOf_lin (K : Kinds N q valz valt Fz Ft hhz hht) (s : SymBlk)
    (hpl : s.b.tri = true → ∀ v0, s.b.v0 = some v0 → ∀ t, t < N →
      (Ft t).getD v0 #[] = Fz.getD v0 #[])
    (bz : Array Trip) (bt : ℕ → Array Trip)
    (hz : tripsOf S valz Fz hhz (s.at e) = some bz)
    (ht : ∀ t, t < N → tripsOf S (valt t) (Ft t) (hht t) (s.at (shs t)) = some (bt t)) :
    LinAt N q e shs bz.toList (fun t => (bt t).toList) (ixOf s) := by
  cases htri : s.b.tri with
  | true => exact tri_lin K s htri (hpl htri) bz bt hz ht
  | false => exact plain_lin K s htri bz bt hz ht

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.amapM_range_get
#print axioms ProofFile.Honest.K4.amapM_range_size
#print axioms ProofFile.Honest.K4.getD_map_range
#print axioms ProofFile.Honest.K4.LinAt.ofRange
#print axioms ProofFile.Honest.K4.sl_at_some
#print axioms ProofFile.Honest.K4.sl_at_none
#print axioms ProofFile.Honest.K4.tri_lin
#print axioms ProofFile.Honest.K4.elem_lin
#print axioms ProofFile.Honest.K4.plain_lin
#print axioms ProofFile.Honest.K4.tripsOf_lin
