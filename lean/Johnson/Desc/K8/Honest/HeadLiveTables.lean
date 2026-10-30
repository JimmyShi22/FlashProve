-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/HeadLiveTables.lean: the proofs of the three statements of
Johnson/Desc/K8/Honest/HeadLiveTablesStatement.lean, to the letter, and two helpers. Lemmas; none of
the library's goals.

How. `longPhiNe`: `longPhi` is `blockRows` of two tables of equality weights, by its text; entry r *
2 ^ lt + i of it is the product of their entries r and i, as words (`OnBytes.Road.blockRows_getD`,
Johnson/Road/FormsKeysPoint.lean); neither reads as 0 (`eqTab_ne`,
Johnson/Desc/K8/Honest/PlanesLiveOf.lean, at the point's two stretches). `phiPNe`: `Fo.phiP_val`
(OnBytes/Tie/Pv/Lookup/Forest/FoPhi.lean). `tableAdded_has`, `tablesAdded_has`: each ask lays, for
each of its parts, a table with the ask's matrix, length and weights on the third vector; that what
lay in the list stays: the library's `LinkJoin.fold_mem`
(Johnson/Desc/First/Link/Law/TabsBelowOfPos.lean). That the tail has the length asked: the library's
`tail_size` (Johnson/Desc/Reads/LensAt.lean). The title: the routine is opened as `tables_tree`
opens it (Johnson/Desc/First/K8/LawCondText.lean); five of the fifteen asks are taken by their
numbers 0, 2, 5, 8, 14.

NEAR. `tableAdded_has` AND `tablesAdded_has` HAVE THE SHAPE OF THE LIBRARY's `tableAdded_tree` AND
`tablesAdded_tree` (LawCondText.lean), with a richer end.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K8.Honest.HeadLiveTablesStatement
import Johnson.Desc.K8.Honest.DigitsLiveOf
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.Reads.LensAt
import Johnson.Desc.First.Link.Law.TabsBelowOfPos
import Johnson.Road.FormsKeysPoint
import OnBytes.Tie.Pv.Lookup.Forest.FoPhi
import Cb.Pv.Head.NormGl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.Own (tableAdded)
open VerifiableInference.Desc.K8.ReadsQuiet (bind_ok need_ok named_ok)

/-- **No entry of a block's weights reads as 0.** -/
theorem longPhiNe : LongPhiNe := by
  intro Z ls lt hs hf j hj
  have sa : (Z.extract 0 ls).size = ls := by
    rw [Array.size_extract]
    omega
  have sb : (Z.extract ls (ls + lt)).size = lt := by
    rw [Array.size_extract]
    omega
  have ta : (eqTab (Z.extract 0 ls)).size = 2 ^ ls := by rw [OnBytes.Road.eqTab_size, sa]
  have tb : (eqTab (Z.extract ls (ls + lt))).size = 2 ^ lt := by rw [OnBytes.Road.eqTab_size, sb]
  have hpos : 0 < 2 ^ lt := Nat.two_pow_pos lt
  obtain ⟨r, i, hr, hi, rfl⟩ : ∃ r i, r < 2 ^ ls ∧ i < 2 ^ lt ∧ j = r * 2 ^ lt + i :=
    ⟨j / 2 ^ lt, j % 2 ^ lt,
      (Nat.div_lt_iff_lt_mul hpos).2 (by rw [← Nat.pow_add]; exact hj), Nat.mod_lt _ hpos,
      (Nat.div_add_mod' j (2 ^ lt)).symm⟩
  have e := OnBytes.Road.blockRows_getD (eqTab (Z.extract 0 ls))
    (eqTab (Z.extract ls (ls + lt))) (r := r) (i := i) (by rw [ta]; exact hr)
    (by rw [tb]; exact hi)
  rw [tb] at e
  show Reading.gl.val ((blockRows (eqTab (Z.extract 0 ls))
    (eqTab (Z.extract ls (ls + lt)))).getD (r * 2 ^ lt + i) zeroE) ≠ 0
  rw [e, Reading.gl.mul]
  exact mul_ne_zero
    (eqTab_ne _ (fun w hw => hf w (mem_extract _ _ _ _ hw)) r (by rw [sa]; exact hr))
    (eqTab_ne _ (fun w hw => hf w (mem_extract _ _ _ _ hw)) i (by rw [sb]; exact hi))

/-- **No entry of the pin's weights reads as 0.** -/
theorem phiPNe : PhiPNe := by
  intro lm j hj
  rw [Fo.phiP_val Reading.gl lm j hj]
  exact pow_ne_zero _ Cb.Pv.Head.gl_two_ne_zero

/-- One table more: each part has its table. -/
theorem tableAdded_has (mats : Array TMat) (t t' : Head.Tables) (M0 parts Lf : Nat)
    (phi : Array E) (nm : String) (e : tableAdded mats t M0 parts Lf phi nm = some t') :
    ∀ q, q < parts → ∃ Fn ∈ t'.funs.toList,
      Fn.mat = M0 + q ∧ Fn.len = Lf ∧ Fn.phi = phi ∧ Fn.tree = 2 := by
  have key : ∀ (l : List Nat) (s : Array HFun × Nat),
      (∀ Fn ∈ s.1.toList, Fn ∈ (l.foldl (fun (s : Array HFun × Nat) q =>
        (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).1.toList) ∧
      ∀ q ∈ l, ∃ Fn ∈ (l.foldl (fun (s : Array HFun × Nat) q =>
        (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).1.toList,
        Fn.mat = M0 + q ∧ Fn.len = Lf ∧ Fn.phi = phi ∧ Fn.tree = 2 := by
    intro l
    induction l with
    | nil => exact fun s => ⟨fun _ h => h, fun q hq => absurd hq List.not_mem_nil⟩
    | cons a l ih =>
      intro s
      obtain ⟨k1, k2⟩ := ih
        (s.1.push { mat := M0 + a, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + a) {}).k * ((mats.getD (M0 + a) {}).m / Lf))
      refine ⟨fun Fn hFn => k1 Fn ?_, fun q hq => ?_⟩
      · show Fn ∈ (s.1.push _).toList
        rw [Array.toList_push]
        exact List.mem_append_left _ hFn
      · rcases List.mem_cons.1 hq with rfl | hq
        · refine ⟨_, k1 { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 } ?_,
            rfl, rfl, rfl, rfl⟩
          show _ ∈ (s.1.push _).toList
          rw [Array.toList_push]
          exact List.mem_append_right _ List.mem_cons_self
        · exact k2 q hq
  unfold tableAdded at e
  simp only at e
  split at e
  · exact nomatch e
  · obtain rfl := Option.some.inj e
    exact fun q hq => (key (List.range parts) (t.funs, t.p)).2 q (List.mem_range.2 hq)

/-- A run of such steps: the like for every ask of the list. -/
theorem tablesAdded_has (mats : Array TMat) :
    ∀ (asks : List (Nat × Nat × Nat × Array E × String)) (t t' : Head.Tables),
      asks.foldlM (fun t a => tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t =
        some t' →
      ∀ a ∈ asks, ∀ q, q < a.2.1 →
        ∃ Fn ∈ t'.funs.toList,
          Fn.mat = a.1 + q ∧ Fn.len = a.2.2.1 ∧ Fn.phi = a.2.2.2.1 ∧ Fn.tree = 2
  | [], _, _, _ => fun a ha => absurd ha List.not_mem_nil
  | b :: l, t, t', e => by
    rw [List.foldlM_cons] at e
    cases h1 : tableAdded mats t b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2 with
    | none =>
      rw [h1] at e
      exact nomatch e
    | some t1 =>
      rw [h1] at e
      intro a ha q hq
      rcases List.mem_cons.1 ha with rfl | ha
      · obtain ⟨Fn, hFn, hh⟩ := tableAdded_has mats t t1 _ _ _ _ _ h1 q hq
        exact ⟨Fn, VerifiableInference.Desc.LinkJoin.fold_mem mats l t1 t' e Fn hFn, hh⟩
      · exact tablesAdded_has mats l t1 t' e a ha q hq

/-- **Each of the head's matrices has a table none of whose weights reads as 0.** -/
theorem head_liveTables : HeadLiveTables := by
  intro h L hp cov x t tl e hfun hmat fZl fZV ftH ftV sZl stH stV hT d0 d1 d2 d3 d4 mu hmu
  unfold VerifiableInference.Desc.K8.ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨ZV, eZV, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, e4, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  obtain ⟨t', e9, e⟩ := bind_ok e
  obtain ⟨_, _, e⟩ := bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  have hla : h.la = h.ls + h.lt :=
    beq_iff_eq.1 (Bool.and_eq_true_iff.1 (need_ok e4)).2
  have eZ := named_ok eZV
  have sZV : ZV.size = h.ls + h.lt := (VerifiableInference.Reads.AtSeat.tail_size eZ).trans hla
  have H := tablesAdded_has _ _ {} t' (named_ok e9)
  have hTp : 0 < h.T := by
    rw [hT]
    exact Nat.two_pow_pos _
  by_cases c0 : mu < h.NHf
  · obtain ⟨Fn, hFn, e1, e2, e3, e4'⟩ :=
      H _ (List.mem_of_getElem? (i := 0) rfl) mu c0
    have e1' : Fn.mat = 0 + mu := e1
    have e2' : Fn.len = 2 ^ h.la := e2
    have e3' : Fn.phi = longPhi x.Zl h.ls h.lt := e3
    refine ⟨Fn, ?_⟩
    unfold LiveTable
    refine ⟨by rw [hfun]; exact hFn, by omega, Or.inr e4', ?_, ?_, fun j hj => ?_⟩
    · rw [e2']
      exact Nat.two_pow_pos _
    · rw [hmat, e2']
      exact d0 mu c0
    · rw [e2', hla] at hj
      rw [e3']
      exact longPhiNe x.Zl h.ls h.lt sZl fZl j hj
  · obtain rfl | rfl | rfl | rfl :
        mu = h.NHf ∨ mu = h.NHf + 1 ∨ mu = h.NHf + 2 ∨ mu = h.NHf + 3 := by omega
    · obtain ⟨Fn, hFn, e1, e2, e3, e4'⟩ :=
        H _ (List.mem_of_getElem? (i := 5) rfl) 0 Nat.one_pos
      have e1' : Fn.mat = h.NHf + 0 := e1
      have e2' : Fn.len = h.T := e2
      have e3' : Fn.phi = eqTab x.tH.r := e3
      refine ⟨Fn, ?_⟩
      unfold LiveTable
      refine ⟨by rw [hfun]; exact hFn, by omega, Or.inr e4', ?_, ?_, fun j hj => ?_⟩
      · rw [e2']
        exact hTp
      · rw [hmat, e2']
        exact d1
      · rw [e2', hT] at hj
        rw [e3']
        exact eqTab_ne _ ftH j (by rw [stH]; exact hj)
    · obtain ⟨Fn, hFn, e1, e2, e3, e4'⟩ :=
        H _ (List.mem_of_getElem? (i := 8) rfl) 0 Nat.one_pos
      have e1' : Fn.mat = h.NHf + 1 + 0 := e1
      have e2' : Fn.len = h.T := e2
      have e3' : Fn.phi = eqTab x.tV.r := e3
      refine ⟨Fn, ?_⟩
      unfold LiveTable
      refine ⟨by rw [hfun]; exact hFn, by omega, Or.inr e4', ?_, ?_, fun j hj => ?_⟩
      · rw [e2']
        exact hTp
      · rw [hmat, e2']
        exact d2
      · rw [e2', hT] at hj
        rw [e3']
        exact eqTab_ne _ ftV j (by rw [stV]; exact hj)
    · obtain ⟨Fn, hFn, e1, e2, e3, e4'⟩ :=
        H _ (List.mem_of_getElem? (i := 14) rfl) 0 Nat.one_pos
      have e1' : Fn.mat = h.NHf + 1 + 1 + 0 := e1
      have e2' : Fn.len = 2 ^ h.lmbH := e2
      have e3' : Fn.phi = Forest.phiP h.lmbH := e3
      refine ⟨Fn, ?_⟩
      unfold LiveTable
      refine ⟨by rw [hfun]; exact hFn, by omega, Or.inr e4', ?_, ?_, fun j hj => ?_⟩
      · rw [e2']
        exact Nat.two_pow_pos _
      · rw [hmat, e2']
        exact d3
      · rw [e2'] at hj
        rw [e3']
        exact phiPNe h.lmbH j hj
    · obtain ⟨Fn, hFn, e1, e2, e3, e4'⟩ :=
        H _ (List.mem_of_getElem? (i := 2) rfl) 0 Nat.one_pos
      have e1' : Fn.mat = h.NHf + 1 + 1 + 1 + 0 := e1
      have e2' : Fn.len = 2 ^ h.la := e2
      have e3' : Fn.phi = longPhi ZV h.ls h.lt := e3
      refine ⟨Fn, ?_⟩
      unfold LiveTable
      refine ⟨by rw [hfun]; exact hFn, by omega, Or.inr e4', ?_, ?_, fun j hj => ?_⟩
      · rw [e2']
        exact Nat.two_pow_pos _
      · rw [hmat, e2']
        exact d4
      · rw [e2', hla] at hj
        rw [e3']
        exact longPhiNe ZV h.ls h.lt sZV (fZV ZV eZ) j hj

end VerifiableInference.Desc.First.K8.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms VerifiableInference.Desc.First.K8.Honest.longPhiNe
#print axioms VerifiableInference.Desc.First.K8.Honest.phiPNe
#print axioms VerifiableInference.Desc.First.K8.Honest.tableAdded_has
#print axioms VerifiableInference.Desc.First.K8.Honest.tablesAdded_has
#print axioms VerifiableInference.Desc.First.K8.Honest.head_liveTables
