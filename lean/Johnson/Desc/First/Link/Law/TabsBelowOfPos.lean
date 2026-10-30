-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TabsBelowOfPos.lean: EVERY ENTRY OF THE HEAD's TABLE OF TABLES ENDS AT
OR BELOW THE WIDTH OF THE ARRAY OF THE VECTOR OF READS: FROM THE CLOSED SENTENCE `PosPlan`
(PosAtBatch.lean). Counting along the text's own fold. Statements and proofs.

The text that makes the head's tables (`tables`, Johnson/Desc/K8/ReadsQuiet.lean) folds fifteen asks
by `Own.tableAdded`: each ask pushes one table a part and lays one entry (name, first entry, length)
into the table of tables. `PosPlan` speaks of the pushed tables; `TabsBelow`
(Johnson/Desc/Kinds/Law/K6RunsRow0.lean) of the entries of the table of tables.

  `EndsIn mats NM C Fn`: `PosPlan`'s clause at one table, at the width C.
  `parts_mem`, `parts_below`: the parts of one ask: what was pushed stays; if the next free entry
    was at most C, every matrix's number is below NM and every table of the outcome has `EndsIn`,
    the next free entry is at most C still.
  `added_mem`, `added_below`; `fold_mem`, `fold_below`: so one ask, and a list of asks: the next
    free entry and every entry of the table of tables end at or below C.
  `tables_below_of`: **tables h L hp cov x = .ok tt; NM = h.NHf + 4; every table of tt has EndsIn
    hp.tl.mats NM C ⊢ ∀ y ∈ tt.tab, y.2.1 + y.2.2 ≤ C.**
  `endsIn_of_pos`: `PosPlan tl Fp (shapesOf funs)` gives `EndsIn tl.mats tl.NM ‹the width›` of every
    table of funs.
Limits. Nothing on the weights. That the tables lie apart is not said. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.PosAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Head (Shape HL HPlanH2 Tables Covered Heard)
open OnBytes.Tie.Pv.Tail.Port (colsU)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (need named)

/-- `PosPlan`'s clause at one table, at the width C. -/
def EndsIn (mats : Array TMat) (NM C : ℕ) (Fn : HFun) : Prop :=
  Fn.mat < NM → 0 < (mats.getD Fn.mat {}).m / Fn.len → 0 < (mats.getD Fn.mat {}).k →
    Fn.start + (mats.getD Fn.mat {}).k * ((mats.getD Fn.mat {}).m / Fn.len) ≤ C

/-- The step of the parts' fold. -/
def partStep (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) (s : Array HFun × ℕ) (q : ℕ) :
    Array HFun × ℕ :=
  (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
    s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))

theorem parts_mem (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) :
    ∀ (l : List ℕ) (s : Array HFun × ℕ) (x : HFun), x ∈ s.1.toList →
      x ∈ (l.foldl (partStep mats M0 Lf phi) s).1.toList
  | [], _, _, h => h
  | q :: l, s, x, h => by
    rw [List.foldl_cons]
    refine parts_mem mats M0 Lf phi l _ x ?_
    show x ∈ (s.1.push _).toList
    rw [Array.toList_push]
    exact List.mem_append_left _ h

theorem parts_below (mats : Array TMat) (NM C M0 Lf : ℕ) (phi : Array E) :
    ∀ (l : List ℕ) (s : Array HFun × ℕ), s.2 ≤ C → (∀ q ∈ l, M0 + q < NM) →
      (∀ Fn ∈ (l.foldl (partStep mats M0 Lf phi) s).1.toList, EndsIn mats NM C Fn) →
      (l.foldl (partStep mats M0 Lf phi) s).2 ≤ C
  | [], _, h, _, _ => h
  | q :: l, s, h, hM, hE => by
    rw [List.foldl_cons] at hE ⊢
    refine parts_below mats NM C M0 Lf phi l _ ?_ (fun r hr => hM r (List.mem_cons_of_mem _ hr)) hE
    show s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf) ≤ C
    have hmem : ({ mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 } : HFun) ∈
        (l.foldl (partStep mats M0 Lf phi) (partStep mats M0 Lf phi s q)).1.toList := by
      refine parts_mem mats M0 Lf phi l _ _ ?_
      show _ ∈ (s.1.push _).toList
      rw [Array.toList_push]
      exact List.mem_append_right _ (List.mem_singleton.2 rfl)
    have K := hE _ hmem (hM q List.mem_cons_self)
    rcases Nat.eq_zero_or_pos ((mats.getD (M0 + q) {}).m / Lf) with z | p1
    · rw [z, Nat.mul_zero]
      exact h
    · rcases Nat.eq_zero_or_pos (mats.getD (M0 + q) {}).k with z | p2
      · rw [z, Nat.zero_mul]
        exact h
      · exact K p1 p2

/-- What `tableAdded` returns, in the step's letters. -/
theorem added_is {mats : Array TMat} {t u : Tables} {M0 parts Lf : ℕ} {phi : Array E}
    {nm : String} (h : Own.tableAdded mats t M0 parts Lf phi nm = some u) :
    u.funs = ((List.range parts).foldl (partStep mats M0 Lf phi) (t.funs, t.p)).1 ∧
      u.p = ((List.range parts).foldl (partStep mats M0 Lf phi) (t.funs, t.p)).2 ∧
      u.tab = t.tab ++ [(nm, t.p, u.p - t.p)] := by
  unfold Own.tableAdded at h
  dsimp only at h
  split at h
  · exact nomatch h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩

theorem added_mem {mats : Array TMat} {t u : Tables} {M0 parts Lf : ℕ} {phi : Array E}
    {nm : String} (h : Own.tableAdded mats t M0 parts Lf phi nm = some u) {x : HFun}
    (hx : x ∈ t.funs.toList) : x ∈ u.funs.toList := by
  rw [(added_is h).1]
  exact parts_mem mats M0 Lf phi _ _ x hx

/-- The state of the fold ends at or below C. -/
def Below (C : ℕ) (t : Tables) : Prop := t.p ≤ C ∧ ∀ y ∈ t.tab, y.2.1 + y.2.2 ≤ C

theorem added_below {mats : Array TMat} {NM C : ℕ} {t u : Tables} {M0 parts Lf : ℕ}
    {phi : Array E} {nm : String} (h : Own.tableAdded mats t M0 parts Lf phi nm = some u)
    (hB : Below C t) (hM : M0 + parts ≤ NM) (hE : ∀ Fn ∈ u.funs.toList, EndsIn mats NM C Fn) :
    Below C u := by
  obtain ⟨e1, e2, e3⟩ := added_is h
  have hp : u.p ≤ C := by
    rw [e2]
    refine parts_below mats NM C M0 Lf phi _ _ hB.1 (fun q hq => ?_) (by rw [← e1]; exact hE)
    have := List.mem_range.1 hq
    omega
  refine ⟨hp, fun y hy => ?_⟩
  rw [e3] at hy
  rcases List.mem_append.1 hy with k | k
  · exact hB.2 y k
  · obtain rfl := List.mem_singleton.1 k
    show t.p + (u.p - t.p) ≤ C
    have := hB.1
    omega

theorem fold_mem (mats : Array TMat) :
    ∀ (asks : List (ℕ × ℕ × ℕ × Array E × String)) (t u : Tables),
      asks.foldlM (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t =
        some u → ∀ x ∈ t.funs.toList, x ∈ u.funs.toList
  | [], t, u, h, x, hx => by
    obtain rfl := Option.some.inj h
    exact hx
  | a :: asks, t, u, h, x, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact fold_mem mats asks m u h2 x (added_mem h1 hx)

theorem fold_below (mats : Array TMat) (NM C : ℕ) :
    ∀ (asks : List (ℕ × ℕ × ℕ × Array E × String)) (t u : Tables),
      asks.foldlM (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t =
        some u → Below C t → (∀ a ∈ asks, a.1 + a.2.1 ≤ NM) →
      (∀ Fn ∈ u.funs.toList, EndsIn mats NM C Fn) → Below C u
  | [], t, u, h, hB, _, _ => by
    obtain rfl := Option.some.inj h
    exact hB
  | a :: asks, t, u, h, hB, hM, hE => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact fold_below mats NM C asks m u h2
      (added_below h1 hB (hM a List.mem_cons_self)
        fun Fn hFn => hE Fn (fold_mem mats asks m u h2 Fn hFn))
      (fun b hb => hM b (List.mem_cons_of_mem _ hb)) hE

/-- **THE TEXT's TABLE OF TABLES ENDS AT OR BELOW C.** -/
theorem tables_below_of (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard)
    (tt : Tables) (e : K8.ReadsQuiet.tables h L hp cov x = .ok tt) {NM C : ℕ}
    (hNM : NM = h.NHf + 4) (hE : ∀ Fn ∈ tt.funs.toList, EndsIn hp.tl.mats NM C Fn) :
    ∀ y ∈ tt.tab, y.2.1 + y.2.2 ≤ C := by
  unfold K8.ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := K9L.ok_bind e
  obtain ⟨ZV, _, e⟩ := K9L.ok_bind e
  obtain ⟨lowN, _, e⟩ := K9L.ok_bind e
  obtain ⟨_, _, e⟩ := K9L.ok_bind e
  dsimp only at e
  obtain ⟨qFC, _, e⟩ := K9L.ok_bind e
  obtain ⟨qROW, _, e⟩ := K9L.ok_bind e
  obtain ⟨b0, _, e⟩ := K9L.ok_bind e
  obtain ⟨b1, _, e⟩ := K9L.ok_bind e
  obtain ⟨t, ht, e⟩ := K9L.ok_bind e
  obtain ⟨_, _, e⟩ := K9L.ok_bind e
  obtain rfl := Except.ok.inj e
  refine (fold_below hp.tl.mats NM C _ {} t (named_some ht)
    ⟨Nat.zero_le _, fun _ hh => by simp at hh⟩ (fun a ha => ?_) hE).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> (dsimp only; omega)

/-- `PosPlan` at the skeleton of a list of tables gives `EndsIn` of each. -/
theorem endsIn_of_pos {tl : HTailF2} {Fp : Fork} {funs : Array HFun}
    (H : PosPlan tl Fp (shapesOf funs)) :
    ∀ Fn ∈ funs.toList,
      EndsIn tl.mats tl.NM (colsU Fp ((tl.ix.U.getD 2 none).getD 0)) Fn := by
  intro Fn hFn
  exact H ⟨Fn.mat, Fn.len, Fn.start⟩ (by
    unfold shapesOf
    exact List.mem_map.2 ⟨Fn, hFn, rfl⟩)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.parts_mem
#print axioms VerifiableInference.Desc.LinkJoin.parts_below
#print axioms VerifiableInference.Desc.LinkJoin.added_is
#print axioms VerifiableInference.Desc.LinkJoin.added_mem
#print axioms VerifiableInference.Desc.LinkJoin.added_below
#print axioms VerifiableInference.Desc.LinkJoin.fold_mem
#print axioms VerifiableInference.Desc.LinkJoin.fold_below
#print axioms VerifiableInference.Desc.LinkJoin.tables_below_of
#print axioms VerifiableInference.Desc.LinkJoin.endsIn_of_pos
