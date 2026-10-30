-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/RowsClasses.lean: code switching (the kind K2): EACH ROW THAT A SWITCH LAYS
LIES IN ONE OF TWO STRETCHES OF ITS GROUP's LIST: «carried» (the carried claim, then the kept
members' stored samples restated) from place 0, «position» (the generators' rows) behind it. NO
BLOCK IMPORTS THIS FILE. Why. The table of joints reads a class of rows off the verifier's state
as «(List.range n).filterMap fun j => G.rows[a + j]?», (a, n) := Numbers.rowsAt m c (classRows, in
Johnson/Desc/First/Close/Law/FillRow.lean; not imported here). Here: what these two
expressions are behind a yes of the switch, and how long the first stretch is.
  slice_list        (List.range n).filterMap (fun j => l.toArray[a + j]?) = (l.drop a).take n
  samples_len       the kept members' samples restated are as many as their stored sample rows
  rows_split_more   rows_split (K2C/PositionCount.lean) with the samples' maker named
  keptSamples x W   the number of the stored sample rows of the frame's kept members, read off the
                    statement IN FRONT
  yes_row_kinds     yes_row_classes with three clauses more: the carried claim and
                    the samples restated are plain rows, the generators' rows generator rows
                    (K2C/RowKinds.lean)
  yes_row_classes   AT A YES (AtYes), where the front's group has no
                    row yet, under KeptPos x.T: there are carried, samples, gens and the group G'
                    behind with: G'.rows = (carried :: samples ++ gens).toArray · rows = carried
                    :: samples ++ gens · the stretch (0, 1 + samples.length) of G'.rows is carried
                    :: samples · the stretch (1 + samples.length, gens.length) is gens ·
                    samples.length = keptSamples x W at the front's frame W · gens.length = the
                    draws × (1 + targetRows x.T + 2)
LEFT, BY NAME: that each kept member has just one stored sample row (then samples.length =
x.T.kept.size: the table's «one row a kept copy») · KeptPos x.T · «the front's group has no row
yet»: frontAt_fresh | finish_fresh (K2C/PositionAtPlan.lean); at the head's link a public clause
on the state. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.PositionAtPlan
import Johnson.Top.H0.Tw.K2C.RowKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model

theorem slice_list {α : Type} (l : List α) (a : Nat) : ∀ n : Nat, a + n ≤ l.length →
    (List.range n).filterMap (fun j => l.toArray[a + j]?) = (l.drop a).take n
  | 0, _ => by simp
  | n + 1, h => by
    have hlt : a + n < l.length := by omega
    rw [List.range_succ, List.filterMap_append, slice_list l a n (by omega)]
    simp only [List.filterMap_cons, List.filterMap_nil, List.getElem?_toArray,
      List.getElem?_eq_getElem hlt]
    rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem hlt]
    rfl

theorem flatten_sum {α : Type} : ∀ L : List (List α), L.flatten.length = (L.map (·.length)).sum
  | [] => rfl
  | l :: L => by
    rw [List.flatten_cons, List.length_append, flatten_sum L, List.map_cons, List.sum_cons]

/-- An Option's mapM, member by member. -/
theorem mapM_map_len {α β : Type} (f : α → Option β) (g : β → Nat) (k : α → Nat)
    (hk : ∀ a b, f a = some b → g b = k a) : ∀ (l : List α) (r : List β), l.mapM f = some r →
    r.map g = l.map k
  | [], r, h => by
    have : r = [] := by simpa using h.symm
    subst this
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, r', hr, rfl⟩ := h
    rw [List.map_cons, List.map_cons, hk a b hb, mapM_map_len f g k hk l r' hr]

theorem samples_len {S : Statement} {W : SwitchFrame} {samples : List OnBytes.Row}
    (h : switchOldSamples S W = some samples) :
    samples.length = (W.kept.map fun k => (S.oracles.getD k.old default).sampleRows.size).sum := by
  unfold switchOldSamples at h
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [flatten_sum]
  refine congrArg List.sum (mapM_map_len _ _ _ (fun k b hb => ?_) _ _ hL)
  have := (mapM_len _ _ _ hb).1
  simpa using this

theorem rows_split_more {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {pos : Positions} {y : Array E} {rows : List OnBytes.Row}
    (h : switchRows S old T g anew pos y = some rows) :
    ∃ (W : SwitchFrame) (carried : OnBytes.Row) (samples : List OnBytes.Row)
      (gens : List (List OnBytes.Row)), switchFrame S old T g anew = some W ∧
      switchCarried W old = some carried ∧ switchOldSamples S W = some samples ∧
      rows = carried :: samples ++ gens.flatten ∧ gens.length = pos.draws.size ∧
      ∀ l ∈ gens, ∃ q sy, l = switchGenerators W old q sy := by
  unfold switchRows at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, W, hW, carried, hc, samples, hs, gens, hg, rfl⟩ := h
  obtain ⟨k1, k2⟩ := mapM_len _ _ _ hg
  refine ⟨W, carried, samples, gens, hW, hc, hs, rfl, by simpa using k1, fun l hl => ?_⟩
  obtain ⟨q, _, e⟩ := k2 l hl
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at e
  obtain ⟨i, _, rfl⟩ := e
  exact ⟨q, _, rfl⟩

/-- The stored sample rows of the frame's kept members, counted at the statement in front. -/
def keptSamples (x : _root_.Tw.K2.Front) (W : SwitchFrame) : Nat :=
  (W.kept.map fun k => (x.st.oracles.getD k.old default).sampleRows.size).sum

/-- **At a yes: the two stretches, with the rows' kinds.** -/
theorem yes_row_kinds {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hp : KeptPos x.T) (hf : G.rows = #[]) :
    ∃ (W : SwitchFrame) (carried : OnBytes.Row) (samples gens : List OnBytes.Row) (G' : Group),
      frameAt x = some W ∧ s'.st.groups[x.f.group]? = some G' ∧
      G'.rows = (carried :: samples ++ gens).toArray ∧ rows = carried :: samples ++ gens ∧
      (List.range (1 + samples.length)).filterMap (fun j => G'.rows[0 + j]?) =
        carried :: samples ∧
      (List.range gens.length).filterMap (fun j => G'.rows[1 + samples.length + j]?) = gens ∧
      samples.length = keptSamples x W ∧
      gens.length = r₂.drawn.poss.length * (1 + targetRows x.T + 2) ∧
      carried.kind = .plain ∧ (∀ r ∈ samples, r.kind = .plain) ∧
      ∀ r ∈ gens, r.kind = .generator := by
  obtain ⟨W, carried, samples, gens, hW, hc, hs, rfl, hl, hg⟩ := rows_split_more A.made
  rw [frame_of_front A] at hW
  have hK := keptOld_of A.check hp
  obtain ⟨G', hG', eR⟩ := Option.map_eq_some_iff.1 A.kept
  have eR' : G'.rows = (carried :: samples ++ gens.flatten).toArray := by
    rw [eR, hf]
    simp
  refine ⟨W, carried, samples, gens.flatten, G', hW, hG', eR', rfl, ?_, ?_, ?_, ?_,
    carried_kind hc, fun r hr => ?_, fun r hr => ?_⟩
  · rw [eR', slice_list _ 0 _ (by simp; omega)]
    simp [Nat.add_comm 1]
  · rw [eR', slice_list _ _ _ (by simp; omega)]
    have e : (carried :: samples ++ gens.flatten).drop (1 + samples.length) = gens.flatten := by
      rw [show carried :: samples ++ gens.flatten = (carried :: samples) ++ gens.flatten from rfl]
      exact List.drop_left' (by simp; omega)
    rw [e, List.take_length]
  · rw [samples_len hs]
    unfold keptSamples
    refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
    have hold : k.old < x.st.oracles.size := by
      unfold frameAt switchFrame at hW
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hW
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hW
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      have hi' : i < (switchKept x.f.rows).size := List.mem_range.1 hi
      show (switchKept x.f.rows).getD i noId < _
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
      exact hK _ (by simp)
    have e1 := A.same.samples k.old
    rw [A.sent.old k.old hold] at e1
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
    cases h3 : S3.oracles[k.old]? with
    | none =>
      cases h0 : x.st.oracles[k.old]? with
      | none => rfl
      | some b =>
        rw [h3, h0] at e1
        cases e1
    | some a =>
      cases h0 : x.st.oracles[k.old]? with
      | none =>
        rw [h3, h0] at e1
        cases e1
      | some b =>
        rw [h3, h0] at e1
        exact congrArg Array.size (Option.some.inj e1)
  · rw [flatten_len (1 + targetRows x.T + 2) gens fun l hm => by
      obtain ⟨q, sy, rfl⟩ := hg l hm
      exact gens_count hW A.check hK q sy, hl]
    simp [Positions.ofDraws]
  · obtain ⟨_, rfl⟩ :=
      (VerifiableInference.Desc.First.K2Hands.switchOldSamples_iff S3 W samples).1 hs
    obtain ⟨k, _, h⟩ := List.mem_flatMap.1 hr
    obtain ⟨smp, _, rfl⟩ := List.mem_map.1 h
    exact sampleRow_kind W k smp
  · obtain ⟨l, hl', hrl⟩ := List.mem_flatten.1 hr
    obtain ⟨q, sy, rfl⟩ := hg l hl'
    exact gens_kind W _ q sy r hrl

/-- **At a yes: the two stretches.** -/
theorem yes_row_classes {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hp : KeptPos x.T) (hf : G.rows = #[]) :
    ∃ (W : SwitchFrame) (carried : OnBytes.Row) (samples gens : List OnBytes.Row) (G' : Group),
      frameAt x = some W ∧ s'.st.groups[x.f.group]? = some G' ∧
      G'.rows = (carried :: samples ++ gens).toArray ∧ rows = carried :: samples ++ gens ∧
      (List.range (1 + samples.length)).filterMap (fun j => G'.rows[0 + j]?) =
        carried :: samples ∧
      (List.range gens.length).filterMap (fun j => G'.rows[1 + samples.length + j]?) = gens ∧
      samples.length = keptSamples x W ∧
      gens.length = r₂.drawn.poss.length * (1 + targetRows x.T + 2) := by
  obtain ⟨W, carried, samples, gens, G', h1, h2, h3, h4, h5, h6, h7, h8, _⟩ :=
    yes_row_kinds A hp hf
  exact ⟨W, carried, samples, gens, G', h1, h2, h3, h4, h5, h6, h7, h8⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.slice_list
#print axioms VerifiableInference.Desc.First.K2.samples_len
#print axioms VerifiableInference.Desc.First.K2.yes_row_kinds
#print axioms VerifiableInference.Desc.First.K2.yes_row_classes
