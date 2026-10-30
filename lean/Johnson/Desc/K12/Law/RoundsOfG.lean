-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RoundsOfG.lean: a declared round is told by what a reader takes of it; and so a
place of a proximity test (the kind K12) whose declared rounds are a stretch of a chain has the very
declared rounds of any place of which readers take that stretch.

Why. WrittenOfG.lean compares two places through what readers take of their declared rounds
(`Fmt.DeclaredRound.round`, Fmt/Parsed.lean). Some tests read the declared rounds themselves: of every
opened tree its shape and its source. This file shows that nothing is lost on the way.
How. A reader keeps a round's entry and each opened tree's shape whole. A source "own n" stays; a
source "taken from chain c, number p" becomes the root and the run value that stand in for it. So
the map is one to one wherever these stand-ins are distinct.
Main names:
  `SrcInj e`: the readers' sources at the stand-ins e tell the declared sources apart.
  `srcInj_nil`: so without an earlier chain: only own trees get through.
  `srcInj_tags`: so at the stand-ins that `Johnson.G.OfPlan.writtenOf` lays for two earlier chains:
    roots of different lengths, two different run values.
  `opens_inj`, `round_inj`, `mapM_round_inj`: the opened trees; a round, given its stored trees; a
    list of rounds without stored trees.
  `layOpens_stored`, `roundsOfNums_stored`: a place's declared rounds have no stored tree.
  `roundsOfNums_at_stretch`: the theorem.
`tagRoot_size` stands also in Johnson/Desc/Sound/Stretch.lean; it is typed again here so that that
file's imports do not stand beneath this one.
Limits: on the makers' texts alone. Both sides are read at one list of stand-ins. Where the stretch
begins, and that a place's declared rounds are a stretch of a chain, are premises. Nothing on
soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.WrittenOfDecl

set_option autoImplicit false
namespace H2K.Pub
open H2U (TestNums roundsOfNums)
open OnBytes.Three (tagRoot tagRun)

/-- The readers' sources tell the declared sources apart. -/
def SrcInj (e : List (List ByteArray × ByteArray)) : Prop :=
  ∀ (d d' : Fmt.TreeSource) (s : Fmt.Src), d.src e = some s → d'.src e = some s → d = d'

theorem src_own (e : List (List ByteArray × ByteArray)) (n : Nat) :
    (Fmt.TreeSource.own n).src e = some (.own n) := rfl

theorem src_taken {e : List (List ByteArray × ByteArray)} {c p : Nat} {s : Fmt.Src}
    (h : (Fmt.TreeSource.taken c p).src e = some s) :
    ∃ x r, e[c]? = some x ∧ x.1[p]? = some r ∧ s = .given r x.2 := by
  unfold Fmt.TreeSource.src at h
  cases h1 : e[c]? with
  | none => simp [h1] at h
  | some x =>
    cases h2 : x.1[p]? with
    | none => simp [h1, h2] at h
    | some r =>
      simp [h1, h2] at h
      exact ⟨x, r, rfl, h2, h.symm⟩

/-- Without an earlier chain only own trees get through. -/
theorem srcInj_nil : SrcInj [] := by
  intro d d' s h h'
  cases d with
  | taken c p =>
    obtain ⟨x, _, hx, _⟩ := src_taken h
    simp at hx
  | own n =>
    cases d' with
    | taken c p =>
      obtain ⟨x, _, hx, _⟩ := src_taken h'
      simp at hx
    | own n' =>
      rw [src_own] at h h'
      cases h
      cases h'
      rfl

theorem tagRoot_size (n : Nat) : (tagRoot n).size = n + 1 := by
  simp [tagRoot, ByteArray.size]

theorem tagRoot_inj {a b : Nat} (h : tagRoot a = tagRoot b) : a = b := by
  have := congrArg ByteArray.size h
  rw [tagRoot_size, tagRoot_size] at this
  omega

/-- The stand-ins of `Johnson.G.OfPlan.writtenOf` for two earlier chains tell all apart. -/
theorem srcInj_tags (a b : Nat) :
    SrcInj [((List.range a).map tagRoot, tagRun 1), ((List.range b).map tagRoot, tagRun 2)] := by
  have key : ∀ (c p : Nat) (x : List ByteArray × ByteArray) (r : ByteArray),
      [((List.range a).map tagRoot, tagRun 1), ((List.range b).map tagRoot, tagRun 2)][c]? =
        some x → x.1[p]? = some r → r = tagRoot p ∧ x.2 = tagRun (c + 1).toUInt8 ∧ c < 2 := by
    intro c p x r hx hr
    match c, hx with
    | 0, hx =>
      cases hx
      simp only [List.getElem?_map] at hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain ⟨_, hq'⟩ := List.getElem?_eq_some_iff.1 hq
      rw [List.getElem_range] at hq'
      exact ⟨by rw [hq'], rfl, by omega⟩
    | 1, hx =>
      cases hx
      simp only [List.getElem?_map] at hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hr
      obtain ⟨_, hq'⟩ := List.getElem?_eq_some_iff.1 hq
      rw [List.getElem_range] at hq'
      exact ⟨by rw [hq'], rfl, by omega⟩
    | c + 2, hx => simp at hx
  intro d d' s h h'
  cases d with
  | own n =>
    cases d' with
    | own n' =>
      rw [src_own] at h h'
      cases h
      cases h'
      rfl
    | taken c p =>
      obtain ⟨_, _, _, _, rfl⟩ := src_taken h'
      rw [src_own] at h
      cases h
  | taken c p =>
    obtain ⟨x, r, hx, hr, rfl⟩ := src_taken h
    cases d' with
    | own n' =>
      rw [src_own] at h'
      cases h'
    | taken c' p' =>
      obtain ⟨x', r', hx', hr', e⟩ := src_taken h'
      obtain ⟨k1, k2, k3⟩ := key c p x r hx hr
      obtain ⟨k1', k2', k3'⟩ := key c' p' x' r' hx' hr'
      injection e with e1 e2
      have hp : p = p' := tagRoot_inj (by rw [← k1, ← k1', e1])
      have hc : c = c' := by
        rw [k2, k2'] at e2
        match c, c', k3, k3', e2 with
        | 0, 0, _, _, _ => rfl
        | 1, 1, _, _, _ => rfl
        | 0, 1, _, _, e2 => exact absurd e2 (by decide)
        | 1, 0, _, _, e2 => exact absurd e2 (by decide)
      rw [hp, hc]

/-- The opened trees, as readers take them, tell the declared ones apart. -/
theorem opens_inj {e : List (List ByteArray × ByteArray)} (he : SrcInj e) :
    ∀ (l l' : List (Fmt.Shape × Fmt.TreeSource)) (os : List (Fmt.Shape × Fmt.Src)),
    (l.mapM fun (o : Fmt.Shape × Fmt.TreeSource) => (o.2.src e).map fun s => (o.1, s)) = some os →
    (l'.mapM fun (o : Fmt.Shape × Fmt.TreeSource) => (o.2.src e).map fun s => (o.1, s)) = some os →
    l = l'
  | [], [], _, _, _ => rfl
  | [], (sh, d) :: l', os, h, h' => by
    rw [List.mapM_nil] at h
    cases h
    rw [List.mapM_cons] at h'
    cases hd : d.src e with
    | none => simp [hd] at h'
    | some s =>
      cases hl : (l'.mapM fun (o : Fmt.Shape × Fmt.TreeSource) =>
          (o.2.src e).map fun s => (o.1, s)) with
      | none => simp [hd, hl] at h'
      | some os' => simp [hd, hl] at h'
  | (sh, d) :: l, [], os, h, h' => by
    rw [List.mapM_nil] at h'
    cases h'
    rw [List.mapM_cons] at h
    cases hd : d.src e with
    | none => simp [hd] at h
    | some s =>
      cases hl : (l.mapM fun (o : Fmt.Shape × Fmt.TreeSource) =>
          (o.2.src e).map fun s => (o.1, s)) with
      | none => simp [hd, hl] at h
      | some os' => simp [hd, hl] at h
  | (sh, d) :: l, (sh', d') :: l', os, h, h' => by
    rw [List.mapM_cons] at h h'
    cases hd : d.src e with
    | none => simp [hd] at h
    | some s =>
      cases hl : (l.mapM fun (o : Fmt.Shape × Fmt.TreeSource) =>
          (o.2.src e).map fun s => (o.1, s)) with
      | none => simp [hd, hl] at h
      | some os1 =>
        cases hd' : d'.src e with
        | none => simp [hd'] at h'
        | some s' =>
          cases hl' : (l'.mapM fun (o : Fmt.Shape × Fmt.TreeSource) =>
              (o.2.src e).map fun s => (o.1, s)) with
          | none => simp [hd', hl'] at h'
          | some os2 =>
            simp [hd, hl] at h
            simp [hd', hl'] at h'
            subst h
            obtain ⟨⟨a1, a2⟩, a3⟩ := List.cons.inj h' |>.imp Prod.mk.inj id
            subst a1 a2 a3
            rw [he d d' _ hd hd', opens_inj he l l' _ hl hl']

/-- **A declared round is told by what a reader takes of it and its stored trees.** -/
theorem round_inj {e : List (List ByteArray × ByteArray)} (he : SrcInj e) {r r' : Fmt.DeclaredRound}
    {x : Fmt.Round} (h : r.round e = some x) (h' : r'.round e = some x)
    (hs : r.stored = r'.stored) : r = r' := by
  unfold Fmt.DeclaredRound.round at h h'
  cases hk : Fmt.kindOf r.entry.name with
  | none => simp [hk] at h
  | some k =>
    cases hk' : Fmt.kindOf r'.entry.name with
    | none => simp [hk'] at h'
    | some k' =>
      cases hl : (r.opens.mapM fun (o : Fmt.Shape × Fmt.TreeSource) =>
          (o.2.src e).map fun s => (o.1, s)) with
      | none => simp [hk, hl] at h
      | some os =>
        cases hl' : (r'.opens.mapM fun (o : Fmt.Shape × Fmt.TreeSource) =>
            (o.2.src e).map fun s => (o.1, s)) with
        | none => simp [hk', hl'] at h'
        | some os' =>
          simp [hk, hl] at h
          simp [hk', hl'] at h'
          subst h
          have e1 : r'.entry = r.entry := congrArg Fmt.Round.entry h'
          have e2 : os' = os := congrArg Fmt.Round.opens h'
          subst e2
          have e3 := opens_inj he _ _ _ hl hl'
          cases r
          cases r'
          simp only at e1 e3 hs
          subst e1 e3 hs
          rfl

/-- The same for lists. -/
theorem mapM_round_inj {e : List (List ByteArray × ByteArray)} (he : SrcInj e) :
    ∀ (ds ds' : List Fmt.DeclaredRound) (xs : List Fmt.Round), ds.mapM (·.round e) = some xs →
    ds'.mapM (·.round e) = some xs → (∀ r ∈ ds, r.stored = []) → (∀ r ∈ ds', r.stored = []) →
    ds = ds'
  | [], [], _, _, _, _, _ => rfl
  | [], r' :: ds', xs, h, h', _, _ => by
    rw [List.mapM_nil] at h
    cases h
    rw [List.mapM_cons] at h'
    cases hr : r'.round e with
    | none => simp [hr] at h'
    | some x =>
      cases hl : ds'.mapM (·.round e) with
      | none => simp [hr, hl] at h'
      | some ys => simp [hr, hl] at h'
  | r :: ds, [], xs, h, h', _, _ => by
    rw [List.mapM_nil] at h'
    cases h'
    rw [List.mapM_cons] at h
    cases hr : r.round e with
    | none => simp [hr] at h
    | some x =>
      cases hl : ds.mapM (·.round e) with
      | none => simp [hr, hl] at h
      | some ys => simp [hr, hl] at h
  | r :: ds, r' :: ds', xs, h, h', s, s' => by
    rw [List.mapM_cons] at h h'
    cases hr : r.round e with
    | none => simp [hr] at h
    | some x =>
      cases hl : ds.mapM (·.round e) with
      | none => simp [hr, hl] at h
      | some ys =>
        cases hr' : r'.round e with
        | none => simp [hr'] at h'
        | some x' =>
          cases hl' : ds'.mapM (·.round e) with
          | none => simp [hr', hl'] at h'
          | some ys' =>
            simp [hr, hl] at h
            simp [hr', hl'] at h'
            subst h
            obtain ⟨a1, a2⟩ := List.cons.inj h'
            subst a1 a2
            rw [round_inj he hr hr' ((s r List.mem_cons_self).trans
                (s' r' List.mem_cons_self).symm),
              mapM_round_inj he ds ds' _ hl hl' (fun q hq => s q (List.mem_cons_of_mem _ hq))
                fun q hq => s' q (List.mem_cons_of_mem _ hq)]

/-- `layOpens` lays no stored tree. -/
theorem layOpens_stored (own : Bool) : ∀ (R : List Fmt.Round) (seen : Bool)
    (X : List (List (Fmt.Shape × Fmt.TreeSource))) (ds : List Fmt.DeclaredRound),
    H2U.layOpens own seen R X = some ds → ∀ r ∈ ds, r.stored = []
  | [], _, [], ds, h => by
    simp only [H2U.layOpens] at h
    cases h
    intro r hr
    cases hr
  | [], _, _ :: _, ds, h => by
    simp only [H2U.layOpens] at h
    cases h
  | q :: rs, seen, X, ds, h => by
    by_cases hq : q.opens.isEmpty = true
    · simp only [H2U.layOpens, hq, if_true] at h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · rfl
      · exact layOpens_stored own rs _ X t ht r hr
    · cases X with
      | nil =>
        simp only [H2U.layOpens, hq] at h
        cases h
      | cons x X' =>
        simp only [H2U.layOpens, hq] at h
        by_cases hx : x.isEmpty = true
        · simp only [hx, if_true] at h
          simp at h
        · simp only [hx] at h
          simp only [Bool.false_eq_true, if_false] at h
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
          intro r hr
          rcases List.mem_cons.1 hr with rfl | hr
          · rfl
          · exact layOpens_stored own rs _ X' t ht r hr

theorem roundsOfNums_stored {N : TestNums} {ds : List Fmt.DeclaredRound}
    (h : roundsOfNums N = some ds) : ∀ r ∈ ds, r.stored = [] := by
  unfold roundsOfNums at h
  cases hs : N.stages with
  | nil =>
    rw [hs] at h
    cases h
  | cons s t =>
    cases t with
    | nil =>
      rw [hs] at h
      cases h
    | cons next rest =>
      rw [hs] at h
      exact layOpens_stored _ _ _ _ _ h

/-- **At a stretch of a chain: the declared rounds themselves.** As `writtenOf_at_stretch`
(WrittenOfG.lean), with one list of stand-ins on both sides, which tells the sources apart. -/
theorem roundsOfNums_at_stretch {N N0 : TestNums} {pre ds post ds0 : List Fmt.DeclaredRound}
    {e : List (List ByteArray × ByteArray)} (he : SrcInj e) {xs : List Fmt.Round}
    (hx : (pre ++ (ds ++ post)).mapM (·.round e) = some xs) (hN : roundsOfNums N = some ds)
    (h0 : roundsOfNums N0 = some ds0)
    (hc : ds0.mapM (·.round e) = some ((xs.drop pre.length).take ds0.length))
    (h2 : N.work = N0.work) (h3 : N.stages = N0.stages) : roundsOfNums N = roundsOfNums N0 := by
  have hl := roundsOfNums_length hN h0 h2 h3
  have hd := mapM_stretch (·.round e) pre ds post xs hx
  rw [hl] at hd
  rw [hN, h0, mapM_round_inj he ds ds0 _ hd hc (roundsOfNums_stored hN) (roundsOfNums_stored h0)]

end H2K.Pub

#print axioms H2K.Pub.srcInj_nil
#print axioms H2K.Pub.srcInj_tags
#print axioms H2K.Pub.round_inj
#print axioms H2K.Pub.mapM_round_inj
#print axioms H2K.Pub.roundsOfNums_at_stretch
