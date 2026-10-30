-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/WalkCols.lean: a walk's columns and tables, for a whole chain.
Where a chain's walk (Honest/Walk.lean) returns, two things hold. Three hypotheses beside that: the
`Lay`'s look-up of a tree is that of `envOf` (`hL`); the `Step`s' declared rounds are the chain's
(`hl`); each round declares as many oracle messages as its entry counts roots (`ho`; `tables_sentC`
takes this one alone). The columns that it has filled, one sub-protocol after another, each from the
tables produced by then, are what `fillCols` (Honest/Frame.lean) returns for the whole chain's reads
at the tables produced at the end (`walk_cols`). And every table produced, real or substitute, has
the length and the width that its round declares (`tables_sentC`). So what Honest/Law/StratRun.lean
does with a run of `run` can be done with a run of `runC`.

  1  `tree_mono`   an available table stays available (under `hL`)
  2  `ChainProgress.ColsTied`, `settle_colsT`, `heard_colsT`, `walk_colsT`, `start_colsT`   an invariant
  3  `walk_cols`   a chain's end
  4  `say_tabs`, `tables_sentC`   the tables produced

Limits.
  * The lemmas on `ChainProgress.start` are general in its fifth argument `front`, the earlier chains'
    columns that this chain's parts are handed; no end reads it. `z.cols` holds the chain's own
    columns alone; no lemma here reads the field `opened`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.WalkReads
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Law.StratPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W Y : Type}

/-! ## 1 An available table stays available -/

theorem tree_mono {L : Lay} {taken : Nat → Nat → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (ps qs : List Played)
    (s : Fmt.TreeSource) (pt : Place × Table) (h : L.tree ps s = some pt) :
    L.tree (ps ++ qs) s = some pt := by
  rw [hL] at h ⊢
  have e1 : envOf L.stored taken ps = (envOf L.stored taken []).add ps := by
    rw [envOf_add, List.nil_append]
  have e2 : envOf L.stored taken (ps ++ qs) = (envOf L.stored taken []).add (ps ++ qs) := by
    rw [envOf_add, List.nil_append]
  rw [e1] at h
  rw [e2]
  exact Env.add_prefix _ ps qs s pt h

/-! ## 2 An invariant -/

/-- `bs`: the chain's whole list. `todo`: the sub-protocols not yet asked. The columns filled are
what `fillCols` returns for the reads of the sub-protocols asked so far, at the tables produced so
far. -/
def ChainProgress.ColsTied (L : Lay) (bs todo : List (Block S Cl)) (z : ChainProgress S Cl W Y) : Prop :=
  ∃ (done : List (Block S Cl)) (front : List Played), bs = done ++ todo ∧
    z.laid = front ++ z.own ∧ front.length = (done.flatMap (·.rounds)).length ∧
    fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid) (done.flatMap (·.rounds))
      (front.map (·.drawn))) [] = .ok z.cols

section
variable {L : Lay} {taken : Nat → Nat → Option (Place × Table)}
  (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree)
include hL

omit hL in
theorem settle_colsT (bs : List (Block S Cl)) :
    ∀ (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y), ChainProgress.ColsTied L bs todo z →
    (∀ b t, todo = b :: t → z.own.length ≤ b.rounds.length) → ChainProgress.settle L todo z = .ok z' →
    ChainProgress.ColsTied L bs z'.todo z' ∧ z'.Waits
  | [], z, z', h, _, hs => by
    simp only [ChainProgress.settle] at hs
    cases hs
    exact ⟨h, fun b t e => (by cases e)⟩
  | b :: t, z, z', h, ho, hs => by
    by_cases hlt : z.own.length < b.rounds.length
    · rw [settle_wait L b t z hlt] at hs
      cases hs
      refine ⟨h, fun b' t' e => ?_⟩
      have e' : b :: t = b' :: t' := e
      cases e'
      exact hlt
    · have hn : z.own.length = b.rounds.length :=
        Nat.le_antisymm (ho b t rfl) (Nat.le_of_not_lt hlt)
      obtain ⟨cols, hc, hs'⟩ := settle_ask_ok hlt hs
      obtain ⟨done, front, h1, h2, h3, h4⟩ := h
      refine settle_colsT bs t _ z' ?_ ?_ hs'
      · refine ⟨done ++ [b], front ++ z.own, ?_, ?_, ?_, ?_⟩
        · rw [h1, List.append_assoc]
          rfl
        · show z.laid = front ++ z.own ++ []
          rw [List.append_nil, h2]
        · rw [List.length_append, List.flatMap_append, List.length_append, h3, hn]
          simp
        · show fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid)
            ((done ++ [b]).flatMap (·.rounds)) ((front ++ z.own).map (·.drawn))) [] =
              .ok (z.cols ++ cols)
          have e : [b].flatMap (·.rounds) = b.rounds := by simp
          rw [List.flatMap_append, e, List.map_append,
            readsOf_append _ _ _ _ _ _ _ _ (by rw [List.length_map, h3]), fillCols_append, h4]
          show (fillCols _ (([] : List OpenedColumn).drop _)).map _ = _
          rw [List.drop_nil, hc]
          rfl
      · intro _ _ _
        exact Nat.zero_le _

theorem heard_colsT (bs : List (Block S Cl)) {z z' : ChainProgress S Cl W Y} {s : Step W Y}
    {x : Told} {d : Fmt.Drawn} (h : ChainProgress.ColsTied L bs z.todo z) (ho : z.Waits)
    (hz : z.heard L s x d = .ok z') : ChainProgress.ColsTied L bs z'.todo z' ∧ z'.Waits := by
  obtain ⟨m', -, hs⟩ := heard_ok hz
  obtain ⟨done, front, h1, h2, h3, h4⟩ := h
  refine settle_colsT bs z.todo _ z' ?_ ?_ hs
  · refine ⟨done, front, h1, ?_, h3, ?_⟩
    · show z.laid ++ [_] = front ++ (z.own ++ [_])
      rw [h2, List.append_assoc]
    · show fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ [_]))
        (done.flatMap (·.rounds)) (front.map (·.drawn))) [] = .ok z.cols
      exact fillCols_mono (fun u pt hu => tree_mono hL z.laid _ u pt hu) _ _ _ h4
  · intro b t e
    show (z.own ++ [_]).length ≤ b.rounds.length
    rw [List.length_append]
    exact ho b t e

theorem walk_colsT (bs : List (Block S Cl)) : ∀ (ss : List (Step W Y))
    (ds : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y), ChainProgress.ColsTied L bs z.todo z → z.Waits →
    walk L ss ds z = .ok z' → ChainProgress.ColsTied L bs z'.todo z' ∧ z'.Waits
  | [], [], z, z', h, ho, hw => by
    rw [walk_nil_ok hw]
    exact ⟨h, ho⟩
  | [], _ :: _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _, [], _, _, _, _, hw => by simp [walk] at hw
  | s :: ss, d :: ds, z, z', h, ho, hw => by
    obtain ⟨x, z₁, -, hz₁, hw₁⟩ := walk_cons_ok hw
    obtain ⟨a1, a2⟩ := heard_colsT hL bs h ho hz₁
    exact walk_colsT bs ss ds z₁ z' a1 a2 hw₁

omit hL in
theorem start_colsT (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a : ChainProgress S Cl W Y} {front : List OpenedColumn} (h : ChainProgress.start L bs m v front = .ok a) :
    ChainProgress.ColsTied L bs a.todo a ∧ a.Waits := by
  unfold ChainProgress.start at h
  refine settle_colsT bs bs _ a ?_ ?_ h
  · exact ⟨[], [], rfl, rfl, rfl, rfl⟩
  · intro _ _ _
    exact Nat.zero_le _

/-! ## 3 A chain's end -/

/-- **A chain's columns are what `fillCols` returns for the whole chain's reads, at the tables
produced at the end.** -/
theorem walk_cols (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hl : ss.map (·.decl) = bs.flatMap (·.rounds))
    (ho : ∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) :
    fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid) (bs.flatMap (·.rounds)) ds)
      [] = .ok z.cols := by
  obtain ⟨a1, a2⟩ := start_colsT bs m v ha
  obtain ⟨⟨done, front, h1, h2, h3, h4⟩, b2⟩ := walk_colsT hL bs ss ds a z a1 a2 hz
  obtain ⟨-, e2⟩ := reads_bare L bs m v ha hz hl ho
  have hlenL : z.laid.length = (ss.zip ds).length := by
    have e := congrArg List.length e2
    rw [List.length_map, List.length_map] at e
    exact e
  have hdr : z.laid.map (·.drawn) = (ss.zip ds).map (·.2) := by
    have e := congrArg (List.map (·.2.2.2)) e2
    rw [List.map_map, List.map_map] at e
    exact e
  have hsd : ds.length = ss.length := by
    have key : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn) (u u' : ChainProgress S Cl W Y),
        walk L l d u = .ok u' → d.length = l.length := by
      intro l
      induction l with
      | nil =>
        intro d u u' hw
        cases d with
        | nil => rfl
        | cons _ _ => simp [walk] at hw
      | cons s l ih =>
        intro d u u' hw
        cases d with
        | nil => simp [walk] at hw
        | cons d₀ d =>
          obtain ⟨_, u₁, -, -, hw₁⟩ := walk_cons_ok hw
          exact congrArg (· + 1) (ih d u₁ u' hw₁)
    exact key ss ds a z hz
  rw [List.map_snd_zip (Nat.le_of_eq hsd)] at hdr
  rw [List.length_zip, hsd, Nat.min_self] at hlenL
  have hl' : ss.length = (bs.flatMap (·.rounds)).length := by rw [← hl, List.length_map]
  have hcount : front.length + z.own.length =
      (done.flatMap (·.rounds)).length + (z.todo.flatMap (·.rounds)).length := by
    rw [← List.length_append, ← h2, hlenL, hl', h1, List.flatMap_append, List.length_append]
  have htodo : z.todo = [] := by
    cases ht : z.todo with
    | nil => rfl
    | cons b t =>
      have h6 := b2 b t ht
      rw [ht, List.flatMap_cons, List.length_append] at hcount
      omega
  rw [htodo] at hcount h1
  have hown : z.own = [] := List.eq_nil_of_length_eq_zero (by
    rw [List.flatMap_nil, List.length_nil] at hcount
    omega)
  rw [List.append_nil] at h1
  rw [hown, List.append_nil] at h2
  subst h1
  rw [← h2, hdr] at h4
  exact h4

end

/-! ## 4 The tables produced -/

/-- A table that a round sends has the numbers that the round declares. -/
theorem say_tabs {z : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} (h : z.say s = .ok x) :
    ∀ (n : Nat) (t : Table), x.tables[n]? = some (some t) →
      (s.oracles.map fun o => (o.logLength, o.words))[n]? = some (t.logLength, t.words) := by
  rw [say_eq] at h
  cases hm : z.mid with
  | some m =>
    rw [hm] at h
    have h' : s.tell none m = .ok x := h
    obtain ⟨-, h1, h2⟩ := tell_yields h'
    cases hmv : s.move.isSome with
    | true =>
      obtain ⟨u, hu, -, ht⟩ := h1 hmv
      simp only [Sending.fits, Bool.and_eq_true, beq_iff_eq] at hu
      intro n t hn
      rw [ht, List.getElem?_map] at hn
      rw [← hu.2, List.getElem?_map]
      cases hu' : u.tables[n]? with
      | none =>
        rw [hu'] at hn
        cases hn
      | some t' =>
        rw [hu'] at hn
        cases hn
        rfl
    | false =>
      obtain ⟨-, ht⟩ := h2 hmv
      intro n t hn
      rw [ht] at hn
      have h4 := List.mem_of_getElem? hn
      have h5 := (List.mem_replicate.1 h4).2
      cases h5
  | none =>
    rw [hm] at h
    have h' : (Except.ok (subTold s.decl s.oracles) : Except Refusal Told) = .ok x := h
    cases h'
    intro n t hn
    have hn' : ((s.oracles.map substituteZeroTable).map some)[n]? = some (some t) := hn
    rw [List.getElem?_map, List.getElem?_map] at hn'
    rw [List.getElem?_map]
    cases ho' : s.oracles[n]? with
    | none =>
      rw [ho'] at hn'
      cases hn'
    | some o =>
      rw [ho'] at hn'
      cases hn'
      rfl

/-- **Every table produced, real or substitute, has the numbers that its round declares**; and as
many are produced as are declared. -/
theorem tables_sentC (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y) (ps : List Played), walk L ss ds z = .ok z' → z'.laid = z.laid ++ ps →
    (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    (tablesOf ps).length = (ss.flatMap (·.oracles)).length ∧
    ∀ (n : Nat) (pt : Place × Table), ((tablesOf ps)[n]?).bind id = some pt →
      ((ss.flatMap (·.oracles)).map fun o => (o.logLength, o.words))[n]? =
        some (pt.2.logLength, pt.2.words)
  | [], [], z, z', ps, h, e, _ => by
    rw [walk_nil_ok h] at e
    have e' : ps = [] := List.self_eq_append_right.1 e
    subst e'
    exact ⟨rfl, fun n pt hn => by simp [tablesOf] at hn⟩
  | [], _ :: _, _, _, _, h, _, _ => by simp [walk] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [walk] at h
  | s :: ss, d :: ds, z, z', ps, h, e, ho => by
    obtain ⟨x, z₁, hx, hz, hw⟩ := walk_cons_ok h
    obtain ⟨qs, e1, -⟩ := walk_laid L ss ds z₁ z' hw
      fun s' hs' => ho s' (List.mem_cons_of_mem _ hs')
    have e2 : ps = ⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩ :: qs := by
      rw [e1, heard_laid hz, List.append_assoc] at e
      exact (List.append_cancel_left e).symm
    subst e2
    obtain ⟨ih1, ih2⟩ := tables_sentC L ss ds z₁ z' qs hw e1
      fun s' hs' => ho s' (List.mem_cons_of_mem _ hs')
    have hl := say_tables hx (ho s List.mem_cons_self)
    have ht := say_tabs hx
    refine ⟨?_, ?_⟩
    · rw [tablesOf_cons, List.length_append, List.length_map, List.flatMap_cons,
        List.length_append, ih1]
      show x.tables.length + _ = _
      rw [hl]
    · intro n pt hn
      rw [List.flatMap_cons, List.map_append]
      rw [tablesOf_cons] at hn
      have hn' : (((x.tables.map fun t => t.map fun u => (s.addr.place, u)) ++
          tablesOf qs)[n]?).bind id = some pt := hn
      by_cases hlt : n < x.tables.length
      · rw [List.getElem?_append_left (by rw [List.length_map]; exact hlt),
          List.getElem?_map] at hn'
        rw [List.getElem?_append_left (by rw [List.length_map, ← hl]; exact hlt)]
        cases hp : x.tables[n]? with
        | none =>
          rw [hp] at hn'
          cases hn'
        | some o =>
          rw [hp] at hn'
          cases o with
          | none => cases hn'
          | some t =>
            cases hn'
            exact ht n t hp
      · have hge : x.tables.length ≤ n := Nat.le_of_not_lt hlt
        rw [List.getElem?_append_right (by rw [List.length_map]; exact hge),
          List.length_map] at hn'
        rw [List.getElem?_append_right (by rw [List.length_map, ← hl]; exact hge),
          List.length_map, ← hl]
        exact ih2 _ pt hn'

end ProofFile.Honest

#print axioms ProofFile.Honest.tree_mono
#print axioms ProofFile.Honest.settle_colsT
#print axioms ProofFile.Honest.heard_colsT
#print axioms ProofFile.Honest.walk_colsT
#print axioms ProofFile.Honest.start_colsT
#print axioms ProofFile.Honest.walk_cols
#print axioms ProofFile.Honest.say_tabs
#print axioms ProofFile.Honest.tables_sentC
#print axioms ProofFile.Honest.ChainProgress.ColsTied
