-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/OpenLaws.lean: the proximity test (the kind K12): how many groups of columns each
part is handed, for all parts and all numbers of a place: the trees that the declared rounds of a
part's slice open. Theorems, and the definitions that state them.

  listsOf N      the lists of trees that the rounds' maker lays in, in order: at the first switch
                 the trees of the test's group (with the first fold's own mask, if it sends one); at
                 each later switch, and at the base case, one tree.
  Dealt cur rest L l   what holds of the rounds l still to be dealt at a stage: no round opens a
                 stored table; the rounds that open trees are each stage's last, and they open the
                 lists L in order.
  listsOf_length, listsOf_tail   there are as many lists as stages; every list but the first names
                 one tree.
  open_top       where the block's test on the plan says yes: the batching is handed no group, and
                 the rounds behind it are `Dealt` at the first stage with `listsOf`.
  open_step      at a stage that is not the last: the fold is handed no group; the switch as many as
                 the first list has trees; what is handed on is `Dealt` at the next stage with the
                 lists behind.
  open_last      at the last stage the base case is handed as many groups as the first list has
                 trees.
Beside the lengths of the slices (the kind's files' law), these say which slice of the groups a
part's decision is shown. Nothing on what a part decides. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open Fmt.M1 (Stage)

variable {T Cl : Type}

/-- A tree as a round's declaration names it. -/
abbrev Told : Type := Fmt.Shape × Fmt.TreeSource

/-- The lists of trees laid at the rounds that open one (false), none at the others (true). -/
def fill : List Bool → List (List Told) → List (List Told)
  | [], _ => []
  | true :: bs, L => [] :: fill bs L
  | false :: bs, x :: L => x :: fill bs L
  | false :: bs, [] => [] :: fill bs []

/-- Which of the rounds from a stage on open no tree. -/
def quiet : Stage → List Stage → List Bool
  | _, [] => [true, false]
  | cur, next :: rest => List.replicate (1 + cur.k) true ++ [true, false] ++ quiet next rest

theorem fill_true (n : Nat) (bs : List Bool) (L : List (List Told)) :
    fill (List.replicate n true ++ bs) L = List.replicate n [] ++ fill bs L := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, fill, ih]

theorem layOpens_shape (own : Bool) (rs : List Fmt.Round) :
    ∀ (seen : Bool) (L : List (List Told)) (ds : List Fmt.DeclaredRound),
      H2U.layOpens own seen rs L = some ds →
        ds.map (·.opens) = fill (rs.map (·.opens.isEmpty)) L ∧ ∀ d ∈ ds, d.stored = [] := by
  induction rs with
  | nil =>
    intro seen L ds h
    cases L with
    | nil => simp [H2U.layOpens] at h; subst h; simp [fill]
    | cons x t => simp [H2U.layOpens] at h
  | cons r rs ih =>
    intro seen L ds h
    simp only [H2U.layOpens] at h
    split at h
    · rename_i he
      cases hq : H2U.layOpens own (seen || r.entry.name == "FOLD epsilon") rs L with
      | none => simp [hq] at h
      | some a =>
        simp [hq] at h
        obtain ⟨h1, h2⟩ := ih _ _ _ hq
        subst h
        refine ⟨by simp [fill, he, h1], ?_⟩
        intro d hd
        cases hd with
        | head => rfl
        | tail _ hd => exact h2 d hd
    · rename_i he
      split at h
      · rename_i x t
        split at h
        · simp at h
        · cases hq : H2U.layOpens own (seen || r.entry.name == "FOLD epsilon") rs t with
          | none => simp [hq] at h
          | some a =>
            simp [hq] at h
            obtain ⟨h1, h2⟩ := ih _ _ _ hq
            subst h
            refine ⟨by simp [fill, he, h1], ?_⟩
            intro d hd
            cases hd with
            | head => rfl
            | tail _ hd => exact h2 d hd
      · simp at h

theorem laterRounds_quiet (work : Nat) (rest : List Stage) :
    ∀ (tree W : Nat) (old : Stage),
      (Fmt.M1.laterRounds work tree W old rest).map (·.opens.isEmpty) = quiet old rest := by
  induction rest with
  | nil => intro tree W old; simp [Fmt.M1.laterRounds, Fmt.M1.rLambda, Fmt.M1.rBase, quiet]
  | cons new rest ih =>
    intro tree W old
    simp [Fmt.M1.laterRounds, Fmt.M1.rEps, Fmt.M1.rTwo, Fmt.M1.rSeed, Fmt.M1.rCs, quiet, ih,
      Nat.add_comm 1, List.replicate_succ]

/-- The lists of trees that the rounds' maker lays in. -/
def listsOf (N : H2U.TestNums) : List (List Told) :=
  let told := N.sent.zipIdx.map fun t => N.own t.1.1 t.1.2 (N.free + t.2)
  (N.first ++ (if N.ownMask then told.take 1 else [])) ::
    (if N.ownMask then told.drop 1 else told).map ([·])

/-- What holds of the rounds still to be dealt at a stage. -/
structure Dealt (cur : Stage) (rest : List Stage) (L : List (List Told)) (l : Laid) : Prop where
  opens : l.map (·.1.opens) = fill (quiet cur rest) L
  stored : ∀ y ∈ l, y.1.stored = []

/-- The groups of a part at rounds that open no stored table: the trees that these rounds open. -/
theorem at_openings (x : Part T) (name : String) (place : Place) (l : Laid)
    (hs : ∀ y ∈ l, y.1.stored = []) :
    (x.at name place l : Block T Cl).openings = ((l.map (·.1.opens)).map (·.length)).sum := by
  have gen : ∀ (l : Laid) (a : Nat), (∀ y ∈ l, y.1.stored = []) →
      (l.map (·.1)).foldl (fun n r => n + r.stored.length + r.opens.length) a =
        a + ((l.map (·.1.opens)).map (·.length)).sum := by
    intro l
    induction l with
    | nil => intro a _; simp
    | cons y l ih =>
      intro a h
      have hy : y.1.stored = [] := h y (by simp)
      simp only [List.map_cons, List.foldl_cons, List.sum_cons, hy, List.length_nil]
      rw [ih _ fun z hz => h z (by simp [hz])]
      omega
  simpa [Block.openings, Part.at] using gen l 0 hs

/-- At a stage that is not the last, the rounds still to be dealt open: nothing in the fold's
rounds, nothing in the switch's first, the first list in its second; then as the next stage says. -/
theorem Dealt.cons {cur next : Stage} {rest : List Stage} {x : List Told} {L : List (List Told)}
    {l : Laid} (h : Dealt cur (next :: rest) (x :: L) l) :
    l.map (·.1.opens) =
      List.replicate (1 + cur.k) [] ++ ([] :: x :: fill (quiet next rest) L) := by
  rw [h.opens]
  simp [quiet, fill_true, fill]

/-- **A stage that is not the last.** -/
theorem open_step (X : Parts T) (p : P12) (j : Nat) (cur next : Stage) (rest : List Stage)
    (x : List Told) (L : List (List Told)) (l : Laid) (h : Dealt cur (next :: rest) (x :: L) l) :
    (foldAt X p j cur l : Block T Cl).openings = 0 ∧
      (switchAt X p j cur next rest.isEmpty l : Block T Cl).openings = x.length ∧
      Dealt next rest L (l.drop (cur.k + 3)) := by
  have ho := h.cons
  have hn : (List.replicate (1 + cur.k) ([] : List Told)).length = 1 + cur.k := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold foldAt
    rw [at_openings _ _ _ _ fun y hy => h.stored y (List.mem_of_mem_take hy), List.map_take, ho,
      List.take_left' hn]
    simp
  · unfold switchAt
    rw [at_openings _ _ _ _ fun y hy =>
      h.stored y (List.mem_of_mem_drop (List.mem_of_mem_take hy)), List.map_take, List.map_drop,
      ho, List.drop_left' hn]
    simp
  · have e : cur.k + 3 = (1 + cur.k) + 2 := by omega
    rw [List.map_drop, ho, e, ← List.drop_drop, List.drop_left' hn]
    simp
  · exact fun y hy => h.stored y (List.mem_of_mem_drop hy)

/-- **The last stage.** -/
theorem open_last (X : Parts T) (p : P12) (j : Nat) (cur : Stage) (x : List Told)
    (L : List (List Told)) (l : Laid) (h : Dealt cur [] (x :: L) l) :
    (stagesFrom X p j cur [] l : Block T Cl).openings = x.length := by
  simp only [stagesFrom]
  rw [at_openings _ _ _ _ h.stored, h.opens]
  simp [quiet, fill]

/-- The maker's rounds, with the lists under their name. -/
theorem roundsOfNums_eq (N : H2U.TestNums) (s next : Stage) (rest : List Stage)
    (hs : N.stages = s :: next :: rest) :
    H2U.roundsOfNums N = H2U.layOpens N.ownMask false
      ({ Fmt.M1.rBat with entry := { Fmt.M1.rBat.entry with rows := N.rows } } ::
        Fmt.M1.laterRounds N.work 0 0 s (next :: rest)) (listsOf N) := by
  simp only [H2U.roundsOfNums, listsOf, hs]

/-- There are as many lists as stages: one for each switch, and one for the base case. -/
theorem listsOf_length (N : H2U.TestNums) (s : Stage) (rest : List Stage)
    (hs : N.stages = s :: rest) : (listsOf N).length = rest.length + 1 := by
  cases hm : N.ownMask <;> simp [listsOf, H2U.TestNums.sent, hs, hm]

/-- Every list but the first names one tree. -/
theorem listsOf_tail (N : H2U.TestNums) : ∀ x ∈ (listsOf N).tail, x.length = 1 := by
  intro x hx
  simp only [listsOf, List.tail_cons, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  rfl

/-- **The top**: from the block's own test on the plan, at any parts. -/
theorem open_top (X : Parts T) (p : P12) (hp : (proximityTestKind X p : Block T Cl).planOk = true) :
    ∃ (first : Stage) (rest : List Stage) (ds : List Fmt.DeclaredRound),
      p.nums.stages = first :: rest ∧ H2U.roundsOfNums p.nums = some ds ∧
      (batAt X p (ds.zip p.oracles) : Block T Cl).openings = 0 ∧
      Dealt first rest (listsOf p.nums) ((ds.zip p.oracles).drop 1) := by
  have hr := k12_rounds X p hp
  have ho := k12_oracles X p hp
  generalize hds : (proximityTestKind X p : Block T Cl).rounds = ds at hr
  have hlen : p.oracles.length = ds.length := by
    have hsh : (proximityTestKind X p : Block T Cl).planOk = true := hp
    unfold proximityTestKind at hsh
    split at hsh
    · rename_i first rest rs os h1 h2 h3
      simp only [Bool.and_eq_true, beq_iff_eq] at hsh
      have : rs = ds := Option.some.inj (h2.symm.trans hr)
      rw [← this]
      exact hsh.1.1.2
    · simp at hsh
  have hfst : (ds.zip p.oracles).map (·.1) = ds := List.map_fst_zip (by omega)
  cases hst : p.nums.stages with
  | nil => simp [H2U.roundsOfNums, hst] at hr
  | cons s more =>
    cases more with
    | nil => simp [H2U.roundsOfNums, hst] at hr
    | cons next rest =>
      rw [roundsOfNums_eq _ _ _ _ hst] at hr
      obtain ⟨h1, h2⟩ := layOpens_shape _ _ _ _ _ hr
      have hop : (ds.zip p.oracles).map (·.1.opens) =
          [] :: fill (quiet s (next :: rest)) (listsOf p.nums) := by
        have : (ds.zip p.oracles).map (·.1.opens) =
            ((ds.zip p.oracles).map (·.1)).map (·.opens) := by
          simp [List.map_map]
        rw [this, hfst, h1]
        simp [fill, laterRounds_quiet, Fmt.M1.rBat]
      have hsto : ∀ y ∈ ds.zip p.oracles, y.1.stored = [] := fun y hy =>
        h2 y.1 (by rw [← hfst]; exact List.mem_map_of_mem hy)
      refine ⟨s, next :: rest, ds, rfl, by rw [roundsOfNums_eq _ _ _ _ hst]; exact hr, ?_, ?_, ?_⟩
      · unfold batAt
        rw [at_openings _ _ _ _ fun y hy => hsto y (List.mem_of_mem_take hy), List.map_take, hop]
        simp
      · rw [List.map_drop, hop]
        simp
      · exact fun y hy => hsto y (List.mem_of_mem_drop hy)

end VerifiableInference.Desc.K12
