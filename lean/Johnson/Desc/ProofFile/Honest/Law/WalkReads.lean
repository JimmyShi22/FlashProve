-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/WalkReads.lean: what a walk (Honest/Walk.lean) reads is determined
by the plan and the challenges; what it produces is compared with the `Step`s. Where a chain's walk
returns, two things hold. Two hypotheses beside that: the `Step`s' declared rounds are the chain's,
and each round declares as many oracle messages as its entry counts roots; `runC_bare` takes the
second at the three chains' `Step`s that `ready` has returned. Its reads, without their words and
their sender, are those of `readsOf` (Honest/Frame.lean) at the chain's declared rounds and the
challenges, with no table supplied. And the rounds that it has produced, reduced to place, part,
number of tables and challenge, are the `Step`s zipped with the challenges, for real rounds and
substitutes alike. The main lemmas are `reads_bare` for a chain and `runC_bare` for a file.
`Run.askedAt` and `Run.drawnAt` (Honest/Side.lean) read of a read its source and position alone, and
of a produced round its place, part, number of tables and challenge alone. What follows for them is
stated in no theorem of this file.

  1  `say_tables`, `walk_laid`   the rounds produced
  2  `ChainProgress.ReadsTied`, `ChainProgress.Waits`, `settle_reads`, `heard_reads`, `walk_reads`, `start_reads`   an
     invariant
  3  `reads_bare`   a chain's end
  4  `runC_bare`   the file

It uses `Read.bare` and `readsOf_bare` (Honest/Law/Rule/Bare.lean): a read without its words and
sender.

Limits.
  * The lemmas on `ChainProgress.start` are general in its fifth argument `front`, the earlier chains'
    columns that this chain's parts are handed; no end reads it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.WalkOn
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.Rule.Bare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi W Y W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The rounds produced -/

theorem say_tables {z : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} (h : z.say s = .ok x)
    (ho : s.oracles.length = s.decl.entry.roots) : x.tables.length = s.oracles.length := by
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
      have e := congrArg List.length hu.2
      rw [List.length_map, List.length_map] at e
      rw [ht, List.length_map, e]
    | false =>
      obtain ⟨-, ht⟩ := h2 hmv
      rw [ht, List.length_replicate, ho]
  | none =>
    rw [hm] at h
    have h' : (Except.ok (subTold s.decl s.oracles) : Except Refusal Told) = .ok x := h
    cases h'
    show ((s.oracles.map substituteZeroTable).map some).length = _
    rw [List.length_map, List.length_map]

/-- **The rounds produced**, real rounds and substitutes alike. -/
theorem walk_laid (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' →
    (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    ∃ ps, z'.laid = z.laid ++ ps ∧
      ps.map (fun p => (p.place, p.part, p.tables.length, p.drawn)) =
        (ss.zip ds).map fun u => (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)
  | [], [], z, z', h, _ => by
    rw [walk_nil_ok h]
    exact ⟨[], (List.append_nil _).symm, rfl⟩
  | [], _ :: _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, h, _ => by simp [walk] at h
  | s :: ss, d :: ds, z, z', h, ho => by
    obtain ⟨x, z₁, hx, hz, hw⟩ := walk_cons_ok h
    obtain ⟨ps, e1, e2⟩ := walk_laid L ss ds z₁ z' hw
      fun s' hs' => ho s' (List.mem_cons_of_mem _ hs')
    refine ⟨⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩ :: ps, ?_, ?_⟩
    · rw [e1, heard_laid hz, List.append_assoc]
      rfl
    · rw [List.map_cons, e2, List.zip_cons_cons, List.map_cons]
      show (s.addr.place, s.addr.part, x.tables.length, d) :: _ = _
      rw [say_tables hx (ho s List.mem_cons_self)]

/-! ## 2 An invariant -/

/-- `bs`: the chain's whole list. `todo`: the sub-protocols not yet asked. The walk's reads are,
except for words and sender, those of the sub-protocols asked so far at the challenges of the rounds
produced for them. -/
def ChainProgress.ReadsTied (L : Lay) (bs todo : List (Block S Cl)) (z : ChainProgress S Cl W Y) : Prop :=
  ∃ (done : List (Block S Cl)) (front : List Played), bs = done ++ todo ∧
    z.laid = front ++ z.own ∧ front.length = (done.flatMap (·.rounds)).length ∧
    z.reads.map Read.bare =
      readsOf L.chain L.firstTree (fun _ _ => none) (fun _ => none) (done.flatMap (·.rounds))
        (front.map (·.drawn))

/-- The sub-protocol that is being played still lacks a round; or none is left. (The same condition
as `ChainProgress.Open`, Honest/Law/WalkFold.lean.) -/
def ChainProgress.Waits (z : ChainProgress S Cl W Y) : Prop :=
  ∀ b t, z.todo = b :: t → z.own.length < b.rounds.length

theorem settle_reads (L : Lay) (bs : List (Block S Cl)) :
    ∀ (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y), ChainProgress.ReadsTied L bs todo z →
    (∀ b t, todo = b :: t → z.own.length ≤ b.rounds.length) → ChainProgress.settle L todo z = .ok z' →
    ChainProgress.ReadsTied L bs z'.todo z' ∧ z'.Waits
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
      obtain ⟨cols, -, hs'⟩ := settle_ask_ok hlt hs
      obtain ⟨done, front, h1, h2, h3, h4⟩ := h
      refine settle_reads L bs t _ z' ?_ ?_ hs'
      · refine ⟨done ++ [b], front ++ z.own, ?_, ?_, ?_, ?_⟩
        · rw [h1, List.append_assoc]
          rfl
        · show z.laid = front ++ z.own ++ []
          rw [List.append_nil, h2]
        · rw [List.length_append, List.flatMap_append, List.length_append, h3, hn]
          simp
        · show (z.reads ++ readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds
            (z.own.map (·.drawn))).map Read.bare = _
          have e : [b].flatMap (·.rounds) = b.rounds := by simp
          rw [List.map_append, h4, readsOf_bare, List.flatMap_append, e, List.map_append,
            readsOf_append _ _ _ _ _ _ _ _ (by rw [List.length_map, h3])]
      · intro _ _ _
        exact Nat.zero_le _

theorem heard_reads (L : Lay) (bs : List (Block S Cl)) {z z' : ChainProgress S Cl W Y} {s : Step W Y}
    {x : Told} {d : Fmt.Drawn} (h : ChainProgress.ReadsTied L bs z.todo z) (ho : z.Waits)
    (hz : z.heard L s x d = .ok z') : ChainProgress.ReadsTied L bs z'.todo z' ∧ z'.Waits := by
  obtain ⟨m', -, hs⟩ := heard_ok hz
  obtain ⟨done, front, h1, h2, h3, h4⟩ := h
  refine settle_reads L bs z.todo _ z' ?_ ?_ hs
  · refine ⟨done, front, h1, ?_, h3, h4⟩
    show z.laid ++ [_] = front ++ (z.own ++ [_])
    rw [h2, List.append_assoc]
  · intro b t e
    show (z.own ++ [_]).length ≤ b.rounds.length
    rw [List.length_append]
    exact ho b t e

theorem walk_reads (L : Lay) (bs : List (Block S Cl)) : ∀ (ss : List (Step W Y))
    (ds : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y), ChainProgress.ReadsTied L bs z.todo z → z.Waits →
    walk L ss ds z = .ok z' → ChainProgress.ReadsTied L bs z'.todo z' ∧ z'.Waits
  | [], [], z, z', h, ho, hw => by
    rw [walk_nil_ok hw]
    exact ⟨h, ho⟩
  | [], _ :: _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _, [], _, _, _, _, hw => by simp [walk] at hw
  | s :: ss, d :: ds, z, z', h, ho, hw => by
    obtain ⟨x, z₁, -, hz₁, hw₁⟩ := walk_cons_ok hw
    obtain ⟨a1, a2⟩ := heard_reads L bs h ho hz₁
    exact walk_reads L bs ss ds z₁ z' a1 a2 hw₁

theorem start_reads (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a : ChainProgress S Cl W Y} {front : List OpenedColumn} (h : ChainProgress.start L bs m v front = .ok a) :
    ChainProgress.ReadsTied L bs a.todo a ∧ a.Waits ∧ a.laid = [] := by
  unfold ChainProgress.start at h
  have key : ChainProgress.ReadsTied L bs a.todo a ∧ a.Waits := by
    refine settle_reads L bs bs _ a ?_ ?_ h
    · exact ⟨[], [], rfl, rfl, rfl, rfl⟩
    · intro _ _ _
      exact Nat.zero_le _
  exact ⟨key.1, key.2, settle_laid L bs _ a h⟩

/-! ## 3 A chain's end -/

/-- **A chain's reads, except for words and sender, are determined by its declared rounds and the
challenges alone.** -/
theorem reads_bare (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hl : ss.map (·.decl) = bs.flatMap (·.rounds))
    (ho : ∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) :
    z.reads.map Read.bare =
        readsOf L.chain L.firstTree (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds))
          ds ∧
      z.laid.map (fun p => (p.place, p.part, p.tables.length, p.drawn)) =
        (ss.zip ds).map fun u => (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2) := by
  obtain ⟨a1, a2, a3⟩ := start_reads L bs m v ha
  obtain ⟨⟨done, front, h1, h2, h3, h4⟩, b2⟩ := walk_reads L bs ss ds a z a1 a2 hz
  obtain ⟨ps, e1, e2⟩ := walk_laid L ss ds a z hz ho
  rw [a3, List.nil_append] at e1
  have hsd : ds.length = ss.length := by
    clear e2 h4
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
  have hlen : z.laid.length = ss.length := by
    have e := congrArg List.length e2
    rw [List.length_map, List.length_map, List.length_zip, hsd, Nat.min_self] at e
    rw [e1]
    exact e
  have hl' : ss.length = (bs.flatMap (·.rounds)).length := by rw [← hl, List.length_map]
  have hcount : front.length + z.own.length =
      (done.flatMap (·.rounds)).length + (z.todo.flatMap (·.rounds)).length := by
    rw [← List.length_append, ← h2, hlen, hl', h1, List.flatMap_append, List.length_append]
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
  have hdr : front.map (·.drawn) = ds := by
    rw [← h2, e1]
    have e := congrArg (List.map (·.2.2.2)) e2
    rw [List.map_map, List.map_map] at e
    have e3 : (ss.zip ds).map ((fun u : Place × Nat × Nat × Fmt.Drawn => u.2.2.2) ∘
        fun u : Step W Y × Fmt.Drawn =>
          (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)) = ds :=
      List.map_snd_zip (Nat.le_of_eq hsd)
    exact e.trans e3
  rw [hdr] at h4
  refine ⟨h4, ?_⟩
  rw [e1]
  exact e2

/-! ## 4 The file -/

/-- **What a run of `runC` reads, except for words and sender, is determined by the plan and the
challenges; the rounds that it produces, reduced to place, part, number of tables and challenge, are
the `Step`s that `ready` has returned, zipped with the challenges.** That a `Step`'s place, part and
number of oracle messages do not depend on the input or the coins is not stated here. -/
theorem runC_bare {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {c : Coins B} {ρ : Draws} {r : RunC F} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
    (o₁ : ∀ s ∈ R.first, s.oracles.length = s.decl.entry.roots)
    (o₂ : ∀ s ∈ R.shared, s.oracles.length = s.decl.entry.roots)
    (o₃ : ∀ s ∈ R.second, s.oracles.length = s.decl.entry.roots) :
    (r.run.reads.1.map Read.bare =
        readsOf 0 0 (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.1 ρ.first ∧
      r.run.played.1.map (fun p => (p.place, p.part, p.tables.length, p.drawn)) =
        (R.first.zip ρ.first).map fun u =>
          (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)) ∧
    (r.run.reads.2.1.map Read.bare =
        readsOf 1 0 (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.2.1 ρ.shared ∧
      r.run.played.2.1.map (fun p => (p.place, p.part, p.tables.length, p.drawn)) =
        (R.shared.zip ρ.shared).map fun u =>
          (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)) ∧
    (r.run.reads.2.2.map Read.bare =
        readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.2.2 ρ.second ∧
      r.run.played.2.2.map (fun p => (p.place, p.part, p.tables.length, p.drawn)) =
        (R.second.zip ρ.second).map fun u =>
          (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)) := by
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, -, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  exact ⟨reads_bare _ F.first.blocksInOrder _ _ ha₁ hz₁ (steps_decl s1) o₁,
    reads_bare _ F.shared.blocksInOrder _ _ ha₂ hz₂ (steps_decl s2) o₂,
    reads_bare _ F.second.blocksInOrder _ _ ha₃ hz₃ (steps_decl s3) o₃⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.say_tables
#print axioms ProofFile.Honest.walk_laid
#print axioms ProofFile.Honest.settle_reads
#print axioms ProofFile.Honest.heard_reads
#print axioms ProofFile.Honest.walk_reads
#print axioms ProofFile.Honest.start_reads
#print axioms ProofFile.Honest.reads_bare
#print axioms ProofFile.Honest.runC_bare
#print axioms ProofFile.Honest.ChainProgress.ReadsTied
#print axioms ProofFile.Honest.ChainProgress.Waits
