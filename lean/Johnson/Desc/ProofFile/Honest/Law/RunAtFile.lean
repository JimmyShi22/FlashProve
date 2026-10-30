-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunAtFile.lean: a part's share of a run of `runC`
(Honest/Walk.lean), for a whole file. The three lemmas of Honest/Law/RunAt.lean on one chain,
applied to the three chains of such a run. They compute `Run.drawnAt` and `Run.askedAt`
(Honest/Side.lean) at an address, and give one direction for `RunC.called`: if the stretch's first
round is a real round, the part was called.

  1  `steps_chain`, `places_chain`, `off_chain`   no other chain has a round at the address, by the
     description's test `FileDescription.placesOk`
  2  `walk_len`, `runC_laidAs`, `runC_asks`   what Honest/Law/WalkReads.lean gives, in the forms of
     RunAt.lean
  3  `At`, `at_first`, `at_shared`, `at_second`   the three chains' shares at an address of one
     chain
  4  `drawnAt_of`, `askedAt_of`, `called_of`   the three lemmas, at any of the three chains

Limits.
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins):
    `runC_laidAs`, `runC_asks`, `at_first`, `at_shared`, `at_second`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W Y W' Y' W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 No other chain has a round at the address -/

theorem steps_chain {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {bs : List (Block S Cl)} {hs : List (Placed V W Y)} {ss : List (Step W Y)}
    (h : chainSteps B rows look v bs hs = .ok ss) {c : Nat} (hc : ∀ b ∈ bs, b.place.chain = c) :
    ∀ s ∈ ss, s.addr.place.chain = c := by
  intro s hs'
  obtain ⟨-, h2⟩ := chainSteps_rows bs hs ss h
  have h1 : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      ss.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs', rfl⟩
  rw [h2] at h1
  obtain ⟨b, hb', hz⟩ := List.mem_flatMap.1 h1
  obtain ⟨z, -, e⟩ := List.mem_map.1 hz
  have e1 : b.place = s.addr.place := congrArg (·.2.2.1) e
  rw [← e1]
  exact hc b hb'

theorem places_chain {F : FileDescription Xi} (hp : F.placesOk = true) :
    (∀ b ∈ F.first.blocksInOrder, b.place.chain = 1) ∧ (∀ b ∈ F.shared.blocksInOrder, b.place.chain = 2) ∧
      ∀ b ∈ F.second.blocksInOrder, b.place.chain = 3 := by
  simp only [FileDescription.placesOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hp
  exact ⟨fun b hb => h1 _ (List.mem_map.2 ⟨b, hb, rfl⟩),
    fun b hb => h2 _ (List.mem_map.2 ⟨b, hb, rfl⟩),
    fun b hb => h3 _ (List.mem_map.2 ⟨b, hb, rfl⟩)⟩

theorem off_chain {ss : List (Step W Y)} {ss' : List (Step W' Y')} {a : Addr} {c c' : Nat}
    (hne : c ≠ c') (h : ∀ s ∈ ss, s.addr.place.chain = c)
    (h' : ∀ s ∈ ss', s.addr.place.chain = c') (ha : ss.any (·.addr == a) = true) :
    ∀ s ∈ ss', (s.addr == a) = false := by
  obtain ⟨s₀, hs₀, e₀⟩ := List.any_eq_true.1 ha
  have e₀' : s₀.addr = a := beq_iff_eq.1 e₀
  intro s hs
  refine Bool.eq_false_iff.2 fun e => hne ?_
  have e' : s.addr = a := beq_iff_eq.1 e
  rw [← h s₀ hs₀, ← h' s hs, e₀', e']

/-! ## 2 What WalkReads.lean gives, in the forms of RunAt.lean -/

theorem walk_len (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (u u' : ChainProgress S Cl W Y), walk L l d u = .ok u' → d.length = l.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | _ :: l, _ :: d, _, u', h => by
    obtain ⟨_, u₁, -, -, h₁⟩ := walk_cons_ok h
    exact congrArg (· + 1) (walk_len L l d u₁ u' h₁)

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

theorem runC_laidAs (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
    (o₁ : ∀ s ∈ R.first, s.oracles.length = s.decl.entry.roots)
    (o₂ : ∀ s ∈ R.shared, s.oracles.length = s.decl.entry.roots)
    (o₃ : ∀ s ∈ R.second, s.oracles.length = s.decl.entry.roots) :
    LaidAs r.run.played.1 R.first ρ.first ∧ LaidAs r.run.played.2.1 R.shared ρ.shared ∧
      LaidAs r.run.played.2.2 R.second ρ.second := by
  obtain ⟨⟨-, b1⟩, ⟨-, b2⟩, ⟨-, b3⟩⟩ := runC_bare h hR o₁ o₂ o₃
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', -, hz₁, -, -, hz₂, -, hz₃, -⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  exact ⟨⟨walk_len _ _ _ _ _ hz₁, b1⟩, ⟨walk_len _ _ _ _ _ hz₂, b2⟩, ⟨walk_len _ _ _ _ _ hz₃, b3⟩⟩

/-- The positions that the run reads of a tree are those that the declared rounds read of it, with
no table supplied. -/
theorem runC_asks (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
    (o₁ : ∀ s ∈ R.first, s.oracles.length = s.decl.entry.roots)
    (o₂ : ∀ s ∈ R.shared, s.oracles.length = s.decl.entry.roots)
    (o₃ : ∀ s ∈ R.second, s.oracles.length = s.decl.entry.roots) (ch j : Nat) :
    (((r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2).filter fun q =>
      q.src == some (ch, j)).map (·.pos)) = treeAsks F ρ ch j := by
  obtain ⟨⟨b1, -⟩, ⟨b2, -⟩, ⟨b3, -⟩⟩ := runC_bare h hR o₁ o₂ o₃
  have e : (r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2).map Read.bare = allBare F ρ := by
    rw [List.map_append, List.map_append, b1, b2, b3]
    rfl
  unfold treeAsks
  rw [← e, pos_bare]

end

/-! ## 3 The three chains' shares -/

/-- What holds of the three lists of rounds that a run has produced, at an address of one chain.
`ch`: that chain's number, from 0. `pl`, `ss`, `ds`: the rounds that it has produced, its `Step`s,
its challenges. The other two chains have no share. -/
structure At (r : Run) (a : Addr) (ch : Nat) (pl : List Played) (ss : List (Step W Y))
    (ds : List Fmt.Drawn) : Prop where
  laid : LaidAs pl ss ds
  part : ∀ qs, partIn 0 r.played.1 qs a ++ partIn 1 r.played.2.1 qs a ++
    partIn 2 r.played.2.2 qs a = partIn ch pl qs a
  mem : ∀ p ∈ pl, p ∈ r.played.1 ++ r.played.2.1 ++ r.played.2.2

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
  (o₁ : ∀ s ∈ R.first, s.oracles.length = s.decl.entry.roots)
  (o₂ : ∀ s ∈ R.shared, s.oracles.length = s.decl.entry.roots)
  (o₃ : ∀ s ∈ R.second, s.oracles.length = s.decl.entry.roots) (hp : F.placesOk = true)
include h hR o₁ o₂ o₃ hp

theorem at_first {a : Addr} (ha : R.first.any (·.addr == a) = true) :
    At r.run a 0 r.run.played.1 R.first ρ.first := by
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  refine ⟨l1, fun qs => ?_, fun p hp' =>
    List.mem_append_left _ (List.mem_append_left _ hp')⟩
  rw [partIn_none l2 (off_chain (by decide) c1 c2 ha),
    partIn_none l3 (off_chain (by decide) c1 c3 ha),
    List.append_nil, List.append_nil]

theorem at_shared {a : Addr} (ha : R.shared.any (·.addr == a) = true) :
    At r.run a 1 r.run.played.2.1 R.shared ρ.shared := by
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  refine ⟨l2, fun qs => ?_, fun p hp' =>
    List.mem_append_left _ (List.mem_append_right _ hp')⟩
  rw [partIn_none l1 (off_chain (by decide) c2 c1 ha),
    partIn_none l3 (off_chain (by decide) c2 c3 ha),
    List.nil_append, List.append_nil]

theorem at_second {a : Addr} (ha : R.second.any (·.addr == a) = true) :
    At r.run a 2 r.run.played.2.2 R.second ρ.second := by
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  refine ⟨l3, fun qs => ?_, fun p hp' => List.mem_append_right _ hp'⟩
  rw [partIn_none l1 (off_chain (by decide) c3 c1 ha),
    partIn_none l2 (off_chain (by decide) c3 c2 ha),
    List.nil_append, List.nil_append]

end

/-! ## 4 The three lemmas -/

section
variable {r : Run} {a : Addr} {ch : Nat} {pl : List Played} {ss : List (Step W Y)}
  {ds : List Fmt.Drawn} {n len : Nat}

/-- The part's challenges are its stretch of the chain's. -/
theorem drawnAt_of (hA : At r a ch pl ss ds) (hs : InStretch ss a n len) :
    r.drawnAt a = (ds.drop n).take len := by
  unfold Run.drawnAt Run.partAt
  rw [hA.part]
  exact drawn_chain hA.laid hs ch _

/-- The positions read of the part's tables. `tree`: the positions read of the chain's tree number
j. -/
theorem askedAt_of (hA : At r a ch pl ss ds) (hs : InStretch ss a n len) (tree : Nat → List Nat)
    (hq : ∀ j, (((r.reads.1 ++ r.reads.2.1 ++ r.reads.2.2).filter fun q =>
      q.src == some (ch, j)).map (·.pos)) = tree j) :
    r.askedAt a = asksFrom tree (((ss.drop n).take len).map (·.oracles.length))
      ((ss.take n).map (·.oracles.length)).sum := by
  unfold Run.askedAt Run.partAt
  rw [hA.part]
  exact asked_chain hA.laid hs ch _ tree hq

end

/-- If the stretch's first round is a real round (one that a prover's side made: `told`), the part
was called. -/
theorem called_of {F : FileDescription Xi} {r : RunC F} {a : Addr} {ch : Nat} {pl : List Played}
    {ss : List (Step W Y)} {ds : List Fmt.Drawn} {n len : Nat} (hA : At r.run a ch pl ss ds)
    (hs : InStretch ss a n len) (hl : 0 < len)
    (ht : ((pl.drop n).head?.map (·.told)) = some true) : r.called a = true := by
  obtain ⟨p, hp, e⟩ := List.any_eq_true.1 (told_chain hA.laid hs hl ht)
  exact List.any_eq_true.2 ⟨p, hA.mem p hp, e⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.steps_chain
#print axioms ProofFile.Honest.places_chain
#print axioms ProofFile.Honest.off_chain
#print axioms ProofFile.Honest.walk_len
#print axioms ProofFile.Honest.runC_laidAs
#print axioms ProofFile.Honest.runC_asks
#print axioms ProofFile.Honest.at_first
#print axioms ProofFile.Honest.at_shared
#print axioms ProofFile.Honest.at_second
#print axioms ProofFile.Honest.drawnAt_of
#print axioms ProofFile.Honest.askedAt_of
#print axioms ProofFile.Honest.called_of
