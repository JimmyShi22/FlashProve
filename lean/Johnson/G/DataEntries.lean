-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/DataEntries.lean: the rounds' data that are made of a plan bear the plan's own entries,
round by round.

Why. A round's data hold an entry: the round's name and eleven numbers, its bits of proof of work
among them. Laws on written rounds divide by 2 to that number of bits. The entry is a field of the
data, so by itself nothing says that it is the entry that the plan states. Here: on the road from
the planner's record to the data of the key file's and of the proof file's rounds
(Johnson/G/RoundsOfPlan.lean) every step keeps the entries, in their order.

Statements and proofs.
  `fill_entries`: the declared rounds that `fill` returns have the given entries.
  `fileOf_entries`: the three lists of declared rounds that `fileOf` returns have the entries of the
    three plans' rounds.
  `round_entry`: a declared round as the readers take it (`Fmt.DeclaredRound.round`) keeps its entry.
  `writtenOf_entries`: the three lists of written rounds that `writtenOf` returns have the entries
    of the declared rounds.
  `dataAt_entries`: the data at three lists of written rounds are those of three empty lists, or
    they have the rounds' entries, the first list without its last. By `of_entry₁`, `of_entry₂`,
    `of_entry₃` (OnBytes/Flat/WholeEntries.lean).
  `dataKAt_entries`, `dataPAt_entries`: what `dataKAt m`, `dataPAt m` return are the data of three
    empty lists, or their three lists have the entries of the rounds of the three plans in m: the
    key file's one-time, shared and second chain; the proof file's first, shared and second chain.
    The first list comes without the plan's last round.
  `fill_nil`, `fill_one`, `fill_refuses`: three trials of `fill`, by evaluation: no entry; one round
    that draws positions; one such round and no list of trees, which is refused.

Limits. Where a step refuses nothing is said. Which of the two cases holds at given public files is
not shown: the data are those of three empty lists where the makers' tests (`okAt`,
OnBytes/Maker/Files.lean) say no. The plans are those that stand in m under `given.plan`; that they
are the plans of the planner's priced rounds (`m.p.chains.made`) is not shown here. Nothing on a
round's kind, items, trees or openings. Nothing on the entry file. Nothing on soundness.


-/
import Johnson.G.RoundsOfPlan
import OnBytes.Flat.WholeEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.OfPlan
open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)

/-! ### Steps that may refuse -/

/-- If a step and what follows it return a value, the step returns one. -/
theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A refusal returns no value. -/
theorem throw_ne {ε α : Type} (e : ε) (a : α) : (throw e : Except ε α) ≠ .ok a := by
  intro h
  have h' : (Except.error e : Except ε α) = .ok a := h
  cases h'

/-- What reads a value that `mapM` returns, member by member. -/
theorem mapM_map {ε α β γ : Type} (f : α → Except ε β) (g : β → γ) (g' : α → γ)
    (hf : ∀ a b, f a = .ok b → g b = g' a) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.map g = l.map g'
  | [], r, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    rfl
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, h1, h⟩ := bind_ok h
    obtain ⟨r', h2, h⟩ := bind_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    rw [List.map_cons, List.map_cons, hf x y h1, mapM_map f g g' hf l r' h2]

/-! ### From the plan's entries to declared rounds -/

/-- A fold that pushes, for each entry, a declared round with that entry. -/
theorem foldl_push_entries {σ : Type}
    (f : Array Fmt.DeclaredRound × σ → Fmt.Entry → Array Fmt.DeclaredRound × σ)
    (hf : ∀ s e, ∃ x : Fmt.DeclaredRound, (f s e).1 = s.1.push x ∧ x.entry = e) :
    ∀ (es : List Fmt.Entry) (s : Array Fmt.DeclaredRound × σ),
      (es.foldl f s).1.toList.map (·.entry) = s.1.toList.map (·.entry) ++ es
  | [], s => by simp
  | e :: es, s => by
    obtain ⟨x, h1, h2⟩ := hf s e
    rw [List.foldl_cons, foldl_push_entries f hf es (f s e), h1, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, h2, List.append_assoc, List.singleton_append]

/-- The declared rounds that `fill` returns have the given entries. -/
theorem fill_entries {at_ : String} {es : List Fmt.Entry}
    {plan : List (List Told × List Fmt.Stored)} {l : List Fmt.DeclaredRound}
    (h : fill at_ es plan = .ok l) : l.map (·.entry) = es := by
  unfold fill at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    split at h
    · obtain ⟨_, h', _⟩ := bind_ok h
      exact absurd h' (throw_ne _ _)
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain rfl := Except.ok.inj h
      refine foldl_push_entries _ (fun s e => ?_) es (#[], plan)
      dsimp only
      split <;> exact ⟨_, rfl, rfl⟩
  · obtain ⟨_, h', _⟩ := bind_ok h
    exact absurd h' (throw_ne _ _)

/-- The three lists of declared rounds that `fileOf` returns have the entries of the three plans'
rounds. -/
theorem fileOf_entries {file : String} {S : Params.LinShape} {P0 P1 P2 : Fmt.Plan}
    {c0 c1 c2 : ChainSends} {first : List (Sent × Nat) → List Fmt.Entry → List (List Told)}
    {input : Sent → Bool} {D : Decl3} (h : fileOf file S P0 P1 P2 c0 c1 c2 first input = .ok D) :
    D.1.map (·.entry) = P0.rounds ∧ D.2.1.map (·.entry) = P1.rounds ∧
      D.2.2.map (·.entry) = P2.rounds := by
  unfold fileOf at h
  obtain ⟨t0, _, h⟩ := bind_ok h
  obtain ⟨t1, _, h⟩ := bind_ok h
  obtain ⟨t2, _, h⟩ := bind_ok h
  obtain ⟨d0, h0, h⟩ := bind_ok h
  obtain ⟨d1, h1, h⟩ := bind_ok h
  obtain ⟨d2, h2, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · exact absurd h (throw_ne _ _)
  · obtain rfl := Except.ok.inj h
    exact ⟨fill_entries h0, fill_entries h1, fill_entries h2⟩

/-! ### From declared rounds to written rounds -/

/-- A declared round as the readers take it keeps its entry. -/
theorem round_entry {earlier : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound}
    {x : Fmt.Round} (h : r.round earlier = some x) : x.entry = r.entry := by
  unfold Fmt.DeclaredRound.round at h
  obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨os, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- The three lists of written rounds that `writtenOf` returns have the entries of the declared
rounds. -/
theorem writtenOf_entries {file : String} {D : Decl3} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file D = .ok R) :
    R.1.map (·.1.entry) = D.1.map (·.entry) ∧ R.2.1.map (·.1.entry) = D.2.1.map (·.entry) ∧
      R.2.2.map (·.1.entry) = D.2.2.map (·.entry) := by
  unfold writtenOf at h
  dsimp only at h
  obtain ⟨r1, h1, h⟩ := bind_ok h
  obtain ⟨r2, h2, h⟩ := bind_ok h
  obtain ⟨r3, h3, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  have key : ∀ (chain : String) (e : List (List ByteArray × ByteArray)) (a : Fmt.DeclaredRound)
      (b : Fmt.Round × List Fmt.Stored),
      (match a.round e with
        | some x => (pure (x, a.stored) : Except String (Fmt.Round × List Fmt.Stored))
        | none => throw <| refusal s!"{file}, {chain} chain" <| s!"the round \"{a.entry.name}\" " ++
            (if (Fmt.kindOf a.entry.name).isNone then "has a name that the format does not know"
             else "takes over a tree that the earlier chain does not send")) = .ok b →
        b.1.entry = a.entry := by
    intro chain e a b hab
    split at hab
    · rename_i x hx
      obtain rfl := Except.ok.inj hab
      exact round_entry hx
    · exact absurd hab (throw_ne _ _)
  exact ⟨mapM_map _ (·.1.entry) (·.entry) (key "first" []) _ _ h1,
    mapM_map _ (·.1.entry) (·.entry) (key "shared" []) _ _ h2,
    mapM_map _ (·.1.entry) (·.entry) (key "second" _) _ _ h3⟩

/-! ### From written rounds to the data -/

/-- The data at three lists of written rounds: those of three empty lists, or with the rounds'
entries, the first list without its last. -/
theorem dataAt_entries (a : ℕ) (R : Rounds × Rounds × Rounds) :
    dataAt a (some R) = Three.Whole.of [] [] [] ∨
      ((WholeD.of a (dataAt a (some R))).ds₁.map (·.entry) = (R.1.map (·.1.entry)).dropLast ∧
        (WholeD.of a (dataAt a (some R))).ds₂.map (·.entry) = R.2.1.map (·.1.entry) ∧
        (WholeD.of a (dataAt a (some R))).ds₃.map (·.entry) = R.2.2.map (·.1.entry)) := by
  unfold dataAt
  split
  · exact Or.inr ⟨Flat.of_entry₁ a R.1 R.2.1 R.2.2, Flat.of_entry₂ a R.1 R.2.1 R.2.2,
      Flat.of_entry₃ a R.1 R.2.1 R.2.2⟩
  · exact Or.inl rfl

/-- From a file's declared rounds, with the entries of three plans' rounds, to its data. -/
theorem data_entries {file : String} {Dc : Decl3} {R : Rounds × Rounds × Rounds}
    {e₁ e₂ e₃ : List Fmt.Entry} (hD : Dc.1.map (·.entry) = e₁ ∧ Dc.2.1.map (·.entry) = e₂ ∧
      Dc.2.2.map (·.entry) = e₃) (hR : writtenOf file Dc = .ok R) (a : ℕ) :
    WholeD.of a (dataAt a (some R)) = WholeD.of a (Three.Whole.of [] [] []) ∨
      ((WholeD.of a (dataAt a (some R))).ds₁.map (·.entry) = e₁.dropLast ∧
        (WholeD.of a (dataAt a (some R))).ds₂.map (·.entry) = e₂ ∧
        (WholeD.of a (dataAt a (some R))).ds₃.map (·.entry) = e₃) := by
  obtain ⟨w1, w2, w3⟩ := writtenOf_entries hR
  rcases dataAt_entries a R with h | ⟨h1, h2, h3⟩
  · exact Or.inl (congrArg (WholeD.of a) h)
  · exact Or.inr ⟨by rw [h1, w1, hD.1], by rw [h2, w2, hD.2.1], by rw [h3, w3, hD.2.2]⟩

/-- **The data of the key file's rounds bear the entries of the key file's three plans.** -/
theorem dataKAt_entries {m : Made} {D : WholeD} (h : dataKAt m = .ok D) :
    (∃ a, D = WholeD.of a (Three.Whole.of [] [] [])) ∨
      (D.ds₁.map (·.entry) = m.p.chains.key.oneTime.given.plan.rounds.dropLast ∧
        D.ds₂.map (·.entry) = m.p.chains.key.shared.given.plan.rounds ∧
        D.ds₃.map (·.entry) = m.p.chains.key.second.given.plan.rounds) := by
  unfold dataKAt at h
  obtain ⟨a, _, h⟩ := bind_ok h
  obtain ⟨Dc, hD, h⟩ := bind_ok h
  obtain ⟨R, hR, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  unfold declKOf at hD
  rcases data_entries (fileOf_entries hD) hR a with h | h
  · exact Or.inl ⟨a, h⟩
  · exact Or.inr h

/-- **The data of the proof file's rounds bear the entries of the proof file's three plans.** -/
theorem dataPAt_entries {m : Made} {D : WholeD} (h : dataPAt m = .ok D) :
    (∃ a, D = WholeD.of a (Three.Whole.of [] [] [])) ∨
      (D.ds₁.map (·.entry) = m.p.chains.proof.first.given.plan.rounds.dropLast ∧
        D.ds₂.map (·.entry) = m.p.chains.proof.shared.given.plan.rounds ∧
        D.ds₃.map (·.entry) = m.p.chains.proof.second.given.plan.rounds) := by
  unfold dataPAt at h
  obtain ⟨a, _, h⟩ := bind_ok h
  obtain ⟨Dc, hD, h⟩ := bind_ok h
  obtain ⟨R, hR, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  unfold declPOf at hD
  rcases data_entries (fileOf_entries hD) hR a with h | h
  · exact Or.inl ⟨a, h⟩
  · exact Or.inr h

/-! ### Three trials of `fill` -/

/-- No entry and no list of trees: no declared round. -/
theorem fill_nil : fill "" [] [] = .ok [] := by decide

/-- One round that draws positions, and one list of one tree. -/
theorem fill_one :
    fill "" [{ name := "LOC" }] [([(⟨0, 1, false, 0⟩, .own 0)], [])] =
      .ok [⟨{ name := "LOC" }, [], [(⟨0, 1, false, 0⟩, .own 0)]⟩] := by decide

/-- One round that draws positions, and no list of trees: refused. -/
theorem fill_refuses : ∀ l, fill "" [{ name := "LOC" }] [] ≠ .ok l := by
  intro l h
  unfold fill at h
  dsimp only at h
  rw [if_neg (by decide)] at h
  obtain ⟨_, h', _⟩ := bind_ok h
  exact absurd h' (throw_ne _ _)

end Johnson.G.OfPlan

#print axioms Johnson.G.OfPlan.bind_ok
#print axioms Johnson.G.OfPlan.throw_ne
#print axioms Johnson.G.OfPlan.mapM_map
#print axioms Johnson.G.OfPlan.foldl_push_entries
#print axioms Johnson.G.OfPlan.fill_entries
#print axioms Johnson.G.OfPlan.fileOf_entries
#print axioms Johnson.G.OfPlan.round_entry
#print axioms Johnson.G.OfPlan.writtenOf_entries
#print axioms Johnson.G.OfPlan.dataAt_entries
#print axioms Johnson.G.OfPlan.data_entries
#print axioms Johnson.G.OfPlan.dataKAt_entries
#print axioms Johnson.G.OfPlan.dataPAt_entries
#print axioms Johnson.G.OfPlan.fill_nil
#print axioms Johnson.G.OfPlan.fill_one
#print axioms Johnson.G.OfPlan.fill_refuses
