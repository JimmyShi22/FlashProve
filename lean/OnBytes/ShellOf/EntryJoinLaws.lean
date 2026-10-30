-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryJoinLaws.lean: the laws on the two Bools of OnBytes/ShellOf/EntryJoin.lean. For
proofs only: no program imports it.

No soundness: a test. This module states laws on what the runs of lean/Ask/ call; it states nothing
on soundness.

  `furtherIs_true`: what a "true" means: there are a value L that `rdLeaf` makes of the first file
    and a pair P that `rdProofHead` makes of the second, with L.root = P.1 and L.answers = P.2.
  `parseP_tables`: where `parseP` returns a value a, a.first is fields 1 and 2 of the parsed key
    file and a.further is fields 3 and 4 of the parsed leaf file.
  `furtherIs_joins`: so, at one leaf file's bytes, a "true" says that a.further is the pair that
    `rdProofHead` makes of the parsed proof file.
  `yesAtP_true`, `yesSmallP_true`, `yesFullP_true`: what a "true" of the entry file's part means:
    the ID has its form; the standard test said yes; the reader returned a value a; the closed check
    `verifyEntrySmall` | `verifyEntryFull` says yes at the public files, a and `gOf O`; and the
    commitment ID that `gOf O` gives of the public files and a.first is the user's: the five
    clauses of `ZeroSaysP` (OnBytes/ShellOf/EntryParsedLaws.lean) that do not speak of the shell.

The laws on `parseP` speak of the reader. The closed check trusts it for nothing. `furtherIs_joins`
leans on `parseP_tables`: with another parser it has to be proved anew. What a yes of the closed
check is worth: see the head of OnBytes/ShellOf/EntryProgLaws.lean: nothing is added here.

-/
import OnBytes.ShellOf.EntryJoin
import OnBytes.ShellOf.EntryProgLaws

set_option autoImplicit false

namespace OnBytes.ShellOf.EntryParsed

open OnBytes.ShellOf.Claimed
open OnBytes.ShellOf.EntryProg
open OnBytes.Tie (AskedE EntryGround)
open TypedOracleCompiler.Slice (verifyEntryFull verifyEntrySmall idOfG)
open TypedOracleCompiler.Run.EntryPageSafe (gOf)
open OnBytes.Slice.Shapes (Cfg)
open Rom

/-- What a "true" means. -/
theorem furtherIs_true {leaf proof : ByteArray} (h : furtherIs leaf proof = true) :
    ∃ L P, rdLeaf leaf = some L ∧ rdProofHead proof = some P ∧ L.root = P.1 ∧ L.answers = P.2 := by
  unfold furtherIs at h
  split at h
  · rename_i L P hL hP
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    exact ⟨L, P, hL, hP, h.1, h.2⟩
  · cases h

/-- A match on two options, given as a parameter `M` together with its three computation rules.
If it returns `v` and neither of the two fallback branches can return `v`, both options were
`some` and the first branch returned `v`. Nothing about `M`, the options or the branches is
unfolded. -/
theorem two_ok {α β R : Type} (M : Option α → Option β → (α → β → R) → (Option β → R) →
      (Option α → R) → R)
    (r1 : ∀ x y f f2 f3, M (some x) (some y) f f2 f3 = f x y)
    (r2 : ∀ y f f2 f3, M none y f f2 f3 = f2 y)
    (r3 : ∀ x f f2 f3, M (some x) none f f2 f3 = f3 (some x))
    {oa : Option α} {ob : Option β} {f : α → β → R} {f2 : Option β → R} {f3 : Option α → R} {v : R}
    (n2 : ∀ y, f2 y ≠ v) (n3 : ∀ x, f3 x ≠ v) (h : M oa ob f f2 f3 = v) :
    ∃ x y, oa = some x ∧ ob = some y ∧ f x y = v := by
  cases oa with
  | none => exact absurd ((r2 _ _ _ _).symm.trans h) (n2 _)
  | some x =>
    cases ob with
    | none => exact absurd ((r3 _ _ _ _).symm.trans h) (n3 _)
    | some y => exact ⟨x, y, rfl, rfl, (r1 _ _ _ _ _).symm.trans h⟩

/-- The same for a match on one option. -/
theorem one_ok {α R : Type} (M : Option α → (Unit → R) → (α → R) → R)
    (r1 : ∀ f1 f2, M none f1 f2 = f1 ()) (r2 : ∀ x f1 f2, M (some x) f1 f2 = f2 x)
    {oa : Option α} {f1 : Unit → R} {f2 : α → R} {v : R} (n1 : f1 () ≠ v)
    (h : M oa f1 f2 = v) : ∃ x, oa = some x ∧ f2 x = v := by
  cases oa with
  | none => exact absurd ((r1 _ _).symm.trans h) n1
  | some x => exact ⟨x, rfl, (r2 _ _ _).symm.trans h⟩

/-- The same for a match on two options with one catch-all branch. -/
theorem both_ok {α R : Type}
    (M : Option α → Option α → (α → α → R) → (Option α → Option α → R) → R)
    (r1 : ∀ x y f f2, M (some x) (some y) f f2 = f x y)
    (r2 : ∀ y f f2, M none y f f2 = f2 none y)
    (r3 : ∀ x f f2, M (some x) none f f2 = f2 (some x) none)
    {oa ob : Option α} {f : α → α → R} {f2 : Option α → Option α → R} {v : R}
    (n2 : ∀ x y, f2 x y ≠ v) (h : M oa ob f f2 = v) :
    ∃ x y, oa = some x ∧ ob = some y ∧ f x y = v := by
  cases oa with
  | none => exact absurd ((r2 _ _ _).symm.trans h) (n2 _ _)
  | some x =>
    cases ob with
    | none => exact absurd ((r3 _ _ _).symm.trans h) (n2 _ _)
    | some y => exact ⟨x, y, rfl, rfl, (r1 _ _ _ _).symm.trans h⟩

/-- If an `if` returns `v` and its `else` branch is not `v`, the `then` branch is `v`. -/
theorem ok_of_ite {R : Type} {c : Prop} [Decidable c] {x y v : R} (n : y ≠ v)
    (h : (if c then x else y) = v) : x = v := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact h
  · rw [if_neg hc] at h
    exact absurd h n

/-- A `have` inside a term can be replaced by its value. -/
theorem ok_of_have {β R : Type} {v : β} {f : β → R} {w : R}
    (h : (have c := v; f c) = w) : f v = w := h

/-- Which bytes became the two tables of the reader's value. -/
theorem parseP_tables {G : EntryGround} {O : ByteArray → ByteArray} {cl : Claim}
    {key ent : ByteArray} {a : AskedE} (h : parseP G O cl key ent = .ok a) :
    ∃ K L, rdKeyHead key = some K ∧ rdLeaf ent = some L ∧
      a.first = ⟨K.1, K.2⟩ ∧ a.further = ⟨L.root, L.answers⟩ := by
  -- `parseP` is rewritten by its own equation. Each of its three matches is then passed, as it
  -- stands in that equation, to a lemma in which the match itself is a parameter (`two_ok`,
  -- `one_ok`, `both_ok`): no part of the match is typed again here, so a proof checker has two
  -- identical terms before it and never has to evaluate what a match inspects.
  rw [parseP] at h
  obtain ⟨K, L, hK, hL, h1⟩ := two_ok _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro _ e; cases e) (by intro _ e; cases e) h
  have h1' := ok_of_have (ok_of_ite (by intro e; cases e) h1)
  obtain ⟨out, -, h2⟩ := one_ok _ (by intros; rfl) (by intros; rfl) (by intro e; cases e) h1'
  obtain ⟨l0, l1, -, -, h3⟩ := both_ok _ (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro _ _ e; cases e) h2
  obtain rfl := Except.ok.inj h3
  exact ⟨K, L, hK, hL, rfl, rfl⟩

/-- At one leaf file's bytes: the reader's further table is the parsed proof file's. -/
theorem furtherIs_joins {G : EntryGround} {O : ByteArray → ByteArray} {cl : Claim}
    {key leaf proof : ByteArray} {a : AskedE}
    (h : parseP G O cl key leaf = .ok a) (hj : furtherIs leaf proof = true) :
    ∃ P, rdProofHead proof = some P ∧ a.further = ⟨P.1, P.2⟩ := by
  obtain ⟨_, L, -, hL, -, hf⟩ := parseP_tables h
  obtain ⟨L', P, hL', hP, h1, h2⟩ := furtherIs_true hj
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  exact ⟨P, hP, by rw [hf, h1, h2]⟩

/-- What a "true" of the entry file's part means, for every form for a run that equals `partAt`. -/
theorem yesAtP_true (V : Cfg → AskedE → Fam (rom 256) → Bool) (z : Params.StdSize)
    (G : EntryGround) (R : Cfg → AskedE → (ByteArray → ByteArray) → Bool)
    (O : ByteArray → ByteArray)
    (hP : ∀ cl a, runAt R G.q.link.table O cl a = partAt V G.q.link.table (gOf O) cl a)
    {id0 : String} {cfg : Params.StdCfg} {key leaf : ByteArray}
    (h : yesAtP z G R O id0 cfg key leaf = true) :
    ∃ id a, Model.Verify.idAsked id0 = some id ∧ Params.stdEntry z cfg = true ∧
      parseP G O ⟨id, cfg⟩ key leaf = .ok a ∧ V (cfgOf cfg) a (gOf O) = true ∧
      idOfG G.q.link.table (cfgOf cfg) a.first (gOf O) = id := by
  unfold yesAtP at h
  split at h
  · rename_i id hid
    rw [Bool.and_eq_true] at h
    obtain ⟨hs, hm⟩ := h
    split at hm
    · rename_i a ha
      obtain ⟨h1, h2⟩ := (partAt_true V _ _ _ a).1 ((hP _ _).symm.trans hm)
      exact ⟨id, a, hid, hs, ha, h1, h2⟩
    · cases hm
  · cases h

theorem yesSmallP_true (O : ByteArray → ByteArray) {id0 : String} {cfg : Params.StdCfg}
    {key leaf : ByteArray} (h : yesSmallP O id0 cfg key leaf = true) :
    ∃ id a, Model.Verify.idAsked id0 = some id ∧ Params.stdEntry Params.stdSmall cfg = true ∧
      parseP Tie.smallRecordGround O ⟨id, cfg⟩ key leaf = .ok a ∧
      verifyEntrySmall (cfgOf cfg) a (gOf O) = true ∧
      idOfG Tie.smallRecordGround.q.link.table (cfgOf cfg) a.first (gOf O) = id :=
  yesAtP_true _ _ _ _ O (runSmall_eq O) h

theorem yesFullP_true (O : ByteArray → ByteArray) {id0 : String} {cfg : Params.StdCfg}
    {key leaf : ByteArray} (h : yesFullP O id0 cfg key leaf = true) :
    ∃ id a, Model.Verify.idAsked id0 = some id ∧ Params.stdEntry Params.stdFull cfg = true ∧
      parseP Tie.recordGround O ⟨id, cfg⟩ key leaf = .ok a ∧
      verifyEntryFull (cfgOf cfg) a (gOf O) = true ∧
      idOfG Tie.recordGround.q.link.table (cfgOf cfg) a.first (gOf O) = id :=
  yesAtP_true _ _ _ _ O (runFull_eq O) h

end OnBytes.ShellOf.EntryParsed
