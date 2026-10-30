-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookTile.lean: the entries that `layFrom` (E2E/KeyBookFace.lean) builds for a lookup lie in
two ranges of their two owners' coins, have no coin in common, and have different names (the last
two under hypotheses on the owners). An entry (`Ahead`, in the frame:
Johnson/Desc/ProofFile/Honest/Frame.lean) is one item of the book of coins (`ProverCoinCounts`, same file), the
public table of which parts of the prover have coins of their own and which are given coins of
another part. It names a range of the coins of one part, its owner (`owner`), in each of the two
fields (`start`, `count`); one other part, its spender (`spender`), is given these coins too. A part
has an address (`Addr`): a place (`Place`, Johnson/Desc/Block.lean: where a sub-protocol is in the
protocol) and the part's number at that place. The theorems are general in the list of spans
(`Span`, E2E/KeyBookFace.lean: a range of a lookup's rounds that is one part). So they apply to a
lookup's entries `bookEntries S f a b`, which is `layFrom S (spansOf f) 0 a b`, at every face f
(`K3.Face`, Johnson/Desc/First/Look/K3LookupGeneral.lean: a lookup's numbers). E2E/KeyBookPasses.lean,
which imports this file, calls them at the key file's two lookups. Two definitions of propositions,
and theorems, on public data only: no prover, no coin's value.

In the list: S (`Seat`, E2E/KeyBookFace.lean) has the lookup's place `place` and, for each of the
two owners, an address and a name: `own` and `ownName` (below: the first owner), `key` and `keyName`
(the second). ps is a list of spans, and p the number, at the place, of the part that is its first
span. a and b are the numbers, among the first and the second owner's coins of the extension field,
of the first coins that are taken. The range from a up to a' has the numbers from a on that are
smaller than a'.

  `lay_block`: every entry of `layFrom S ps p a b` satisfies `InBlock` at the two owners, at the
    range from a up to `a + takenOwn ps`, at the range from b up to `b + takenKey ps` and at the
    place `S.place`; and its spender's number at the place is at least p. No hypothesis
  `lay_apart`: the entries of `layFrom S ps p a b` are pairwise `Apart`. Under hO
  `lay_names`: the names of the entries of `layFrom S ps p a b` differ pairwise. Under h₁ and h₂
  `lay_keyed`: every entry's name is the name (`Key.name`, E2E/KeyBookNames.lean) of a key
    `Key.run w q u`, for some owner's word w and use u (the string at the name's end that says what
    the coins are for), in which q is the four numbers of the entry's spender (`quadOf`: chain,
    link, piece, part; not the place's kind). Under h₁ and h₂
  `InBlock O₁ O₂ a a' b b' pl e`: a definition: the entry e is marked as spent (`once` is true); it
    has no coin of the base field (`start.f` and `count.f` are 0); its spender is at the place pl;
    and either its owner is O₁ and its coins of the extension field are in the range from a up to
    a', or its owner is O₂ and they are in the range from b up to b'. Below: e is in the block
  `Apart x y`: a definition: `x.shares y` and `y.shares x` are both false (`Ahead.shares`, in the
    frame: two entries have a coin in common)
  `taken_nil`, `taken_draw`, `taken_sum`: `takenOwn` and `takenKey` (E2E/KeyBook.lean: how many
    coins a list of spans takes of the first owner, and of the second), span by span. Both are 0 at
    the empty list. A span `draw` adds nothing. A span `sum k second` adds `ownRun k` to the first,
    and the number of the end values of k (0 if k has none) to the second if second is true, else to
    the first
  `InBlock.wider`: an entry in a block is in every block with wider ranges
  `Apart.symm`: `Apart` is symmetric
  `apart_of_owner`, `apart_of_behind`, `apart_of_blocks`: x and y are `Apart` if their owners
    differ; if x has no coin of the base field and its range in the extension field ends no later
    than that of y begins; if O₁ ≠ O₂, x is in a block, and y is in a block whose two ranges begin
    where the two ranges of the first block end
  `meets_zero_left`, `meets_zero_right`, `meets_behind`: `meets` (in the frame: two intervals have a
    number in common) is false if the first interval has length 0; if the second has; and, in either
    order of the two, if one ends no later than the other begins
  `names_of_quads`: two entries, each with the name of a key `Key.run` at the four numbers of its
    own spender, have different names if the two spenders' four numbers differ
  `filter_replicate_not`, `filter_replicate_id`: of n copies of a Boolean s, the number of those
    that are false is n if s is false, else 0; the number of those that are true is n if s is true,
    else 0

By what. The four theorems on `layFrom` go by induction on the list of spans and unfold `layFrom`.
`lay_block` takes the counts from `taken_sum`. `lay_apart` takes the block of the later spans'
entries from `lay_block` and calls `apart_of_blocks`, `apart_of_owner` and `apart_of_behind`.
`lay_keyed` rewrites by h₁ or h₂ and calls `runName_key` (E2E/KeyBookNames.lean: a name that
`runName` builds from one of the four words is the name of a key). `lay_names` calls `name_inj`
(same file: two keys with one name are one key): the entries of one span differ in the use, "sum" or
"ends"; an entry of a later span differs in the spender's number, by `lay_keyed`, `lay_block` and
`names_of_quads`. Definitions: `Who`, `Key`, `Quad` (E2E/KeyBookNames.lean); `Span.homes`
(E2E/KeyBookFace.lean); `ownRun` (Johnson/Desc/ProofFile/Honest/Sum.lean); `runName`
(Johnson/Desc/ProofFile/Honest/ForKinds.lean).

Hypotheses. hO (`lay_apart`, `apart_of_blocks`): the two owners' addresses differ. h₁, h₂
(`lay_keyed`, `lay_names`): the first owner's name is `w₁.word` and the second's is `w₂.word`, for
two values w₁ and w₂ of `Who`, the type of the four owners' words of the key file's book; the two
may be equal.

Limits. That the entries together contain every coin of the two ranges is not stated here:
`lay_block` says that they lie in the ranges, `lay_apart` that no two overlap. `unroll_lay`
(E2E/KeyBookFace.lean) lists the entries' coins one by one, where the owners' addresses differ. p, a
and b are free parameters: that the two ranges lie within the owners' counts of coins is not stated.
The theorems speak of the entries of one call of `layFrom` only: nothing is stated of the other
entries of a book, for which see E2E/KeyBookPasses.lean. No property of a protocol is stated:
nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookNames

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part
open ProofFile.Honest (Addr Ahead Due runName ownRun meets)

/-! ## 1 What a list of spans takes -/

theorem filter_replicate_not (n : Nat) (s : Bool) :
    ((List.replicate n s).filter (!·)).length = if s then 0 else n := by
  cases s <;> simp

theorem filter_replicate_id (n : Nat) (s : Bool) :
    ((List.replicate n s).filter (·)).length = if s then n else 0 := by
  cases s <;> simp

theorem taken_nil : takenOwn [] = 0 ∧ takenKey [] = 0 := ⟨rfl, rfl⟩

theorem taken_draw (s : String) (n : Nat) (l : List Span) :
    takenOwn (.draw s n :: l) = takenOwn l ∧ takenKey (.draw s n :: l) = takenKey l := ⟨rfl, rfl⟩

theorem taken_sum (k : MaskedSum.Call) (second : Bool) (l : List Span) :
    takenOwn (.sum k second :: l) =
        ownRun k + (if second then 0 else (k.ends.map (·.n)).getD 0) + takenOwn l ∧
      takenKey (.sum k second :: l) =
        (if second then (k.ends.map (·.n)).getD 0 else 0) + takenKey l := by
  unfold takenOwn takenKey
  simp only [List.flatMap_cons, Span.homes, List.filter_append, List.length_append,
    filter_replicate_not, filter_replicate_id]
  simp

/-! ## 2 The block -/

/-- The entry e is in the block: it is marked as spent, has no coin of the base field, has its
spender at the place pl, and its coins of the extension field are in the range from a up to a' of
the owner O₁ or in the range from b up to b' of the owner O₂ (a' and b' not included). -/
def InBlock (O₁ O₂ : Addr) (a a' b b' : Nat) (pl : Place) (e : Ahead) : Prop :=
  e.once = true ∧ e.start.f = 0 ∧ e.count.f = 0 ∧ e.spender.place = pl ∧
    ((e.owner = O₁ ∧ a ≤ e.start.e ∧ e.start.e + e.count.e ≤ a') ∨
      (e.owner = O₂ ∧ b ≤ e.start.e ∧ e.start.e + e.count.e ≤ b'))

theorem InBlock.wider {O₁ O₂ : Addr} {a a' b b' c c' d d' : Nat} {pl : Place} {e : Ahead}
    (h : InBlock O₁ O₂ a a' b b' pl e) (h1 : c ≤ a) (h2 : a' ≤ c') (h3 : d ≤ b) (h4 : b' ≤ d') :
    InBlock O₁ O₂ c c' d d' pl e := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := h
  refine ⟨x1, x2, x3, x4, ?_⟩
  rcases x5 with ⟨y1, y2, y3⟩ | ⟨y1, y2, y3⟩
  · exact Or.inl ⟨y1, by omega, by omega⟩
  · exact Or.inr ⟨y1, by omega, by omega⟩

/-- **Every entry that `layFrom` builds for a list of spans is in the block that the list takes.**
The block's ranges begin at a and b and have the lengths `takenOwn ps` and `takenKey ps`. The
spender's number at the place is at least p. -/
theorem lay_block (S : Seat) (ps : List Span) (p a b : Nat) :
    ∀ e ∈ layFrom S ps p a b,
      InBlock S.own S.key a (a + takenOwn ps) b (b + takenKey ps) S.place e ∧
        p ≤ e.spender.part := by
  induction ps generalizing p a b with
  | nil => intro e he; cases he
  | cons s l ih =>
    intro e he
    cases s with
    | draw n m =>
      obtain ⟨h1, h2⟩ := ih (p + 1) a b e he
      exact ⟨h1, by omega⟩
    | sum k second =>
      obtain ⟨t1, t2⟩ := taken_sum k second l
      simp only [layFrom, List.mem_append, List.mem_singleton] at he
      rcases he with (rfl | he) | he
      · exact ⟨⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, Nat.le_refl _, by
          show a + ownRun k ≤ _
          omega⟩⟩, Nat.le_refl _⟩
      · split at he
        · cases he
        · split at he
          · rename_i hs
            rw [List.mem_singleton] at he
            subst he
            subst hs
            exact ⟨⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, Nat.le_refl _, by
              show b + (k.ends.map (·.n)).getD 0 ≤ _
              simp only [if_true] at t2
              omega⟩⟩, Nat.le_refl _⟩
          · rename_i hs
            rw [List.mem_singleton] at he
            subst he
            have hs' : second = false := by simpa using hs
            subst hs'
            exact ⟨⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, by
              show a ≤ a + ownRun k
              omega, by
              show a + ownRun k + (k.ends.map (·.n)).getD 0 ≤ _
              simp only [Bool.false_eq_true, if_false] at t1
              omega⟩⟩, Nat.le_refl _⟩
      · obtain ⟨h1, h2⟩ := ih _ _ _ e he
        exact ⟨h1.wider (by omega) (by omega) (by omega) (by omega), by omega⟩

/-! ## 3 Entries without a common coin -/

/-- Neither of two entries has a coin in common with the other, by `Ahead.shares`. -/
def Apart (x y : Ahead) : Prop := x.shares y = false ∧ y.shares x = false

theorem Apart.symm {x y : Ahead} (h : Apart x y) : Apart y x := ⟨h.2, h.1⟩

theorem meets_zero_left (a b m : Nat) : meets a 0 b m = false := by simp [meets]

theorem meets_zero_right (a n b : Nat) : meets a n b 0 = false := by simp [meets]

theorem meets_behind {a n b m : Nat} (h : a + n ≤ b) :
    meets a n b m = false ∧ meets b m a n = false := by
  unfold meets
  constructor
  · have : ¬ (b < a + n) := by omega
    simp [this]
  · have : ¬ (b < a + n) := by omega
    simp [this]

/-- Two entries with different owners are `Apart`. -/
theorem apart_of_owner {x y : Ahead} (h : x.owner ≠ y.owner) : Apart x y := by
  have h1 : (x.owner == y.owner) = false := beq_eq_false_iff_ne.2 h
  have h2 : (y.owner == x.owner) = false := beq_eq_false_iff_ne.2 (Ne.symm h)
  exact ⟨by simp [Ahead.shares, h1], by simp [Ahead.shares, h2]⟩

/-- If x has no coin of the base field, and its range in the extension field ends no later than that
of y begins, then x and y are `Apart`. -/
theorem apart_of_behind {x y : Ahead} (hx : x.count.f = 0)
    (h : x.start.e + x.count.e ≤ y.start.e) : Apart x y := by
  obtain ⟨m1, m2⟩ := meets_behind (m := y.count.e) h
  exact ⟨by simp [Ahead.shares, hx, meets_zero_left, m1],
    by simp [Ahead.shares, hx, meets_zero_right, m2]⟩

/-- An entry in a block is `Apart` from an entry in a block whose two ranges begin where the two
ranges of the first block end. Hypothesis: the two owners' addresses differ. -/
theorem apart_of_blocks {O₁ O₂ : Addr} (hO : O₁ ≠ O₂) {a a' a'' b b' b'' : Nat} {pl pl' : Place}
    {x y : Ahead} (hx : InBlock O₁ O₂ a a' b b' pl x) (hy : InBlock O₁ O₂ a' a'' b' b'' pl' y) :
    Apart x y := by
  obtain ⟨-, -, x3, -, x5⟩ := hx
  obtain ⟨-, -, -, -, y5⟩ := hy
  rcases x5 with ⟨u1, -, u3⟩ | ⟨u1, -, u3⟩ <;> rcases y5 with ⟨v1, v2, -⟩ | ⟨v1, v2, -⟩
  · exact apart_of_behind x3 (by omega)
  · exact apart_of_owner (by rw [u1, v1]; exact hO)
  · exact apart_of_owner (by rw [u1, v1]; exact hO.symm)
  · exact apart_of_behind x3 (by omega)

/-- **The entries of a list of spans are pairwise `Apart`.** Hypothesis: the two owners' addresses
differ. -/
theorem lay_apart (S : Seat) (hO : S.own ≠ S.key) (ps : List Span) (p a b : Nat) :
    (layFrom S ps p a b).Pairwise Apart := by
  induction ps generalizing p a b with
  | nil => exact List.Pairwise.nil
  | cons s l ih =>
    cases s with
    | draw n m => exact ih (p + 1) a b
    | sum k second =>
      have hrest := lay_block S l (p + 1)
        (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
        (b + if second then (k.ends.map (·.n)).getD 0 else 0)
      simp only [layFrom]
      rw [List.append_assoc, List.singleton_append, List.pairwise_cons, List.pairwise_append]
      refine ⟨?_, ?_, ih _ _ _, ?_⟩
      · -- the span's entry with the use "sum" against all entries after it
        intro y hy
        rw [List.mem_append] at hy
        have hx : InBlock S.own S.key a (a + ownRun k) b b S.place
            ⟨runName S.ownName ⟨S.place, p⟩ "sum", S.own, ⟨0, a⟩, ⟨0, ownRun k⟩, ⟨S.place, p⟩,
              true⟩ :=
          ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩
        rcases hy with hy | hy
        · split at hy
          · cases hy
          · split at hy <;> (rw [List.mem_singleton] at hy; subst hy)
            · exact apart_of_owner hO
            · exact apart_of_behind rfl (Nat.le_refl _)
        · exact apart_of_blocks hO hx ((hrest y hy).1.wider (by omega) (Nat.le_refl _) (by omega)
            (Nat.le_refl _))
      · -- the span has at most one entry with the use "ends"
        split
        · exact List.Pairwise.nil
        · split <;> exact List.pairwise_singleton _ _
      · -- the span's entry with the use "ends" against the entries of the later spans
        intro x hx y hy
        split at hx
        · cases hx
        · split at hx
          · rename_i hs
            rw [List.mem_singleton] at hx
            subst hx
            subst hs
            have hb : InBlock S.own S.key a (a + ownRun k + 0) b (b + (k.ends.map (·.n)).getD 0)
                S.place ⟨runName S.keyName ⟨S.place, p⟩ "ends", S.key, ⟨0, b⟩,
                  ⟨0, (k.ends.map (·.n)).getD 0⟩, ⟨S.place, p⟩, true⟩ :=
              ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩⟩
            exact apart_of_blocks hO hb (by simpa using (hrest y hy).1)
          · rename_i hs
            rw [List.mem_singleton] at hx
            subst hx
            have hs' : second = false := by simpa using hs
            subst hs'
            have hb : InBlock S.own S.key a (a + ownRun k + (k.ends.map (·.n)).getD 0) b (b + 0)
                S.place ⟨runName S.ownName ⟨S.place, p⟩ "ends", S.own, ⟨0, a + ownRun k⟩,
                  ⟨0, (k.ends.map (·.n)).getD 0⟩, ⟨S.place, p⟩, true⟩ :=
              ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, by
                show a ≤ a + ownRun k
                omega, Nat.le_refl _⟩⟩
            exact apart_of_blocks hO hb (by simpa using (hrest y hy).1)

/-! ## 4 Names -/

/-- Every entry's name is the name of a key `Key.run` whose four numbers are those of the entry's
spender (`quadOf`). Hypotheses: each owner's name is one of the four words of `Who.word`. -/
theorem lay_keyed (S : Seat) (w₁ w₂ : Who) (h₁ : S.ownName = w₁.word) (h₂ : S.keyName = w₂.word)
    (ps : List Span) (p a b : Nat) :
    ∀ e ∈ layFrom S ps p a b, ∃ w u, e.name.toList = (Key.run w (quadOf e.spender) u).name := by
  induction ps generalizing p a b with
  | nil => intro e he; cases he
  | cons s l ih =>
    intro e he
    cases s with
    | draw n m => exact ih (p + 1) a b e he
    | sum k second =>
      simp only [layFrom, List.mem_append, List.mem_singleton] at he
      rcases he with (rfl | he) | he
      · exact ⟨w₁, "sum", by
          show (runName S.ownName _ _).toList = _
          rw [h₁]
          exact runName_key _ _ _⟩
      · split at he
        · cases he
        · split at he <;> (rw [List.mem_singleton] at he; subst he)
          · exact ⟨w₂, "ends", by
              show (runName S.keyName _ _).toList = _
              rw [h₂]
              exact runName_key _ _ _⟩
          · exact ⟨w₁, "ends", by
              show (runName S.ownName _ _).toList = _
              rw [h₁]
              exact runName_key _ _ _⟩
      · exact ih _ _ _ e he

/-- Two entries, each with the name of a key `Key.run` at the four numbers of its own spender, have
different names if the two spenders' four numbers differ. -/
theorem names_of_quads {x y : Ahead} {w w' : Who} {u u' : String}
    (hx : x.name.toList = (Key.run w (quadOf x.spender) u).name)
    (hy : y.name.toList = (Key.run w' (quadOf y.spender) u').name)
    (h : quadOf x.spender ≠ quadOf y.spender) : x.name ≠ y.name := by
  intro e
  rw [e, hy] at hx
  have := name_inj hx
  injection this with _ hq _
  exact h hq.symm

/-- **The names of the entries of a list of spans differ pairwise.** Hypotheses: each owner's name
is one of the four words of `Who.word`. -/
theorem lay_names (S : Seat) (w₁ w₂ : Who) (h₁ : S.ownName = w₁.word) (h₂ : S.keyName = w₂.word)
    (ps : List Span) (p a b : Nat) :
    (layFrom S ps p a b).Pairwise fun x y => x.name ≠ y.name := by
  induction ps generalizing p a b with
  | nil => exact List.Pairwise.nil
  | cons s l ih =>
    cases s with
    | draw n m => exact ih (p + 1) a b
    | sum k second =>
      have hpart := lay_block S l (p + 1)
        (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
        (b + if second then (k.ends.map (·.n)).getD 0 else 0)
      have hkey := lay_keyed S w₁ w₂ h₁ h₂ l (p + 1)
        (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
        (b + if second then (k.ends.map (·.n)).getD 0 else 0)
      -- an entry whose spender is part p differs in its name from every entry of the later spans
      have hfar : ∀ (x : Ahead) (w : Who) (u : String), x.spender = ⟨S.place, p⟩ →
          x.name.toList = (Key.run w (quadOf x.spender) u).name →
          ∀ y ∈ layFrom S l (p + 1)
            (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
            (b + if second then (k.ends.map (·.n)).getD 0 else 0), x.name ≠ y.name := by
        intro x w u hs hx y hy
        obtain ⟨w', u', hy'⟩ := hkey y hy
        refine names_of_quads hx hy' ?_
        intro hq
        have h4 : x.spender.part = y.spender.part := congrArg (fun q : Quad => q.2.2.2) hq
        have := (hpart y hy).2
        rw [hs] at h4
        simp only at h4
        omega
      have n1 : (runName S.ownName ⟨S.place, p⟩ "sum").toList =
          (Key.run w₁ (quadOf ⟨S.place, p⟩) "sum").name := by rw [h₁]; exact runName_key _ _ _
      have n2 : (runName S.keyName ⟨S.place, p⟩ "ends").toList =
          (Key.run w₂ (quadOf ⟨S.place, p⟩) "ends").name := by rw [h₂]; exact runName_key _ _ _
      have n3 : (runName S.ownName ⟨S.place, p⟩ "ends").toList =
          (Key.run w₁ (quadOf ⟨S.place, p⟩) "ends").name := by rw [h₁]; exact runName_key _ _ _
      have use_ne : ∀ (w w' : Who) (q : Quad),
          (Key.run w q "sum").name ≠ (Key.run w' q "ends").name := by
        intro w w' q e
        have := name_inj e
        injection this with _ _ hu
        exact absurd hu (by decide)
      simp only [layFrom]
      rw [List.append_assoc, List.singleton_append, List.pairwise_cons, List.pairwise_append]
      refine ⟨?_, ?_, ih _ _ _, ?_⟩
      · intro y hy
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · split at hy
          · cases hy
          · split at hy <;> (rw [List.mem_singleton] at hy; subst hy)
            · intro e
              exact use_ne w₁ w₂ _ (by rw [← n1, ← n2]; exact congrArg String.toList e)
            · intro e
              exact use_ne w₁ w₁ _ (by rw [← n1, ← n3]; exact congrArg String.toList e)
        · exact hfar _ w₁ "sum" rfl n1 y hy
      · split
        · exact List.Pairwise.nil
        · split <;> exact List.pairwise_singleton _ _
      · intro x hx y hy
        split at hx
        · cases hx
        · split at hx <;> (rw [List.mem_singleton] at hx; subst hx)
          · exact hfar _ w₂ "ends" rfl n2 y hy
          · exact hfar _ w₁ "ends" rfl n3 y hy

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.lay_block
#print axioms AtPublicFiles.KeyBook.lay_apart
#print axioms AtPublicFiles.KeyBook.lay_keyed
#print axioms AtPublicFiles.KeyBook.lay_names
#print axioms AtPublicFiles.KeyBook.filter_replicate_not
#print axioms AtPublicFiles.KeyBook.filter_replicate_id
#print axioms AtPublicFiles.KeyBook.taken_nil
#print axioms AtPublicFiles.KeyBook.taken_draw
#print axioms AtPublicFiles.KeyBook.taken_sum
#print axioms AtPublicFiles.KeyBook.InBlock
#print axioms AtPublicFiles.KeyBook.InBlock.wider
#print axioms AtPublicFiles.KeyBook.Apart
#print axioms AtPublicFiles.KeyBook.Apart.symm
#print axioms AtPublicFiles.KeyBook.meets_zero_left
#print axioms AtPublicFiles.KeyBook.meets_zero_right
#print axioms AtPublicFiles.KeyBook.meets_behind
#print axioms AtPublicFiles.KeyBook.apart_of_owner
#print axioms AtPublicFiles.KeyBook.apart_of_behind
#print axioms AtPublicFiles.KeyBook.apart_of_blocks
#print axioms AtPublicFiles.KeyBook.names_of_quads
