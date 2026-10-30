-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadSpecs.lean: what the descriptions under which a file's three chains are read have
in common with the plain data of the three chains (`Three.Whole`, OnBytes/Three/Data.lean): the
stored tables round by round, and the number of the first own tree.

Statements and proofs. The program makes a chain's description from rounds that a dry run of the
chain's block states (`Params.describeWith`, OnBytes/Params/Chains.lean). The plain data are made
from three such lists of rounds (`Three.Whole.of`).

Main names:
  `describeWith_facts`: the rounds, the stored tables and the first tree's number of a description
    that is returned are the arguments'.
  `stored_ds₁`, `stored_ds₂`, `stored_ds₃`: the stored tables of the data's rounds are those of the
    rounds from which the data were made.
  `spec_stored`: so a description made from a list of rounds has the stored tables of the data's
    rounds made from a list with the same stored tables (`StoredAlike`).
  `readChain_roots`: a chain that the program's reader has read holds as many roots as its
    description's rounds have items of the kind root.
  `firstTree₃`: the number that the program gives to the third chain's first own tree
    (`Proof.secondFirstTree`) is the data's (`Three.first₃`), if the first chain was read under a
    description made from the data's first list of rounds.
Limits: the data's third list of rounds is made at made-up names of the trees that the third chain
takes over, the description's at the file's own roots. That the two lists have the same stored
tables is the hypothesis `StoredAlike`; it is not proved here. Nothing on soundness.


-/
import OnBytes.Maker.ReadFacts
import OnBytes.Params.Laws

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie

/-! ## A description and its arguments -/

/-- The rounds, the stored tables and the first tree's number of a description that is returned. -/
theorem describeWith_facts {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (h : Params.describeWith g label st rand R ft = some S) :
    S.base.rounds = R.map (·.1) ∧ S.stored = R.map (·.2) ∧ S.base.firstTree = ft := by
  unfold Params.describeWith at h
  rw [Params.Given.describe_eq h]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The data's rounds -/

/-- The fold of `Three.sentBefore` adds one number for each round. -/
theorem sentFold_size : ∀ (R : Params.Rounds) (a : ℕ × Array ℕ),
    (R.foldl (fun (a : ℕ × Array ℕ) r =>
      (a.1 + r.1.items.countP (· == .root), a.2.push a.1)) a).2.size = a.2.size + R.length
  | [], a => rfl
  | r :: R, a => by
    rw [List.foldl_cons, sentFold_size R, Array.size_push, List.length_cons]
    omega

theorem sentBefore_length (R : Params.Rounds) : (Three.sentBefore R).length = R.length := by
  unfold Three.sentBefore
  rw [Array.length_toList, sentFold_size]
  simp

/-- The stored tables of rounds' data made round by round. -/
theorem zipWith_stored (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ) :
    ∀ (R : Params.Rounds) (L : List ℕ), L.length = R.length →
    (List.zipWith (Three.rdOf all t₁ t₂ here base first) R L).map (·.stored) = R.map (·.2)
  | [], _, _ => by simp
  | _ :: _, [], e => by cases e
  | r :: R, n :: L, e => by
    rw [List.zipWith_cons_cons, List.map_cons, List.map_cons,
      zipWith_stored all t₁ t₂ here base first R L (Nat.succ.inj e)]
    rfl

theorem rdsFromL_stored (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    (R : Params.Rounds) :
    (Three.rdsFromL all t₁ t₂ here base first R).map (·.stored) = R.map (·.2) :=
  zipWith_stored all t₁ t₂ here base first R _ (sentBefore_length R)

theorem stored_ds₁ (R₁ R₂ R₃ : Params.Rounds) :
    (Three.Whole.of R₁ R₂ R₃).ds₁.map (·.stored) = R₁.map (·.2) := rdsFromL_stored _ _ _ _ _ _ R₁

theorem stored_ds₂ (R₁ R₂ R₃ : Params.Rounds) :
    (Three.Whole.of R₁ R₂ R₃).ds₂.map (·.stored) = R₂.map (·.2) := rdsFromL_stored _ _ _ _ _ _ R₂

theorem stored_ds₃ (R₁ R₂ R₃ : Params.Rounds) :
    (Three.Whole.of R₁ R₂ R₃).ds₃.map (·.stored) = R₃.map (·.2) := rdsFromL_stored _ _ _ _ _ _ R₃

/-- **A hypothesis on two lists of rounds**: round by round they open the same stored tables. -/
def StoredAlike (R R' : Params.Rounds) : Prop := R.map (·.2) = R'.map (·.2)

/-- A description made from R has the stored tables of rounds' data whose stored tables are those
of a list R' that is alike. -/
theorem spec_stored {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R R' : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX} {dl : List Three.RDL}
    (h : Params.describeWith g label st rand R ft = some S) (ha : StoredAlike R R')
    (hd : dl.map (·.stored) = R'.map (·.2)) : S.stored = dl.map (·.stored) := by
  rw [(describeWith_facts h).2.1, hd]
  exact ha

/-! ## The number of roots that a chain as read holds -/

/-- What one item's reader returns is a root just if the item is of the kind root. -/
theorem readItem_roots (f : Fmt.Fld) (t : Fmt.Item) (b : ByteArray) (i : ℕ) (x : Fmt.ItemValue) (j : ℕ)
    (e : Fmt.readItem f t b i = some (x, j)) (l : List Fmt.ItemValue) :
    (Fmt.rootsOf (x :: l)).length = (if t == .root then 1 else 0) + (Fmt.rootsOf l).length := by
  cases t <;> simp only [Fmt.readItem, Option.map_eq_some_iff] at e <;>
    obtain ⟨y, -, hy⟩ := e <;> obtain ⟨rfl, -⟩ := Prod.mk.inj hy
  · simp [Fmt.rootsOf]
  · simp [Fmt.rootsOf]
  · simp [Fmt.rootsOf]
  · simp [Fmt.rootsOf]; omega
  · simp [Fmt.rootsOf]

theorem readItems_roots (f : Fmt.Fld) : ∀ (ts : List Fmt.Item) (b : ByteArray) (i : ℕ)
    (l : List Fmt.ItemValue) (k : ℕ), Fmt.readItems f ts b i = some (l, k) →
    (Fmt.rootsOf l).length = ts.countP (· == .root)
  | [], b, i, l, k, e => by
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    rfl
  | t :: ts, b, i, l, k, e => by
    unfold Fmt.readItems at e
    cases h1 : Fmt.readItem f t b i with
    | none => rw [h1] at e; cases e
    | some xj =>
      obtain ⟨x, j⟩ := xj
      rw [h1] at e
      dsimp only at e
      cases h2 : Fmt.readItems f ts b j with
      | none => rw [h2] at e; cases e
      | some lk =>
        obtain ⟨l', k'⟩ := lk
        rw [h2] at e
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
        rw [readItem_roots f t b i x j h1 l', readItems_roots f ts b j l' k' h2,
          List.countP_cons]
        omega

theorem whole_roots (f : Fmt.Fld) (ts : List Fmt.Item) (msg : ByteArray) (l : List Fmt.ItemValue)
    (e : Fmt.whole (Fmt.readItems f ts) msg = some l) :
    (Fmt.rootsOf l).length = ts.countP (· == .root) := by
  unfold Fmt.whole at e
  cases h1 : Fmt.readItems f ts msg 0 with
  | none => rw [h1] at e; cases e
  | some lk =>
    obtain ⟨l', k⟩ := lk
    rw [h1] at e
    dsimp only at e
    split at e
    · obtain rfl := Option.some.inj e
      exact readItems_roots f ts msg 0 _ k h1
    · cases e

/-- Pairs of the two halves of a list of pairs. -/
theorem zip_fst_snd {α β : Type} : ∀ l : List (α × β), (l.map (·.1)).zip (l.map (·.2)) = l
  | [] => rfl
  | x :: l => by rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_fst_snd l]

/-- All rounds of a chain. -/
theorem rounds_roots (P : Fmt.Plan) : ∀ {rs : List (Fmt.Round × List Fmt.Stored)}
    {ros : List Fmt.RoundOut}, List.Forall₂ (RoundRead P) rs ros →
    (ros.flatMap fun x => Fmt.rootsOf x.vals).length =
      (rs.map fun r => r.1.items.countP (· == .root)).sum
  | _, _, .nil => rfl
  | r :: rs, ro :: ros, .cons h t => by
    rw [List.flatMap_cons, List.length_append, whole_roots P.field r.1.items ro.msg ro.vals h.vals,
      rounds_roots P t, List.map_cons, List.sum_cons]

/-- **A chain that the program's reader has read, under a description made from the rounds R**,
holds as many roots as R has items of the kind root. -/
theorem readChain_roots {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (hS : Params.describeWith g label st rand R ft = some S) (seen : Fmt.Seen) (b : ByteArray)
    (i : ℕ) (c : ChainRead) (e : readChain S seen b i = some (c.out, c.next)) :
    c.roots.length = Three.rootsIn R := by
  obtain ⟨-, H⟩ := readChain_read S seen b i c.out c.next e
  obtain ⟨f1, f2, -⟩ := describeWith_facts hS
  have hz : S.base.rounds.zip S.stored = R := by
    rw [f1, f2]
    exact zip_fst_snd R
  rw [hz] at H
  unfold ChainRead.roots Three.rootsIn
  rw [← rounds_roots _ H]
  exact congrArg List.length (List.flatMap_congr fun x _ => rootsT_eq x.vals)

/-- **The number of the third chain's first own tree.** -/
theorem firstTree₃ (R₁ R₂ R₃ : Params.Rounds) (first : ChainRead)
    (h : first.roots.length = Three.rootsIn R₁) :
    Proof.secondFirstTree first = Three.first₃ (Three.Whole.of R₁ R₂ R₃).t₁ := by
  show first.roots.length + 1 = Three.rootsIn R₁ + 1
  rw [h]

end OnBytes.Maker
