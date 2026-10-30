-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OpenedAt.lean: what a state's field `opened` (`Mid.opened`,
Honest/Frame.lean) holds, against what a `Before` holds for the reads of declared rounds
(`Before.opened`, `readsBefore`, Honest/Side.lean). Two definitions, and the law that rounds laid
behind a `Before` leave what it holds for these reads.

  1  `OpenedAt`   the hypothesis of `Good.exact` (Honest/Side.lean) on the field, under a name
     `HeldAt`   its half that names no state: the `Before` holds just these columns
     `OpenedAt.of_halves`   from that half and the field's value
  2  `Before.more`   a `Before` with further rounds behind
     `readsOf_cap`, `Before.drawnOf_more`, `readsBefore_more`, `Before.colAt_more`, `mapM_some_of`
     small lemmas
     `HeldAt.more`   **the law**
  3  `Laid.front_add`   what has been produced, with a stretch's rounds behind, is such a `Before`

By what. The law's way is that of a lemma `opened_cut` (not in the library) of the
authors of Honest/K12/LiveField.lean, which cuts a `Before` where this file lengthens one;
`readsOf_cap` is their `readsOf_take`. Their second premise, on the trees that the shorter `Before`
lists, is read here off `HeldAt`: a column that is held is held of a tree that is listed.

Limits.
  * `HeldAt.more` has a premise: the `Before` holds a challenge for each of the declared rounds,
    chain by chain. It is paid nowhere here; its callers carry it (`RowInv.drawn`,
    Honest/Law/Rule/RowHere.lean; `TieAt`, Honest/Law/Rule/OpenedStep.lean).
  * Nothing here says that `OpenedAt` or `HeldAt` holds at a run: Honest/Law/Rule/OpenedRun.lean.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartLaw
import Johnson.Desc.ProofFile.Honest.Gap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place OpenedColumn)

variable {W Y : Type}

/-! ## 1 The two definitions -/

/-- **The field is what the `Before` holds for the reads of `pre`**: to the sign the hypothesis of
`Good.exact` on the field. A definition, meant as a hypothesis. -/
def OpenedAt (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (m : Mid W Y) (f : Before) : Prop :=
  m.opened = f.opened (readsBefore pre f)

/-- The `Before` holds a column for each read of `pre` at the challenges that `f` lists (a round of
`pre` beyond them is dropped: `readsBefore`, Honest/Side.lean), and they are `c`. A definition,
meant as a hypothesis. -/
def HeldAt (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (f : Before) (c : List OpenedColumn) : Prop :=
  f.opened (readsBefore pre f) = some c

theorem OpenedAt.of_halves {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {m : Mid W Y}
    {f : Before} {c : List OpenedColumn} (hw : m.opened = some c) (hf : HeldAt pre f c) :
    OpenedAt pre m f := by
  unfold OpenedAt
  unfold HeldAt at hf
  rw [hw, hf]

/-! ## 2 Rounds laid behind -/

/-- The same with further rounds behind. The stored tables' columns stay. -/
def Before.more (f : Before) (l : List (Nat × Shown × Fmt.Drawn)) : Before :=
  { f with rounds := f.rounds ++ l }

/-- `readsOf` reads of its challenges no more than it has declared rounds. -/
theorem readsOf_cap (chain firstTree : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    readsOf chain firstTree stored tree ds Rs =
      readsOf chain firstTree stored tree ds (Rs.take ds.length)
  | [], _ => by simp [readsOf]
  | _ :: _, [] => by simp [readsOf]
  | d :: ds, R :: Rs => by
    rw [List.length_cons, List.take_succ_cons, readsOf, readsOf,
      readsOf_cap chain firstTree stored tree ds Rs]

/-- A chain's challenges in the longer `Before` begin with those in the shorter. -/
theorem Before.drawnOf_more (f : Before) (l : List (Nat × Shown × Fmt.Drawn)) (ch : Nat) :
    f.drawnOf ch <+: (f.more l).drawnOf ch := by
  unfold Before.drawnOf Before.more
  exact ((List.prefix_append _ _).filter _).map _

/-- `h1`: the shorter `Before` holds a challenge for each of the declared rounds, chain by chain. -/
theorem readsBefore_more (f : Before) (l : List (Nat × Shown × Fmt.Drawn))
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (h1 : ∀ x ∈ pre, x.2.2.length ≤ (f.drawnOf x.1).length) :
    readsBefore pre (f.more l) = readsBefore pre f := by
  unfold readsBefore
  refine List.flatMap_congr fun x hx => ?_
  obtain ⟨r, hr⟩ := f.drawnOf_more l x.1
  rw [readsOf_cap _ _ _ _ x.2.2 ((f.more l).drawnOf x.1),
    readsOf_cap _ _ _ _ x.2.2 (f.drawnOf x.1), ← hr,
    List.take_append_of_le_length (h1 x hx)]

/-- A column that the shorter `Before` holds for a read, the longer holds too. -/
theorem Before.colAt_more (f : Before) (l : List (Nat × Shown × Fmt.Drawn)) (q : Read) (c : OpenedColumn) :
    f.colAt q = some c → (f.more l).colAt q = some c := by
  unfold Before.colAt
  cases hi : q.item with
  | some i => exact id
  | none =>
    cases hs : q.src with
    | none => exact id
    | some p =>
      obtain ⟨ch, k⟩ := p
      show ((f.treeCols ch k).bind fun cols =>
          (cols.find? fun z => z.1 == q.pos).map fun z => ((q.key, q.pos, z.2) : OpenedColumn)) = some c →
        (((f.more l).treeCols ch k).bind fun cols =>
          (cols.find? fun z => z.1 == q.pos).map fun z => ((q.key, q.pos, z.2) : OpenedColumn)) = some c
      cases ht : f.treeCols ch k with
      | none =>
        intro h
        cases h
      | some cols =>
        have e : (f.more l).treeCols ch k = some cols := by
          unfold Before.treeCols at ht ⊢
          obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.1 ht
          obtain ⟨r, hr⟩ : (f.rounds.filter fun r => r.1 == ch) <+:
              ((f.more l).rounds.filter fun r => r.1 == ch) := (List.prefix_append _ _).filter _
          rw [← hr, List.flatMap_append, List.getElem?_append_left hk]
          exact ht
        rw [e]
        exact id

/-- Where one function answers wherever another does, and the same, so does `mapM`. -/
theorem mapM_some_of {α β : Type} (g g' : α → Option β)
    (hg : ∀ a b, g a = some b → g' a = some b) :
    ∀ (l : List α) (c : List β), l.mapM g = some c → l.mapM g' = some c
  | [], c, h => by
    rw [List.mapM_nil] at h ⊢
    exact h
  | a :: l, c, h => by
    rw [List.mapM_cons] at h ⊢
    cases ha : g a with
    | none =>
      rw [ha] at h
      cases h
    | some b =>
      rw [ha] at h
      cases hl : l.mapM g with
      | none =>
        rw [hl] at h
        cases h
      | some r =>
        rw [hl] at h
        rw [hg a b ha, mapM_some_of g g' hg l r hl]
        exact h

/-- **Rounds laid behind a `Before` leave what it holds for the reads of `pre`.** `h1`: as in
`readsBefore_more`. -/
theorem HeldAt.more {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {f : Before} {c : List OpenedColumn}
    (l : List (Nat × Shown × Fmt.Drawn))
    (h1 : ∀ x ∈ pre, x.2.2.length ≤ (f.drawnOf x.1).length) (h : HeldAt pre f c) :
    HeldAt pre (f.more l) c := by
  unfold HeldAt at h ⊢
  rw [readsBefore_more f l pre h1]
  unfold Before.opened at h ⊢
  exact mapM_some_of _ _ (fun q z => f.colAt_more l q z) _ _ h

/-! ## 3 What has been produced -/

/-- What a simulator of the chain is given, after one more stretch. -/
theorem Laid.front_add (L : Laid) (ch : Nat) (st : List (Nat × Nat × List UInt64))
    (a : List (Shown × Fmt.Drawn)) :
    (L.add ch a).front ch st = (L.front ch st).more (a.map fun z => (ch, z.1, z.2)) := by
  unfold Laid.add Laid.front Before.more
  by_cases h0 : (ch == 0) = true
  · simp [h0]
  · by_cases h1 : (ch == 1) = true
    · simp [h0, h1]
    · simp [h0, h1]

end ProofFile.Honest

#print axioms ProofFile.Honest.OpenedAt
#print axioms ProofFile.Honest.HeldAt
#print axioms ProofFile.Honest.OpenedAt.of_halves
#print axioms ProofFile.Honest.Before.more
#print axioms ProofFile.Honest.readsOf_cap
#print axioms ProofFile.Honest.Before.drawnOf_more
#print axioms ProofFile.Honest.readsBefore_more
#print axioms ProofFile.Honest.Before.colAt_more
#print axioms ProofFile.Honest.mapM_some_of
#print axioms ProofFile.Honest.HeldAt.more
#print axioms ProofFile.Honest.Laid.front_add
