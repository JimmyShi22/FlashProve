-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/PlanListsKeyMembers.lean: a key's three chains under the scope of a one-time test, and
the few different rounds of which their lists are made.

OnBytes/Params/PlanListsChains.lean has the plans of a shared chain and of a second chain under the
scope `if x.lines.oneTime then .once else …`. For the sizes of a key that scope is `.once`
(`keySized_oneTime`, OnBytes/Plan/PlanListsKey.lean); this file states the two plans so.
OnBytes/Params/PlanListsMembers.lean says which descriptions can be members of a sumcheck's, a
tree's, a lookup's list and of a fold's rounds. This file goes on to a fold, the stages, a proximity
test, the proof of the ranges and a key's one-time chain as a whole.

Main theorems: `keyShared_is`, `keySecond_is`, `mem_foldList`, `mem_stagesList`,
`mem_stagesList_at`, `mem_ioppList`, `forall_ioppList`, `forall_ioppList_at`, `mem_linSharedTests`,
`mem_entryChainList`, `mem_rangesListAt`, `mem_oneTimeListAt`.
What is not claimed: that each of the named descriptions is a member. That the plans are finished or
hold: that is a hypothesis. The laws go one step down each; only `forall_ioppList` goes from a
test's list to its few descriptions at once. A second chain's list is an `ioppList` by its
definition. The lists of a sending, a code switch, a last step and a record are closed lists of two,
two, two and at most one member, and have no law. For proofs only; the program, that is the Lean
port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.PlanListsMembers
import OnBytes.Plan.PlanListsKey

set_option autoImplicit false

namespace OnBytes.Plan

open OnBytes.Params

/-- The plan of a key's shared chain, under the scope `.once`. -/
theorem keyShared_is {l : Lines} {shape : Shape} {z : KeySized} {s : Setting} {P : Planned}
    (hz : keySized l shape = some z) (h : sharedPlan s z.codes z.once = .ok P) :
    ∃ L, linSizeOf z.codes z.once = some L ∧
      linColumns s .once z.once.table L = z.once.shape.fold.columns ∧
      PlanIs P s .once (linSharedTests s .once z.once L ++ [sealRound]) := by
  have h1 := sharedPlan_is h
  rw [(keySized_oneTime hz).1] at h1
  exact h1

/-- The plan of a key's second chain, under the scope `.once`; its test has two stages at least. -/
theorem keySecond_is {l : Lines} {shape : Shape} {z : KeySized} {s : Setting} {P : Planned}
    (hz : keySized l shape = some z) (h : secondPlan s z.once = .ok P) :
    PlanIs P s .once (secondChainList s .once z.once) ∧ 2 ≤ z.once.own.stages.length := by
  have h1 := secondPlan_is h
  rw [(keySized_oneTime hz).1] at h1
  exact h1

/-- The members of a fold's list: its first round, and rounds 1 to k. -/
theorem mem_foldList {s : Setting} {g : GroupSize} {roots : Nat} {y : RoundSpec}
    (h : y ∈ foldList s g roots) :
    y = foldFirst s g roots ∨ ∃ i, 1 ≤ i ∧ i < 1 + g.k ∧ y = foldRound s g (analysis s g) i := by
  unfold foldList at h
  rcases List.mem_cons.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (mem_foldFromList h)

/-- The members of the list of a test's stages: a member of the fold of some stage, at some number
of roots; or of the code switch from some stage to some stage; or of the last step at some stage and
some number of roots. That the second stage follows the first, that the last step is the last
stage's, and which roots, is not kept here; `mem_stagesList_at` keeps the places. -/
theorem mem_stagesList {s : Setting} {c : Scope} {fm : Nat} {mr : Bool} {w : RoundSpec} :
    ∀ {first : Bool} {st : List StageSize}, w ∈ stagesList s c fm mr first st →
      (∃ x ∈ st, ∃ roots, w ∈ foldList s x.g roots) ∨
      (∃ x ∈ st, ∃ y ∈ st, w ∈ csList s c x.g y.g (stageCubeBits y.g) 1
        (x.g.slots + (if x.g.hasMask then 2 else 0)) 1) ∨
      (∃ x ∈ st, ∃ roots, w ∈ baseList s c x.g roots)
  | _, [], h => by
      unfold stagesList at h
      cases h
  | _, [x], h => by
      unfold stagesList at h
      exact Or.inr (Or.inr ⟨x, List.mem_singleton.2 rfl, _, h⟩)
  | first, x :: y :: rest, h => by
      unfold stagesList at h
      rcases List.mem_append.1 h with h | h
      · exact Or.inl ⟨x, List.mem_cons_self, _, h⟩
      rcases List.mem_append.1 h with h | h
      · exact Or.inr (Or.inl ⟨x, List.mem_cons_self, y,
          List.mem_cons_of_mem _ List.mem_cons_self, h⟩)
      · rcases mem_stagesList h with ⟨a, ha, r, hw⟩ | ⟨a, ha, b, hb, hw⟩ | ⟨a, ha, r, hw⟩
        · exact Or.inl ⟨a, List.mem_cons_of_mem _ ha, r, hw⟩
        · exact Or.inr (Or.inl ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, hw⟩)
        · exact Or.inr (Or.inr ⟨a, List.mem_cons_of_mem _ ha, r, hw⟩)

/-- The same with the places: a member of the fold, at some number of roots, of a stage x that
another stage y follows, or of the code switch from x to y; or of the last step at the last stage,
at its own number of roots. Which roots a fold has is not kept: `stagesList` has fm at the first
stage and, after it, the last step's number. -/
theorem mem_stagesList_at {s : Setting} {c : Scope} {fm : Nat} {mr : Bool} {w : RoundSpec} :
    ∀ {first : Bool} {st : List StageSize}, w ∈ stagesList s c fm mr first st →
      (∃ pre x y post, st = pre ++ x :: y :: post ∧
        ((∃ roots, w ∈ foldList s x.g roots) ∨
          w ∈ csList s c x.g y.g (stageCubeBits y.g) 1
            (x.g.slots + (if x.g.hasMask then 2 else 0)) 1)) ∨
      (∃ pre x, st = pre ++ [x] ∧ w ∈ baseList s c x.g (if mr then 0 else 1))
  | _, [], h => by
      unfold stagesList at h
      cases h
  | _, [x], h => by
      unfold stagesList at h
      exact Or.inr ⟨[], x, rfl, h⟩
  | first, x :: y :: rest, h => by
      unfold stagesList at h
      rcases List.mem_append.1 h with h | h
      · exact Or.inl ⟨[], x, y, rest, rfl, Or.inl ⟨_, h⟩⟩
      rcases List.mem_append.1 h with h | h
      · exact Or.inl ⟨[], x, y, rest, rfl, Or.inr h⟩
      · rcases mem_stagesList_at h with ⟨pre, a, b, post, e, hw⟩ | ⟨pre, a, e, hw⟩
        · exact Or.inl ⟨x :: pre, a, b, post, congrArg (List.cons x) e, hw⟩
        · exact Or.inr ⟨x :: pre, a, congrArg (List.cons x) e, hw⟩

/-- The members of a proximity test's list: the round that batches, and those of its stages. -/
theorem mem_ioppList {s : Setting} {c : Scope} {st : List StageSize} {rows fm : Nat} {mr : Bool}
    {w : RoundSpec} (h : w ∈ ioppList s c st rows fm mr) :
    w = batRound s (st.take 1 |>.map (·.g)) rows ∨ w ∈ stagesList s c fm mr true st := by
  unfold ioppList at h
  exact List.mem_cons.1 h

/-- What holds of the few holds of every member of a proximity test's list: the round that batches;
each stage's first round of a fold, at any number of roots; its rounds 1 to k; the two rounds of a
code switch between any two of its stages; the two rounds of a last step at any stage and any number
of roots. For a Q that needs the places: `forall_ioppList_at`. -/
theorem forall_ioppList {s : Setting} {c : Scope} {st : List StageSize} {rows fm : Nat} {mr : Bool}
    {Q : RoundSpec → Prop} (hb : Q (batRound s (st.take 1 |>.map (·.g)) rows))
    (h1 : ∀ x ∈ st, ∀ roots, Q (foldFirst s x.g roots))
    (h2 : ∀ x ∈ st, ∀ i, 1 ≤ i → i < 1 + x.g.k → Q (foldRound s x.g (analysis s x.g) i))
    (h3 : ∀ x ∈ st, ∀ y ∈ st, ∀ w ∈ csList s c x.g y.g (stageCubeBits y.g) 1
      (x.g.slots + (if x.g.hasMask then 2 else 0)) 1, Q w)
    (h4 : ∀ x ∈ st, ∀ roots, ∀ w ∈ baseList s c x.g roots, Q w) :
    ∀ w ∈ ioppList s c st rows fm mr, Q w := by
  intro w hw
  rcases mem_ioppList hw with rfl | hw
  · exact hb
  rcases mem_stagesList hw with ⟨x, hx, r, hw⟩ | ⟨x, hx, y, hy, hw⟩ | ⟨x, hx, r, hw⟩
  · rcases mem_foldList hw with rfl | ⟨i, hi, hk, rfl⟩
    · exact h1 x hx r
    · exact h2 x hx i hi hk
  · exact h3 x hx y hy w hw
  · exact h4 x hx r w hw

/-- The same with the places: asked of a fold and a code switch only at a stage x that a stage y
follows, and of the last step only at the last stage and its own number of roots. -/
theorem forall_ioppList_at {s : Setting} {c : Scope} {st : List StageSize} {rows fm : Nat}
    {mr : Bool} {Q : RoundSpec → Prop} (hb : Q (batRound s (st.take 1 |>.map (·.g)) rows))
    (h1 : ∀ pre x y post, st = pre ++ x :: y :: post → ∀ roots, Q (foldFirst s x.g roots))
    (h2 : ∀ pre x y post, st = pre ++ x :: y :: post → ∀ i, 1 ≤ i → i < 1 + x.g.k →
      Q (foldRound s x.g (analysis s x.g) i))
    (h3 : ∀ pre x y post, st = pre ++ x :: y :: post →
      ∀ w ∈ csList s c x.g y.g (stageCubeBits y.g) 1
        (x.g.slots + (if x.g.hasMask then 2 else 0)) 1, Q w)
    (h4 : ∀ pre x, st = pre ++ [x] → ∀ w ∈ baseList s c x.g (if mr then 0 else 1), Q w) :
    ∀ w ∈ ioppList s c st rows fm mr, Q w := by
  intro w hw
  rcases mem_ioppList hw with rfl | hw
  · exact hb
  rcases mem_stagesList_at hw with ⟨pre, x, y, post, e, ⟨r, hw⟩ | hw⟩ | ⟨pre, x, e, hw⟩
  · rcases mem_foldList hw with rfl | ⟨i, hi, hk, rfl⟩
    · exact h1 pre x y post e r
    · exact h2 pre x y post e i hi hk
  · exact h3 pre x y post e w hw
  · exact h4 pre x e w hw

/-- The members of the list of the test on the table on a shared chain, with its proximity tests. -/
theorem mem_linSharedTests {s : Setting} {c : Scope} {x : LinSized} {L : LinSize} {w : RoundSpec}
    (h : w ∈ linSharedTests s c x L) :
    w ∈ linSharedList s c x.table L ∨ w = .silent "SPLIT" (24 * 1) 0 ∨
      w ∈ ioppList s c x.folded.stages
        (x.shape.fold.index.answers + linColumns s c x.table L + 1 + 2 * s.samples)
        (if x.shape.masksAhead then 0 else 1) x.shape.choice.masksRide ∨
      (x.shape.sharedSplitNeeded = true ∧
        w ∈ ioppList s c x.omega.stages (1 + 2 * s.samples) 1 x.shape.choice.masksRide) := by
  unfold linSharedTests at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  split at h
  · rename_i hs
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr (Or.inl h)
    rcases List.mem_append.1 h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨hs, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- The members of the list of an entry's chain. -/
theorem mem_entryChainList {s : Setting} {c : Scope} {x : LinkSized} {w : RoundSpec}
    (h : w ∈ entryChainList s c x) :
    w ∈ recordList s x.table ∨
      w ∈ linkBlockList s c x.table
        ⟨clog2 x.shape.rows + clog2 x.linked.group.main.ell, [x.linked.group]⟩ ∨
      w ∈ ioppList s c x.linked.stages
        (2 * x.shape.table.answers + linkColumnsFirst s c x.table +
          linkColumnsFurther s c x.table + 1 + 2 * s.samples)
        (if x.shape.masksAhead then 0 else 1) x.shape.choice.masksRide := by
  unfold entryChainList at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  rcases List.mem_append.1 h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The members of the list of the proof of the ranges: the two rounds of the sending; for a lookup,
one of its thirteen descriptions; those of the proximity test; those of the joining. -/
theorem mem_rangesListAt {s : Setting} {c : Scope} {codes : Codes} {z : RangesSized} {n : Nat}
    {w : RoundSpec} (h : w ∈ rangesListAt s c codes z n) :
    w ∈ sendList s [⟨cubeBitsOf codes z.x.message.shape, [z.test.first]⟩] n ∨
      (∃ x ∈ lookupSizes z.x z.matrix, w ∈ lookupMembers s x) ∨
      w ∈ ioppList s c z.test.stages (Wf.rowsBatched z.x z.matrix)
        (if z.x.choice.masksRide then 0 else 1) z.x.choice.masksRide ∨
      (1 < z.pending ∧
        (w = .said "BAT-sigma" .field (powersError s z.pending)
            { drawE := 1, rows := z.pending, priced := .asSaid } 0 0 0 ∨
          w = pscEpsilon s ∨ w = pscVariable s 3)) := by
  unfold rangesListAt at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨l', hl, hw⟩ := List.mem_flatten.1 h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    exact Or.inr (Or.inl ⟨x, hx, mem_lookupList hw⟩)
  rcases List.mem_append.1 h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · split at h
    · rename_i hp
      refine Or.inr (Or.inr (Or.inr ⟨hp, ?_⟩))
      rcases List.mem_cons.1 h with h | h
      · exact Or.inl h
      · rcases mem_pscList h with h | ⟨g, hg, h⟩ | ⟨hw, _⟩
        · exact Or.inr (Or.inl h)
        · rw [(List.mem_replicate.1 hg).2] at h
          exact Or.inr (Or.inr h)
        · cases hw
    · cases h

/-- The members of the list of a key's one-time chain, part by part. -/
theorem mem_oneTimeListAt {z : KeySized} {n : Nat} {L : LinSize} {w : RoundSpec}
    (h : w ∈ oneTimeListAt z n L) :
    w ∈ recordList z.set z.once.table ∨
      w ∈ sendList z.set [⟨cubeBitsOf z.codes z.once.input.shape, [z.once.own.first]⟩] 1 ∨
      w ∈ rangesListAt z.set .once z.codes z.ranges n ∨
      w ∈ sendList z.set (L.w :: L.besideW) L.rootsW ∨ w = sealRound := by
  unfold oneTimeListAt at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  rcases List.mem_append.1 h with h | h
  · exact Or.inr (Or.inl h)
  rcases List.mem_append.1 h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  rcases List.mem_append.1 h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_singleton.1 h))))

end OnBytes.Plan

#print axioms OnBytes.Plan.keyShared_is
#print axioms OnBytes.Plan.keySecond_is
#print axioms OnBytes.Plan.mem_stagesList
#print axioms OnBytes.Plan.mem_stagesList_at
#print axioms OnBytes.Plan.forall_ioppList
#print axioms OnBytes.Plan.forall_ioppList_at
#print axioms OnBytes.Plan.mem_linSharedTests
#print axioms OnBytes.Plan.mem_entryChainList
#print axioms OnBytes.Plan.mem_rangesListAt
#print axioms OnBytes.Plan.mem_oneTimeListAt
