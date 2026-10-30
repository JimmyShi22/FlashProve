-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/PlanListsConfigure.lean: from a yes of `configure` to the lists of a key's three chains
and of an entry's chain.

`configure` (OnBytes/Params/Configure.lean) sizes the three files, plans all chains and spells their
parameter bytes. OnBytes/Plan/PlanListsKey.lean and OnBytes/Params/PlanListsChains.lean say what a
plan is, given that the routine which makes it returned it. This file takes these hypotheses from
`configure`'s yes: the key's sizes are `keySized`'s; its three plans and the entry's are the
routines' own, under one setting, the lines', and the scope `.once`; the caller's bits are at most
the line `sec`. It also says what the sizes L hold that the plans of the test on the table read, and
which table a key's and a link's sizes hold.

Main theorems: `sized_key`, `configure_plans`, `configure_sec`, `configure_key_is`,
`linSizeOf_lines`, `linColumns_once`, `keySized_table`, `linkSized_table`.
What is not claimed: that `configure` says yes. Nothing on a proof's three chains. What
OnBytes/Plan/PlanListsKey.lean and OnBytes/Params/PlanListsChains.lean do not claim is not claimed
here. For proofs only; the program, that is the Lean port built from OnBytes/, does not import this
file.

-/
import OnBytes.Params.Configure
import OnBytes.Plan.PlanListsKeyMembers

set_option autoImplicit false

namespace OnBytes.Params

/-- If a step that stops on a condition, with the steps that follow it, returns a value, the
condition failed. -/
theorem exc_guard_not {ε β : Type} {c : Prop} [Decidable c] {e : ε} {next : PUnit → Except ε β}
    {b : β} (h : (if c then (throw e : Except ε PUnit) >>= next else pure PUnit.unit >>= next) =
      .ok b) : ¬ c := by
  intro hc
  rw [if_pos hc] at h
  cases h

/-- What `sized` returns holds the key's sizes that `keySized` makes. -/
theorem sized_key {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    Plan.keySized l x.ranges = some z.key := by
  unfold sized at h
  extract_lets at h
  replace h := exc_guard h
  obtain ⟨proof, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨key, hk, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨⟨link, codes⟩, _, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  exact orRefuse_ok hk

/-- The sizes that the plans of the test on the table read hold the lines' word on a one-time test
and their number of requests, and they name no further oracle message with a sample beside W
(`besideW` keeps its default, the empty list). The prover's message with W can hold more
(`linMessageW`, OnBytes/Iop/Lin.lean): the fresh mask of the own test's first fold, which has no
sample; and, where W and Omega differ in code (`ownSplitNeeded`), a split's message, which has one,
and which these sizes do not name. `linSized` writes one code for W and Omega; that is read off its
definition, and no theorem here states it. -/
theorem linSizeOf_lines {codes : Codes} {x : LinSized} {L : LinSize}
    (h : linSizeOf codes x = some L) :
    L.oneTime = x.lines.oneTime ∧ L.instances = x.lines.requests ∧ L.besideW = [] := by
  unfold linSizeOf at h
  extract_lets at h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- In a one-time test the number of columns is that at the one-time agreement. -/
theorem linColumns_once {s : Setting} {c : Scope} {T : TableSize} {x : LinSize}
    (h : x.oneTime = true) :
    linColumns s c T x = scopePositions s c (tableAnalysis s T).once.agree (Bound.ofWord 0) := by
  unfold linColumns
  simp [h]

/-- A link's sizes hold the table that they were made for. -/
theorem linkSized_table {s : Setting} {l : Lines} {T : TableSize} {codes c : Codes}
    {x : LinkSized} (h : linkSized s l T codes = some (x, c)) : x.table = T := by
  unfold linkSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨y, _, h⟩ := opt_bind h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- A key's sizes hold the table that follows from the lines. -/
theorem keySized_table {l : Lines} {shape : Plan.Shape} {z : Plan.KeySized}
    (h : Plan.keySized l shape = some z) :
    deriveTable (settingOf l) l = some z.once.table := by
  unfold Plan.keySized at h
  extract_lets at h
  obtain ⟨T, hT, h⟩ := opt_bind h
  obtain ⟨L, _, h⟩ := opt_bind h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, _, h⟩ := opt_bind h
  cases h
  exact hT.trans (congrArg some (linSized_table ho).symm)

/-- What `configure` returns: the sizes are `sized`'s; the key's three plans and the entry's plan
are what the four routines returned on these sizes; and the caller's bits are at most the line
`sec`. -/
theorem configure_plans {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) :
    sized l x = .ok made.sized ∧ bits ≤ l.sec ∧ ∃ P1 P2 P3, made.key = [P1, P2, P3] ∧
      Plan.oneTimePlan made.sized.key = .ok P1 ∧
      sharedPlan made.sized.set made.sized.key.codes made.sized.key.once = .ok P2 ∧
      secondPlan made.sized.set made.sized.key.once = .ok P3 ∧
      finishHeld made.sized.set .once (linkPlan made.sized.link) = .ok made.entry := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨P1, h1, h⟩ := exc_bind h
  obtain ⟨P2, h2, h⟩ := exc_bind h
  obtain ⟨P3, h3, h⟩ := exc_bind h
  obtain ⟨entry, he, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    have hs := exc_guard_not h
    replace h := exc_guard h
    cases h
    exact ⟨hz, Nat.not_lt.1 hs, P1, P2, P3, rfl, h1, h2, h3, he⟩
  · cases h

/-- The caller's bits are at most the line `sec`, which is the setting's target. -/
theorem configure_sec {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) : bits ≤ (settingOf l).target :=
  (configure_plans h).2.1

/-- From `configure`'s yes: the plans of a key's three chains and of an entry's chain against their
lists, all under the lines' setting and the scope `.once`. n: the trees of the message of the
multiplicities. L: the sizes that the plans of the test on the table read, the same for the one-time
chain and the shared chain; they are a one-time test's, of one request. Kept besides: the key's
sizes are `keySized`'s; `sizedFits`; the numbers of columns are those in the shapes; the second
chain's test has two stages at least. -/
theorem configure_key_is {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    Plan.keySized l x.ranges = some made.sized.key ∧ made.sized.key.set = settingOf l ∧
      ∃ P1 P2 P3 n L, made.key = [P1, P2, P3] ∧
      treesOf made.sized.key.codes (Wf.messageOf made.sized.key.ranges.x) = some n ∧
      linSizeOf made.sized.key.codes made.sized.key.once = some L ∧
      L.oneTime = true ∧ L.instances = 1 ∧ L.besideW = [] ∧
      Plan.sizedFits made.sized.key.codes made.sized.key.ranges.x.stages
        made.sized.key.ranges.test.stages = true ∧
      linColumns (settingOf l) .once made.sized.key.once.table L =
        made.sized.key.once.shape.fold.columns ∧
      2 ≤ made.sized.key.once.own.stages.length ∧
      linkColumnsFirst (settingOf l) .once made.sized.link.table =
        made.sized.link.shape.columnsFirst ∧
      linkColumnsFurther (settingOf l) .once made.sized.link.table =
        made.sized.link.shape.columnsFurther ∧
      PlanIs P1 (settingOf l) .once (Plan.oneTimeListAt made.sized.key n L) ∧
      PlanIs P2 (settingOf l) .once
        (linSharedTests (settingOf l) .once made.sized.key.once L ++ [sealRound]) ∧
      PlanIs P3 (settingOf l) .once (secondChainList (settingOf l) .once made.sized.key.once) ∧
      PlanIs made.entry (settingOf l) .once
        (entryChainList (settingOf l) .once made.sized.link) := by
  obtain ⟨hz, _, P1, P2, P3, hk, h1, h2, h3, he⟩ := configure_plans h
  have hkey := sized_key hz
  have hset : made.sized.set = settingOf l := (sized_link hz).1
  obtain ⟨hot, hks⟩ := Plan.keySized_oneTime hkey
  rw [hset] at h2 h3 he
  obtain ⟨n, L, hn, hL, hf, p1⟩ := Plan.oneTimePlan_is h1
  obtain ⟨L', hL', hcol, p2⟩ := Plan.keyShared_is hkey h2
  have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
  rw [hLL] at p2 hcol
  rw [hks] at p1
  obtain ⟨p3, h2s⟩ := Plan.keySecond_is hkey h3
  obtain ⟨p4, hc1, hc2⟩ := linkPlan_is he
  obtain ⟨l1, l2, l3⟩ := linSizeOf_lines hL
  exact ⟨hkey, hks, P1, P2, P3, n, L, hk, hn, hL, l1.trans hot,
    l2.trans (Plan.keySized_requests hkey), l3, hf, hcol, h2s, hc1, hc2, p1, p2, p3, p4⟩

end OnBytes.Params

#print axioms OnBytes.Params.sized_key
#print axioms OnBytes.Params.linSizeOf_lines
#print axioms OnBytes.Params.linColumns_once
#print axioms OnBytes.Params.linkSized_table
#print axioms OnBytes.Params.keySized_table
#print axioms OnBytes.Params.configure_plans
#print axioms OnBytes.Params.configure_sec
#print axioms OnBytes.Params.configure_key_is
