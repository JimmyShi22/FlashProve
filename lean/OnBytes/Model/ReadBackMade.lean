-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/ReadBackMade.lean: the plans that the program reads back from the parameter bytes of
the seven chains are the plans that `configure` has made, where these fit the format's words.

`Params.configure` makes a plan for each of the seven chains (a key's three, an entry's one, a
proof's three) and spells each chain's parameter bytes from its plan, the digest that it was given
and the chain's items (`configure_bytes`). `configure_at` (OnBytes/Tie/EntryPlanAtCfg.lean) says the
like at every digest, with its own names for the lists of items; this file does not import it. The
program reads these bytes back (`KeyChains.read`, `Link.read`, `ProofChains.read`,
OnBytes/Params/Chains.lean). The bounds on a chain's rounds from a plan that holds
(OnBytes/Slice/KeyTestsEntries.lean [not in this library] and the files beside it; so here read: not
proved in this library) speak of the made plans' entries. This
file ties the two, under one condition on the made plans: where a made plan fits the format's words
(`Fmt.Plan.fit`), the plan that the chain's reader returns is the made plan, whole: field, salt,
nonce, bytes of a listed position, answers, the word `saved` and the entries (`key_read_made`,
`entry_read_made`, `proof_read_made`, by `Given.read_plan`, OnBytes/Params/ReadBackPlan.lean).
`key_read_rounds` says it in the terms that a key's three runs read: the rounds of each chain
(`Given.rounds`) and the number of answers.

Main definitions: `madeLinItems`, `madeEntryItems`, `madeFirstItems`.
Main theorems: `configure_bytes`, `oneTimeItems_names`, `madeLinItems_names`,
`madeEntryItems_names`, `madeFirstItems_names`, `KeyChains.read_three`, `ProofChains.read_three`,
`key_read_made`, `key_read_rounds`, `entry_read_made`, `proof_read_made`.
What is not claimed: that the made plans fit: that is a hypothesis, for each plan. `configure` has
no test of it as a whole (the head of OnBytes/Params/ReadBackPlan.lean says which words the planner
bounds), and no theorem says it of the planner's plans, but for the entry's plan at two sets of
typed lines (`record_entry_fit` and `small_record_entry_fit`, OnBytes/Model/FitRecord.lean and
FitRecordSmall.lean). It does not follow from a yes of `configure` alone: the bytes of a
listed position are the line `listed`, which `configure` tests only where it is below 8, while the
reader of a parameter file admits 0 to 8. Run on the small example's lines with `listed` put to 2 ^
64, `configure` says yes and none of the seven plans fits; that is a run of Lean's interpreter, kept
in no file of this tree, and no theorem. Nothing on the plan that is read back where a made plan
does not fit. That `configure` says yes or that a reader returns a value. Nothing on the items that
are read back beside the plan (codes, shapes, notices): that they are those of the sizes is not
shown here; for the shape of the stored tables see OnBytes/Model/VerifyShape.lean. The four lemmas
on the items' names serve no theorem of this file: they are what `Given.read_items`
(OnBytes/Params/ReadBackLaws.lean) asks. The rounds of a chain are the plan's entries but for the
entry of a table's own sample (`Fmt.Plan.rounds`): of a key's one-time chain under a table with such
a sample the rounds are not all the entries. For a proof's chains and an entry's chain no such
statement on rounds and answers is made. `key_read_rounds` asks the whole of `Fmt.Plan.fit`, though
its clauses on rounds read the entries alone. For proofs only; the program, that is the Lean port
built from OnBytes/, does not import this file.

-/
import OnBytes.Model.VerifyDigest
import OnBytes.Params.ReadBackPlan
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- The two items of a shared chain, and the first two of a proof's first chain. -/
def madeLinItems (codes : Codes) (S : LinShape) : List (String × ByteArray) :=
  [("codes", spellCodes codes), ("the test on the table", spellLin S)]

/-- The items of an entry's chain. -/
def madeEntryItems (z : Sized) : List (String × ByteArray) :=
  [("codes", spellCodes z.entryCodes), ("the link", spellLink z.link.shape)]

/-- The items of a proof's first chain. -/
def madeFirstItems (l : Lines) (x : Shapes) (z : Sized) : List (String × ByteArray) :=
  madeLinItems z.proof.codes z.proof.batch.shape ++
    [("request's shape", spellReq z.proof.request), ("layout", spellLayout x.layout),
     ("links' identifiers", spellWords x.identifiers),
     ("pending rows", spellWord x.sub.pendingRows),
     ("binding tree", spellBinding ⟨clog2 l.slots, z.set.saltBytes⟩)]

/-- **What `configure` spells**: the parameter bytes of each of the seven chains are spelled from
the made plan of that chain, the digest, and the chain's items. -/
theorem configure_bytes {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    ∃ P1 P2 P3 F S2 S3, made.key = [P1, P2, P3] ∧ made.proof = [F, S2, S3] ∧
      made.keyOneTime = paramsBytes P1.plan cfg (Plan.oneTimeItems made.sized.key) ∧
      made.keyShared = paramsBytes P2.plan cfg
        (madeLinItems made.sized.key.codes made.sized.key.once.shape) ∧
      made.keySecond = paramsBytes P3.plan cfg [] ∧
      made.entryLink = paramsBytes made.entry.plan cfg (madeEntryItems made.sized) ∧
      made.first = paramsBytes F.plan cfg (madeFirstItems l x made.sized) ∧
      made.shared = paramsBytes S2.plan cfg
        (madeLinItems made.sized.proof.codes made.sized.proof.batch.shape) ∧
      made.second = paramsBytes S3.plan cfg [] := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, hp, h⟩ := exc_bind h
  obtain ⟨P1, h1, h⟩ := exc_bind h
  obtain ⟨P2, h2, h⟩ := exc_bind h
  obtain ⟨P3, h3, h⟩ := exc_bind h
  obtain ⟨entry, he, h⟩ := exc_bind h
  unfold proofPlans at hp
  obtain ⟨F, _, hp⟩ := exc_bind hp
  obtain ⟨S2, _, hp⟩ := exc_bind hp
  obtain ⟨S3, _, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨_, _, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  exact ⟨P1, P2, P3, F, S2, S3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The names of the items of a key's one-time chain are within the format's rule for names; the
next three lemmas say it of the other chains' items. -/
theorem oneTimeItems_names (z : Plan.KeySized) : ∀ y ∈ Plan.oneTimeItems z, okName y.1 = true := by
  intro y hy
  simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

theorem madeLinItems_names (codes : Codes) (S : LinShape) :
    ∀ y ∈ madeLinItems codes S, okName y.1 = true := by
  intro y hy
  simp only [madeLinItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> dsimp only <;> decide

theorem madeEntryItems_names (z : Sized) : ∀ y ∈ madeEntryItems z, okName y.1 = true := by
  intro y hy
  simp only [madeEntryItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> dsimp only <;> decide

theorem madeFirstItems_names (l : Lines) (x : Shapes) (z : Sized) :
    ∀ y ∈ madeFirstItems l x z, okName y.1 = true := by
  intro y hy
  simp only [madeFirstItems, madeLinItems, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- What `KeyChains.read` returns holds what the three readers return; and the plans of its shared
chain and second chain have no entry for a table's own sample. -/
theorem KeyChains.read_three {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) :
    OneTime.read a = some k.oneTime ∧ Shared.read b = some k.shared ∧
      Second.read c = some k.second ∧ k.shared.given.record = none ∧
      k.second.given.record = none := by
  unfold KeyChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, hz, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    exact ⟨hx, hy, hz, hc.1.2, hc.2⟩
  · cases h

/-- The same for a proof's three chains. -/
theorem ProofChains.read_three {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) :
    First.read a = some k.first ∧ Shared.read b = some k.shared ∧
      Second.read c = some k.second ∧ k.shared.given.record = none ∧
      k.second.given.record = none := by
  unfold ProofChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, hz, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    exact ⟨hx, hy, hz, hc.1.2, hc.2⟩
  · cases h

section
variable {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}

/-- **A key's three plans as read back are the plans as made**, whole, where the made plans fit the
format's words (`Fmt.Plan.fit`). -/
theorem key_read_made (h : configure l x cfg bits = .ok made) {k : KeyChains}
    (hk : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some k)
    (hf : ∀ P ∈ made.key, P.plan.fit = true) {P1 P2 P3 : Planned}
    (hm : made.key = [P1, P2, P3]) :
    k.oneTime.given.plan = P1.plan ∧ k.shared.given.plan = P2.plan ∧
      k.second.given.plan = P3.plan := by
  obtain ⟨Q1, Q2, Q3, _, _, _, hq, _, e1, e2, e3, _, _, _, _⟩ := configure_bytes h
  rw [hm] at hq hf
  obtain ⟨rfl, rfl, rfl⟩ : P1 = Q1 ∧ P2 = Q2 ∧ P3 = Q3 := by
    simpa using hq
  obtain ⟨r1, r2, r3, _, _⟩ := KeyChains.read_three hk
  have g1 := OneTime.read_given r1
  have g2 := Shared.read_given r2
  have g3 := Second.read_given r3
  rw [e1] at g1
  rw [e2] at g2
  rw [e3] at g3
  exact ⟨Given.read_plan (hf P1 (by simp)) g1, Given.read_plan (hf P2 (by simp)) g2,
    Given.read_plan (hf P3 (by simp)) g3⟩

/-- **The same for what a key's three runs start from.** The rounds of the shared chain and of the
second chain as read back are the made plans' entries. The rounds of the one-time chain are the made
plan's entries but for the entry of a table's own sample (`Fmt.Plan.rounds`): all of them where the
made plan has no such entry. The number of answers in each of the three plans is that of the setting
that the lines fix (`settingOf`). -/
theorem key_read_rounds (h : configure l x cfg bits = .ok made) {k : KeyChains}
    (hk : KeyChains.read made.keyOneTime made.keyShared made.keySecond = some k)
    (hf : ∀ P ∈ made.key, P.plan.fit = true) {P1 P2 P3 : Planned}
    (hm : made.key = [P1, P2, P3]) :
    k.oneTime.given.rounds = P1.plan.rounds ∧
      ((P1.plan.entries.find? fun e => e.name == recordName) = none →
        k.oneTime.given.rounds = P1.plan.entries) ∧
      k.shared.given.rounds = P2.plan.entries ∧ k.second.given.rounds = P3.plan.entries ∧
      k.oneTime.given.plan.samples = (settingOf l).samples ∧
      k.shared.given.plan.samples = (settingOf l).samples ∧
      k.second.given.plan.samples = (settingOf l).samples := by
  obtain ⟨e1, e2, e3⟩ := key_read_made h hk hf hm
  obtain ⟨_, _, _, n2, n3⟩ := KeyChains.read_three hk
  obtain ⟨_, _, Q1, Q2, Q3, _, _, hq, _, _, _, _, _, _, _, _, _, _, p1, p2, p3, _⟩ :=
    configure_key_is h
  rw [hm] at hq
  obtain ⟨rfl, rfl, rfl⟩ : P1 = Q1 ∧ P2 = Q2 ∧ P3 = Q3 := by
    simpa using hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show k.oneTime.given.plan.rounds = _
    rw [e1]
  · intro n1
    show k.oneTime.given.plan.rounds = _
    rw [e1, rounds_of_noRecord n1]
  · show k.shared.given.plan.rounds = _
    rw [rounds_of_noRecord n2, e2]
  · show k.second.given.plan.rounds = _
    rw [rounds_of_noRecord n3, e3]
  · rw [e1]
    show P1.set.samples = _
    rw [p1.set]
  · rw [e2]
    show P2.set.samples = _
    rw [p2.set]
  · rw [e3]
    show P3.set.samples = _
    rw [p3.set]

/-- **The entry's plan as read back is the plan as made**, where the made plan fits. -/
theorem entry_read_made (h : configure l x cfg bits = .ok made) {q : Link}
    (hq : Link.read made.entryLink = some q) (f : made.entry.plan.fit = true) :
    q.given.plan = made.entry.plan := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, e, _, _, _⟩ := configure_bytes h
  have g := Link.read_given hq
  rw [e] at g
  exact Given.read_plan f g

/-- **A proof's three plans as read back are the plans as made**, where the made plans fit. -/
theorem proof_read_made (h : configure l x cfg bits = .ok made) {k : ProofChains}
    (hk : ProofChains.read made.first made.shared made.second = some k)
    (hf : ∀ P ∈ made.proof, P.plan.fit = true) {F S2 S3 : Planned}
    (hm : made.proof = [F, S2, S3]) :
    k.first.given.plan = F.plan ∧ k.shared.given.plan = S2.plan ∧
      k.second.given.plan = S3.plan := by
  obtain ⟨_, _, _, Q1, Q2, Q3, _, hq, _, _, _, _, e1, e2, e3⟩ := configure_bytes h
  rw [hm] at hq hf
  obtain ⟨rfl, rfl, rfl⟩ : F = Q1 ∧ S2 = Q2 ∧ S3 = Q3 := by
    simpa using hq
  obtain ⟨r1, r2, r3, _, _⟩ := ProofChains.read_three hk
  have g1 := First.read_given r1
  have g2 := Shared.read_given r2
  have g3 := Second.read_given r3
  rw [e1] at g1
  rw [e2] at g2
  rw [e3] at g3
  exact ⟨Given.read_plan (hf F (by simp)) g1, Given.read_plan (hf S2 (by simp)) g2,
    Given.read_plan (hf S3 (by simp)) g3⟩

end

end OnBytes.Params

#print axioms OnBytes.Params.configure_bytes
#print axioms OnBytes.Params.key_read_made
#print axioms OnBytes.Params.key_read_rounds
#print axioms OnBytes.Params.entry_read_made
#print axioms OnBytes.Params.proof_read_made
