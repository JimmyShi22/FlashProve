-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/PlansPriced.lean: the plans from which a file's rounds are declared are the planner's own
plans, whose rounds bear its numbers for their errors, where these plans fit the format's words.

THE THEOREMS HERE ARE TOOLS: they hold at all public files, and name no description of the protocol
and no value of the release. No line under Owed/ [not in this library] is to be laid on them.

Why. What the planner makes of the three public files (`madeOf`, Johnson/G/RoundsOfPlan.lean) holds
each chain's plan twice: as the planner's record, whose rounds bear the planner's numbers for their
errors (`m.p.chains.made`), and as the plan that is read back from the chain's parameter bytes
(`given.plan`). The declared rounds, and so the rounds' data, are made of the second. A law on the
planner's numbers speaks of the first.

Definitions, statements and proofs.
  `KeyPlansPriced m K₁ K₂ K₃`: three equations between plans:
      m.p.chains.key.oneTime.given.plan = K₁.plan, m.p.chains.key.shared.given.plan = K₂.plan,
      m.p.chains.key.second.given.plan = K₃.plan.
  `ProofPlansPriced m F₁ F₂ F₃`: the like for m.p.chains.proof.first, .shared, .second.
  `EntryPlanPriced m`: m.p.chains.link.given.plan = m.p.chains.made.entry.plan.
  In the first two the records K₁ … F₃ are letters of the planner's type of records; the definitions
  say nothing of their numbers.
  `madeOf_chains`: what `madeOf` returns holds chains that `chainsOf` has returned.
  `chainsOf_made`: what `chainsOf` returns holds what `configure` has made, and the key's, the
    entry's and the proof's chains as read back from its parameter bytes.
  `keyPlansPriced_of_fit`, `proofPlansPriced_of_fit`: if `madeOf` returns m, the planner's record
    has the three plans K₁, K₂, K₃ for the key (F₁, F₂, F₃ for the proof), and the public test
    `Desc.keyFit` (`Desc.proofFit`, Johnson/Desc/FitOk.lean) says yes of it, then the three
    equations hold. By `key_read_made`, `proof_read_made` (OnBytes/Model/ReadBackMade.lean).
  `entryPlanPriced_of_fit`: the like for the entry file's chain, from `Desc.entryFit`, by
    `entry_read_made`.

What of OnBytes/Model/ is used. All of it is a function of the public files alone: the making of the
plans and the reading back of their parameter bytes. Nothing that reads a proof, a key file or an
entry file is named.
  Named in statements: `Model.Verify.chainsOf`, `Model.Verify.Chains`
    (OnBytes/Model/VerifyChains.lean), `Model.Verify.Public` (OnBytes/Model/VerifyPublic.lean); and,
    through `m.p` and `m.p.chains`, the records `Model.Verify.Planned` (OnBytes/Model/Verify.lean)
    and `Model.Verify.Chains`.
  Unfolded in proofs: `Model.Verify.chainsOf`; `Model.Verify.planned` (OnBytes/Model/Verify.lean).
  Theorems called: `key_read_made`, `entry_read_made`, `proof_read_made`
    (OnBytes/Model/ReadBackMade.lean).
  Reached through the imports, by a walk of the import lines at the library's state at which this
  was written: 63 files under OnBytes/Model/. Johnson/G/RoundsOfPlan.lean reaches 59 of them
  already; the four more are ReadBackMade, VerifyDerives, VerifyDigest, VerifyLaws.

Limits. That the made plans fit the format's words is a premise; it is shown of no plan here.
Nothing on soundness.


-/
import Johnson.G.DataEntries
import Johnson.Desc.FitOk
import OnBytes.Model.ReadBackMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.OfPlan
open OnBytes OnBytes.Params VerifiableInference

/-- The plans from which the key file's rounds are declared are the plans of three records of the
planner's type. -/
def KeyPlansPriced (m : Made) (K₁ K₂ K₃ : Planned) : Prop :=
  m.p.chains.key.oneTime.given.plan = K₁.plan ∧ m.p.chains.key.shared.given.plan = K₂.plan ∧
    m.p.chains.key.second.given.plan = K₃.plan

/-- The plans from which the proof file's rounds are declared are the plans of three records of the
planner's type. -/
def ProofPlansPriced (m : Made) (F₁ F₂ F₃ : Planned) : Prop :=
  m.p.chains.proof.first.given.plan = F₁.plan ∧ m.p.chains.proof.shared.given.plan = F₂.plan ∧
    m.p.chains.proof.second.given.plan = F₃.plan

/-- The plan of the entry file's chain as read back is the plan of the planner's record. -/
def EntryPlanPriced (m : Made) : Prop :=
  m.p.chains.link.given.plan = m.p.chains.made.entry.plan

/-- What `chainsOf` returns. -/
theorem chainsOf_made {X : Model.Verify.Public} {layout : Option ByteArray} {cfg : ByteArray}
    {c : Model.Verify.Chains} (h : Model.Verify.chainsOf X layout cfg = .ok c) :
    ∃ l x, configure l x cfg 0 = .ok c.made ∧
      KeyChains.read c.made.keyOneTime c.made.keyShared c.made.keySecond = some c.key ∧
      Link.read c.made.entryLink = some c.link ∧
      ProofChains.read c.made.first c.made.shared c.made.second = some c.proof := by
  unfold Model.Verify.chainsOf at h
  obtain ⟨⟨links, shapes⟩, _, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨z, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨made, hm, h⟩ := bind_ok h
  split at h
  · rename_i key link proof hk hl hp
    obtain rfl := Except.ok.inj h
    exact ⟨_, _, hm, hk, hl, hp⟩
  · exact absurd h (throw_ne _ _)

/-- What `madeOf` returns holds chains that `chainsOf` has returned. -/
theorem madeOf_chains {pol lay KL : ByteArray} {m : Made} (h : madeOf pol lay KL = .ok m) :
    ∃ X layout cfg, Model.Verify.chainsOf X layout cfg = .ok m.p.chains := by
  unfold madeOf at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨s, _, h⟩ := bind_ok h
  have hm : m.p = p := by
    split at h
    · obtain rfl := Except.ok.inj h
      rfl
    · exact absurd h (throw_ne _ _)
  unfold Model.Verify.planned at hp
  obtain ⟨X, _, hp⟩ := bind_ok hp
  dsimp only at hp
  obtain ⟨c, hc, hp⟩ := bind_ok hp
  obtain ⟨b, _, hp⟩ := bind_ok hp
  obtain rfl := Except.ok.inj hp
  rw [hm]
  exact ⟨_, _, _, hc⟩

/-- The key file's three equations, where the made plans fit the format's words. -/
theorem keyPlansPriced_of_fit {pol lay KL : ByteArray} {m : Made}
    (h : madeOf pol lay KL = .ok m) {K₁ K₂ K₃ : Planned}
    (hm : m.p.chains.made.key = [K₁, K₂, K₃])
    (hf : Desc.keyFit m.p.chains.made = true) : KeyPlansPriced m K₁ K₂ K₃ := by
  obtain ⟨X, layout, cfg, hc⟩ := madeOf_chains h
  obtain ⟨l, x, h1, h2, _, _⟩ := chainsOf_made hc
  exact key_read_made h1 h2 (fun P hP => List.all_eq_true.1 hf P hP) hm

/-- The entry file's equation, where the made plan fits the format's words. -/
theorem entryPlanPriced_of_fit {pol lay KL : ByteArray} {m : Made}
    (h : madeOf pol lay KL = .ok m) (hf : Desc.entryFit m.p.chains.made = true) :
    EntryPlanPriced m := by
  obtain ⟨X, layout, cfg, hc⟩ := madeOf_chains h
  obtain ⟨l, x, h1, _, h2, _⟩ := chainsOf_made hc
  exact entry_read_made h1 h2 hf

/-- The proof file's three equations, where the made plans fit the format's words. -/
theorem proofPlansPriced_of_fit {pol lay KL : ByteArray} {m : Made}
    (h : madeOf pol lay KL = .ok m) {F₁ F₂ F₃ : Planned}
    (hm : m.p.chains.made.proof = [F₁, F₂, F₃])
    (hf : Desc.proofFit m.p.chains.made = true) : ProofPlansPriced m F₁ F₂ F₃ := by
  obtain ⟨X, layout, cfg, hc⟩ := madeOf_chains h
  obtain ⟨l, x, h1, _, _, h3⟩ := chainsOf_made hc
  exact proof_read_made h1 h3 (fun P hP => List.all_eq_true.1 hf P hP) hm

end Johnson.G.OfPlan

#print axioms Johnson.G.OfPlan.chainsOf_made
#print axioms Johnson.G.OfPlan.madeOf_chains
#print axioms Johnson.G.OfPlan.keyPlansPriced_of_fit
#print axioms Johnson.G.OfPlan.entryPlanPriced_of_fit
#print axioms Johnson.G.OfPlan.proofPlansPriced_of_fit
