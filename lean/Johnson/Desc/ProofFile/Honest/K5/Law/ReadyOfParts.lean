-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReadyOfParts.lean: Its code names no kind. By the
frame's authors' word its home is to be Honest/Law/ReadyOfParts.lean, in the frame's own namespace;
it stands in this folder until it is moved. CONDITIONAL: `ready` (Honest/Frame.lean) RETURNS WHERE
ITS PARTS DO: `chainSteps` returns at a list of sub-protocols where it returns at each of them by
itself; `ready` returns where `readyTests` accepts, the request has a trace and `chainSteps` returns
at the three chains. Statements with their proofs; no definition. The ways back are the frame's
(`ready_ok`, Honest/Law/Run.lean; `chainSteps_cons_ok`, Honest/Law/Rule/Member.lean). Two namesakes
of `K12.chainSteps_one` (Honest/K13/DebtsKit.lean, Honest/K3/Law/Thread/OneBlock.lean) go the other
way, from the return to the lending.

  `chainSteps_bare`        at one sub-protocol at whose place no side stands: it returns where the
                           sub-protocol has as many lists of oracle messages as rounds
  `chainSteps_side`        at one sub-protocol with a side: it returns where the five tests pass and
                           the lending returns. After the law of the same content by the writers
                           of the proximity test's rounds (sub-protocol K12):
                           `K12.chainSteps_one` (Honest/K12/StepsReturn.lean): A KNOWING TWIN, laid
                           here so that a caller need not stand over that kind's own files
  `chainSteps_of_members`  it returns at a list where it returns at each member by itself: a few
                           lines over the frame's `chainSteps_append` (Honest/Law/Cut.lean)
  `ready_of_parts`         `ready` returns where its tests, the trace and the three chains do

Limits. Completeness's road: never under a law over coins. Implications. Nothing says that any of
the premises holds at any prover. What `ready` returns is not said. "`ready` returns" says nothing
on whether a part plays or a round is reached. No property is claimed. Nothing is claimed on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block FileDescription)

variable {S Cl V W Y Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **At one sub-protocol at whose place no side stands `chainSteps` returns**, where the
sub-protocol has as many lists of oracle messages as rounds. -/
theorem chainSteps_bare (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (hs : List (Placed V W Y)) {b : Block S Cl}
    (h0 : b.oracles.length = b.rounds.length)
    (hf : (hs.find? fun g => g.place == b.place) = none) :
    ∃ l, chainSteps B rows look v [b] hs = .ok l := by
  have e0 : ¬ (b.oracles.length != b.rounds.length) = true := by
    rw [h0]
    simp
  unfold chainSteps
  rw [if_neg e0, hf]
  exact ⟨_, rfl⟩

/-- **At one sub-protocol at whose place the side g is the first of the list**: if the five tests
pass (ho, hr, hc, h1, h2) and `lendRow` returns c for the parts of g (hl), `chainSteps` returns
`g.steps b v c`. Statement and proof are those of `K12.chainSteps_one`
(Honest/K12/StepsReturn.lean), to the sign. -/
theorem chainSteps_side (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X)) (g : Placed V W X)
    (hf : (hs.find? fun h => h.place == b.place) = some g)
    (ho : b.oracles.length = b.rounds.length) (hr : g.rounds = b.rounds.length)
    (hc : B.cuts.lookup b.place = some (g.parts.map (·.moves.length)))
    (h1 : rows.any (fun r => r.1.place == b.place && decide (g.parts.length ≤ r.1.part)) = false)
    (h2 : B.ahead.any (fun e =>
      e.spender.place == b.place && decide (g.parts.length ≤ e.spender.part)) = false)
    (c : RowCoins g.parts) (hl : lendRow B rows look b.place g.parts 0 = .ok c) :
    chainSteps B rows look v [b] hs = .ok (g.steps b v c) := by
  have e1 : (b.oracles.length != b.rounds.length) = false := by simp [ho]
  have e2 : (g.rounds != b.rounds.length) = false := by simp [hr]
  have e3 : (B.cuts.lookup b.place != some (g.parts.map (·.moves.length))) = false := by simp [hc]
  simp only [chainSteps, hf, e1, e2, e3, h1, h2, hl, Bool.false_eq_true, if_false]
  show Except.ok (g.steps b v c ++ []) = _
  rw [List.append_nil]

/-- **`chainSteps` returns at a list of sub-protocols where it returns at each of them by itself**,
at the same book, table, coins and sides. An induction over the frame's `chainSteps_append`
(Honest/Law/Cut.lean). -/
theorem chainSteps_of_members (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (v : Option V) (hs : List (Placed V W Y)) :
    ∀ bs : List (Block S Cl), (∀ b ∈ bs, ∃ l, chainSteps B rows look v [b] hs = .ok l) →
      ∃ l, chainSteps B rows look v bs hs = .ok l
  | [], _ => ⟨[], rfl⟩
  | b :: bs, H => by
    obtain ⟨l₁, h₁⟩ := H b List.mem_cons_self
    obtain ⟨l₂, h₂⟩ := chainSteps_of_members B rows look v hs bs
      fun x hx => H x (List.mem_cons_of_mem _ hx)
    have e := chainSteps_append (B := B) (rows := rows) (look := look) (v := v) hs [b] bs
    rw [h₁, h₂] at e
    exact ⟨l₁ ++ l₂, e⟩

/-- **`ready` returns where `readyTests` accepts, the request has a trace and `chainSteps` returns
at the three chains.** The converse of `ready_ok` (Honest/Law/Run.lean). -/
theorem ready_of_parts {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {tr : Tr} (hT : readyTests F B H w₀ = .ok ())
    (ht : H.trace w₀ x = some tr)
    (h₁ : ∃ l, chainSteps B (B.rowsOf 0) (c.look 0)
      (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first = .ok l)
    (h₂ : ∃ l, chainSteps B (B.rowsOf 1) (sharedLook B c.shared)
      (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder H.shared = .ok l)
    (h₃ : ∃ l, chainSteps B (B.rowsOf 2) (c.look 2)
      (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second = .ok l) :
    ∃ R, ready F B H w₀ rc x c = .ok R := by
  obtain ⟨l1, e1⟩ := h₁
  obtain ⟨l2, e2⟩ := h₂
  obtain ⟨l3, e3⟩ := h₃
  have e2' : sharedSteps F B H ⟨w₀, rc, H.key x⟩ c.shared = .ok l2 := by
    unfold sharedSteps
    rw [e2]
    rfl
  refine ⟨⟨⟨w₀, rc, x, tr⟩, ⟨w₀, rc, H.key x⟩, l1, l2, l3⟩, ?_⟩
  unfold ready
  rw [hT, ht]
  show ((unfit (chainSteps B (B.rowsOf 0) (c.look 0)
    (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first)).bind
      fun m₁ => (sharedSteps F B H ⟨w₀, rc, H.key x⟩ c.shared).bind fun m₂ =>
        (unfit (chainSteps B (B.rowsOf 2) (c.look 2)
          (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second)).map
            fun m₃ => (⟨⟨w₀, rc, x, tr⟩, ⟨w₀, rc, H.key x⟩, m₁, m₂, m₃⟩ :
              Ready W₀ Rc Xi Ky Tr X₀ X)) = _
  rw [e1, e2', e3]
  rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.chainSteps_bare
#print axioms ProofFile.Honest.K5.chainSteps_side
#print axioms ProofFile.Honest.K5.chainSteps_of_members
#print axioms ProofFile.Honest.K5.ready_of_parts
