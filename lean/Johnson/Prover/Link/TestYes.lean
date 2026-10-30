-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/TestYes.lean: THE PROXIMITY TEST's BLOCK SAYS YES WHERE ITS FOUR SHARES DO: the
converse of the library's k12_ok (Johnson/Desc/K12/FrameLaws.lean), by its four_ok, which is an iff.
Statement and proof, general in the parts X and the record T. No prover and no value stands in this
file.

  k12_yes   the place has a first stage, rounds and oracle messages · the front says yes on nothing
            · the batching on its own round and groups · the group is the first stage's · the
            stages' block on all that lies behind ⟹ the test's block says yes on the whole

Not shown here. That any share says yes. Nothing on soundness, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc VerifiableInference.Desc.K12

variable {T Cl : Type}

theorem k12_yes (X : Parts T) (p : P12) (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (Nat × Nat))) (t t₀ t₁ t' : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hs : p.nums.stages = first :: rest) (hr : H2U.roundsOfNums p.nums = some ds)
    (ho : H2U.testOracles p.nums = some os)
    (h0 : (X.front p).decide t [] [] = .ok t₀)
    (h1 : (batAt X p (ds.zip p.oracles) : Block T Cl).decide t₀
      (rs.take (batAt X p (ds.zip p.oracles) : Block T Cl).rounds.length)
      (gs.take (batAt X p (ds.zip p.oracles) : Block T Cl).openings) = .ok t₁)
    (h2 : (X.group t₁).any (firstFits first) = true)
    (h3 : (stagesFrom X p 0 first rest ((ds.zip p.oracles).drop 1) : Block T Cl).decide t₁
      (rs.drop (batAt X p (ds.zip p.oracles) : Block T Cl).rounds.length)
      (gs.drop (batAt X p (ds.zip p.oracles) : Block T Cl).openings) = .ok t') :
    (proximityTestKind X p : Block T Cl).decide t rs gs = .ok t' := by
  unfold proximityTestKind
  rw [hs, hr, ho]
  exact (four_ok "the front" "the batching" "the test"
    ((X.front p).at "the front" p.place [] : Block T Cl) (batAt X p (ds.zip p.oracles))
    (asks "the group is not the first stage's" p.place fun t =>
      (X.group t).any (firstFits first))
    (stagesFrom X p 0 first rest ((ds.zip p.oracles).drop 1))
    (by simp [Part.at]) (by simp [asks]) t t' rs gs).2
    ⟨t₀, t₁, t₁, by simpa [Part.at] using h0, h1, (asks_ok _ _ _ _ _ _ _).2 ⟨h2, rfl⟩, h3⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.k12_yes
