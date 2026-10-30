-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/KeyRounds.lean: for a key file's one-time chain, the limits are a matter of the rounds
alone.

`key_check_oneTime` (OnBytes/Tie/KeyFile.lean) has the hypothesis that the program's description of
the one-time chain breaks no limit (`limitsOfX`, OnBytes/Tie/Limits.lean). "The program" is the Lean
text `verify-on-bytes` (OnBytes/Main.lean). That description is made from the chain's parameters,
the table's root and answers, and the rounds that the dry run of the chain's block states. This file
proves that a description which `OneTime.describe` returns breaks no limit exactly if these rounds
pass a test, `roundsFit`, that looks at nothing else. The dry run does not depend on the key file.
So at given parameters of the one-time chain the hypothesis on the limits holds for every key file
of which the program makes a description, or for none, and the test needs to be made only once.

Main definition: `roundsFit`.
Main theorems: `limits_of_rounds`, `rounds_of_limits`, `key_check_rounds`.
It claims nothing on soundness. `key_check_rounds` says "if the check says yes", as
`key_check_oneTime` does, and all that the head of OnBytes/Tie/KeyFile.lean says of that theorem's
reach holds of this one. That `roundsFit` is true at some parameters is not shown here. If the dry
run returns nothing, the hypothesis of `key_check_rounds` holds emptily: then `Key.check` refuses
every file, and the theorem says nothing.
-/
import OnBytes.Tie.SpecXBase
import OnBytes.Tie.KeyFile

set_option autoImplicit false

namespace OnBytes.Tie

/-- Four limits that look at a chain's rounds, each with the stored tables that it opens, as one
test: no round sends more than one root; no opened tree is one taken over from another chain (each
opening names a tree by its own number; that this number is below the count of trees the chain sends
is not tested here); every tree that the chain sends is opened at most once; no round opens a stored
table. The two others, `notInOrder` and `noRandomBytes`, are broken by no description that
`OneTime.describe` returns (steps of the proof of `limits_of_rounds` that do not use the test; no
theorem states it). `Fmt.Spec.ok`, which `notInOrder` tests, asks more than the bound on an
opening's number: the number is below the count of roots sent up to and with the opening's round. -/
def roundsFit (r : Params.Rounds) : Bool :=
  (r.map (·.1)).all (·.entry.roots ≤ 1) &&
  ((r.map (·.1)).flatMap (·.opens)).all (fun o => (ownNumber o).isSome) &&
  (List.range (((r.map (·.1)).map (·.entry.roots)).sum)).all (fun n =>
    decide
      ((((r.map (·.1)).flatMap (·.opens)).filter fun o => ownNumber o == some n).length ≤ 1)) &&
  (r.map (·.2)).all (·.isEmpty)

/-- A description whose random bytes are in the file is not changed by `inFile`. -/
theorem inFile_self (S : Fmt.Spec) (h : S.rand = .inFile) : inFile S = S := by
  cases S
  dsimp only at h
  subst h
  rfl

/-- A description that `OneTime.describe` returns breaks no limit if its rounds pass `roundsFit`. -/
theorem limits_of_rounds (p : Params.OneTime) (table : Params.TableName) (r : Params.Rounds)
    (S : Fmt.SpecX) (h : p.describe table r = some S) (hf : roundsFit r = true) :
    limitsOfX S = [] := by
  unfold Params.OneTime.describe Params.describeWith at h
  have hok := specX_base S (Params.Given.describe_ok h)
  have hS := Params.Given.describe_eq h
  have hrand : S.base.rand = .inFile := by rw [hS]
  have hr : S.base.rounds = r.map (·.1) := by rw [hS]
  have hs : S.stored = r.map (·.2) := by rw [hS]
  unfold roundsFit at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨f1, f2⟩, f3⟩, f4⟩ := hf
  unfold limitsOfX limitsOf oneRoot ownOnly atMostOnce opensOf
  rw [inFile_self _ hrand, hok, hr, hs, f1, f2, f3, f4, hrand]
  rfl

/-- The converse of `limits_of_rounds`: if a description that `OneTime.describe` returns breaks no
limit, its rounds pass `roundsFit`. -/
theorem rounds_of_limits (p : Params.OneTime) (table : Params.TableName) (r : Params.Rounds)
    (S : Fmt.SpecX) (h : p.describe table r = some S) (hl : limitsOfX S = []) :
    roundsFit r = true := by
  unfold Params.OneTime.describe Params.describeWith at h
  have hS := Params.Given.describe_eq h
  have hr : S.base.rounds = r.map (·.1) := by rw [hS]
  have hs : S.stored = r.map (·.2) := by rw [hS]
  have g : ∀ (c : Bool) (x : Limit), (if c = true then [] else [x]) = [] → c = true := by
    intro c x hc
    cases c <;> simp_all
  unfold limitsOfX limitsOf oneRoot ownOnly atMostOnce opensOf at hl
  rw [hr, hs] at hl
  simp only [List.append_eq_nil_iff] at hl
  obtain ⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, _⟩, h4⟩ := hl
  unfold roundsFit
  rw [g _ _ h1, g _ _ h2, g _ _ h3, g _ _ h4]
  rfl

/-- `key_check_oneTime` with the test on the rounds in the place of the limits. If the rounds that
the dry run of the one-time chain's block states at the parameters k pass `roundsFit`, then for
every key file of at most 2^32 - 160 bytes: if the program's check says yes, the compiled verifier
of the protocol made from the program's description of the one-time chain and the program's own
decision on it (`oneTimeDec`) accepts what was read of that chain. What `key_check_oneTime` says of
a tree that is sent and never opened, and of the two later chains, holds here too. -/
theorem key_check_rounds (k : Params.KeyChains)
    (hf : ∀ x, (Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime) = some x →
      roundsFit x.1 = true)
    (file : ByteArray) (table : Params.TableName) (h : Key.check k file = .ok table)
    (hb : file.size + 16 ≤ 2 ^ 32 - 144) :
    ∃ (j : ℕ) (rounds : Params.Rounds) (dry : Proof.FirstEnd) (S : Fmt.SpecX) (r : ChainRead)
      (s' : Session),
      Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j) ∧
      (Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime) = some (rounds, dry) ∧
      k.oneTime.describe table rounds = some S ∧
      readIn S file j Session.start = some (r, s') ∧
      CompiledAccepts S.base (oneTimeDec k.oneTime) r.out := by
  obtain ⟨j, rounds, dry, S, r, s', h1, h2, h3, h4, h5⟩ := key_check_oneTime k file table h
  exact ⟨j, rounds, dry, S, r, s', h1, h2, h3, h4,
    h5 (limits_of_rounds _ _ _ _ h3 (hf _ h2)) hb⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.limits_of_rounds
#print axioms OnBytes.Tie.rounds_of_limits
#print axioms OnBytes.Tie.key_check_rounds
