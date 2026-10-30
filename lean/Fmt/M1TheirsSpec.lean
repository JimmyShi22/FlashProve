-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1TheirsSpec.lean: one Lean name for the description of the first toy (a product test) at each
of the programs' own two sets of parameters, with theorems and tests that the other terms under
which that description is written agree with it. "Theirs": the programs' own two sets of parameters.

A description is what a verifier knows before it sees a file: the label, the parameter bytes, the
statement, the rounds (`Fmt.Spec`, Fmt/Rules8.lean). The programs (the C++ implementation that comes
with this Lean code) run the first toy at full parameters and at tiny parameters. A theorem that is
proved at one term for the description says nothing about a run at another term, unless the two
terms are one.

Sources. The description has been written in three ways in this development: (1) from the sizes and
the public file: specOf P (configDigest [public file]) (itemsOf P); (2) as the definition `spec` of
a generated set of files (Fmt/M1PlanKnownT.lean, Fmt/M1PlanKnownR.lean, Fmt/M1PlanKnownF.lean); (3)
read off the parameter bytes: specFrom (Fmt/M1Prog.lean). No Mathlib is imported.

1. What the file contains.
   `Theirs.sizesFull`, `Theirs.specFull`, `Theirs.sizesTiny`, `Theirs.specTiny`: the names: the
     sizes (`toyPar`; those of the tiny parameters) and the description in form (1).
   `sameRand`, `sameRound`, `sameSpec`: a test of this library's own, with its two helpers, that
   compares two
     descriptions field by field: label, plan, parameter bytes, statement, the case of the random
     bytes, the first tree's number, the configuration's digest, and every round's entry, kind,
     items and openings.

2. What is checked when the file compiles (tests, #guard). By evaluation, field by field
(`sameSpec`): `specFrom Theirs.full` gives (`sizesFull`, `specFull`), and `specFrom Theirs.tiny`
gives (`sizesTiny`, `specTiny`). Here `Theirs.full` and `Theirs.tiny` are the programs' own
parameter bytes (Fmt/M1Theirs.lean). Five further tests: the sizes at tiny parameters are also those
that Fmt/M1All.lean has under the name `parTheirTiny`, and they are not `parTiny`, which is another
record (sizes of this library's own); `sameSpec` can fail (the two sets of parameters; one round's
entry altered; another configuration's digest), and it holds of a description and itself.

3. Theorems (statements under `Fmt.M1.Spec`, with their proofs).
   `known_F`, `known_T`, `known_R`: the generated sets' sizes and descriptions are these:
     `KnownF.par = sizesFull`, `KnownF.spec = specFull`; `KnownT` and `KnownR`: `sizesTiny`,
     `specTiny`. Each by unfolding definitions alone (`rfl`; nothing is computed).
   `specFrom_form`: for all bytes: whatever `specFrom` gives is of the shape of form (1):
     `specFrom b = some (P, S)` → there is what the reader of parameters read, p, with
     `paramsRead b = some p`, `parOf p = some P`, `S = specOf P p.cfg p.others p.plan.nonce`, and
     `S.params = b`.

4. What is not claimed.
   The first two tests of part 2 are tests, not theorems: an equation "specFrom Theirs.full = some
     (sizesFull, specFull)" is not proved. (One try by evaluation in the kernel, of the test's truth
     value at tiny parameters, ended at once in an overflow of the stack; no other way was tried in
     this file.) Fmt/M1SpecKnown.lean states, and Fmt/M1SpecKnownProofs.lean proves, the equation at
     the bytes that Lean spells: `specFrom Theirs.specFull.params = some (sizesFull, specFull)`, and
     the same at tiny parameters. That these bytes are the programs' literals `Theirs.full` and
     `Theirs.tiny` is a test of Fmt/M1Theirs.lean.
   So a theorem or a test that is to speak of one and the same term names `specFull` or `specTiny`
     (or a generated set's `spec`, which is that term by the theorems above), not `specFrom`.
   That `sameSpec` holds exactly of equal descriptions is not proved either (it compares every
     field).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1Prog
import Fmt.M1Theirs
import Fmt.M1PlanKnownT
import Fmt.M1PlanKnownR
import Fmt.M1PlanKnownF

namespace Fmt
namespace M1

namespace Theirs

/-- the sizes at full parameters -/
abbrev sizesFull : Par := toyPar
/-- The description at full parameters. -/
def specFull : Spec := specOf toyPar (configDigest [pubFull]) (itemsOf toyPar)
/-- the sizes at tiny parameters -/
abbrev sizesTiny : Par := tinyPar'
/-- The description at tiny parameters. -/
def specTiny : Spec := specOf tinyPar' (configDigest [pubTiny]) (itemsOf tinyPar')

end Theirs

def sameRound (a b : Round) : Bool :=
  a.entry == b.entry && a.kind == b.kind && a.items == b.items && a.opens == b.opens

def sameRand : Rand → Rand → Bool
  | .inFile, .inFile => true
  | .given x, .given y => x == y
  | .none, .none => true
  | _, _ => false

/-- Compares two descriptions field by field. -/
def sameSpec (A B : Spec) : Bool :=
  A.label == B.label && samePlan A.plan B.plan && A.params == B.params &&
    A.statement == B.statement && sameRand A.rand B.rand &&
    A.firstTree == B.firstTree && A.cfg == B.cfg &&
  A.rounds.length == B.rounds.length && (A.rounds.zip B.rounds).all fun x => sameRound x.1 x.2

namespace Spec

def known_F : Prop := KnownF.par = Theirs.sizesFull ∧ KnownF.spec = Theirs.specFull
def known_T : Prop := KnownT.par = Theirs.sizesTiny ∧ KnownT.spec = Theirs.specTiny
def known_R : Prop := KnownR.par = Theirs.sizesTiny ∧ KnownR.spec = Theirs.specTiny

def specFrom_form : Prop :=
  ∀ (b : ByteArray) (P : Par) (S : _root_.Fmt.Spec), specFrom b = some (P, S) →
    ∃ p : Params, paramsRead b = some p ∧ parOf p = some P ∧
      S = specOf P p.cfg p.others p.plan.nonce ∧ S.params = b

end Spec

theorem known_F : Spec.known_F := ⟨rfl, rfl⟩
theorem known_T : Spec.known_T := ⟨rfl, rfl⟩
theorem known_R : Spec.known_R := ⟨rfl, rfl⟩

theorem specFrom_form : Spec.specFrom_form := by
  intro b P S h
  unfold specFrom at h
  cases hp : paramsRead b with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    cases hq : parOf p with
    | none => rw [hq] at h; cases h
    | some Q =>
      rw [hq] at h
      simp only [Option.bind_some] at h
      split at h
      · rename_i hc
        have e := Option.some.inj h
        have e1 : Q = P := congrArg Prod.fst e
        have e2 : specOf Q p.cfg p.others p.plan.nonce = S := congrArg Prod.snd e
        subst e1
        subst e2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨p, rfl, hq, rfl, hc.1.2⟩
      · cases h

-- Read off the programs' bytes: the sizes and the description are the named ones, field by field.
#guard (specFrom Theirs.full).any fun x => samePar x.1 Theirs.sizesFull && sameSpec x.2 Theirs.specFull
#guard (specFrom Theirs.tiny).any fun x => samePar x.1 Theirs.sizesTiny && sameSpec x.2 Theirs.specTiny
-- The sizes at tiny parameters: Fmt/M1All.lean's `parTheirTiny`, not `parTiny` (sizes of this
-- library's own).
#guard samePar Theirs.sizesTiny parTheirTiny && !samePar Theirs.sizesTiny parTiny
-- `sameSpec` can fail: the two sets of parameters; a round's entry altered; another configuration.
#guard sameSpec Theirs.specFull Theirs.specTiny == false
#guard sameSpec Theirs.specTiny { Theirs.specTiny with rounds := Theirs.specTiny.rounds.map fun r => if r.entry.name == "BAT" then { r with entry := { r.entry with rows := 5 } } else r } == false
#guard sameSpec Theirs.specTiny { Theirs.specTiny with cfg := zero32 } == false
#guard sameSpec Theirs.specTiny Theirs.specTiny && sameSpec Theirs.specFull Theirs.specFull

end M1
end Fmt
