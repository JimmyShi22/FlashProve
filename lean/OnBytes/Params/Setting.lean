-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Setting.lean: what the derivation of sizes takes as given.

These are the field, the target, the bits of proof of work ("work" below) and two readings of cited
bounds (blocks/numbers/setting.h). The target, the work, the two readings, the answers to a sample
and two widths in bytes follow from the first lines of the parameter file (`settingOf`; setting_of
in blocks/frame/derive.h). `settingOf` leaves the remainder at its default values: the field,
`instances` and `nonceBytes`. This program serves one field,
p = 2 ^ 64 - 2 ^ 32 + 1 with its cubic extension, and plain Reed-Solomon codes.

The cited bound on mutual correlated agreement up to the Johnson radius is Theorem 4.6 of IACR
ePrint 2025/2055, taken with M = 1. It is assumed: no proof of it has been verified for this
program.

Main definitions: `ErrorKind`, `Scope`, `CountSource`, `Radius`, `Setting`, `settingOf`.
-/
import OnBytes.Params.File
import OnBytes.Params.Real

namespace OnBytes.Params

/-- By which argument a round's error is bounded. It selects the round's bits of work. -/
inductive ErrorKind where
  /-- a polynomial that is not zero vanishes at the challenge -/
  | field
  /-- two members of a list have the same out-of-domain sample -/
  | sample
  /-- a combination of words is close to the code though the words are not jointly close (mutual
  correlated agreement); the one kind whose bound has a count, and so a `CountSource` -/
  | closeness
  /-- a word that is far from what is claimed agrees with it at all drawn positions -/
  | query
  /-- a vector that is not small has small images under all drawn combinations -/
  | small
  /-- the round has no error -/
  | zero
  deriving DecidableEq, Repr, Inhabited

/-- Who pays for a round's proof of work, and how often. -/
inductive Scope where
  /-- once for each request -/
  | request
  /-- once for each batch -/
  | shared
  /-- once for each commitment -/
  | once
  deriving DecidableEq, Repr, Inhabited

/-- From which bound the count in a closeness error comes, the strongest footing first. -/
inductive CountSource where
  /-- within a third of the code's minimum distance d: if 3 floor (delta n) < d, the count is
  floor (delta n) + 1, for every additive code and so for every interleaving. A lemma of the paper
  that this protocol builds on (see THIRD_PARTY.md), proved there, on paper ("the proved lemma" in
  OnBytes/Shell/Lines.lean). IACR ePrint 2026/680 states the same count for linear codes
  (Theorem 4.8, with Lemma 4.6 for the mutual form); blocks/numbers/codes.h names further published
  statements. OnBytes/Slice/CodeFacts.lean has a bound with this count for the format's Reed-Solomon
  codes (`mcaEq_third`); no theorem ties the number that the planner uses to it -/
  | third
  /-- up to the Johnson radius, delta < 1 - sqrt rho: IACR ePrint 2025/2055, Theorem 4.6 with M = 1,
  which is assumed (see the head of this file) -/
  | johnson
  deriving DecidableEq, Repr, Inhabited

/-- The rule that fixes the distance of a group of rows (`GroupSize`). -/
inductive Radius where
  /-- up to the Johnson radius less a slack -/
  | johnson
  /-- no rule: a distance that a caller names, in whole positions; no line of the parameter file
  gives it -/
  | named
  deriving DecidableEq, Repr, Inhabited

/-- What the derivation takes as given. -/
structure Setting where
  /-- the base field has p elements -/
  p : Nat := 2 ^ 64 - 2 ^ 32 + 1
  /-- the extension field has p ^ degree elements -/
  degree : Nat := 3
  /-- every round's error times 2 ^ -work is to be at most 2 ^ -target -/
  target : Nat := 128
  /-- how the integer m of the assumed theorem is read. It ties the slack eta, which is
  1 - sqrt rho - delta, to the size of the bound. True: as Theorem 4.6 prints it,
  m = max (ceil (sqrt rho / eta)) 3. False: with sqrt rho / (2 eta), as the same report's
  Theorem 1.5 and IACR ePrint 2026/680, Theorem 4.12, have it. The printed reading gives the larger
  m at a distance, and so the larger count -/
  printed : Bool := true
  /-- what a combination of the rows of an interleaved word costs. True: the number of rows times
  the cost of a line through two words (IACR ePrint 2026/680, Lemma 4.7), except where the count has
  the source `.third` (`mcaError`). False: as much as such a line, by a short argument that is the
  C++ programs' own and is given in blocks/numbers/setting.h -/
  rowsFactor : Bool := false
  /-- a round of a request's own part counts so many times: the requests that share a session;
  `settingOf` leaves it 1 -/
  instances : Nat := 1
  /-- the answers to each out-of-domain sample -/
  samples : Nat := 1
  /-- the bytes of a leaf's salt -/
  saltBytes : Nat := 40
  /-- the bytes of a nonce in a file -/
  nonceBytes : Nat := 8
  /-- the bytes of a listed position; 0: none is listed -/
  positionBytes : Nat := 0
  /-- the bits of work before a round's challenge, by the kind of the round's error (`ErrorKind`):
  this field and the four below; each holds three numbers, one for each `Scope` -/
  workField : Work := ⟨0, 0, 0⟩
  workSample : Work := ⟨0, 0, 0⟩
  workCloseness : Work := ⟨0, 0, 0⟩
  workQuery : Work := ⟨0, 0, 0⟩
  workSmall : Work := ⟨0, 0, 0⟩
  deriving DecidableEq, Repr, Inhabited

/-- The number of elements of the extension field. -/
def Setting.cardE (s : Setting) : Nat := s.p ^ s.degree

/-- The bits of one line of work in a scope. -/
def Work.of (w : Work) : Scope → Nat
  | .request => w.request
  | .shared => w.shared
  | .once => w.once

/-- The bits of work of a round, by the kind of its error and its scope. -/
def Setting.workOf (s : Setting) (k : ErrorKind) (c : Scope) : Nat :=
  match k with
  | .field => s.workField.of c
  | .sample => s.workSample.of c
  | .closeness => s.workCloseness.of c
  | .query => s.workQuery.of c
  | .small => s.workSmall.of c
  | .zero => 0

/-- The setting that the parameter file's lines fix (setting_of in blocks/frame/derive.h). The line
`reading` is 1 for the printed reading; the line `rowcost` is 1 for no factor of the rows, and every
other value sets the factor. The field, `instances` and `nonceBytes` keep their
default values. -/
def settingOf (l : Lines) : Setting where
  target := l.sec
  printed := l.reading == 1
  rowsFactor := l.rowcost != 1
  samples := l.answers
  saltBytes := l.salt
  positionBytes := l.listed
  workField := l.workField
  workSample := l.workSample
  workCloseness := l.workCloseness
  workQuery := l.workPositions
  workSmall := l.workSmallness

end OnBytes.Params
