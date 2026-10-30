-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Members.lean: instances of the hypotheses of
Honest/K3/Law/Statements.lean, and that file's definitions held against the verifier's own text, by
evaluation at a small synthetic lookup (Honest/K3/Toy.lean: 8 keys, 4 rows, 3 planes; 50 rounds, 73
slots). Definitions with code, 34 tests by evaluation, and one small theorem (a test's acceptance
gives the hypothesis).

Terms. Honest/K3/GLOSSARY.md ("course", "fit", "lawful", "synthetic", "test by evaluation").

What is shown, at two orders of the key tree's rounds, two lists of challenges and two rows of
coins; by the file's sections.
  1. `Fit` has an instance (`fitC`, with `fit_of`, whose `h` is that the test accepts); the part of
     `Inv R 0` that a test can read has one.
  2. The course's rounds are the rounds that the frame's `play` yields on `lookRow` (what `RowPlays`
     says).
  3. `hearV` returns on them, and what it returns is what `HeardIs` says, field by field.
  4. Behind the hearing, on the played coins: the hidden value under each end slot is `Course.T`
     (the last clause of `Inv`); each stage's `Course.form` is worth `Course.claimed` (what
     `FormWorth` says).
  5. `Course.shown` is what the stage's last round shows.
  6. `Lawful` with code (`lawfulL`) accepts at the honest data, at two fillings of the summands, and
     rejects at a key outside the table, at a false count, at a bit that is 2, and at keys read off
     other data: each at the clauses that it should fail.
Each test says in a comment what makes it fail.

Imported. Honest/SumLaw/Toy.lean.

Users. This file is imported by Honest/K3/Law/SpecMember.lean and Honest/K3/Law/TopMembers.lean
[not in this library].

Limits. One size. All of it is by evaluation, not by proof, but for `fit_of`. `lawfulL`, `invC` and
`sameAff` compare words; that `lawfulL` says what `Lawful` says is not shown here (it calls
`sumsToC` of Honest/SumLaw/Toy.lean). No statement of Statements.lean is proved by this.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements
import Johnson.Desc.ProofFile.Honest.K3.ToyFast
import Johnson.Desc.ProofFile.Honest.SumLaw.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Members
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (Aff Fork ofNat)
open VerifiableInference.Desc.Part.MaskedSum (Ends)
open VerifiableInference.Desc.K3 (HeardV hearV planesV entriesV eqPairs)
open ProofFile.Honest.SumToy (sig formAt)
open ProofFile.Honest.SumLaw.Toy (same sumsToC scal)
open ProofFile.Honest.K3.Toy (W3 Made f₁ f₂ J₁ J₂ g₁ g₃ h₁ h₃ honest badKey badCount badBit atOf
  askOf drawsBy csOf maskOf ledger rowIn prodAt bitTab)

/-! ## The course at the small lookup -/

/-- The end values' coins, by slot. -/
def endCs (name : String) (g : Nat → W3) (at_ : Nat) : (o : Option Ends) → CsAll (endRuns name o)
  | none => ()
  | some e => (csOf e.n (fun j => g (at_ + j)), ())

/-- A stage's coins: the owner's coin number j lies under slot j. -/
def coinsFor (a : At) (first : Nat) (g : Nat → W3) (s : Stage) : StageCoins a s :=
  show Handed ⟨0, 0⟩ _ [] from
    (Cs.empty,
      (csOf (ownRun (shapeAt a s)) (fun i => g (first + firstSlot a.face s + i)),
        endCs _ g (first + firstSlot a.face s + s.own a.face) (shapeAt a s).ends), ())

/-- **The small lookup's course**: the two rounds in front are heard; the rest are the lookup's. In
front of it no round is shown and no columns are handed (`Seen.bare []`). -/
def courseOf (f : LFace) (J : LookJobs Hidden) (d : Nat → Made) (g : Nat → W3)
    (h : Nat → Nat → W3) : Course Ask :=
  { a := atOf f, J := J.asked, first := Toy.first, c := coinsFor (atOf f) Toy.first g
    t := ⟨askOf d, (drawsBy f h).take (Toy.baseOf f), ()⟩, seen := .bare []
    ds := (drawsBy f h).drop (Toy.baseOf f) }

def R₁ : Course Ask := courseOf f₁ J₁ honest g₁ h₁
def R₂ : Course Ask := courseOf f₂ J₂ honest g₃ h₃

/-! ## 1 Fit, and the ledger in front -/

/-- `Fit`, with code. -/
def fitC {W : Type} (R : Course W) : Bool :=
  R.f.ok && R.t.heard.length == R.a.base && drawsFit ((entriesV R.f).map declOf) R.ds

/-- An acceptance by the test gives the hypothesis. -/
theorem fit_of {W : Type} (R : Course W) (h : fitC R = true) : Fit R := by
  simp only [fitC, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

-- Fails at: a face that fails its tests; another number of rounds in front; a challenge too few;
-- Y's sample 0.
#guard fitC R₁ && fitC R₂
#guard !fitC { R₁ with ds := R₁.ds.dropLast }
#guard !fitC { R₁ with a := { R₁.a with base := 3 } }
#guard !fitC { R₁ with ds := R₁.ds.map fun d => { d with elems := d.elems.map fun _ => (0, 0, 0) } }

/-- The clauses of `Inv R n F` that read the ledger alone, with code. -/
def invC {W : Type} (R : Course W) (n : Nat) (F : Fork) : Bool :=
  F.vp.size == F.ns && F.mf.size == F.ns && F.gotF.size == F.ns &&
    F.next == R.first + slotsIn R.f n && decide (R.first + R.f.slots ≤ F.ns) &&
    (List.range (R.first + R.f.slots - F.next)).all (fun j => !F.gotF.getD (F.next + j) false) &&
    ((stages R.f).take n).all fun s =>
      (List.range (s.tail R.f)).all fun j => F.gotF.getD (R.endSlot s + j) false

-- Fails at: a ledger whose count stands elsewhere; one with a slot too few.
#guard invC R₁ 0 (ledger f₁) && invC R₂ 0 (ledger f₂)
#guard !invC R₁ 0 { ledger f₁ with next := 5 }
#guard !invC R₁ 0 { ledger f₁ with ns := 76 }

/-! ## 2 The course's rounds are the played rounds -/

-- Fails at: a stage cut otherwise; a coin under another slot; a state that hears otherwise.
#guard R₁.rounds.isSome && R₂.rounds.isSome
#guard sig R₁.rounds == sig (Toy.run f₁ (rowIn f₁ J₁) honest g₁ h₁)
#guard sig R₂.rounds == sig (Toy.run f₂ (rowIn f₂ J₂) honest g₃ h₃)
#guard sig (courseOf f₁ J₁ honest (fun j => g₁ (j + 1)) h₁).rounds !=
  sig (Toy.run f₁ (rowIn f₁ J₁) honest g₁ h₁)

/-! ## 3 What was heard -/

/-- Two forms have the same slots, coefficients and constant, and no entry of a virtual row. -/
def sameAff (a b : Aff) : Bool :=
  a.ents.isEmpty && b.ents.isEmpty && a.slots.toList == b.slots.toList && a.const == b.const

/-- The hearing on the course's rounds. -/
def heardOf (R : Course Ask) : Option (HeardV × Fork) :=
  R.rounds.bind fun x => hearV R.f (ledger R.f) x

/-- `HeardIs`, with code. (The points are no clause of `HeardIs`; Honest/K3/HeardGuards.lean
[not in this library] holds those.) -/
def heardC (R : Course Ask) (g : HeardV) : Bool :=
  g.a == R.factor && g.sBit == R.endSlot .bits && g.rows.size == R.f.lins &&
    g.keys.length == R.f.parts.length &&
    (g.keys.zip R.f.parts.zipIdx).all (fun x => sameAff x.1.2 (R.form (.key x.2.2 x.2.1))) &&
    sameAff g.leaves.start (R.form .leaves) &&
    g.leaves.first == R.first + firstSlot R.f .leaves && g.leaves.r == R.r .leaves

-- Fails at: a slot's number, a LINE's sample, the order of JOIN's coordinates, a plane's slot
-- written otherwise.
#guard (heardOf R₁).any fun y => heardC R₁ y.1
#guard (heardOf R₂).any fun y => heardC R₂ y.1
#guard (heardOf R₁).any fun y => !heardC { R₁ with first := 5 } y.1
-- Behind the last stage the ledger's clauses hold, and the leaves' own slots are free.
#guard (heardOf R₁).any fun y => invC R₁ (stages f₁).length y.2 &&
  (List.range (Stage.own f₁ .leaves)).all fun j =>
    !y.2.gotF.getD (R₁.first + firstSlot f₁ .leaves + j) false

/-! ## 4 The invariant's last clause, and the forms' worth -/

/-- The stages that are sumchecks. -/
def sums (f : LFace) : List Stage := (stages f).filter fun s => (s.call f).isSome

/-- On the ledger behind the hearing and the played coins: under every end slot lies the job's
true end value. -/
def endsC (R : Course Ask) (g : Nat → W3) (G : Fork) : Bool :=
  (stages R.f).all fun s => (List.range (s.tail R.f)).all fun j =>
    same (formAt G (maskOf g) (Aff.slot (R.endSlot s + j))) (R.T s j)

/-- There: every stage's form, and the forms that the key trees leave, are worth what they should
be. -/
def worthC (R : Course Ask) (g : Nat → W3) (G : Fork) : Bool :=
  (sums R.f ++ R.f.parts.zipIdx.map fun y => Stage.key y.2 y.1).all fun s =>
    same (formAt G (maskOf g) (R.form s)) (R.claimed s)

-- 16 end values (3 + 2 at the tie; 2 at each of 3 + 2 levels; 1 at the bits) and 9 sumchecks at
-- this size, written. Fails at another cut (a first writing of these two numbers, 17 and 13,
-- failed).
#guard ((stages f₁).map (Stage.tail f₁)).sum == 16 && (sums f₁).length == 9
-- Fails at: an end slot's number; a coin under another slot; a job's end values in another order.
#guard (heardOf R₁).any fun y => endsC R₁ g₁ y.2
#guard (heardOf R₂).any fun y => endsC R₂ g₃ y.2
#guard (heardOf R₁).any fun y => !endsC R₁ (fun j => g₁ (j + 1)) y.2
-- Meant to fail if `claimed` is written otherwise than `form` at a stage; what is seen to reject
-- stands under the next caption.
#guard (heardOf R₁).any fun y => worthC R₁ g₁ y.2
#guard (heardOf R₂).any fun y => worthC R₂ g₃ y.2
-- The test can reject: at coins moved by one slot; at forms on slots moved by one.
#guard (heardOf R₁).any fun y => !worthC R₁ (fun j => g₁ (j + 1)) y.2
#guard (heardOf R₁).any fun y => !worthC { R₁ with first := 5 } g₁ y.2

/-! ## 5 The shown end values -/

-- Fails at: beta taken from another round; masks in another order. Here and in the next test each
-- stage is played with no round shown and no columns handed (`Seen.bare []`).
#guard (sums f₁).all fun s => s.tail f₁ == 0 ||
  ((R₁.stage s (R₁.stateAt s) (.bare []) (R₁.draws s)).bind (·.getLast?)).map scal ==
    some (R₁.shown s)
-- The test can reject: against the shown values of a course at other coins, at every such stage.
#guard (sums f₁).all fun s => s.tail f₁ == 0 ||
  ((R₁.stage s (R₁.stateAt s) (.bare []) (R₁.draws s)).bind (·.getLast?)).map scal !=
    some ((courseOf f₁ J₁ honest g₃ h₁).shown s)

/-! ## 6 Lawful, with code -/

/-- The planes' value under a product form, of the data. -/
def planesE (f : LFace) (w : Hidden) (pairs : List (E × E)) : E :=
  (List.range (2 ^ (f.mu + f.d))).foldl
    (fun s x => addE s (mulE (prodAt pairs x) (bitTab f w x))) zeroE

/-- Part i's keys at a point, the highest variable first, of the data. -/
def keysE (f : LFace) (w : Hidden) (theta : E) (i : Nat) (z : Array E) : E :=
  Toy.ext (f.parts.getD i 0) (w.key theta i) (Toy.coord (f.parts.getD i 0) z)

/-- The five clauses of `Lawful`, with code: for `sums` the stages that fail; then
the other four. -/
def lawfulL (R : Course Ask) (pl : List (E × E) → E) (ks : Nat → Array E → E) :
    List Stage × Bool × Bool × Bool × Bool :=
  ((stages R.f).filter fun s => decide (0 < s.tail R.f) &&
      !sumsToC (R.call s).all (R.poly s) [] (R.r s) (R.claimed s) (endTerm R.factor s (R.shown s)),
    sumsToC (R.call .leaves).all (R.poly .leaves) [] (R.r .leaves) (R.claimed .leaves)
      (addE oneE (mulE (R.f.leaf R.pts.theta R.pts.alpha R.zb0)
        (pl (eqPairs (R.f.mu + R.f.d) R.zb0)))),
    same (R.T .bits 0) (pl (eqPairs (R.f.mu + R.f.d) R.zb1)),
    same (pl (countPairs R.f)) (ofNat R.f.count),
    R.f.parts.zipIdx.all fun y =>
      same (R.claimed (.key y.2 y.1)) (subE R.pts.alpha (ks y.2 (R.pts.keyPt y.2 y.1))))

/-- The same at a course of the small lookup, planes and keys read off its data. -/
def lawfulAt (f : LFace) (J : LookJobs Hidden) (d : Nat → Made) (g : Nat → W3)
    (h : Nat → Nat → W3) :
    List Stage × Bool × Bool × Bool × Bool :=
  let R := courseOf f J d g h
  let w := askOf d (drawsBy f h)
  lawfulL R (planesE f w) (keysE f w R.pts.theta)

-- The honest data: all five clauses. Meant to fail if a summand, an end value or a point is
-- changed; what is seen to reject stands in the lines on altered data below.
#guard lawfulAt f₁ J₁ honest g₁ h₁ == ([], true, true, true, true)
#guard lawfulAt f₂ J₂ honest g₃ h₃ == ([], true, true, true, true)
-- The second filling (tables folded).
#guard lawfulAt f₁ Toy.F₁ honest g₁ h₁ == ([], true, true, true, true)
#guard lawfulAt f₂ Toy.F₂ honest g₃ h₃ == ([], true, true, true, true)
-- A key outside the table: the tie's first step alone.
#guard lawfulAt f₁ J₁ badKey g₁ h₁ == ([.tie 0], true, true, true, true)
-- A false count: the tie's first step and the counts' sum.
#guard lawfulAt f₁ J₁ badCount g₁ h₁ == ([.tie 0], true, true, false, true)
-- A bit that is 2: these two and the bits' sumcheck.
#guard lawfulAt f₁ J₁ badBit g₁ h₁ == ([.tie 0, .bits], true, true, false, true)
-- Keys read off other data than the summands': the last clause alone.
#guard lawfulL R₁ (planesE f₁ (askOf honest (drawsBy f₁ h₁)))
    (keysE f₁ (askOf badKey (drawsBy f₁ h₁)) R₁.pts.theta) == ([], true, true, true, false)
-- The filling that says nothing is not lawful.
#guard (lawfulAt f₁ Toy.noJobs honest g₁ h₁).1 != []

end ProofFile.Honest.K3.Law.Members

#print axioms ProofFile.Honest.K3.Law.Members.fit_of
