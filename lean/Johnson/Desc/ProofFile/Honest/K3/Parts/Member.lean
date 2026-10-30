-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Member.lean: the honest side of the kind "lookup" (K3): A
MEMBER, BY EVALUATION, of the premises of `lawfulSpecP` (Honest/K3/Parts/Proof.lean): a course at a
synthetic face with THREE PARTS OF KEYS, whose summands are the specification's at parts.
Definitions with code, theorems with proofs, `#guard` lines.

The face: no shift (the verifier's tests allow several parts only without one); parts of 8, 4 and 2
keys; part 0's level with two variables binds bit 0 first; 4 rows; 3 planes of 4; one key of
padding, the table's row 1. The data: thirteen keys that are rows of the table, and the padding at
the last place of part 1; the rows 0 to 3 are met 6, 0, 5 and 2 times. The challenges: synthetic,
none 0; two rounds stand in front of the lookup.

  1  `sameC`, `same_of`; `numberedPC`, `numberedP_of`   `NumberedP`: ALL SEVEN CLAUSES BY A TEST
     WITH CODE, beside the theorem that yields them out of `Fit` (Honest/K3/Parts/Numbered.lean)
  2  `numsShared_of_ok`   `NumsShared` at public numbers made of a face, out of the verifier's tests
  3  `midPC`, `midP_of`; `specPC`, `specAtP_of`   `SpecAtP`: the clauses that are equations between
                              values, by a test
  4  `member_lawfulP`   from an acceptance by the three tests to `Lawful`
  5  the course; the tests accept it, and reject bent ones; AND `Lawful` WITH CODE
     (Honest/K3/Law/Members.lean: `lawfulL`) ACCEPTS IT: the conclusion, found by evaluation of
     the summands themselves, beside the theorem

HOW FAR IT GOES. That the tests accept is held by `#guard`: by Lean's evaluator, not by its kernel.

Limits. One size.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Proof
import Johnson.Desc.ProofFile.Honest.K3.Law.Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.K3 (entriesV)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (planesOf)
open ProofFile.Honest.K3.Law.Members (fitC fit_of coinsFor lawfulL planesE keysE)

variable {P : Type}

/-! ## 1 NumberedP -/

/-- `SameForP`, with code. -/
def sameC (f : LFace) : Stage → Pts → Pts → Bool
  | .tie _, p, q => decide (p.theta = q.theta) && decide (p.alpha = q.alpha)
  | .split _, p, q => decide (p.theta = q.theta) && decide (p.alpha = q.alpha)
  | .key i m, p, q => decide (p.theta = q.theta) && decide (p.alpha = q.alpha) &&
      decide (p.keyPt i m = q.keyPt i m)
  | .tab l, p, q => decide (p.theta = q.theta) && decide (p.alpha = q.alpha) &&
      decide (p.tabPt l = q.tabPt l)
  | .leaves, p, q => decide (p.theta = q.theta) && decide (p.alpha = q.alpha) &&
      decide (p.tabPt f.d = q.tabPt f.d)
  | .bits, p, q => decide (p.theta = q.theta) && decide (p.alpha = q.alpha) &&
      decide (p.zeroPt = q.zeroPt)
  | _, _, _ => true

/-- An acceptance by the test gives the proposition. -/
theorem same_of (f : LFace) (s : Stage) (p q : Pts) (h : sameC f s p q = true) :
    SameForP f s p q := by
  cases s <;> simp only [sameC, Bool.and_eq_true, decide_eq_true_eq] at h <;>
    first
      | exact trivial
      | exact ⟨h.1, h.2⟩
      | exact ⟨h.1.1, h.1.2, h.2⟩

/-- `NumberedP`, with code. -/
def numberedPC {W : Type} (R : Course W) : Bool :=
  ((stages R.f).all fun s => sameC R.f s (ptsOf R.f R.a.base (R.front s).heard) R.pts) &&
  ((stages R.f).all fun s => (R.r s).length == (shapeAt R.a s).all.length) &&
  (R.f.parts.zipIdx.all fun y => (List.range y.1).all fun m =>
    decide (R.pts.keyPt y.2 (m + 1) =
      behind m (R.f.orders y.2 m) ((R.r (.key y.2 m)).take m) (R.xiK y.2 m))) &&
  ((List.range R.f.d).all fun l =>
    decide (R.pts.tabPt (l + 1) = behind (R.f.mu + l) (orderDefault (R.f.mu + l))
      ((R.r (.tab l)).take (R.f.mu + l)) (R.xiT l))) &&
  decide (R.zb0 = (R.r .leaves).toArray) &&
  decide (R.zb1 = ((R.r .bits).take (R.f.mu + R.f.d)).toArray) &&
  ((stages R.f).all fun s => (R.masks s).length == s.tail R.f)

/-- An acceptance by the test gives the premise. -/
theorem numberedP_of {W : Type} (R : Course W) (h : numberedPC R = true) : NumberedP R := by
  simp only [numberedPC, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    beq_iff_eq] at h
  exact ⟨fun s hs => same_of _ _ _ _ (h.1.1.1.1.1.1 s hs), h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2,
    h.1.1.2, h.1.2, h.2⟩

/-! ## 2 NumsShared -/

/-- **At public numbers made of a face that passes the verifier's tests, the shared numbers are the
face's.** -/
theorem numsShared_of_ok (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (theta : KE)
    (hok : f.ok = true) : NumsShared f (numsOf f row pads theta) := by
  have h2 := two_le_planes_of_ok f hok
  refine ⟨rfl, rfl, ?_, fun _ => rfl, rfl, rfl⟩
  show f.planes = f.planes - 2 + 2
  omega

/-! ## 3 SpecAtP -/

/-- The relation after the challenge at parts, with code. -/
def midPC (A : DataP P) : Bool :=
  decide (∀ u, u < 2 ^ A.D.N.d → ∀ j, j < 2 ^ A.D.N.w → A.D.bits u j * (A.D.bits u j - 1) = 0) &&
  decide (∑ u ∈ Finset.range (2 ^ A.D.N.d), ∑ j ∈ Finset.range (A.D.N.n + 2),
      (2 : KE) ^ j * A.D.bits u j =
    (((A.vs.map (2 ^ ·)).sum - Cb.Lkp.padNum A.D.N.pads : Nat) : KE)) &&
  decide (A.rest 0 = A.D.a * ∏ j ∈ Finset.range (A.D.N.n + 2), A.D.G j ^ 2 ^ j)

theorem midP_of (A : DataP P) (h : midPC A = true) : A.Mid := by
  simp only [midPC, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The clauses of `SpecAtP` that are equations between values, with code, one by one: the public
factor; the table at the leaves' sumcheck's own point; the count of padding; the
relation at parts. -/
def specPL (R : Course Ask) (N : KE → TwV.Nums P KE) (w : Hidden) : List Bool :=
  [decide (up R.factor = (dataAt N w R.pts).a),
   decide (up (R.f.leaf R.pts.theta R.pts.alpha R.zb0) =
    ((List.range (2 ^ R.f.d)).map fun r => TwV.eqN ((byBit R.zb0).drop R.f.mu) r *
      (up R.pts.alpha - 1 - (N (up R.pts.theta)).tab r)).sum),
   decide (((N (up R.pts.theta)).pads.map (·.2)).sum = (R.f.padding.map (·.1)).sum),
   midPC (dataP N R.f.parts R.f.orders w R.pts)]

/-- **Four times yes gives `SpecAtP`**, at a course whose summands are the specification's at parts
at public numbers made of its own face, and whose input is one structure at every list. -/
theorem specAtP_of (R : Course Ask) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden)
    (hJ : R.J = (specJobsPAt R.f row pads).asked) (hw : ∀ l, R.t.input l = w) (hF : Fit R)
    (h : specPL R (numsOf R.f row pads) w = [true, true, true, true]) :
    SpecAtP R (numsOf R.f row pads) w := by
  simp only [specPL, List.cons.injEq, decide_eq_true_eq, and_true] at h
  exact ⟨hJ, fun s _ => hw _, numsShared_of_ok R.f row pads _ hF.ok, h.1, h.2.1, h.2.2.1,
    midP_of _ h.2.2.2⟩

/-! ## 4 From the tests to Lawful -/

/-- **From an acceptance by the three tests to `Lawful`, at several parts.** -/
theorem member_lawfulP (R : Course Ask) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden)
    (hJ : R.J = (specJobsPAt R.f row pads).asked) (hw : ∀ l, R.t.input l = w)
    (h1 : fitC R = true) (h2 : numberedPC R = true)
    (h3 : specPL R (numsOf R.f row pads) w = [true, true, true, true]) :
    Lawful R (planesOf (dataAt (numsOf R.f row pads) w R.pts))
      (keysOfP (dataP (numsOf R.f row pads) R.f.parts R.f.orders w R.pts)) :=
  lawfulSpecP Unit _ _ R (fit_of R h1) (numberedP_of R h2)
    (specAtP_of R row pads w hJ hw (fit_of R h1) h3)

/-! ## 5 The course -/

/-- **The face**: three parts. -/
def f3 : LFace :=
  { Toy.f₁ with
    shifted := false, parts := [3, 2, 1]
    orders := fun i m => if i == 0 && m == 2 then [0, 1] else orderDefault m }

/-- The rows that the keys hold, part by part; at part 1's last place the padding: row 1. -/
def rowsOf : List (List Nat) := [[0, 0, 2, 0, 2, 3, 0, 2], [0, 2, 3, 1], [0, 2]]

/-- The structure of keys and bits. rows: the keys' rows; counts: how often each row is met. -/
def hid3 (rows : List (List Nat)) (counts : List Nat) : Hidden where
  key := fun theta i x => Toy.rowAt theta ((rows.getD i []).getD x 0)
  bit := Toy.bitsOf counts

def w3 : Hidden := hid3 rowsOf [6, 0, 5, 2]

/-- A synthetic element, never 0. -/
def ch (k : Nat) : E := E.mk3 (1000 + 7 * k).toUInt64 (k + 1).toUInt64 (2 * k + 3).toUInt64

/-- Synthetic challenges of the lookup's rounds: as many elements a round as the verifier's entry
states. -/
def ds3 : List Fmt.Drawn :=
  (entriesV f3).zipIdx.map fun x =>
    ⟨(List.range x.1.drawE).map fun j => (ch (100 * x.2 + j)).triple, [], [], none⟩

/-- Two rounds in front. -/
def front3 : List Fmt.Drawn := [⟨[(ch 7001).triple], [], [], none⟩,
    ⟨[(ch 7002).triple], [], [], none⟩]

def at3 : At := ⟨Toy.pL, f3, 2⟩

/-- **The course.** -/
def courseAt (w : Hidden) : Course Ask :=
  { a := at3, J := (specJobsPAt f3 Toy.rowAt [(1, 1)]).asked, first := 4, c := coinsFor at3 4 Toy.g₁
    t := ⟨fun _ => w, front3, ()⟩, seen := .bare [], ds := ds3 }

def M3 : Course Ask := courseAt w3

/-- The four answers at a course of this face. -/
def four (w : Hidden) (pads : List (Nat × Nat)) : List Bool :=
  specPL (courseAt w) (numsOf f3 Toy.rowAt pads) w

-- written: the sizes: 14 keys in three parts; two parts' steps; 13 sumchecks with end values
#guard (f3.parts, f3.allKeys, f3.count, f3.planes, f3.mu, f3.d) == ([3, 2, 1], 14, 13, 3, 2, 2)
#guard ((stages f3).filter fun s => match s with | .split _ => true | _ => false) ==
  [.split 0, .split 1]
-- THE TESTS ACCEPT
#guard fitC M3
#guard numberedPC M3
#guard four w3 [(1, 1)] == [true, true, true, true]
-- AND Lawful WITH CODE ACCEPTS: the summands themselves, evaluated
#guard lawfulL M3 (planesE f3 w3) (keysE f3 w3 M3.pts.theta) == ([], true, true, true, true)
-- AND NO OF BENT ONES. The lists of parts 1 and 2 changed over: the parts have other sizes, so
-- other keys are read
#guard four (hid3 [rowsOf.getD 0 [], rowsOf.getD 2 [], rowsOf.getD 1 []] [6, 0, 5, 2]) [(1, 1)] ==
  [true, true, true, false]
-- a key at another row; a count too high; the padding at another row
#guard four (hid3 [[0, 0, 2, 0, 2, 3, 0, 2], [0, 2, 3, 1], [0, 3]] [6, 0, 5, 2]) [(1, 1)] ==
  [true, true, true, false]
#guard four (hid3 rowsOf [7, 0, 5, 2]) [(1, 1)] == [true, true, true, false]
#guard four w3 [(2, 1)] == [false, true, true, false]
-- a course that counts one round more in front of the lookup
#guard !numberedPC { M3 with a := { M3.a with base := 3 } }

/-- **The member, BY EVALUATION**: from the evaluated equations to `Lawful` of the course
with three parts. -/
theorem M3_lawful (h1 : fitC M3 = true) (h2 : numberedPC M3 = true)
    (h3 : four w3 [(1, 1)] = [true, true, true, true]) :
    Lawful M3 (planesOf (dataAt (numsOf f3 Toy.rowAt [(1, 1)]) w3 M3.pts))
      (keysOfP (dataP (numsOf f3 Toy.rowAt [(1, 1)]) f3.parts f3.orders w3 M3.pts)) :=
  member_lawfulP M3 Toy.rowAt [(1, 1)] w3 rfl (fun _ => rfl) h1 h2 h3

#print axioms ProofFile.Honest.K3.Parts.same_of
#print axioms ProofFile.Honest.K3.Parts.numberedP_of
#print axioms ProofFile.Honest.K3.Parts.numsShared_of_ok
#print axioms ProofFile.Honest.K3.Parts.midP_of
#print axioms ProofFile.Honest.K3.Parts.specAtP_of
#print axioms ProofFile.Honest.K3.Parts.member_lawfulP
#print axioms ProofFile.Honest.K3.Parts.M3_lawful

end ProofFile.Honest.K3.Parts
