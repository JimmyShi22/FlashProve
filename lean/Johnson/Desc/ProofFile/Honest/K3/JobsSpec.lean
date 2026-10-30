-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsSpec.lean: the honest side of the kind "lookup" (K3): the
summands of its masked sumchecks, read off the specification's structure field by field. Definitions
with code, and four small theorems on orders of binding. Its tests by evaluation are in
Honest/K3/JobsSpecGuards.lean [not in this library].

Terms. Honest/K3/GLOSSARY.md ("specification", "job, summand", "filling", "points", "program's
elements", "library's field").

What it does. Johnson/HonestTrace/LookDefs.lean says, over any field K, what each of a lookup's
masked sumchecks sums: a structure `Job K` (round, inY, ends and more) for the tie's steps
(`tieJob`), the key tree's levels (`keyJob`), the table side's levels (`tabJob`), the leaves
(`leavesJob`) and the bits (`bitsJob`). These are what that file's statements speak of. The row of
parts (Honest/K3/Stages.lean) wants, for each stage, three functions on the program's elements
(`StageJob`). This file carries the first into the second, at K := the library's extension field
`Cb.Gl.E`. No summand is written here: every value comes out of a field of a `Job`.

What is defined and shown.
  1 `up`, `down`, `ups`, `downs`: between the program's elements and the library's field.
  2 `byBit`, `backBit`: the one translation of points.
  3 `dataAt`: the specification's data at a run.
  4 `carry`, `idle`, `jobAt`, `specJobs`: a `Job` as a `StageJob`; the filling, at public numbers N.
  5 `specJobsF`: the filling at a proof file's lookup of shape h.
  6 `numsOf`, `specJobsAt`, `numsFit`: public numbers made of a face, a table and a padding; a test.
  7 `specPoints`, `specShape` (with `pointsOf`, `shapeOf`): what the specification says of a stage's
    points and shape: for tests.
  8 `countDown_eq`, `numsF_oK`, `numsF_oT`, `numsF_oE_oB`: the orders at a proof file's lookup: four
    theorems.

The public numbers. The specification reads a structure `TwV.Nums P K` (Cb/Pv/Lookup/Out/TwV.lean).
Of it the five jobs read v', d, w, n, tab, pads and the four orders oK, oT, oE, oB; they read none
of its places (kAt, bAt, the ledgers). The table depends on the shift, so the filling takes N as a
function of the shift. At a proof file's lookup N is `Fo.numsF h lm jLK`: the public numbers of the
specification's statements on a sub-proof's lookup (`dataF`). The data are not `dataF` as a term:
keys and bits come out of the input here, and a bit is set to 0 at a plane that does not count. That
the jobs read keys and bits inside the sizes alone is stated in Honest/K3/JobsSpecOwed.lean
(`JobsCongr`) and proved in Honest/K3/JobsSpecCongr.lean. The specification's statements have the
shift's round only where the shape has several calls, while the face of a proof file's lookup always
has it. For the lookups on digits `premF_Z` (Johnson/HonestTrace/LookAtDigits.lean) gives `PremF`
at the shape tl.f9 of the
lookup on the digits, under its own hypotheses.

Points: two conventions, one translation. The verifier's text keeps a point as an array, the highest
bit first: place a holds the coordinate of bit m - 1 - a (`First.ProdV.layBack`, `stepDown`,
`levelVars`). The specification keeps it as a list, coordinate i with bit i (`TwV.eqN`). So a point
is reversed, and nothing else: `byBit`. An order of binding is in both a list whose member l is the
bit that round l fixes: it is not translated. Challenges and end values are by round, and by number,
in both: they are not reordered.

Which bit is which. A key's number is its place in the part. A leaf of the table side has the number
u * 2 ^ w + j: row u, plane j: the plane's bits are the low ones. A level's new bit is the highest:
the first end value is the level below on the half where that bit is 0, the second on the half where
it is 1.

What "round" holds. The later variables are summed with their equality weights, the earlier ones
stand at their challenges, and there is no equality factor of the round's own variable or of an
earlier one in it (`pjRound`, `wtN`). All coefficients, lowest first: three, but two in the leaves'
rounds that bind a plane's bit.

Limits.
One part of keys alone. The specification has one key vector. At `Stage.split`, and at
`Stage.key i m` with i not 0, the entry is `idle`: empty lists, which the masked sumcheck's part
pads with zeros without a warning. A proof file's lookup has one part.
A bit is read as 0 at a plane from n + 2 on, whatever the input holds there.
It is slow: a round of a sumcheck with m variables costs up to about 4 ^ m steps, each in arithmetic
on long numbers, and every value of a tree's level is made anew from the leaves at every reading. It
is meant for statements and for small tests: at the lookups of the small example,
which have from 2 ^ 22 keys up, it cannot be evaluated.
Nothing here says that a `Job` is right: that is the matter of the statements beside it. Nothing
here plays a round or hears one: that these lists make the verifier's claims 0 is tested, by
evaluation, in the lookup's small synthetic example (Honest/K3/Toy.lean). `numsFit` tests at one
shift and one alpha, and at the corners of the cube alone.
`up` reads words as numbers modulo the prime; `down (up x) = x` where the words of x are below the
prime.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages
import Johnson.HonestTrace.LookDefs
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE)
open OnBytes.HonestTrace.Look (Job Data tieJob keyJob tabJob leavesJob bitsJob)

/-! ## 1 Between the two sorts of elements -/

/-- The library's extension field. -/
abbrev KE : Type := Cb.Gl.E

/-- One of the program's elements, in the library's field: the library's own reading
(OnBytes/Slice/ProgField.lean), under a short name. -/
abbrev up (x : E) : KE := OnBytes.Slice.readE x

/-- An element of the library's field, as the program's: words below the prime. -/
def down (x : KE) : E := OnBytes.E.ofTriple (OnBytes.Slice.ofE x)

/-- Lists, member by member. -/
def ups (l : List E) : List KE := l.map up

/-- Lists, member by member. -/
def downs (l : List KE) : List E := l.map down

/-! ## 2 The one translation of points -/

/-- **A point of the verifier's text (an array, the highest bit first) as the specification's (a
list, coordinate i with bit i)**: reversed. -/
def byBit (z : Array E) : List KE := ups z.toList.reverse

/-- Back. -/
def backBit (z : List KE) : Array E := (downs z.reverse).toArray

/-! ## 3 The specification's data at a run -/

variable {P : Type}

/-- **The specification's data**, of public numbers (a function of the shift), the input and the
challenges in front: the keys are part 0's; a bit is 0 at a plane that does not count. -/
def dataAt (N : KE → TwV.Nums P KE) (w : Hidden) (p : Pts) : Data P KE where
  N := N (up p.theta)
  key := fun x => up (w.key p.theta 0 x)
  bits := fun u j => if j < (N (up p.theta)).n + 2 then up (w.bit u j) else 0
  al := up p.alpha

/-! ## 4 The filling -/

/-- **A job of the specification as a stage's summand**: round, inY and ends, field by field. -/
def carry (J : Hidden → Pts → Job KE) : StageJob Hidden where
  round := fun w p rs => downs ((J w p).round (ups rs))
  inY := fun w p rs m => downs ((J w p).inY (ups rs) (ups m))
  ends := fun w p rs => downs ((J w p).ends (ups rs))

/-- Empty lists: at a stage that sends nothing, and at a stage for which the specification has no
job. -/
def idle : StageJob Hidden where
  round := fun _ _ _ => []
  inY := fun _ _ _ _ => []
  ends := fun _ _ _ => []

/-- **The specification's job at a stage**, at the run's points; none at a stage that sends nothing,
at the parts' step, and at a part of keys other than the first. -/
def jobAt (N : KE → TwV.Nums P KE) (w : Hidden) (p : Pts) : Stage → Option (Job KE)
  | .tie s => some (tieJob (dataAt N w p) s)
  | .key 0 m => some (keyJob (dataAt N w p) m (byBit (p.keyPt 0 m)))
  | .tab l => some (tabJob (dataAt N w p) l (byBit (p.tabPt l)))
  | .leaves => some (leavesJob (dataAt N w p) (byBit (p.tabPt (N (up p.theta)).d)))
  | .bits => some (bitsJob (dataAt N w p) (byBit p.zeroPt))
  | _ => none

/-- **The specification's filling of the row's letter**, at public numbers N. -/
def specJobs (N : KE → TwV.Nums P KE) : LookJobs Hidden where
  job
    | .tie s => carry fun w p => tieJob (dataAt N w p) s
    | .key 0 m => carry fun w p => keyJob (dataAt N w p) m (byBit (p.keyPt 0 m))
    | .tab l => carry fun w p => tabJob (dataAt N w p) l (byBit (p.tabPt l))
    | .leaves => carry fun w p => leavesJob (dataAt N w p) (byBit (p.tabPt (N (up p.theta)).d))
    | .bits => carry fun w p => bitsJob (dataAt N w p) (byBit p.zeroPt)
    | _ => idle

/-! ## 5 At a proof file's lookup -/

/-- **The filling at a proof file's lookup of shape h.** The numbers lm and jLK say where hidden
values lie: no job reads them; they stand here so that the public numbers are the term that the
specification's statements have. -/
def specJobsF (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat) : LookJobs Hidden :=
  specJobs fun theta => _root_.Fo.numsF h lm jLK theta

/-! ## 6 Public numbers made of a face -/

/-- A ledger without places. -/
def noLed : TwV.Led Unit := ⟨fun _ _ => (), (), fun _ => ()⟩

/-- **Public numbers of a face with one part**, a table (of the shift: the value of row u) and a
padding (row, how many keys): the face has the padding by keys and the table at points alone. The
orders are those by which the verifier's text goes: the face's for the key tree;
`orderDefault` for the table side; the leaves' and the bits' round j binds bit m - 1 - j. The two
subtractions are among the natural numbers: at a first part of size 0, or at fewer than two planes,
the numbers are another lookup's. -/
def numsOf (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (theta : KE) :
    TwV.Nums Unit KE where
  v' := f.parts.headD 0 - 1
  d := f.d
  w := f.mu
  n := f.planes - 2
  tab := fun u => up (row (down theta) u)
  pads := pads
  oK := f.orders 0
  oT := fun l => OnBytes.Model.orderDefault (f.mu + l)
  oE := OnBytes.Model.orderDefault (f.mu + f.d)
  oB := OnBytes.Model.orderDefault (f.mu + f.d)
  kAt := fun _ => none
  kC := fun _ => 0
  bAt := fun _ _ => ()
  ledTie := fun _ => noLed
  ledK := fun _ => noLed
  ledT := fun _ => noLed
  ledE := noLed
  ledB := noLed

/-- The filling at such numbers. -/
def specJobsAt (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) : LookJobs Hidden :=
  specJobs (numsOf f row pads)

/-- The corner of the leaves' cube at row u and plane 0, as the face's `leaf` reads a point: one
coordinate for each round, the highest bit first. -/
def cornerOf (f : LFace) (u : Nat) : Array E :=
  ((List.range (f.mu + f.d)).map fun a =>
    if (u * 2 ^ f.mu).testBit (f.mu + f.d - 1 - a) then oneE else zeroE).toArray

/-- **A test that table and padding are the face's**, at one shift and one alpha: one part; the
public factor is the face's; at each row's corner the face's `leaf` is alpha - 1 - the row's value;
as many keys are padding. -/
def numsFit (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (theta alpha : E) : Bool :=
  f.parts.length == 1 &&
    down (TwV.fac (numsOf f row pads (up theta)) (up alpha)) == f.factor theta alpha &&
    ((List.range (2 ^ f.d)).all fun u =>
      f.leaf theta alpha (cornerOf f u) == down (up alpha - 1 - up (row theta u))) &&
    (pads.map (·.2)).sum == (f.padding.map (·.1)).sum

/-! ## 7 What the specification says of points and shape -/

/-- The points at which a stage's variables are summed, by round, as the specification has them. -/
def specPoints (N : KE → TwV.Nums P KE) (w : Hidden) (p : Pts) (s : Stage) : List E :=
  ((jobAt N w p s).map fun J => downs J.zs).getD []

/-- A stage's shape as the specification has it: for each variable the number of coefficients; the
degree in Y and the number of end values (counted at no challenges: it does not depend on them). -/
def specShape (N : KE → TwV.Nums P KE) (w : Hidden) (p : Pts) (s : Stage) :
    Option (List Nat × Option (Nat × Nat)) :=
  (jobAt N w p s).map fun J => (J.dg.map (· + 1), J.dY.map fun dY => (dY, (J.ends []).length))

/-- The same of a call of the masked sumcheck. -/
def shapeOf (k : VerifiableInference.Desc.Part.MaskedSum.Call) : List Nat × Option (Nat × Nat) :=
  (k.vs.map (·.d), k.ends.map fun e => (e.dY, e.n))

/-- The points of a call's variables. -/
def pointsOf (vs : List VerifiableInference.Desc.Part.MaskedSum.Var) : List E :=
  vs.filterMap fun
    | .point z _ => some z
    | .plain _ => none

/-! ## 8 The orders at a proof file's lookup -/

/-- Counting down from m - 1 is the list of the numbers below m, reversed. -/
theorem countDown_eq (m : Nat) :
    (List.range m).map (FoNums.placeOf m) = OnBytes.Model.orderDefault m := by
  unfold OnBytes.Model.orderDefault FoNums.placeOf
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1 ⊢

/-- At a proof file's lookup the specification's order for the key tree's level with l variables is
the face's. -/
theorem numsF_oK (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat) (theta : KE) (l : Nat) :
    (_root_.Fo.numsF h lm jLK theta).oK l = (VerifiableInference.Desc.K3.faceOf h).orders 0 l := rfl

/-- Its order for the table side's level number l is the one by which the verifier's text goes. -/
theorem numsF_oT (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat) (theta : KE) (l : Nat) :
    (_root_.Fo.numsF h lm jLK theta).oT l =
      OnBytes.Model.orderDefault ((VerifiableInference.Desc.K3.faceOf h).mu + l) := rfl

/-- Its orders for the leaves and for the bits: round j binds bit m - 1 - j. -/
theorem numsF_oE_oB (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat) (theta : KE) :
    (_root_.Fo.numsF h lm jLK theta).oE = OnBytes.Model.orderDefault (5 + h.d) ∧
      (_root_.Fo.numsF h lm jLK theta).oB = OnBytes.Model.orderDefault (5 + h.d) :=
  ⟨countDown_eq _, countDown_eq _⟩

#print axioms ProofFile.Honest.K3.countDown_eq
#print axioms ProofFile.Honest.K3.numsF_oK
#print axioms ProofFile.Honest.K3.numsF_oT
#print axioms ProofFile.Honest.K3.numsF_oE_oB

end ProofFile.Honest.K3
