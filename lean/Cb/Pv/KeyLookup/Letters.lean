-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Letters.lean: the letters of a lookup whose keys come in parts, and the joints
between the ten stretches of its chain.

It imports the library alone (no file of the port).

What it is for. The lookup is a chain of ten stretches: draw · fused tie · the parts' steps · join
point · the key sides · table · closing · zero point ·
bits · read-out. So that each stretch can be proved «from joint j to joint j + 1» alone, this file
fixes, before any
block is written: the public numbers and shapes (`Pub`, `Pub.Adm`); the data (`Dat`); the values
that the claims
speak of (`root`, `rest`, `fac`, `plane`, `pow`, `keyU`, `tabU`); ONE type of state for all inner
joints (`X`); and
for each joint a predicate on (state, entries) (`Drawn` … `Done`), made a joint of the library's
kind by `jt`.

THE JOINTS' STATE IS ONE FLAT RECORD, the same type at every
inner joint; which claims are open is said by the joint's predicate, not by the type. A block of the
library's
kind reads its data off a state of any type and nests that state in its own; so a stretch's block is
laid over `X`
and ends with a map back into `X` (a step without rounds). A family of types by recursion on the
parts then
lives inside a stretch and not at a joint.

Main names.
  `Pub`        parts (part i has 2^(v i) keys), d (2^d rows of the table), mu (2^mu places for
               planes), pl (live
               planes), the runs of padding and the one row that they hold, the last key level's
               first variables.
  `Pub.Adm p`  the conditions on public numbers and shapes (the library's `LkB.Adm` at the sum of
               the parts, and the
               port's tests of form as far as a proof may want them).
  `Dat`        `Pub`, states, entries, keys by part, table, and where the bit (row u, LIVE plane j)
               is.
  `Dat.bit`    the bit read off the entries: at a plane that is not live the constant 0, which
               stands for no entry.
  `SCl`        a masked claim on a scalar: value + ⟨mask form, entries⟩ = public target.
  `X`          the state at every inner joint.
  `Dat.jt`     the joint of the library's kind (`Cb.LdLkp.cj`) of a predicate: beside any riding
               joint R0; the exact
               side says Mu besides (a letter: «the planes hold the counts»).
  `Dat.In`, `Drawn`, `Tie k`, `Tied`, `Parts k`, `Roots`, `Joined`, `Keys k`, `Table l`, `Closed`,
      `Zero`, `Bitten`, `Done`.

Which variable is which. A number's bit t is variable t (`numLE`, the library's): in a key's number;
in a place of
the table's tree the plane's mu variables are the LOW ones, a row's bit t is variable mu + t. Level
l of a tree
holds, at the number y < 2^l, the product over all leaves whose number is y modulo 2^l.
The end claims on the keys (`cls`, `Out`: an `MCl`) are read by the library's `Blocks.ext` (`eqN`,
Blocks/Basic.lean): there coordinate t of the claim's point goes with bit v i − 1 − t of a key's
number (coordinate 0: the top bit); the tree's point is turned when the claim leaves it
(`LkInst.topCl`).

Not claimed. Nothing is proved here but that the file types. No block, no error, no round. Nothing
on an honest
prover. Places of masks are no letters of this file: each stretch brings its own.

-/
import Cb.Ld.LdLkpAsm2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.Lkp Finset

/-! ### the public record -/

/-- A run of padding: in part `part` the keys number first, first + 2^logStep, …: `length` of them.
-/
structure Run where
  part : ℕ
  first : ℕ
  logStep : ℕ
  length : ℕ
  deriving DecidableEq, Repr

/-- Key number b of part i lies in the run. -/
def Run.holds (r : Run) (i b : ℕ) : Bool :=
  r.part == i && decide (r.first ≤ b) && (b - r.first) % 2 ^ r.logStep == 0 &&
    decide ((b - r.first) / 2 ^ r.logStep < r.length)

/-- Everything public about one lookup. -/
structure Pub where
  /-- part i has 2^(parts[i]) keys -/
  parts : List ℕ
  /-- the table has 2^d rows -/
  d : ℕ
  /-- a count has 2^mu places for bits -/
  mu : ℕ
  /-- the first pl of them are live -/
  pl : ℕ
  /-- the runs of padding -/
  runs : List Run
  /-- the number of the one row of the table that every place of padding holds -/
  padRow : ℕ
  /-- the variables that the first rounds of each part's last key level bind, in that order -/
  order : List ℕ
  deriving DecidableEq, Repr

namespace Pub
variable (S : Pub)

/-- the number of parts; the bits of part i -/
def m : ℕ := S.parts.length
def v (i : ℕ) : ℕ := S.parts.getD i 0

/-- the number of all keys, padding counted; of all places of padding; of those in part i -/
def allKeys : ℕ := (S.parts.map fun x => 2 ^ x).sum
def padCount : ℕ := (S.runs.map (·.length)).sum
def padIn (i : ℕ) : ℕ := ((S.runs.filter fun r => r.part == i).map (·.length)).sum

/-- key number b of part i is padding -/
def isPad (i b : ℕ) : Bool := S.runs.any fun r => r.holds i b

/-- the least number of bits of a part -/
def least : ℕ := S.parts.foldl min (S.v 0)

/-- The conditions on public numbers and shapes; p is the characteristic where a statement says so.
-/
structure Adm (p : ℕ) : Prop where
  some   : 1 ≤ S.m
  planes : 2 ≤ S.pl
  room   : S.pl ≤ 2 ^ S.mu
  bits   : ∀ i < S.m, 1 ≤ S.v i ∧ S.v i < S.pl
  keys   : S.allKeys < 2 ^ S.pl
  pads   : S.padCount ≤ S.allKeys
  char   : 2 ^ S.d * (2 ^ S.pl - 1) < p
  /-- the table has at least two rows: the table's tree is laid as a chain of at least one level. At
  the key it is the port's own clause: its one caller refuses d = 0
  (OnBytes/Key/Ranges.lean:90, `lookupOk`); `Lkp.Public.ok` alone does
  not. -/
  tabs   : 1 ≤ S.d
  row    : S.padRow < 2 ^ S.d
  inPart : ∀ r ∈ S.runs, r.part < S.m ∧ 1 ≤ r.length ∧
    r.first + (r.length - 1) * 2 ^ r.logStep < 2 ^ S.v r.part
  apart  : S.runs.Pairwise fun a b => ∀ i k, ¬ (a.holds i k = true ∧ b.holds i k = true)
  notAll : ∀ i < S.m, S.padIn i < 2 ^ S.v i
  order  : (∀ j ∈ S.order, j + 1 < S.least) ∧ S.order.Nodup

end Pub

/-! ### the data -/

/-- The data of a lookup with parts. -/
structure Dat (E : Type) [Field E] [Fintype E] extends Pub where
  St : Type
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  /-- key number b of part i, any function of state and entries -/
  key : St → (J → E) → ℕ → ℕ → E
  tab : St → ℕ → E
  /-- where the bit (row u, plane j) is; read at j < pl alone -/
  bAt : ℕ → ℕ → J

attribute [instance] Dat.finJ Dat.decJ

/-- A masked claim on a scalar: mask form, public target. -/
structure SCl (E J : Type) where
  mf : J → E
  tg : E

def SCl.Holds {E J : Type} [Field E] [Fintype J] (c : SCl E J) (val : E) (μ : J → E) : Prop :=
  val + ∑ i, c.mf i * μ i = c.tg

/-- The extension of a vector of 2^k entries, bit t of an entry's number being variable t. -/
noncomputable def mleN {E : Type} [Field E] (k : ℕ) (f : ℕ → E) (pt : ℕ → E) : E :=
  Alg.mle (fun x : Fin k → Bool => f (numLE x)) fun i => pt i

/-- The state at every inner joint. Which fields a joint reads is said by its predicate. -/
structure X (E St J : Type) where
  st : St
  /-- the first draw -/
  al : E
  /-- on the product of the roots of the parts that are still together -/
  all : SCl E J
  /-- the tie's claim under way: on a product of powers of planes' roots -/
  run : SCl E J
  /-- on the root of part i -/
  roots : ℕ → SCl E J
  /-- on the root of plane j -/
  planes : ℕ → SCl E J
  /-- the table side's one claim, at the point pt -/
  top : SCl E J
  /-- the join point (variables below mu), and behind it the table's levels' draws -/
  pt : ℕ → E
  /-- the end claim on part i's keys -/
  cls : ℕ → MCl E J
  /-- the zero point -/
  zt : ℕ → E
  /-- all rows so far -/
  rows : List (Row E J)

noncomputable section
namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E)

abbrev XS : Type := X E A.St A.J

/-- What is left at the end: state, a claim a part, the rows. -/
abbrev Out : Type := A.St × (Fin A.m → MCl E A.J) × List (Row E A.J)

/-- The state right after the first draw: no claim, no row. -/
def ini (st : A.St) (al : E) : A.XS :=
  { st := st, al := al, all := ⟨0, 0⟩, run := ⟨0, 0⟩, roots := fun _ => ⟨0, 0⟩, planes := fun _ =>
      ⟨0, 0⟩,
    top := ⟨0, 0⟩, pt := 0, cls := fun _ => ⟨0, 0, 0⟩, zt := 0, rows := [] }

/-! ### the values -/

/-- The bit (row u, plane j). At a plane that is not live: 0, and no entry is read. -/
def bit (μ : A.J → E) (u j : ℕ) : E := if j < A.pl then μ (A.bAt u j) else 0

/-- the root of part i; the product of the roots from part k on -/
def root (st : A.St) (μ : A.J → E) (al : E) (i : ℕ) : E := keyProd (A.v i) (A.key st μ i) al
def rest (st : A.St) (μ : A.J → E) (al : E) (k : ℕ) : E := ∏ i ∈ Ico k A.m, A.root st μ al i

/-- the public factor for padding -/
def fac (st : A.St) (al : E) : E := (al - A.tab st A.padRow) ^ A.padCount

/-- the root of plane j (1 at a plane that is not live); the product of the planes from k on, plane
j to the
power 2^(j - k) -/
def plane (st : A.St) (μ : A.J → E) (al : E) (j : ℕ) : E := tabProd A.d (A.tab st) (A.bit μ) al j
def pow (st : A.St) (μ : A.J → E) (al : E) (k : ℕ) : E :=
  ∏ j ∈ Ico k A.pl, A.plane st μ al j ^ 2 ^ (j - k)

/-- level l of part i's tree, at the number y -/
def keyU (st : A.St) (μ : A.J → E) (al : E) (i l y : ℕ) : E :=
  ∏ z ∈ range (2 ^ (A.v i - l)), (al - A.key st μ i (y + 2 ^ l * z))

/-- a leaf of the table's tree; level l, at the number (plane | y) = plane + 2^mu y -/
def leaf (st : A.St) (μ : A.J → E) (al : E) (u j : ℕ) : E := 1 + A.bit μ u j * (al - 1 - A.tab st u)
def tabU (st : A.St) (μ : A.J → E) (al : E) (l n : ℕ) : E :=
  ∏ z ∈ range (2 ^ (A.d - l)), A.leaf st μ al (n / 2 ^ A.mu + 2 ^ l * z) (n % 2 ^ A.mu)

/-- the bit at the number (plane | row) -/
def bitN (μ : A.J → E) (n : ℕ) : E := A.bit μ (n / 2 ^ A.mu) (n % 2 ^ A.mu)

/-! ### what the joints say -/

/-- A property of the data, on shapes: a place of padding holds the padding's row. -/
def PadIs : Prop := ∀ st μ i b, A.isPad i b = true → A.key st μ i b = A.tab st A.padRow

/-- all are bits; the counts add up to the number of keys that are not padding -/
def Bts (μ : A.J → E) : Prop := Bits A.d A.mu (A.bit μ)
def Num (μ : A.J → E) : Prop :=
  ∑ u ∈ range (2 ^ A.d), ∑ j ∈ range A.pl, (2 : E) ^ j * A.bit μ u j =
    ((A.allKeys - A.padCount : ℕ) : E)

/-- `Num` as a row. -/
def numRow : Row E A.J :=
  ⟨fun i => ∑ u ∈ range (2 ^ A.d), ∑ j ∈ range A.pl, if A.bAt u j = i then (2 : E) ^ j else 0,
    ((A.allKeys - A.padCount : ℕ) : E)⟩

/-- JOINT 0, on the caller's state: every key of every part is a row of the table. -/
def In (st : A.St) (μ : A.J → E) : Prop := ∀ i < A.m, InTable (A.v i) A.d (A.key st μ i) (A.tab st)

variable (x : A.XS) (μ : A.J → E)

/-- what rides from the draw to the bits' test and the read-out; the rows so far -/
def Side : Prop := (A.Bts μ ∧ A.Num μ) ∧ RowsHold x.rows μ

def AllPlanes : Prop := ∀ j < A.pl, (x.planes j).Holds (A.plane x.st μ x.al j) μ
def AllRoots : Prop := ∀ i < A.m, (x.roots i).Holds (A.root x.st μ x.al i) μ
def AllCls : Prop := ∀ i < A.m, (x.cls i).Holds (A.v i) (A.key x.st μ i) μ

/-- JOINT 1, after the draw: the product of all roots is the factor times the planes' powers. -/
def Drawn : Prop := A.Side x μ ∧ A.rest x.st μ x.al 0 = A.fac x.st x.al * A.pow x.st μ x.al 0

/-- INSIDE STRETCH 2, after k steps of the tie (1 ≤ k ≤ pl - 1; the first is the fused one). -/
def Tie (k : ℕ) : Prop :=
  A.Side x μ ∧ x.all.Holds (A.rest x.st μ x.al 0) μ ∧ x.run.Holds (A.pow x.st μ x.al k) μ ∧
    ∀ j < k, (x.planes j).Holds (A.plane x.st μ x.al j) μ

/-- JOINT 2, after the tie. -/
def Tied : Prop := A.Side x μ ∧ x.all.Holds (A.rest x.st μ x.al 0) μ ∧ A.AllPlanes x μ

/-- INSIDE STRETCH 3, after k of the m - 1 parts' steps (`Parts 0` is `Tied`). -/
def Parts (k : ℕ) : Prop :=
  A.Side x μ ∧ A.AllPlanes x μ ∧ x.all.Holds (A.rest x.st μ x.al k) μ ∧
    ∀ i < k, (x.roots i).Holds (A.root x.st μ x.al i) μ

/-- JOINT 3, after the parts' steps. -/
def Roots : Prop := A.Side x μ ∧ A.AllPlanes x μ ∧ A.AllRoots x μ

/-- the table side's claim at level l -/
def TopAt (l : ℕ) : Prop := x.top.Holds (mleN (A.mu + l) (A.tabU x.st μ x.al l) x.pt) μ

/-- JOINT 4, after the join point. -/
def Joined : Prop := A.Side x μ ∧ A.AllRoots x μ ∧ A.TopAt x μ 0

/-- INSIDE STRETCH 5, after k key sides (`Keys 0` is `Joined`). -/
def Keys (k : ℕ) : Prop :=
  A.Side x μ ∧ A.TopAt x μ 0 ∧ (∀ i < k, (x.cls i).Holds (A.v i) (A.key x.st μ i) μ) ∧
    ∀ i < A.m, k ≤ i → (x.roots i).Holds (A.root x.st μ x.al i) μ

/-- JOINT 5 (l = 0) and INSIDE STRETCH 6, after l levels of the table's tree; JOINT 6 is l = d. -/
def Table (l : ℕ) : Prop := A.Side x μ ∧ A.AllCls x μ ∧ A.TopAt x μ l

/-- JOINT 7, after the closing: its row is among the rows. -/
def Closed : Prop := A.Side x μ ∧ A.AllCls x μ

/-- JOINT 8, after the zero point: «all are bits» has become a claim at that point. -/
def Zero : Prop :=
  (A.Num μ ∧ RowsHold x.rows μ) ∧ A.AllCls x μ ∧
    mleN (A.mu + A.d) (fun n => A.bitN μ n * (A.bitN μ n - 1)) x.zt = 0

/-- JOINT 9, after the bits' sumcheck: its rows are among the rows. -/
def Bitten : Prop := (A.Num μ ∧ RowsHold x.rows μ) ∧ A.AllCls x μ

/-- The read-out: a step without rounds; the row on the counts comes last. -/
def rd : A.Out := (x.st, fun i => x.cls i, x.rows ++ [A.numRow])

/-- JOINT 10, what is left: a claim a part, and the rows. -/
def Done (o : A.Out) : Prop :=
  (∀ i : Fin A.m, (o.2.1 i).Holds (A.v i) (A.key o.1 μ i) μ) ∧ RowsHold o.2.2 μ

/-! ### the joints, in the library's kind -/
section
variable {Ex : ExtSpec} {Kc M Wp : Type} (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
  (Mu : A.St → (A.J → E) → Prop)

/-- The joint of a predicate on (state, entries): beside R0; the exact side says Mu besides. -/
@[reducible] def jt (Φ : A.XS → (A.J → E) → Prop) : Rels Kc A.XS Ex (M × Wp) :=
  cj R0 msg (fun x => x.st) (fun x μ => Φ x μ ∧ Mu x.st μ) Φ

@[reducible] def jtIn : Rels Kc A.St Ex (M × Wp) :=
  cj R0 msg id (fun st μ => A.In st μ ∧ Mu st μ) A.In

@[reducible] def jtOut : Rels Kc A.Out Ex (M × Wp) :=
  cj R0 msg Prod.fst (fun o μ => A.Done μ o) fun o μ => A.Done μ o

end
end Dat
end
end Lk6
