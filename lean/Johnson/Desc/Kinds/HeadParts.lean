-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadParts.lean: what lies beneath the texts on the output head's own rounds
(Head.lean, Norm.lean, HeadRow.lean). It shows nothing by itself: definitions with code, no theorem,
nothing on soundness.

In order: the field's signs, points and forms; a hidden scalar; the parts of a block's hearing (a
point drawn, hidden scalars sent and batched, the masked sumcheck); a read's weights; named
constants. The norm's row of digits and its arithmetic are a part of their own
(OnBytes/Desc/First/P6/NormRow.lean).

STAND-INS, named as such. Form is `verify-on-bytes`'s Aff, and the ledger of hidden scalars its Fork
(OnBytes/Model/Hide.lean): of the ledger hideRun, shown and the field next are called by name.
THE MASKED SUMCHECK IS A PART OF ITS OWN (Johnson/Desc/Part/MaskedSum4.lean, MaskedSumMore.lean):
sumcheck and level here call its hear for the rounds, its rowLaid for what the row writes into the
ledger, and its rowForm for the form that is left.
A hearing reads a round's items and draws, and how many there are. A round's name and kind, the
element that is never 0, that no position or matrix entry is drawn: asked where a block's rounds are
held against the plan's entries, and by the strict reading that the kind's frame lays in front.

-/
import Johnson.Desc.Part.MaskedSumMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds

open OnBytes OnBytes.Model

/-! ## The field's signs, points, forms

E: the extension of degree 3 of the field of p = 2^64 - 2^32 + 1 elements. -/

scoped instance : Add E := ⟨addE⟩
scoped instance : Sub E := ⟨subE⟩
scoped instance : Mul E := ⟨mulE⟩
scoped instance : Pow E Nat := ⟨powE⟩
/-- A natural number in the base field: its residue modulo p. -/
def natF (v : Nat) : F := (v % pW.toNat).toUInt64
/-- A natural number in E. -/
def natE (v : Nat) : E := ofF (natF v)

scoped instance : NatCast E := ⟨natE⟩
scoped instance (n : Nat) : OfNat E n := ⟨natE n⟩
scoped instance : HMul Nat E E := ⟨fun n x => scaleE (natF n) x⟩
scoped instance : HMul E Nat E := ⟨fun x n => scaleE (natF n) x⟩

/-- A point: its coordinates, that of the highest bit first. -/
abbrev Point : Type := Array E

/-- The equality weight of the index i at the point z: a product with one factor for each coordinate
x of z: x if the coordinate's bit of i is 1, and 1 - x if it is 0. It is 0 from 2^(the number of
coordinates) on. -/
def eq (z : Point) (i : Nat) : E :=
  if i < 2 ^ z.size then
    (z.foldl (fun (s : E × Nat) x =>
      (if i.testBit (s.2 - 1) then s.1 * x else s.1 - s.1 * x, s.2 - 1)) (1, z.size)).1
  else 0

/-- All equality weights of a point, made once: entry i is eq z i. -/
def eqAll (z : Point) : Array E :=
  z.foldl (fun t x => t.foldl (fun n a => (n.push (a - a * x)).push (a * x)) #[]) #[1]

/-- 1/2. -/
def half : E := invE 2

/-- n coordinates 1/2: under them an equality-weighted sum over n bits is 2^-n times the plain
sum. -/
def halves (n : Nat) : Point := Array.replicate n half

/-- The last n coordinates. -/
def Point.last (z : Point) (n : Nat) : Point := z.extract (z.size - n) z.size

/-- A public constant plus public coefficients on hidden scalars and on entries of committed
vectors. -/
abbrev Form : Type := Aff

scoped instance : Coe E Form := ⟨Aff.ofConst⟩
scoped instance : NatCast Form := ⟨fun n => Aff.ofConst (natE n)⟩
scoped instance (n : Nat) : OfNat Form n := ⟨Aff.ofConst (natE n)⟩
scoped instance : HSMul E Form Form := ⟨fun k f => Aff.scale f k⟩
scoped instance : HSMul Nat Form Form := ⟨fun k f => Aff.scale f (natE k)⟩
scoped instance : HAdd Form E Form := ⟨fun f x => f + Aff.ofConst x⟩
scoped instance : HAdd E Form Form := ⟨fun x f => Aff.ofConst x + f⟩
scoped instance : HSub Form E Form := ⟨fun f x => f - Aff.ofConst x⟩
scoped instance : HAdd Form Nat Form := ⟨fun f n => f + Aff.ofConst (natE n)⟩
scoped instance : HSub Form Nat Form := ⟨fun f n => f - Aff.ofConst (natE n)⟩

/-- The least w with n <= 2^w. -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- The sum of f i over i < n. -/
def sumTo {α : Type} [Add α] [OfNat α 0] (n : Nat) (f : Nat → α) : α :=
  (List.range n).foldl (fun s i => s + f i) 0

@[inherit_doc sumTo]
scoped macro "∑ " i:ident " < " n:term ", " f:term:67 : term => `(sumTo $n fun $i => $f)

/-- A hidden scalar is sent masked: the verifier sees what is shown, and has the scalar itself only
as a variable of a form. -/
structure Hid where
  var : Form := {}
  shown : E := zeroE
  deriving Inhabited

/-! ## The parts of a hearing -/

/-- The verifier on a block's own rounds: from the ledger of hidden scalars and the rounds not yet
read: nothing, or a value, the ledger behind and the rounds that are left. -/
def Hear (α : Type) : Type := Fork → List Fmt.RoundView → Option (α × Fork × List Fmt.RoundView)

instance : Monad Hear where
  pure a := fun F rs => some (a, F, rs)
  bind x f := fun F rs =>
    match x F rs with
    | some (a, G, left) => f a G left
    | none => none

/-- The value, or a refusal. -/
def Hear.need {α : Type} (x : Option α) : Hear α := fun F rs => x.map fun a => (a, F, rs)

/-- The next round: n scalars are sent, k elements are drawn. -/
def Hear.round (n k : Nat) : Hear (List E × List E) := fun F rs =>
  match rs with
  | r :: left => (Part.MaskedSum.roundOf n k r).map fun x => (x, F, left)
  | [] => none

/-- The next n rounds, whole. -/
def Hear.stretch (n : Nat) : Hear (List Fmt.RoundView) := fun F rs =>
  if rs.length < n then none else some (rs.take n, F, rs.drop n)

/-- The ledger. -/
def Hear.ledger : Hear Fork := fun F rs => some (F, F, rs)

/-- The ledger is laid. -/
def Hear.lay (F : Fork) : Hear Unit := fun _ rs => some ((), F, rs)

/-- Scalars that were sent are laid into the ledger as hidden scalars, under the next numbers, each
with the factor 1 on its mask. -/
def hide (v : List E) : Hear (Array Hid) := fun F rs =>
  (({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray oneE).map fun G =>
    (v.toArray.mapIdx fun j x => { var := Aff.slot (F.next + j), shown := x }, G, rs)

/-- The n hidden scalars under the numbers from first on. -/
def hiddenFrom (first n : Nat) : Hear (Array Hid) := fun F rs =>
  ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
    ({ var := Aff.slot (first + j), shown := x } : Hid)).map fun l => (l.toArray, F, rs)

/-- One round: the prover sends nothing; n elements are drawn. -/
def drawPoint (n : Nat) : Hear Point := do pure (← Hear.round 0 n).2.toArray

/-- The same under another name of round: a point on the numbers of things that are batched. -/
def drawJoin (n : Nat) : Hear Point := drawPoint n

/-- One round: the prover sends n hidden scalars; one element is drawn, to batch them in runs of
rows. -/
def sendThenBatch (n : Nat) (_rows : Nat := n) : Hear (Array Hid × E) := do
  let (v, g) ← Hear.round n 1
  pure (← hide v, ← Hear.need g.head?)

/-- A masked sumcheck, as it was heard. -/
structure Sum where
  /-- the challenges, in the order of the rounds -/
  r : Point := #[]
  /-- the claimed sum, where the prover sends one -/
  claimed : Hid := {}
  /-- the end values -/
  ends : Array Hid := #[]
  /-- of a level: the element drawn in its last round -/
  down : E := zeroE
  /-- the rest of what was heard, as the part hands it back -/
  psc : Option Part.MaskedSum.Heard := none
  deriving Inhabited

/-- End value j. -/
def Sum.end_ (s : Sum) (j : Nat) : Hid := s.ends.getD j {}

/-- The one form that the sumcheck leaves: the part's rowForm. It is 0 just if the hiding polynomial
and eps times the summand, at the challenges, continue the rounds from a sum that equals the start
form. S0: the summand on the end values as shown; their masks are in the form. Where there is no
sumcheck: the constant 1, a form that is never 0. -/
def Sum.left (s : Sum) (S0 : E) : Form :=
  (s.psc.map fun h => Part.MaskedSum.rowForm h S0 {}).getD (Aff.ofConst oneE)

/-- The part's hearing of a sumcheck in the coordinates of z, each round's polynomial of three
coefficients, two in the further variable. lead: how many scalars of the caller's stand in front in
the first message: they are laid into the ledger as hidden scalars first; C: the start form, of
these. Behind the hearing the part's rowLaid: the hiding polynomial's coefficients get their numbers
among the hidden scalars at the hearing. Returns the lead, and the sumcheck. -/
def heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    Hear (Array Hid × Sum) := do
  let rs ← Hear.stretch (z.size + 3)
  let k : Part.MaskedSum.Call :=
    { lead, vs := z.toList.map (.point · 3), ends := some ⟨2, ends⟩ }
  let c ← hide (← Hear.need (Part.MaskedSum.leadScalars k rs))
  let (h, G) ← Hear.need (Part.MaskedSum.hear (C c) k (← Hear.ledger) rs)
  Hear.lay (← Hear.need (Part.MaskedSum.rowLaid h G))
  pure (c, { r := (Part.MaskedSum.challenges k h).toArray, ends := ← hiddenFrom h.sEnd ends,
             psc := some h })

/-- A masked sumcheck of a sum of products of two maps, under the equality weights of the point z.
The start form is the claimed sum, which the prover sends. Rounds: the claimed sum and the hiding
polynomial's sum, eps; one round for each coordinate of z; a round in a further variable, beta; the
end values. -/
def sumcheck (z : Point) (ends : Nat) : Hear Sum := do
  let (c, s) ← heardBy 1 (fun c => (c.getD 0 {}).var) z ends
  pure { s with claimed := c.getD 0 {} }

/-- The same for a sum that the prover does not send: start is the form that it must equal; it is
fixed before eps is drawn. Two end values. It ends in a round of its own in which one element is
drawn: a level of a product tree hands that element down; where there is no level beneath, nothing
reads it. -/
def level (z : Point) (start : Form) : Hear Sum := do
  let (_, s) ← heardBy 0 (fun _ => start) z 2
  let (_, g) ← Hear.round 0 1
  pure { s with down := ← Hear.need g.head? }

/-- What a round is, for the table of rounds: so many scalars are sent in the clear (masked or not),
so many elements are drawn. No round of these parts has an oracle message. -/
structure Round where
  /-- the round's name in the format's list of rounds -/
  name : String
  sent : Nat
  drawn : Nat
  /-- the drawn element is drawn by the rule that never gives 0 -/
  notZero : Bool := false
  /-- for a round that batches rows: how many -/
  rows : Nat := 0
  deriving BEq, Repr

/-- The round's entry in the plan. An element takes 24 bytes. work: the setting's bits of work in
front of a challenge whose error is a field's; a round without a challenge has none. -/
def Round.entry (work : Nat) (r : Round) : Fmt.Entry :=
  { name := r.name, work := if r.drawn == 0 then 0 else work, msg := 24 * r.sent, drawE := r.drawn,
    drawNZ := if r.notZero then 1 else 0, rows := r.rows }

/-- The rounds of drawPoint, sendThenBatch, sumcheck and level. -/
def drawPoint.rounds (n : Nat) : List Round := [⟨"ZERO", 0, n, false, 0⟩]
@[inherit_doc drawPoint.rounds] def drawJoin.rounds (n : Nat) : List Round :=
  [⟨"JOIN", 0, n, false, 0⟩]
@[inherit_doc drawPoint.rounds] def sendThenBatch.rounds (n : Nat) (rows : Nat := n) : List Round :=
  [⟨"BAT-sigma", n, 1, false, rows⟩]
@[inherit_doc drawPoint.rounds] def sumcheck.rounds (m ends : Nat) : List Round :=
  ⟨"PSC epsilon", 2, 1, false, 0⟩ :: List.replicate m ⟨"PSC round", 2, 1, false, 0⟩
    ++ [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", ends, 0, false, 0⟩]
@[inherit_doc drawPoint.rounds] def level.rounds (m : Nat) : List Round :=
  ⟨"PSC epsilon", 1, 1, false, 0⟩ :: List.replicate m ⟨"PSC round", 2, 1, false, 0⟩
    ++ [⟨"PSC Y", 2, 1, true, 0⟩, ⟨"PSC values", 2, 0, false, 0⟩, ⟨"LINE", 0, 1, false, 0⟩]

/-! ## Reads -/

/-- A read sums a committed matrix's cells under public weights. long: entry i is a block of S2
features, weighed on the feature in the block and on the position. short: entry i is feature i,
weighed on the position. The range check ties each entry to the committed cells. -/
inductive Weights | long (onFeature onPosition : Nat → E) | short (onPosition : Nat → E)

/-- A claim on a committed matrix of weights Wh: the sum over v and k of
onVocabulary v * eq onFeatures k * Wh k v is value. The merge starts from such claims. -/
structure SumOnMatrix where
  value : Hid
  onFeatures : Point
  onVocabulary : Nat → E

/-! ## Named constants, and the digits' multipliers -/

/-- A cell holds a byte less 128; two cells at the radix 256 hold a number less 32896. -/
def off1 : Nat := 128
@[inherit_doc off1] def off2 : Nat := 32896
/-- A table value less its three cells at the radix 256: 128 * 65793 + 1. -/
def offE : Nat := 8421505
/-- What the digit over adds to a margin: more than any gap. -/
def BIG : Nat := 2 ^ 37

/-- The number of the row's digits that are the norm's. -/
def NR : Nat := 99

/-- The multiplier of digit j in its key: the key mul j * D j is in the range of 8 bits, so the
digit is below 256 / mul j. -/
def mul (j : Nat) : Nat :=
  if j == 9 then 4 else if j == 58 then 2 else if j == 59 then 128 else if j == 63 then 2
  else if j == 76 then 2 else if j == 79 then 32 else 1

end VerifiableInference.Desc.Kinds
