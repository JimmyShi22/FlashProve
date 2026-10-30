-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadLaw.lean: THE OUTPUT HEAD's LAW, AND THE NEXT TOKEN's: STATED. PROOFS: Law/.
Four statements, each a `def ... : Prop`, over the text of the two kinds of block as it stands
(Head.lean, HeadPublic.lean, HeadCells.lean, HeadParts.lean, HeadOk.lean, ReplyKind.lean).
Definitions with code; no theorem; no `sorry`; no axiom. No hash is named: these rounds use none.

THE FORMS AT THE CELLS. The head's forms take all that they read through classes. Here the classes
are filled from INTEGER CELLS and a point: a read is the constant form that holds its true sum,
under the weights that `Read.of` itself names; the one claimed sum is the constant form of the true
sum. A form so made has no variable left, and its value is its constant (`keyAt`, `clipAt`, ...).
Nothing of a form's formula is written a second time.
THE RELATION ON CELLS (`CellRel`) is made of the head's own forms AT THE CORNERS: at the point whose
coordinates are the bits of a position t, under the weights that are 1 at one entry x and 0
elsewhere (`corner x t`), the form `key k` is the key of entry x at position t, and `clip`, `table`
are the two lines at position t.

LEMMA 1 (`Lemma1Statement`): no chance in it. Under the tests on public numbers, weights of at most
  2^12 and activations of at most 2047 in absolute value: the relation on cells gives (a), (b), (c)
  of Head.lean's head, in integers (`Says`).
LEMMA 2a (`Lemma2aStatement`): no chance in it. At EVERY point the two guests and the five keys are
  the sums of their corner values under the equality weights: of degree 1 in each coordinate, in
  values that the cells and public data fix.
LEMMA 2b (`Lemma2bStatement`): the reduction, round by round, for the head's one masked sumcheck.
  For all cells and all mask entries, fixed beforehand, there is a function from partial transcripts
  to short lists of bad elements such that: a hearing that returns, whose two forms are 0, whose
  reads are true and whose claim on the weights is true, and in which no bad element was drawn, has
  the true claimed sum.
THE NEXT TOKEN's (`ReplyLemmaStatement`): no chance in it. The block lays its seat once, with a
  token; and a record whose seat holds what the last record's holds reads there the token that the
  client asked about.

WHAT IS NOT HERE. THIS IS THE HEAD's HALF: of the block's four sumchecks, 35 forms, nine keys and
twelve reads it covers one, six, five and five. The final norm's are not stated: that the
activations are the clamped norm of the committed stream, and at most 2047, is taken. That a read is
the sum of its cells, that a key is a row of its table, that the claim on the weights holds: other
blocks' laws. The length of a list of bad elements is a safe ceiling read off the rounds, not the
sumcheck's sharp degree. No tie to a theorem of another library. Nothing on what a proof hides.
WHAT HAS BEEN TRIED. The file elaborates. By runs on small made-up examples, which try the
DEFINITIONS and prove nothing: Lemma 2a's equations at one made-up point, and each corner value
against the integer that the head's words name (17 comparisons agree; 6 wrong variants part, a token
that is no token among them); Lemma 1 at cells that an honest prover would lay, at sizes that pass
the tests on the plan: all its conditions hold together and so do (a), (b), (c); at two cheats the
relation breaks; at a table without the upper bound the conditions hold and (b) fails. Lemma 2b and
the next token's lemma have been tried by no run.
EVERY NATURAL LETTER THAT IS LAID INTO THE FIELD, AND WHAT BOUNDS IT IN LEMMA 1 (a reading): n in
InBits, u in IsRow: by their definitions; tab u: TableOk; a cell: `small`; a weight, an activation:
the lemma's two conditions; y and the tokens: below V; C, theta, cap, V, d, T: the tests on the
plan. EVERY = AND ∈ ON FIELD ELEMENTS (a reading): in Lemma 1, 2a and 2b's conclusion both sides are
outputs of the field's operations or images of bounded naturals; the one membership, in `NoBad`,
stands under `Canonical`.
WHICH PUBLIC CONDITIONS EACH STATEMENT HAS (a reading of each term): Lemma 1: the tests on the plan
and the request, y < V, the table's, the two bounds. 2a: the request's and y < V; it is an identity
of sums and needs no bound and no test on the plan. 2b: the same two, a ledger in front that is well
laid, canonical elements; it speaks in the field alone and needs no bound. The next token's: none:
its V, T, r, e are letters.




`Canonical`, `NoBad` and Lemma 2b are stated over raw rounds.

-/
import Johnson.Desc.Kinds.HeadRow
import Johnson.Desc.Kinds.HeadOk
import Johnson.Desc.Kinds.ReplyKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open Norm (lt ls d lPd T S2)

/-! ## 1. Integer cells, and the classes filled from them -/

/-- An integer in the field. -/
def ofInt (z : Int) : E := if z < 0 then (0 : E) - (z.natAbs : E) else (z.natAbs : E)

/-- What was committed: the cells of the three matrices (matrix, feature, position), and the head's
weights (feature, vocabulary entry). -/
structure Cells where
  cell : Matrix → Nat → Nat → Int
  Wh : Nat → Nat → Int

/-- What comes in from the lookup: its point on the positions and on a block's features, and for
each key the weight of each block of entries. -/
structure Pt where
  (zt zl : Point)
  ewh : Key → Nat → E

/-- The n bits of i as a point, the highest first. -/
def bits (n i : Nat) : Point :=
  ((List.range n).map fun j => if i.testBit (n - 1 - j) then (1 : E) else 0).toArray

variable [Sizes] [Policy] [Request] [Token]

/-- The corner of entry x and position t. -/
def corner (x t : Nat) : Pt :=
  { zt := bits lt t, zl := bits ls (x % S2), ewh := fun _ i => if i == x / S2 then 1 else 0 }

/-- A key's first vocabulary entry. -/
def first : Key → Nat
  | .tableB => JVa
  | _ => 0

/-- The weight of entry x of key k: its block's, times the equality weight inside the block. -/
def Pt.ew (p : Pt) (k : Key) (x : Nat) : E := p.ewh k (x / S2) * eq p.zl (x % S2)

/-- The norm's class: of it the head's forms read the two points alone. -/
@[reducible] def Pt.normIn (p : Pt) : FinalNorm.In :=
  { zt := p.zt, zl := p.zl, ew := fun _ _ => 0, ewh := fun _ _ => 0, wsum := fun _ => 0 }

/-- The head's class, as HeadCells.lean's `In` says what each field is. -/
@[reducible] def Pt.headIn (p : Pt) : In :=
  { ew := p.ew, ewh := p.ewh
    wsum := fun k => ∑ x < len k, p.ew k x
    wx := fun k => ∑ x < len k, if first k + x < V then p.ew k x else 0
    below := fun v => ∑ x < v, p.ew .marginTop x }

/-- The activation of feature k at position t: two limbs. -/
def act (c : Cells) (t k : Nat) : Int := c.cell .act k t + 256 * c.cell .act (d + k) t

/-- Entry i of a read, in truth: the sum of its cells under its weights. An entry of a read with
long weights is a block of S2 features. -/
def readAt (c : Cells) (x : Matrix × Weights) (i : Nat) : E :=
  match x.2 with
  | .long f g => ∑ j < S2, ∑ t < T, f j * g t * ofInt (c.cell x.1 (S2 * i + j) t)
  | .short g => ∑ t < T, g t * ofInt (c.cell x.1 i t)

section At
variable [FinalNorm.In] [In]

/-- The second map of the head's sumcheck (Head.lean, `hear`): at a checked position, under the
top digit's weights, the weights' column of win t less that of each entry below V. -/
def UH (c : Cells) (k t : Nat) : E :=
  if checked t then
    wx .marginTop * ofInt (c.Wh k (win t)) - ∑ v < V, ew .marginTop v * ofInt (c.Wh k v)
  else 0

/-- The sum that 2^lPd times the claimed sum must be. -/
def trueSum (c : Cells) : E :=
  ∑ t < T, ∑ k < d, eq FinalNorm.zt t * ofInt (act c t k) * UH c k t

/-- What was heard, in truth, as far as the keys and the policy's forms read it. -/
@[reducible] def heardAt (c : Cells) : Heard :=
  { logits := { claimed := { var := ((OnBytes.invE (2 ^ lPd) * trueSum c : E) : Form) } } }

/-- The reads, in truth: constant forms. -/
@[reducible] def readsAt (c : Cells) [Heard] : Reads :=
  { entry := fun r i => ((readAt c r.of i : E) : Form) }

end At

/-- A form of the head at the cells and a point: its constant. -/
def formAt (c : Cells) (p : Pt)
    (f : [FinalNorm.In] → [In] → [Heard] → [Reads] → Form) : E :=
  let _ := p.normIn
  let _ := p.headIn
  let _ := heardAt c
  let _ := readsAt c
  f.const

def keyAt (c : Cells) (p : Pt) (k : Key) : E := formAt c p (key k)
def clipAt (c : Cells) (p : Pt) : E := formAt c p clip
def tableAt (c : Cells) (p : Pt) : E := formAt c p table
def meanAt (c : Cells) : E := formAt c (corner 0 0) mean
def countAt (c : Cells) : E := formAt c (corner 0 0) count

/-! ## 2. The relation on cells -/

/-- A number below 2^w. -/
def InBits (w : Nat) (x : E) : Prop := ∃ n : Nat, n < 2 ^ w ∧ x = (n : E)

/-- A row of the table: u with row u's value. -/
def IsRow (tab : Nat → Nat) (x : E) : Prop :=
  ∃ u : Nat, u < 2 ^ 16 ∧ x = ((u + 2 ^ 16 * tab u : Nat) : E)

/-- Row 0 holds 2^F; every row at least 1 AND AT MOST 2^F. Without the upper bound Lemma 1 is false:
`IsRow` lays u + 2^16 * tab u into the field, where a large value wraps, and a row could then stand
for "middle digit 0, table value 1". -/
def TableOk (tab : Nat → Nat) : Prop := tab 0 = 2 ^ F ∧ ∀ u, 1 ≤ tab u ∧ tab u ≤ 2 ^ F

/-- THE RELATION: what the lookup, the range check and the one tested equation are meant to leave of
the head's cells, entry by entry and position by position. -/
structure CellRel (c : Cells) (tab : Nat → Nat) : Prop where
  small : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18
  /-- the 21 digits of the six numbers are bytes: the norm's key on the row's digits -/
  bytes : ∀ t, t < T → ∀ j, j < 21 →
    0 ≤ c.cell .row (NR + j) t + 128 ∧ c.cell .row (NR + j) t + 128 < 256
  top : ∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c (corner x t) .marginTop)
  mid : ∀ t, t < T → ∀ x, x < JV → InBits 16 (keyAt c (corner x t) .marginMid)
  low : ∀ t, t < T → ∀ x, x < JV → InBits 8 (keyAt c (corner x t) .marginLow)
  rowA : ∀ t, t < T → ∀ x, x < len .tableA → IsRow tab (keyAt c (corner x t) .tableA)
  rowB : ∀ t, t < T → ∀ x, x < len .tableB → IsRow tab (keyAt c (corner x t) .tableB)
  lines : ∀ t, t < T → clipAt c (corner 0 t) = 0 ∧ tableAt c (corner 0 t) = 0
  sums : meanAt c = 0 ∧ countAt c = 0

/-! ## 3. What an accepted proof is about, in integers (Head.lean's head) -/

def sumZ (n : Nat) (f : Nat → Int) : Int := (List.range n).foldl (fun s i => s + f i) 0

/-- The integer logit of vocabulary entry v at position t. -/
def logit (c : Cells) (t v : Nat) : Int := sumZ d fun k => act c t k * c.Wh k v

/-- The largest of logit t v - logit t (win t) + [v < win t] over v < V. At v = win t that is 0. -/
def gap (c : Cells) (t : Nat) : Int :=
  (List.range V).foldl
    (fun m v => max m (logit c t v - logit c t (win t) + if v < win t then 1 else 0)) 0

def cost (c : Cells) (t : Nat) : Int := gap c t + 2 ^ sh

/-- (a), (b), (c). -/
structure Says (c : Cells) : Prop where
  a : sumZ T (fun t => if costed t then min (cost c t) C else 0) ≤ theta * RC
  b : ((List.range T).filter fun t => costed t && decide ((C : Int) < cost c t)).length ≤ cap
  c : e = T → gap c (T - 1) = 0

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open Norm (lt ls d lPd T S2)

/-! ## 4. The statements -/

/-- **LEMMA 1**: from the relation on cells to the claim under the policy. PROVED: `lemma1`. No
chance in it. -/
def Lemma1Statement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat) (c : Cells),
    planOk sT = true → Request.ok = true → y < V → TableOk tab →
    (∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) → (∀ t k, (act c t k).natAbs ≤ 2047) →
    CellRel c tab → Says c

/-- **LEMMA 2a**: the guests and the keys at a point are made of their corner values. PROVED:
`lemma2a`. No chance in it. For clip and table it is the first half of what a host that draws zt
coordinate by coordinate needs of a guest: THE DEGREE: the value at zt is a polynomial of degree 1
in each coordinate, in whose coefficients the point does not occur: they are functions of the cells
and public data; it is 0 at every corner exactly if it is the zero polynomial. For a key it says the
same in zt, and that the key is linear in the weights of its entries: `ewh`, a free letter here,
with zl, which is borrowed from the host too. That these are equality weights of the column's
coordinates is HeadIn.lean's, and is not stated.
THE REQUEST's TOKENS AND y MUST BE BELOW V: the ties' term sums the top key's
weights below win t, and beyond the key's entries these are a free letter. The tests on the plan are
not needed.
WHAT IT DOES NOT SAY. THE ORDER IN TIME, the second half of the host's premise: that every value is
fixed before the first round that draws a coordinate of the point. `Cells` is a letter: nothing here
ties it to a message. That is owed where the blocks are laid in a link: the cells lie in messages
sent in front of the lookup. WHICH coordinates of the host's point zt is: its last lt. And THE FORM
THAT IS TESTED at zt reads entries of reads, which are committed BEHIND zt: it is this polynomial
only through the reads' own law (a read is the sum of its cells: the range check's).
In a library of ours that is not in this repository with this file, the lookup's lemma already takes
such guests as a parameter: a family of arrays that are tested on the lookup's challenges. No tie to
it is stated. -/
def Lemma2aStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (c : Cells) (p : Pt), Request.ok = true → y < V →
    p.zt.size = lt → p.zl.size = ls →
    clipAt c p = (∑ t < T, eq p.zt t * clipAt c (corner 0 t)) ∧
    tableAt c p = (∑ t < T, eq p.zt t * tableAt c (corner 0 t)) ∧
    ∀ k, keyAt c p k = ∑ x < len k, ∑ t < T, p.ew k x * eq p.zt t * keyAt c (corner x t) k

/-- The hidden scalar under number j: what was shown, less its factor times its mask entry. -/
def hidden (F : Fork) (mask : Nat → E) (j : Nat) : E :=
  F.vp.getD j 0 - F.mf.getD j 0 * mask j

/-- A form without entries of reads, at the hidden scalars. -/
def atHidden (F : Fork) (mask : Nat → E) (f : Form) : E :=
  f.slots.foldl (fun s x => s + x.2 * hidden F mask x.1) f.const

/-- Every element that is sent or drawn is written in the one canonical way: each of its three words
is below the prime. A round holds an element as three machine words, and two elements are equal if
the words are; the field's operations take residues first. So without this a field element would
have several writings, alike in every form and unlike for "is in the list". Who
pays it: the test on the view in front of all blocks. -/
def Canonical (t : List Fmt.RoundView) : Prop :=
  ∀ r, r ∈ t →
    (∀ x, Fmt.ItemValue.e x ∈ r.vals → OnBytes.okE (E.ofTriple x) = true) ∧
    ∀ x, x ∈ r.drawn.elems → OnBytes.okE (E.ofTriple x) = true

/-- The ledger has a place for each of its numbers: a mark, a shown value and a factor. In a ledger
that has not, what is laid under a number would be lost without a word. WHO PAYS IT: the verifier
itself: it makes the three lists at the plan's count of numbers before anything is heard, and laying
a number keeps their lengths. -/
def WellLaid (F : Fork) : Prop := F.gotF.size = F.ns ∧ F.vp.size = F.ns ∧ F.mf.size = F.ns

/-- No element that was drawn is bad for the transcript up to the message in front of it: the rounds
in front, whole, and of this round the message alone: ALL that it draws is struck (elements,
positions, matrix entries, the digest), so that the rule can read nothing that comes with the draw.
-/
def NoBad (bad : List Fmt.RoundView → List E) (t : List Fmt.RoundView) : Prop :=
  ∀ i r, t[i]? = some r → ∀ x, x ∈ r.drawn.elems →
    E.ofTriple x ∉ bad (t.take i ++ [{ r with drawn := ⟨[], [], [], none⟩ }])

/-- **LEMMA 2b**: the head's one sumcheck, round by round. PROVED: `lemma2b`. The
sumcheck is the third line of Head.lean's `hear`, called as it is called there.
IN: 2^lPd times the claimed sum, which the top digit's key holds, is the true sum at zt.
OUT: the sumcheck's own form and the form on its first end value are 0; the claim on the weights,
whose value is the second end value, is true. The reads stand at their true values BY THE WAY THE
CLASSES ARE FILLED (`readsAt`), not as a condition: that they are true is the range check's law.
ERROR: in each round that draws, at most as many bad elements as the round sends scalars, and one.
WHY THAT CEILING IS SAFE HERE (`lemma2b` proves it; a reading of `sumcheck.rounds` and `heardBy` in
HeadParts.lean says why): every round of this sumcheck that draws sends two scalars and draws ONE
element. The first element drawn enters the running claim linearly. Each further round's message is
a polynomial of three coefficients, one of them derived: degree 2. So 3 is above each degree. The
part's own law may sharpen it. THE LAST ELEMENT (beta) MUST NOT BE 0 for the masks to bind, and at
these bytes no line of the hearing asks that: the rule may list 0 there beside the two roots: three
in all: the ceiling has just that room. A round is raw here: beside elements it may hold other
items, positions, matrix entries, a digest: the hearing takes a round only in the shape that it
asks, or does not read them; the statement says nothing of them.
THE REQUEST's TOKENS AND y MUST BE BELOW V: the true sum holds the weights' column
of win t, and the claim on the weights sums the columns below V alone.
THE ORDER OF THE LETTERS is the round-by-round one: the cells, the point, the mask entries and the
ledger in front of the rounds (F0, behind the normalization's: it says under which numbers the
hidden scalars will lie) stand before the rule for the bad elements; the rule sees the rounds in
front and the message, not the draw. THAT THESE FOUR ARE FIXED IN TIME before the first of these
rounds is not said by a letter's place: it is owed where the blocks are laid in a link. -/
def Lemma2bStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] (c : Cells) (p : Pt) (mask : Nat → E) (F0 : Fork),
    Request.ok = true → y < V → WellLaid F0 → p.zt.size = lt → p.zl.size = ls →
    ∃ bad : List Fmt.RoundView → List E,
      (∀ h, (bad h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum),
        let _ := p.normIn
        let _ := p.headIn
        Canonical t →
        sumcheck (FinalNorm.zt ++ halves lPd) 2 F0 t = some (S, F1, []) →
        let _ : Heard := { logits := S }
        let _ := readsAt c
        (∀ f, f ∈ logitForms → atHidden F1 mask f = 0) →
        atHidden F1 mask forTheMerge.value.var =
          (∑ v < V, ∑ k < d, forTheMerge.onVocabulary v * eq forTheMerge.onFeatures k *
            ofInt (c.Wh k v)) →
        NoBad bad t →
        (2 ^ lPd : E) * atHidden F1 mask logits.claimed.var = trueSum c

/-- **THE NEXT TOKEN's LEMMA.** PROVED: `replyLemma`. No chance in it. L: the one seat, which gives
back what was laid. FIRST: the block lays the seat once: it was empty in front, and behind it holds
a token below V. SECOND: sHead: any record, such as the one at which the head reads; sEnd: the last
record. If both seats hold the same and the last test says yes at sEnd, then the token read at sHead
is the one that the client asked about (`asked`); it is below V; and it is 0 where the last position
is not checked. WHAT IT DOES NOT SAY: that no block between touches the seat: that is for the law of
the fold over blocks; that the head's y is read at this seat: that is a reading of the head's text
(HeadFrame.lean takes y from `Reply.token` of the same seat); that V, T, r, e here are the head's:
whoever lays the two blocks side by side hands both the same numbers. -/
def ReplyLemmaStatement : Prop :=
  ∀ (S : Type) (L : Reply.Seat S), (∀ s x, L.reply (L.setReply s x) = some x) →
    ∀ (V T r e asked : Nat),
      (∀ (s s' : S) (rs : List Fmt.RoundView), Reply.decide V L s rs = some s' →
        L.reply s = none ∧ ∃ n, n < V ∧ Reply.token L s' = some n) ∧
      (∀ (sHead sEnd : S), L.reply sHead = L.reply sEnd →
        Reply.fin V T r e asked L sEnd = true →
        Reply.token L sHead = some asked ∧ asked < V ∧ (e < T → asked = 0))

end VerifiableInference.Desc.Kinds.Head.Law
