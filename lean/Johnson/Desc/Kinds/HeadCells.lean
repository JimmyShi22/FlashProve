-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadCells.lean: a part of THE OUTPUT HEAD'S OWN ROUNDS (Head.lean): its letters,
behind HeadPublic.lean: what comes in; the names of its keys and reads; the sums of cells, as forms,
of which the kind's formulas are made; the claim on the weights. Definitions with code; no theorem.
In Lean what is given stands in classes (Sizes, Policy, Request, Token, In, Heard, Reads; the
normalization's too), so that a formula names d, C or zt without arguments.
To the format's 11.4: wide act row stream: hf hd hr xbL. marginTop marginMid marginLow tableA
tableB: HD0 HD1 HD2 HE0 HE1. paid over slackMean slackClip slackCap slackTable: gc gb gu gk gz gs.

-/
import Johnson.Desc.Kinds.HeadPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open OnBytes (E)
open Norm (lt ls d lPd T S2)
open FinalNorm (zt zl)

variable [Sizes] [Policy] [Request]

/-! ## 3. Keys, and what comes in -/

/-- The head's five keys: the margin's three digits, and the table in two halves. -/
inductive Key | marginTop | marginMid | marginLow | tableA | tableB
/-- A key's number. -/
def Key.idx : Key → Nat
  | .marginTop => 0 | .marginMid => 1 | .marginLow => 2 | .tableA => 3 | .tableB => 4
/-- The number of a key's entries: an entry stands for a vocabulary entry, padding among them. -/
def len : Key → Nat
  | .tableA => JVa | .tableB => JV - JVa | _ => JV

/-- What comes in from the next token's block: y, the next token as the proof names it. (The
client's own is called asked; that block's last test is y = asked.) -/
class Token where y : Nat
export Token (y)

/-- What comes in from the lookup.
  zt, zl    its point on the positions, and on a block's features: with the norm's In.
  ew k x    the public weight of entry x of key k: the equality weight of its column.
  ewh k i   that of block i: ew k (S2 i + j) = ewh k i * eq zl j.
  wsum k    the sum of all ew k x.
  wx k      the sum over the entries that stand for a vocabulary entry below V.
  below v   the sum of ew .marginTop x over x < v. -/
class In where
  (ew ewh : Key → Nat → E)
  (wsum wx : Key → E)
  below : Nat → E
export In (ew ewh wsum wx below)
variable [Token] [FinalNorm.In] [In]

/-- The token that a checked position is about. -/
def win (t : Nat) : Nat := if t + 1 < T then tok (t + 1) else y

/-- What the head's one step leaves: a masked sumcheck (HeadParts.lean, Sum). -/
class Heard where logits : Sum
export Heard (logits)
/-- All that is heard at the place: by the normalization's two parts, and by the head. -/
abbrev HeardAll : Type := Norm.Heard × FinalNorm.Heard × Heard

variable [Heard]

/-- A key of the place: the final normalization's four and the head's five. -/
abbrev PlaceKey : Type := FinalNorm.Key ⊕ Key

/-! ## 4. Reads, and sums of cells as forms -/

/-- The head's five reads (a read, long and short weights: HeadParts.lean). -/
inductive Read | wideAtKeys | wideAtCosts | actAtLogits | rowAtCosts | rowCount

/-- The weights of zt at the positions with a cost, 0 elsewhere. -/
def phiC (t : Nat) : E := if costed t then eq zt t else 0
/-- The challenges of logits on the position. -/
def rH : Point := logits.r.extract 0 lt
/-- Its challenges on the feature. -/
def rs : Point := logits.r.extract lt (lt + lPd)

/-- To the merge: the sumcheck's second end value, UH at the challenges: under the weights of the
top digit's key, logit t (win t) - logit t v at rH, as a claim on the committed weights Wh
(SumOnMatrix: HeadParts.lean). No form says what that end value is: this claim does. -/
def forTheMerge : SumOnMatrix :=
  { value := logits.end_ 1, onFeatures := rs, onVocabulary := fun v =>
      wx .marginTop * (∑ t < T, if checked t && win t == v then eq rH t else 0)
        - (∑ t < T, if checked t then eq rH t else 0) * ew .marginTop v }

/-- Entry i of a read, as a variable of a form. -/
class Reads where entry : Read → Nat → Form
export Reads (entry)
variable [Reads]

/-- The weight at zt of the checked positions. -/
def ON : E := ∑ t < T, if checked t then eq zt t else 0
/-- The weight at zt of the positions with a cost. -/
def ERC : E := ∑ t < T, phiC t

/-- A number, summed over the positions with a cost under the weights of zt. A cell holds its digit
less off1 = 128. -/
def atCosts (n : Number) : Form :=
  ∑ l < n.digits.2, (256 ^ l : Nat) • (entry .rowAtCosts (NR + n.digits.1 + l) + off1 * ERC)
/-- A number, summed plainly over the positions with a cost. -/
def summed (n : Number) : Form :=
  ∑ l < n.digits.2, (256 ^ l : Nat) • (entry .rowCount (NR + n.digits.1 + l) + off1 * RC)

/-- A number that wide holds in nl limbs, limb l in the features from f0 + l stride on, under a
key's weights and zt. S2 divides d, JV and JVa, so a block never straddles two limbs. -/
def wideAt (k : Key) (f0 nl stride : Nat) : Form :=
  ∑ i < len k / S2, ∑ l < nl, (256 ^ l * ewh k i) • entry .wideAtKeys ((f0 + l * stride) / S2 + i)

/-- A pair (v, t) is real if v < V and t is checked. The margin's middle digit under a key's
weights: its cells at every pair, and the cells' offset off2 = 128 * 257 AT THE REAL PAIRS ALONE: so
at a pair that is not real the key is the bare cells. v0: the key's first vocabulary entry. -/
def mid (k : Key) (v0 : Nat := 0) : Form := off2 * wx k * ON + wideAt k (4 * d + v0) 2 JV
/-- The low digit, likewise. -/
def low (k : Key) : Form := off1 * wx k * ON + wideAt k (4 * d + 2 * JV) 1 JV
/-- The middle digit's table value. Row u of the table holds 2^F at u = 0, and from 1 to 2^F
everywhere. Its offset offE = 128 * 65793 + 1 stands at EVERY pair. -/
def tableValue (k : Key) (v0 : Nat := 0) : Form :=
  offE * wsum k + wideAt k (4 * d + 3 * JV + v0) 3 JV

/-- The table values of all JV entries of a position, summed over the positions with a cost under
the weights of zt: three limbs, from the read wideAtCosts, with the cells' offset. -/
def tableValuesAtCosts : Form :=
  (offE * JV) * ERC + ∑ l < 3, ∑ i < JV / S2,
    (256 ^ l : Nat) • entry .wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i)

end VerifiableInference.Desc.Kinds.Head
