-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- DEFINITIONS ONLY.
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyReaders1.lean: THE KEY FILE's FIRST CHAIN: THE TABLE OF JOINTS' READERS AT THE KEY FILE's DESCRIPTION descriptionFromSource (Johnson/Desc/Key/Desc.lean; written over an earlier working state of these files): at its first chain's state FirstState := ChainState LookupRecord: THE EIGHT READERS AND THE
BOOK's THREE ARE THE FILLING OF Johnson/RunOne/KeyReaders.lean (unturned): here they are called, and what the table holds beyond that filling is filled beside: book.own · book.handed (handedSt, Johnson/RunOne/KeyHanded.lean) · book.ties (ties₁: the ties to the plan: KeyShape.lean) · K3's three readers · the numbers.
A FILE OF ITS OWN, WITH CODE, WITHOUT THE RULES' GROUND, SO THAT THE VERY TEXT THAT KeyRows1At.lean's on₁ | L₁ STAND ON IS WHAT AN HONEST RUN EVALUATES (a test file outside this library imports it: no second text).
  plan₁ · readers₁ · book₁ · k3At₁ · n₁ · slots₁
No theorem. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyK3Items
import Johnson.Desc.Sound.BookOrder
import Johnson.Desc.Key.KeyShape
import Johnson.RunOne.KeyReaders
import Johnson.RunOne.KeyHanded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState lookupsOf)

/-- The first chain's statement's numbers: message 0 is I, 1 is B, 2 B's fresh mask; each stage of the ranges' test BUT THE FIRST (which is B's own group) sends two messages; V stands behind them: 3 + 2 · (stages − 1). [BY A RUN at both sizes' public files:
four stages; V is message 9 in the state's statement.] -/
def plan₁ (one : OneTime) : KPlan := KeyReaders.planOf one (1 + 2 * one.ranges.stages.length)

def readers₁ (one : OneTime) : KReaders FirstState := KeyReaders.readers one

/-- **The ties between the plan, which the claims read, and the state's own copies, which the blocks read**, at border b (at two lookups: the first clause). STATIC: the plan has just two lookups · the lookups' own message has the number 1 (K.orc 1). ON THE STATE: its
statement's codes are the plan's · from border 1 on: the number under which it holds the index-mask message is 0 (K.orc 0) · from behind B's sending up to the ranges' test (borders 2 to 15): the ranges' group's members are just B · the message that is to mask the test's first
fold is message 2, without a sample, not yet spent. -/
def tiesA (one : OneTime) (b : Nat) (s : FirstState) : Bool :=
  (lookupsOf one).length == 2 && one.ranges.messageId == 1 && decide (s.d.st.codes = one.codes) && (b == 0 || s.idx == 0) &&
    (!(decide (2 ≤ b) && decide (b ≤ 15)) ||
      (((s.d.st.groups[s.grp]?).any fun G => G.members.toList == [1]) && s.rider == some 2 && ((s.d.st.oracles[2]?).any fun x => !x.sampled && !x.spentAsMask)))

/-- How many oracle messages, groups and trees the first chain's statement and book hold at border b (at two lookups): st: the stages of the ranges' test: each but the first sends two messages in one tree and makes a group. -/
def counts₁ (one : OneTime) (b : Nat) : Nat × Nat × Nat :=
  let st := one.ranges.stages.length
  if b == 0 then (0, 0, 0) else if b == 1 then (1, 0, 1) else if b ≤ 15 then (3, 1, 2) else if b ≤ 17 then (1 + 2 * st, st, st + 1) else (3 + 2 * st, st + 1, st + 2)

/-- **THE COUNTS, AND WHAT LIES EMPTY IN FRONT OF THE LOOKUPS.** A law is owed at EVERY state with the promise: a sending gives its message the NEXT number and the next tree: so that B is message 1 in tree 1 and V message orc 2 in tree st + 1 BEHIND a sending, the numbers of messages, groups
and trees must be promised IN FRONT of it; and what border 2 asks of the lookups' record (no rows, no keys, no ledger, nothing heard, no claim), which neither sending touches, must be promised at borders 0 and 1. AND: BEHIND V's SENDING THE NUMBER UNDER WHICH THE STATE's CLAIM HOLDS W (lin.w), at which EvalIs makes the row, IS THE PLAN's NUMBER OF THE WITNESS's MESSAGE 2: no other clause said so; AND FROM BEHIND THE BATCHING ON (border 17) THE CLAIM's MASKS' MESSAGES ARE JUST THE INDEX-MASK MESSAGE: K13's rows join to the own group «listOfT (claim.masks … oracle)», then W: without
that clause in front, w.1.send could not earn «the own group's members are [orc 0, orc 2]» (a counter-state: a claim without masks); AND EVERY VECTOR OF THE CLAIM's ROW WEIGHTS IS Tensor.ok (wanted by the last chain's first row: asked by no test; it must ride in from the first chain; earned where the claim is made). AND: FROM BORDER 17 ON EVERY MASK ENTRY OF THE CLAIM LIES AT THE PART .mask: «Eval» (linEvalRow: units := claim.masks) reads each entry at its own part, the pile (rowOfLinClaim drops the part; mkOf reads .mask) at the mask part: without this clause a made-up state with one entry at .main is inside the promise and row 2.1's field is false there. EARNED at 1.16 (the batching lays memberClaim, which writes .mask); KEPT wherever the claim is carried unturned; SPENT at 2.1. -/
def sizesB (one : OneTime) (b : Nat) (s : FirstState) : Bool :=
  s.d.st.oracles.size == (counts₁ one b).1 && s.d.st.groups.size == (counts₁ one b).2.1 && s.d.book.trees.size == (counts₁ one b).2.2 && s.d.book.place.size == s.d.st.oracles.size &&
    (decide (2 ≤ b) || (s.base.rows.isEmpty && s.base.keys.isEmpty && s.base.fork.isNone && s.base.heard.isNone && s.lin.isNone)) &&
    (decide (b < 17) || s.lin.any fun L => listOfT (L.claim.masks.toList.map (·.oracle)) == [0] && L.claim.masks.all (·.part == .mask)) &&
    (decide (b < 18) || s.lin.map (·.w) == (plan₁ one).orc 2) &&
    (decide (b < 17) || (s.lin.map fun L => L.claim.g.all (·.ok)) == some true)

/-- How many lookups have laid their rows and their claims on the keys at border b (at two lookups). -/
def done₁ (b : Nat) : Nat := if b ≤ 5 then 0 else if b ≤ 11 then 1 else 2

/-- **WHAT THE FILE's LAST TEST ASKS OF THE FIRST CHAIN's LAST STATE (firstEndOk), AND NO END BLOCK ASKS**: so that «the three chains' yes ⇒ the last test's yes» is a lemma (KeyTenAt.finD_of_shape), these ride in the promise from where a block writes them:
just as many lists of rows and of claims on the keys as lookups have laid (the invariant through a link asks these lengths too) · from border 17: the chain has come to its end (K13's seat sets the mark) · from 18: the claim's own group and W's number are laid, AND THE RECORD CALLS THE MESSAGE BEHIND W ITS MASK (the last chain's start takes the three numbers by name out of the record) · from 16: every group from the
ranges' group on (from 18: but the last, the own one) has begun its test and holds no open row (K12's seat's «ended» asks it of all of them). -/
def moreB (b : Nat) (s : FirstState) : Bool :=
  s.base.rows.length == done₁ b && s.base.keys.length == done₁ b && (decide (b < 17) || s.atEnd) && (decide (b < 18) || s.lin.any fun l => l.own != noId && l.w != noId && l.mask == some (l.w + 1)) &&
    (decide (b < 16) || ((if b < 18 then s.d.st.groups.toList.drop s.grp else (s.d.st.groups.toList.drop s.grp).dropLast).all fun G => G.inRun && G.rows.isEmpty)) &&
    VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots

/-- **The ties at border b.** -/
def ties₁ (one : OneTime) (b : Nat) (s : FirstState) : Bool := tiesA one b s && moreB b s && sizesB one b s

def book₁ (one : OneTime) : KBook FirstState :=
  { KeyReaders.book with
    own := fun s => s.lin.map (·.own)
    handed := fun s => KeyRows23.handedSt one.given.plan.samples [0] s.d.st
    ties := ties₁ one }

def k3At₁ : K3At FirstState := { fork := fun s => s.base.fork, heard := fun s => s.base.heard, home := fun s => s.base.home }

/-- The number of lookups. -/
def n₁ (one : OneTime) : Nat := (lookupsOf one).length

/-- The number of hidden values of lookup l. -/
def slots₁ (one : OneTime) (l : Nat) : Nat := (((lookupsOf one)[l]?).map fun x => (K3.faceOfLkp x).slots).getD 0

end Johnson.RunOne.KeyRows1
