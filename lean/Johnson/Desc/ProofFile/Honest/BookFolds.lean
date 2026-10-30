-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookFolds.lean: the fourth of the files that compute the book of coins
(`ProverCoinCounts`, Honest/Frame.lean): the entries by which a fold spends a fresh table that was sent ahead,
and those of a masked sumcheck outside a segment, which spends the index-mask message alone. From
public data alone. It names no prover's side. Executable definitions, and tests at made-up lists;
no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

A fresh table that is sent ahead is part of a sending (mask rows alone, no sample: `isFresh`,
Honest/BookRows.lean). The fold that spends it is taken to be the first fold after that sending: in
its chain, or, where none follows there, in the chain that the caller names after it. The fold
spends the table's first 2k + 1 coins: its hiding polynomial's coefficients; k: the fold's rounds
"FOLD round". A fold whose "FOLD epsilon" sends a root of its own has its table among its own coins:
no entry.

  1  `PlanB`, `planOf`, `addrIn`, `foldBehind`   a chain's sub-protocols without their state's type,
     so that two chains can be in one list
  2  `foldEntries`   the entries
  3  `loneSumWants`   a sumcheck outside a segment

Limits.
  * That the first fold after a sending is the spender is assumed, as in Honest/BookRows.lean.
  * The fresh tables that are sent with a proximity test's switches are not looked at: such a
    sending is left out, as there. Why: at a place of the kind K12 `cutOfNames` (Honest/BookOf.lean)
    makes two parts at the most, and every switch and every later fold lie in the second. So such
    a table's coins are that part's own (`switchDue`, Honest/BookSwitch.lean, counts them), and a
    part needs no entry for its own coins. No test here asks that a switch is at a place of that
    kind, nor that the fold after it is at the same place.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-! ## 1 A chain without its state's type -/

/-- A sub-protocol by its place, the cut of Honest/BookOf.lean and its declared rounds. -/
structure PlanB where
  place : Place
  cut : List Nat
  rounds : List Fmt.DeclaredRound

def planOf (bs : List (Block S Cl)) : List PlanB := bs.map fun b => ⟨b.place, partsCut b, b.rounds⟩

/-- The address of the part that holds round number i, from 0, of a list. -/
def addrIn : List PlanB → Nat → Option Addr
  | [], _ => none
  | b :: bs, i =>
    if i < b.rounds.length then
      let starts := b.cut.foldl (fun (l : List Nat × Nat) k => (l.1 ++ [l.2], l.2 + k)) ([], 0)
      some ⟨b.place, (starts.1.filter (· ≤ i)).length - 1⟩
    else addrIn bs (i - b.rounds.length)

/-- **The first fold after round number i**: the number of its round "FOLD epsilon", whether that
round sends a root, and how many rounds "FOLD round" follow it. -/
def foldBehind (l : List PlanB) (i : Nat) : Option (Nat × Bool × Nat) :=
  let rs := (l.flatMap (·.rounds)).zipIdx.drop (i + 1)
  match rs.dropWhile fun r => r.1.entry.name != "FOLD epsilon" with
  | [] => none
  | e :: u => some (e.2, e.1.entry.roots != 0,
      (u.takeWhile fun r => r.1.entry.name == "FOLD round").length)

/-! ## 2 The entries -/

/-- One sending's fresh tables: each with its number in the sending. -/
def freshOf (ns : List OnBytes.OracleNotice) : List Nat :=
  (ns.zipIdx.filter fun x => isFresh x.1).map (·.2)

/-- **The entries by which folds spend the fresh tables that a chain's sendings send ahead.**
`here`: the chain. `later`: the chain after it in which a table is spent that no fold of this chain
follows. An error where the sendings are not as many as the chain's rounds "SEND seed", where there
is no fold after a fresh table, where that fold sends a table of its own, or where an address or a
start is lacking. -/
def foldEntries (here later : List PlanB) (c : Johnson.G.ChainSends) : Except String (List Ahead) :=
  let seeds := ((here.flatMap (·.rounds)).zipIdx.filter fun r =>
    r.1.entry.name == "SEND seed").map (·.2)
  if seeds.length != c.sends.length then
    .error "the sendings are not as many as the chain's rounds SEND seed"
  else
    List.flatten <$> ((seeds.zip c.sends).filter fun x => !isSwitch x.2.label).mapM fun x =>
      (freshOf x.2.sent).mapM fun j =>
        match foldBehind (here ++ later) x.1 with
        | none => .error (x.2.label ++ ": no fold stands behind its fresh table")
        | some (_, true, _) => .error (x.2.label ++ ": the fold behind sends a table of its own")
        | some (e, false, k) =>
          match addrIn here x.1, addrIn (here ++ later) e, maskStart c.codes k x.2.sent j with
          | some o, some p, some st =>
            .ok ⟨runName foldMaskRun p "fold", o, st, ⟨0, 2 * k + 1⟩, p, true⟩
          | _, _, _ => .error (x.2.label ++ ": an address or a start is lacking")

/-! ## 3 A sumcheck outside a segment -/

/-- **The range of a masked sumcheck that spends the index-mask message alone**: all its scalars,
from that message's next free entry t on. It returns the range and the next t. -/
def loneSumWants (idx : MsgAt) (p : PartAt) (t : Nat) : List Want × Nat :=
  if p.isSum && p.ownScalars != 0 then ([⟨p.addr, "sum", idx, t, p.ownScalars⟩], t + p.ownScalars)
  else ([], t)

/-! ### Tests at made-up lists -/

def rd (name : String) (roots : Nat := 0) : Fmt.DeclaredRound :=
  { entry := { name := name, msg := 32 * roots, roots := roots } }

/-- A sending; a draw; a closing of two rounds. After it, in another chain: a fold of one round. -/
def toyHere : List PlanB :=
  [⟨⟨1, some 0, 1, .K1⟩, [2], [rd "SEND seed" 1, rd "SEND answer"]⟩,
   ⟨⟨1, some 0, 2, .K9⟩, [1], [rd "BAT-sigma"]⟩,
   ⟨⟨1, some 0, 3, .K10⟩, [4], [rd "BAT", rd "FOLD epsilon", rd "FOLD round", rd "FOLD round"]⟩,
   ⟨⟨1, none, 4, .K1⟩, [1], [rd "SEND seed" 1]⟩]
def toyLater : List PlanB :=
  [⟨⟨3, none, 0, .K12⟩, [3], [rd "BAT", rd "FOLD epsilon", rd "FOLD round"]⟩]

/-- Both sendings hold a row with a mask row, then a fresh table. -/
def toyFresh : OnBytes.OracleNotice :=
  ⟨{ mainRows := 0, maskRows := 1, maskCode := 0, answers := 0 }, 0⟩
def toySends : Johnson.G.ChainSends :=
  { file := "toy", chain := 0, codes := toyCodes
    sends := [⟨1, "link 0, moment 0", [toyA, toyFresh], { name := "SEND seed" }, { name := "x" }⟩,
      ⟨2, "W", [toyB, toyFresh], { name := "SEND seed" }, { name := "x" }⟩] }

-- the fold after the first sending: its "FOLD epsilon" is round 4, it sends no root, k = 2; after
-- the second: in the later chain: round 9, k = 1
#guard foldBehind (toyHere ++ toyLater) 0 == some (4, false, 2) &&
  foldBehind (toyHere ++ toyLater) 7 == some (9, false, 1) && foldBehind toyHere 7 == none
#guard addrIn toyHere 4 == some ⟨⟨1, some 0, 3, .K10⟩, 0⟩ &&
  addrIn (toyHere ++ toyLater) 9 == some ⟨⟨3, none, 0, .K12⟩, 0⟩
-- the two entries: owner, spender, start, count. The first table begins after toyA's coins of the
-- extension field (32 entries and a tail of 4); the second after toyB's (7 + 32 + 4)
#guard ((foldEntries toyHere toyLater toySends).toOption.map fun l => l.map fun e =>
    (e.owner.place.piece, e.spender.place.kind, e.start, e.count, e.once)) ==
  some [(1, .K10, ⟨15, 36⟩, ⟨0, 5⟩, true), (4, .K12, ⟨0, 43⟩, ⟨0, 3⟩, true)]
-- without the later chain the second table has no fold after it
#guard (foldEntries toyHere [] toySends).toOption.isNone
-- a fold that sends a table of its own
#guard (foldEntries
  (toyHere.take 2 ++ [⟨⟨1, some 0, 3, .K10⟩, [2], [rd "FOLD epsilon" 1, rd "FOLD round"]⟩])
  [] { toySends with sends := toySends.sends.take 1 }).toOption.isNone
-- a sumcheck outside a segment
#guard loneSumWants toyIdx ⟨⟨⟨1, none, 3, .K13⟩, 1⟩, [("PSC epsilon", 1), ("PSC round", 2)]⟩ 2 ==
  ([⟨⟨⟨1, none, 3, .K13⟩, 1⟩, "sum", toyIdx, 2, 3⟩], 5)

end ProofFile.Honest
