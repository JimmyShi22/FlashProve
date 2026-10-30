-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Strat.lean: from a prover of Honest/Frame.lean to strategies of the
library's own types, for a general description: the shared part's strategy and a slot's
(`Iop.SStrat`, `Iop.LStrat`: Iop/Batch.lean), over the shape of a file's reduction
(`FileDescription.toIOR`, Johnson/Desc/BlockSlot.lean; `chainsOf`, OnBytes/Maker/Whole.lean):
  the front round | chain 1 | the joining round | chain 2 | the seam | chain 3,
of which the joining round and chain 2 are shared. Chains 1, 2 and 3 are the chains that
Honest/Frame.lean calls the first, the shared and the second. Executable definitions; no theorem.

Three terms of the library (Iop/Batch.lean). A slot: one request's prover. The shared part: what is
sent once for all requests of a batch. A local round: one whose challenge each request draws for
itself; a shared round: one whose challenge all requests have in common.

What is shared with `run`, and what is not. A round: a strategy sends what `Step.tell` returns and
goes on by `Step.hear`, the two functions of which `play`, and so `run`, is made. The rounds: those
that `ready` and `readyShared` prepare. The test on the sealing round: `sealTest`. The start of each
chain: `Ready.start₁`, `startShared`, `Ready.start₃`. The slot's strategy needs the shared
chain's end (`Prover.meet`): it hears that chain's challenges and plays the same rounds by `play`.
The sequence of the chains is written a second time here: `run` and `midAt` have it in `Ready.ends`,
which takes all challenges at once; a strategy hears them one by one and cannot call it.

  1  `orcOf`, `plainOf`, `msgOf`, `drOf`   a round's typed message, from what the round sends; the
     fixed substitute where there is nothing; a typed challenge as a `Fmt.Drawn`
  2  `tellAt`, `hearAt`; `speakL`, `speakLEnd`, `hushL`, `speakS`, `hushS`, `hushSEnd`   a chain:
     who speaks (the slot; the shared part), and whether the chain is that speaker's own
  3  `KeyAndJoiningRoundMessages`, `KeyAndJoiningRoundMessages.ofFour`   what no part computes: the key without an instance, and what the three
     rounds without a challenge send
  4  `strat0`, `requestStrategy`   the two strategies

Where the honest side stops or is at fault. A strategy cannot return an error. From the first error
on (a stop, a fault, an error of `ready`) the speaker sends the round's fixed substitute
(`Round.dOrc`, `Round.dPlain`) in every later round of a chain, as the library means it
(Iop/Batch.lean, at `BatchHonestProver.strat`). The front round, the joining round and the seam send `KeyAndJoiningRoundMessages`'s
values at every list of challenges, whatever error there has been: they depend on no challenge, and
their fixed substitutes tF, tJ, t3 are sent by nobody. A stop after a part's last challenge changes
no message of that part. Where the shared chain has stopped, the slot's third chain sends
substitutes too.

The data. The strategies walk D's three lists of rounds; `ready` walks the description's
sub-protocols. D is a parameter here: nothing compares it with the description (`FileDescription.data`
makes one). At a D that does not fit, a strategy does not stop. Where D declares other items than
the `Step`, the message is the substitute from that item on, while the run goes on with what the
`Step` sent. Items, tables and words beyond what D declares are dropped. With fewer `Step`s than D
has rounds, substitutes are sent from there on. D's first list is without the sealing round: that
round is played here, at the empty challenge, between chain 1 and the joining round, as `run` plays
it.

Where no prover's side is defined. `run` shows no item at such a round and returns an error for a
column of such a table; a strategy sends the substitute there, so the library's views show zeros. So
the strategies' run shows `run`'s views only if a prover's side is defined at every round that
declares an item, and at every table that is read. (`lacking`, Honest/Frame.lean, names the
sub-protocols that send something and have no prover's side: a wider list.)

Limits.
  * The structure `Iop.BatchHonestProver` is filled in Honest/Record.lean: its sets of challenges and its
    external string are not defined here.
  * After the last part of chain 3 a stop changes nothing of the transcript; after the last part of
    chain 2 it changes the slot's chain 3 alone. What tells these lists of challenges apart is the
    sets of `Iop.BatchHonestProver`.
  * The nonce of a round with proof of work is 0.
  * That the key which `KeyAndJoiningRoundMessages.keyOf` computes is `Prover.key` of the instance, and that what the
    three rounds send agrees with the instance, has to be proved by whoever states something.
  * Of the verdict of the file's interactive oracle reduction (`FileDescription.out_eq`) four tests are
    reached by nothing here: the proofs of work (`passT`), that no draw is shortened (`fullOf`),
    that a symbol of the stored table carries its position (`carriesOf`), and `silent`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.BlockSlot
import OnBytes.Maker.SilentParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (RDT WholeD uLT roundT PosT SymT chainsOf FrontMsg)
open Iop (Shape RoundSplits SStrat LStrat)
open _root_.Run.PQ (CK PlainOf)
open Compile.Joined (JoinMsg)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 W Y : Type}

/-! ## 1 A message -/

/-- A round's oracle part: at a position of the n-th tree, that table's column, its words by index.
0 where a table or a word is missing; tables beyond the declared trees, and words beyond a tree's
declared width, are dropped. -/
def orcOf : (ts : List Fmt.Shape) → List (Option Table) → (p : PosT ts) → SymT ts p
  | _ :: _, l, .inl x => fun i => (((l.head?.join.map fun t => t.col x.val).getD [])[i.val]?).getD 0
  | _ :: ts, l, .inr p => orcOf ts l.tail p

/-- A round's plain part: the items in the clear, put into the round's declared items. A root has no
place there and is skipped. The fixed substitute from the first item on that does not fit; items
beyond the declared ones are dropped. -/
def plainOf : (l : List Fmt.Item) → List Fmt.ItemValue → PlainOf l
  | [], _ => ()
  | .root :: l, g => plainOf l g
  | .f :: l, .f x :: g => ((x, plainOf l g) : UInt64 × PlainOf l)
  | .word :: l, .word x :: g => ((x, plainOf l g) : UInt64 × PlainOf l)
  | .e :: l, .e x :: g => ((x, plainOf l g) : Fmt.Ext × PlainOf l)
  | .answer :: l, .answer x :: g => ((x, plainOf l g) : Fmt.Ext × PlainOf l)
  | l, _ => _root_.Run.PQ.PlainOf.dflt l

/-- **A round's typed message.** `none`: the round's fixed substitute. -/
def msgOf (C : CK) (d : RDT) : Option Told → (roundT C d).up.Msg
  | some x => (orcOf d.trees x.tables, Iop.GPlain.mk d.entry.work (plainOf d.items x.vals) (0 : ℕ))
  | none => ((roundT C d).dOrc, (roundT C d).dPlain)

/-- A typed challenge as a `Fmt.Drawn` (what the format says was drawn), as the library's `drawnSL`
reads it. -/
def drOf (C : CK) (d : RDT) (c : (roundT C d).up.Chal) : Fmt.Drawn :=
  C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)

/-! ## 2 A chain -/

/-- What a round sends; `none` if there is no round, the chain has stopped, or the round returns an
error. -/
def tellAt (s : Option (Step W Y)) (m : Option (Mid W Y)) : Option Told :=
  s.bind fun s => m.bind fun m => (s.tell none m).toOption

/-- The state of the chain after the round's challenge; `none` from the first error on. -/
def hearAt (s : Option (Step W Y)) (x : Option Told) (d : Fmt.Drawn) (m : Option (Mid W Y)) :
    Option (Mid W Y) :=
  s.bind fun s => x.bind fun x => m.bind fun m => (s.hear x d m).toOption

section
variable (C : CK) {rest : Shape} {A : RoundSplits rest}

/-- The slot's strategy over a local chain after which more rounds come. `ds`: the chain's rounds,
as the data have them. `ss`: the `Step`s for them. `m`: the state of the run, or `none` once there
has been an error. `k`: builds the strategy for the rounds after this chain, from the state of the
run at the chain's end. -/
def speakL : (ds : List RDT) → List (Step W Y) → Option (Mid W Y) →
    (Option (Mid W Y) → LStrat rest A) →
    LStrat (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A)
  | [], _, m, k => k m
  | d :: ds, ss, m, k =>
    (msgOf C d (tellAt ss.head? m), fun (c : (roundT C d).up.Chal) =>
      speakL ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) k)

/-- The slot's strategy over a shared chain: it sends nothing and hears the challenges. `acc`: those
heard so far. `k`: builds the strategy for the rounds after this chain, from all that were heard. -/
def hushL : (ds : List RDT) → List Fmt.Drawn → (List Fmt.Drawn → LStrat rest A) →
    LStrat (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A)
  | [], acc, k => k acc
  | d :: ds, acc, k =>
    ((), fun (c : (roundT C d).up.Chal) => hushL ds (acc ++ [drOf C d c]) k)

/-- The shared part's strategy over a shared chain. `ds`, `ss`, `m`: as in `speakL`. `k`: the
strategy for the rounds after this chain. -/
def speakS : (ds : List RDT) → List (Step W Y) → Option (Mid W Y) → SStrat rest A →
    SStrat (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.const (Iop.RAnn.ofShared .sh) (uLT C ds)) A)
  | [], _, _, k => k
  | d :: ds, ss, m, k =>
    (msgOf C d (tellAt ss.head? m), fun (c : (roundT C d).up.Chal) =>
      speakS ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) k)

/-- The shared part's strategy over a local chain: it sends nothing and hears nothing. `k`: the
strategy for the rounds after this chain. -/
def hushS : (ds : List RDT) → SStrat rest A →
    SStrat (uLT C ds ++ rest) (Iop.RoundSplits.app (Iop.RoundSplits.allLocal (uLT C ds)) A)
  | [], k => k
  | _ :: ds, k => ((), fun (_ : Unit) => hushS ds k)

end

/-- The slot's strategy over the last chain: as `speakL`, with nothing after it. -/
def speakLEnd (C : CK) : (ds : List RDT) → List (Step W Y) → Option (Mid W Y) →
    LStrat (uLT C ds) (Iop.RoundSplits.allLocal (uLT C ds))
  | [], _, _ => ()
  | d :: ds, ss, m =>
    (msgOf C d (tellAt ss.head? m), fun (c : (roundT C d).up.Chal) =>
      speakLEnd C ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m))

/-- The shared part's strategy over the last chain: it sends nothing and hears nothing. -/
def hushSEnd (C : CK) : (ds : List RDT) → SStrat (uLT C ds) (Iop.RoundSplits.allLocal (uLT C ds))
  | [] => ()
  | _ :: ds => ((), fun (_ : Unit) => hushSEnd C ds)

/-! ## 3 What no part computes -/

/-- **What goes with a prover.** Sd: the seed of the stored table's out-of-domain sample. The key
and what the joining round sends are computed without an instance, by type: the shared part's
strategy has none. -/
structure KeyAndJoiningRoundMessages (W₀ Rc Sd Xi Ky TF TJ T3 : Type) where
  /-- the key that the prover's sides in the shared chain are given -/
  keyOf : W₀ → Rc → Sd → Ky
  /-- what the front round sends -/
  front : W₀ → Rc → Sd → Xi → TF
  /-- what the joining round sends -/
  join : W₀ → Rc → Sd → TJ
  /-- what the seam sends -/
  seam : W₀ → Rc → Sd → Xi → T3

/-- At the proof file's own three types (OnBytes/Maker/SilentParts.lean), from four values: the
answers, the copy's number, and the second and the third chain's run values. The four are constants:
so one such `KeyAndJoiningRoundMessages` serves those instances alone whose answers and copy's number are these. And
"without an instance, by type" holds of a fixed `KeyAndJoiningRoundMessages`: whoever takes the four from an instance
passes it to the shared part through them. Honest/Record.lean supplies the two run values as coins.
-/
def KeyAndJoiningRoundMessages.ofFour (keyOf : W₀ → Rc → Sd → Ky) (answers : List OnBytes.E) (copy : ℕ)
    (run2 run3 : ByteArray) :
    KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky (FrontMsg (List OnBytes.E)) (JoinMsg (List OnBytes.E) ByteArray)
      ByteArray :=
  ⟨keyOf, fun _ _ _ _ => ⟨answers, copy⟩, fun _ _ _ => ⟨answers, run2⟩, fun _ _ _ _ => run3⟩

/-! ## 4 The two strategies -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)

/-- **The shared part's strategy**, from the index, the stored tables' pads and encoding randomness
and the seed, and from the shared chain's own coins. It is silent in the front round and chain 1,
sends the joining round's plain part (at every list of challenges, also where `readyShared` has
returned an error), plays chain 2, and is silent from the seam on. -/
def strat0 (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) :
    SStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  let ky := J.keyOf w.1 w.2.1 w.2.2
  let ss := (readyShared F B H w.1 w.2.1 ky c₀).toOption
  ((), fun (_ : Unit) =>
    hushS C D.ds₁
      ((((), J.join w.1 w.2.1 w.2.2) : Unit × TJ), fun (_ : Unit) =>
        speakS C D.ds₂ (ss.getD []) (ss.map fun _ => startShared H ⟨w.1, w.2.1, ky⟩)
          ((), fun (_ : Unit) => hushSEnd C D.ds₃)))

/-- **A slot's strategy**, from the same, the shared chain's coins, the instance, and the first and
the second chain's coins. It sends the front round's plain part and plays chain 1 and the sealing
round; is silent in the joining round and chain 2, whose challenges it hears; plays that chain's
rounds by `play` for their end; sends the seam's plain part, and plays chain 3. The front round's
and the seam's plain parts are sent at every list of challenges, whatever error there has been. -/
def requestStrategy (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second) :
    LStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  let ky := J.keyOf w.1 w.2.1 w.2.2
  let R := (ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption
  let ss := (readyShared F B H w.1 w.2.1 ky c₀).toOption
  let first := (R.map (·.first)).getD []
  ((((), J.front w.1 w.2.1 w.2.2 x) : Unit × TF), fun (_ : Unit) =>
    speakL C D.ds₁ first (R.map fun R => R.start₁ H) fun m₁ =>
      let e₁ := m₁.bind fun m =>
        (((play (first.drop D.ds₁.length) [⟨[], [], [], none⟩] [] m).bind sealTest).toOption.map
          (·.2))
      ((), fun (_ : Unit) =>
        hushL C D.ds₂ [] fun ds₂ =>
          let e₂ := ss.bind fun l =>
            ((play l ds₂ [] (startShared H ⟨w.1, w.2.1, ky⟩)).toOption.map (·.2))
          let m₃ := R.bind fun R => e₁.bind fun a => e₂.map fun b => R.start₃ H a b
          ((((), J.seam w.1 w.2.1 w.2.2 x) : Unit × T3),
            fun (_ : Unit) => speakLEnd C D.ds₃ ((R.map (·.second)).getD []) m₃)))

end

end ProofFile.Honest
