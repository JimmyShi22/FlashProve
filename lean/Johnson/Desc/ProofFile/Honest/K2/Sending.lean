-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Sending.lean: THE SHARED SENDING AS THE CODE SWITCH's PART CALLS IT
(`Sender`, Honest/K2/Part.lean), over the sending's core (Johnson/Prover/Send/Core.lean). It defines
part of the honest prover. Definitions with code; no theorem.

What is this file's own: `messageRows`: how one oracle message's rows are made of what the caller
says of its main rows and of the message's own stretch of coins, in the order of coins that
Honest/K2/Part.lean's head states. What is the core's: the code words' symbols and their order in a
tree's column (`col`); the held words (`held`); the answers, each the left side of the kind K1's own
sample row on the held words (`answers`). ONE LETTER: `table`: the table of a fold's fresh mask, of
the fold's row variables, those of its mask rows, and the hiding polynomial's coefficients by
number: row, place.

THREE PUBLIC TESTS STAND IN FRONT. `messageRows` itself asks, at every message, THE VERIFIER's OWN
TEST ON THE SHAPE OF A MESSAGE THAT IS SENT (`sentShapeFits`, Johnson/Desc/Own/Sent.lean: it has a
row; the codes of its rows are in their lists; its main rows lie over one of the two fields), and
refuses otherwise: without that a code that is not in its list would count as a code of length 0,
and the message's rows would be empty in silence. It asks, at a fresh mask, that THE TABLE FITS THE
MESSAGE's SHAPE (`K1.rideFits`, Honest/K1/Coins.lean), and refuses otherwise: without that it would
cut the table at the mask code's message length in silence; so every caller is held, the closing
too. `rowsAll` asks the shared sending's whole test on a sending (`K1.sendFits`, the same file: the
codes' message lengths are powers of two; every sampled message's pad fits its row; the like of a
fresh mask).

Coins. A message is handed ITS OWN stretch, cut off the sending's coins at the message's count. All
its coins are read at once, each sort from its first number on. A read beyond the count is a
refusal, and so is a stretch that holds more coins than the message lays.

ONE DEFAULT REACHES A SEED's FACTOR. The sender's answers cut the seeds off the elements drawn by
the library's `K1.cutSeeds` (Johnson/Desc/K1/Own.lean), which LAYS 0 FOR A FACTOR WHERE THE LIST IS
TOO SHORT (and cuts a seed's coordinates short): there a pad has weight 0 in its answer. THE SENDER
DOES NOT REFUSE THERE. It is shut outside this file: a challenge that the kind's first round can
draw has just the place's elements, and both statements on the sender ask that length (`seedsFit`,
Honest/K2/Exact.lean, which this library may not hold).

  `FreshTable`    the type of the letter `table`
  `messageRows`   one message's rows in full; `zeroMessage`
  `sendingPar`, `rideOf`   a sending's messages as the core's public letter; which of them is a
                 fold's fresh mask, as the shared sending says it
  `rowsAll`      the messages of a sending, each of its own stretch of the sending's coins
  `coreSender`   the sender

Limits. The answers are counted at a statement that holds the sending's messages alone, numbered
from 0: that they are the answers at the run's statement, where the messages have later numbers, is
not shown here. The sample rows that a switch's text lays are `formMade`'s
(Johnson/Desc/Own/Send.lean), not K1's `sampleRow`: that the two have one left side is not shown
here. Of `sendingPar` the core reads the codes and the messages alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Part
import Johnson.Desc.ProofFile.Honest.K1.Coins
import Johnson.Prover.Send.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (zeroG)
open Johnson.Prover.Send (Rows)

/-- The table of a fold's fresh mask, as a letter: the fold's row variables; those of its mask rows;
the coefficients by number; row; place. -/
abbrev FreshTable : Type := Nat → Nat → (Nat → Cb.Gl.E) → Nat → Nat → Cb.Gl.E

/-- **One oracle message's rows in full**: of its main rows outside the pad, and of ITS OWN stretch
of coins. fold: `some n` at the fresh mask of a fold with n row variables. Of an entry of a row over
the base field the first coordinate is read. EACH COIN STANDS AT ONE PLACE, but for a fresh mask's
coefficients, which the letter `table` lays: outside the message's rows, its rows' places (from the
code's message length on, too) and its tails' numbers all six functions yield 0. -/
def messageRows (table : FreshTable) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (fold : Option Nat) (data : Nat → Nat → Cb.Gl.E) (k : Stretch) : Except String Rows := do
  let c := codes.base.getD s.code default
  let z := codes.mask.getD s.maskCode default
  let overE := s.mainDeg == 3
  let tails := s.mainRows * c.r
  let pad : List Nat :=
    if s.maskRows != 0 then []
    else ((VerifiableInference.Desc.Own.padMade codes s).getD []).map (·.index)
  let padAt (b j : Nat) : Option Nat :=
    (pad.zipIdx.find? (·.1 == b + j * 2 ^ OnBytes.ceilLog2 s.mainRows)).map (·.2)
  let inMain := tails + pad.length
  let e₀ := if overE then inMain else 0
  let inMask := match fold with
    | some n => 2 * n + 1
    | none => s.maskRows * z.ell
  if !VerifiableInference.Desc.Own.sentShapeFits codes s then
    throw "a message's shape does not fit the codes"
  if (fold.map fun n => K1.rideFits codes s ⟨n, OnBytes.ceilLog2 s.maskRows⟩) == some false then
    throw "a fresh mask's table does not fit its message"
  -- every coin of the message is read here, once
  let coinsF ← k.fs 0 (if overE then 0 else inMain)
  let coinsE ← k.es 0 e₀
  let maskCoins ← k.es e₀ inMask
  let tailCoins ← k.es (e₀ + inMask) (s.maskRows * z.r)
  if k.due != (⟨if overE then 0 else inMain, e₀ + inMask + s.maskRows * z.r⟩ : Due) then
    throw "a message is handed more coins than it lays"
  let inMainAt (b j : Nat) : Bool := decide (b < s.mainRows) && decide (j < c.ell)
  let inTailAt (b q : Nat) : Bool := decide (b < s.mainRows) && decide (q < c.r)
  pure
    { mainE := fun b j =>
        if !(overE && inMainAt b j) then zeroG else
        match padAt b j with
        | some t => coinsE.getD (tails + t) zeroG
        | none => data b j
      mainF := fun b j =>
        if overE || !inMainAt b j then OnBytes.Slice.toF 0 else
        match padAt b j with
        | some t => coinsF.getD (tails + t) (OnBytes.Slice.toF 0)
        | none => (data b j).c0
      mainTlE := fun b q => if overE && inTailAt b q then coinsE.getD (b * c.r + q) zeroG else zeroG
      mainTlF := fun b q =>
        if !overE && inTailAt b q then coinsF.getD (b * c.r + q) (OnBytes.Slice.toF 0)
        else OnBytes.Slice.toF 0
      mask := fun r i =>
        if !(decide (r < s.maskRows) && decide (i < z.ell)) then zeroG else
        match fold with
        | some n => table n (OnBytes.ceilLog2 s.maskRows) (maskCoins.getD · zeroG) r i
        | none => maskCoins.getD (i * s.maskRows + r) zeroG
      maskTl := fun r q =>
        if decide (r < s.maskRows) && decide (q < z.r) then tailCoins.getD (r * z.r + q) zeroG
        else zeroG }

/-- A message of zeros. -/
def zeroMessage : Rows :=
  ⟨fun _ _ => zeroG, fun _ _ => OnBytes.Slice.toF 0, fun _ _ => zeroG,
    fun _ _ => OnBytes.Slice.toF 0, fun _ _ => zeroG, fun _ _ => zeroG⟩

/-- A sending's messages as the core's public letter. -/
def sendingPar (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    VerifiableInference.Desc.K1.Par :=
  { place := default, codes := codes, gp := ⟨0, 0⟩, work := 0, parts := [("", sent)] }

/-- Which message of a sending is a fold's fresh mask, as the shared sending says it: the fold's row
variables, and those of the message's mask rows. -/
def rideOf (sent : Array OnBytes.OracleNotice) (fresh : Option (Nat × Nat)) (k : Nat) :
    Option K1.Ride :=
  (foldAt fresh k).map fun n => ⟨n, OnBytes.ceilLog2 (sent.getD k default).shape.maskRows⟩

/-- The messages of a sending in full, by number: each of its own stretch of the sending's coins. A
number beyond the sending: a message of zeros. A refusal where the sending does not pass the shared
sending's public test. -/
def rowsAll (table : FreshTable) (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (data : Nat → Nat → Nat → Cb.Gl.E)
    (c : Cs (sendingDue codes sent fresh)) : Except String (Nat → Rows) :=
  if !K1.sendFits (sendingPar codes sent) (rideOf sent fresh) then
    .error "the sending does not fit its place"
  else
  ((List.range sent.size).mapM fun k =>
    ((Stretch.of c).cut (dueBefore codes sent fresh k)
      (messageDue codes (sent.getD k default).shape (foldAt fresh k))).bind
      (messageRows table codes (sent.getD k default).shape (foldAt fresh k) (data k))).map
    fun l k => l.getD k zeroMessage

/-- **The sender**, over the core. "answers: ONLY
UNDER seedsFit: see the head, "One default reaches a seed's factor"". -/
def coreSender (table : FreshTable) : Sender where
  tables codes sent fresh data c :=
    let lay := (VerifiableInference.Desc.Own.treesMade codes sent).getD {}
    (rowsAll table codes sent fresh data c).map fun V =>
      lay.shapes.toList.zipIdx.map fun t =>
        ⟨t.1.logN, t.1.mainWidth + t.1.maskWidth, fun x w =>
          OnBytes.Slice.toF
            ((Johnson.Prover.Send.col (sendingPar codes sent) V t.2 x).getD w.val 0)⟩
  answers codes sent fresh data c drawn :=
    let P := sendingPar codes sent
    (rowsAll table codes sent fresh data c).map fun V =>
      (Johnson.Prover.Send.answers P
        { codes := codes, oracles := sent.map fun n => { shape := n.shape } } 0
        (Johnson.Prover.Send.held (fun _ _ _ => zeroG) 0 P V)
        (VerifiableInference.Desc.K1.cutSeeds P.coordinates P.seeds
          (drawn.map OnBytes.E.ofTriple))).map OnBytes.Slice.toE

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.FreshTable
#print axioms ProofFile.Honest.K2.messageRows
#print axioms ProofFile.Honest.K2.zeroMessage
#print axioms ProofFile.Honest.K2.sendingPar
#print axioms ProofFile.Honest.K2.rideOf
#print axioms ProofFile.Honest.K2.rowsAll
#print axioms ProofFile.Honest.K2.coreSender
