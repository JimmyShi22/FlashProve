--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SendMoves.lean: what an honest prover lays beneath the roots of the linear
claim's two shared sendings, "send o_u" and "send o_omega", in the form in which the shared
sending's core takes it (Johnson/Prover/Send/Core.lean: for each oracle message of the sending,
every row in full as field values). This file holds definitions only; no theorem is stated.

An oracle message that carries a vector holds three sorts of entries in its main table: the vector's
data, at the places that the layout gives them; the pad of the message's own out-of-domain (OOD)
sample, which is random; and free places, which hold 0. Where the message has no mask row, the pad
lies at the end of its last main row.

  MsgCoins    the coins, that is the random values, of one oracle message: its main rows' tails,
              its pad (one entry for each OOD answer), its mask rows' entries and their tails
  ownPadPlaces  the places of the message's pad, as the verifier's statement notes them
  padCoin     at an index of the main table that is a place of the pad: the pad's random value
  vecMain     the main rows of a message that carries a vector: THE PAD's RANDOM VALUE AT A PLACE OF
              THE PAD, the vector's entry at every other place
  vecRows     all rows of such a message
  coinRows    all rows of a message that has mask rows only: its entries and tails as MsgCoins has
              them. Of o_sp every entry is random. THE FIRST MASK IS A FOLD's FRESH TABLE: its
              entries hold the coefficients of that fold's hiding polynomial, packed, and 0 beyond:
              this file does not say so: there MsgCoins.mask is whatever its caller lays
  sendsU      "send o_u": o_u carries the folded row uHon; the first mask of the proximity test on
              G_u goes out with it
  sendsOmega  "send o_omega": o_omega carries omegaHon; the mask message o_sp goes out with it
  chainWords  the tables of all four messages by number, part and index, as the core holds them
  answersAt   the OOD answers shown in a sending's second round: the core's, at the held words
  kappaOf     the entry of o_sp at an index of its mask table
  muSent      the scalar sent at "SPLIT": muHon at that entry

The data are Johnson/Desc/K14/Honest/Moves.lean's uHon, omegaHon and muHon. Their 0 outside the
places that they name serves here as the 0 of the free places alone: at a place of the pad vecMain
lays the random value.

Places beyond a code's message length. The shared sending's core asks of its caller that a row hold
0 from its code's message length on. vecMain lays at every place the entry of the vector that the
layout numbers there, and coinRows what MsgCoins has there. A row of a table has 2 ^ logEll places,
and logEll is the least number whose power of two reaches the code's message length (Code.logEll,
OnBytes/Iop/Ground.lean). So where every code's message length is a power of two (lengthsFit,
Johnson/Desc/Own/Lin.lean, which "LIN point" tests on the statement's codes) a table has no place
beyond that length. Nothing here is meant for codes that fail that test: there the layout itself
would number entries of the vector at places that no code word holds.

What is not here. From which random source the values of MsgCoins come, and in which order: they are
free variables. The roots and the written columns: they are the core's, and so is the formula of an
OOD answer. vecMain gives one random value to each OOD answer: that fits main rows over the
extension field, which both vectors' messages have.
What is not claimed. Nothing: no statement is made.

-/
import Johnson.Desc.K14.Honest.Moves
import Johnson.Desc.Own.Send
import Johnson.Prover.Send.Core
import OnBytes.Slice.BlkSendRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open Johnson.Prover.Send (Rows held answers)
open Desc.K14.Law

/-- The random values of one oracle message. Row, then place. -/
structure MsgCoins where
  /-- the main rows' tails -/
  tail : ℕ → ℕ → Cb.Gl.E
  /-- the pad of the message's own OOD sample, where it lies in a main row: one entry an answer -/
  pad : ℕ → Cb.Gl.E
  /-- the mask rows' entries; where there is a mask row, the pad is among them -/
  mask : ℕ → ℕ → Cb.Gl.E
  /-- the mask rows' tails -/
  maskTail : ℕ → ℕ → Cb.Gl.E

/-- The places of the pad of a message's own OOD sample. -/
def ownPadPlaces (codes : Codes) (s : OracleShape) : List PadPlace :=
  if s.answers == 0 then [] else (VerifiableInference.Desc.Own.padMade codes s).getD []

/-- At an index of the main table that is a place of the pad: the pad's random value. -/
def padCoin (places : List PadPlace) (pad : ℕ → Cb.Gl.E) (t : ℕ) : Option Cb.Gl.E :=
  (places.find? fun p => p.part == .main && p.index == t).map fun p => pad p.answer

/-- **The main rows of a message that carries a vector**: entry (row r, place j) has the index
r + j * 2 ^ rowBits of the table. At a place of the pad: the pad's random value. Elsewhere: the
vector's entry that the layout has at that index. -/
def vecMain (lay : VectorLay) (places : List PadPlace) (data pad : ℕ → Cb.Gl.E) : ℕ → ℕ → Cb.Gl.E :=
  fun r j => (padCoin places pad (r + j * 2 ^ lay.rowBits)).getD
    (data (lay.entryAt (r + j * 2 ^ lay.rowBits)))

/-- All rows of a message that carries a vector over the extension field. -/
def vecRows (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (data : ℕ → Cb.Gl.E)
    (c : MsgCoins) : Rows :=
  { mainE := vecMain (vectorLay codes s rowsHigh) (ownPadPlaces codes s) data c.pad
    mainF := fun _ _ => 0
    mainTlE := c.tail
    mainTlF := fun _ _ => 0
    mask := c.mask
    maskTl := c.maskTail }

/-- All rows of a message that has mask rows only: entries and tails as c has them. -/
def coinRows (c : MsgCoins) : Rows :=
  { mainE := fun _ _ => 0
    mainF := fun _ _ => 0
    mainTlE := fun _ _ => 0
    mainTlF := fun _ _ => 0
    mask := c.mask
    maskTl := c.maskTail }

/-- **"send o_u"**: message 0 is o_u, which carries the folded row; what follows is the first mask
of the proximity test on G_u. w: the rows' weights; Rw: the committed table's rows before encoding.
A row is meant to be 0 from the place ell up to the place tailFirst, where its tail begins: nothing
here asks it, no constraint of the shared rounds reads these places, and o_u's own sample row does.
-/
def sendsU (codes : Codes) (S : LinShape) (w : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (cU cMask : MsgCoins) : ℕ → Rows
  | 0 => vecRows codes S.fold.u S.fold.rowsHigh (uHon S.fold w Rw) cU
  | _ => coinRows cMask

/-- **"send o_omega"**: message 0 is o_omega, which carries omega_col; what follows is the mask
message o_sp. u: the folded row. -/
def sendsOmega (codes : Codes) (S : LinShape) (psiLo : List Cb.Gl.E)
    (u : ℕ → Cb.Gl.E) (cOmega cSp : MsgCoins) : ℕ → Rows
  | 0 => vecRows codes S.omega S.omegaRowsHigh (omegaHon S psiLo u) cOmega
  | _ => coinRows cSp

/-- **The tables of the two sendings' messages**, by number, part and index. first: the number that
the first message of "send o_u" gets; next: the number that the first message of "send o_omega"
gets. -/
def chainWords (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par) (VU VO : ℕ → Rows) : Words Cb.Gl.E :=
  held (held w₀ first PU VU) next PO VO

/-- **The OOD answers shown in a sending's second round**: the core's, at the held words. T: the
statement in front of the sending; r₁: the sending's first round, in which the verifier samples the
OOD seeds; w: the words in front. -/
def answersAt (Q : VerifiableInference.Desc.K1.Par) (T : Statement) (r₁ : Fmt.RoundView)
    (w : Words Cb.Gl.E) (V : ℕ → Rows) : List Fmt.ItemValue :=
  (answers Q (Slice.stSent T Q.sent) T.oracles.size (held w T.oracles.size Q V)
    (VerifiableInference.Desc.K1.cutSeeds Q.coordinates Q.seeds
      (r₁.drawn.elems.map E.ofTriple))).map Fmt.ItemValue.answer

/-- The entry of a message of mask rows at an index of its mask table: in an index the row's number
is the low part. rows: the number of mask rows. -/
def kappaOf (c : MsgCoins) (rows kappa : ℕ) : Cb.Gl.E :=
  c.mask (kappa % 2 ^ ceilLog2 rows) (kappa / 2 ^ ceilLog2 rows)

/-- **The scalar sent at "SPLIT"**: omega_col at z_fd plus the entry number kappa of o_sp. -/
def muSent (S : LinShape) (psiLo z : List Cb.Gl.E) (u : ℕ → Cb.Gl.E) (cSp : MsgCoins)
    (kappa : ℕ) : Cb.Gl.E :=
  muHon S z (omegaHon S psiLo u) (kappaOf cSp S.sharedSplit.maskRows kappa)

end Desc.K14.Honest
