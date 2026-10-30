-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyMsgOm.lean: a sent message of a key file's chains as an oracle message of the
library, with its sample. DEFINITIONS, AND STATEMENTS THAT ARE NOT PROVED.


The library's unit "oracle message" (Cb/Ld/LdSig.lean: OMsg) has a code, a radius and a sample map
on all entries of the message; its decoder takes the word as sent, a seed and the answers, and
picks among the messages near the word the one with these answers. This file makes that unit from
a message's format (OnBytes/Slice/KeyGroup.lean: Mb), one entry and one number (MbAt).

The sample map is the library's row with a pad (Cb/Obj/LdObjectToyKit.lean: StdM): at an entry that
is not the pad, the equality kernel at the seed's point and the corner whose bits are the entry's
index on the message's cube; at the pad, the seed's factor. The cube's numbers are functions of the
format: row bits and place bits are the ceilings of the logarithms of the numbers of rows and of a
row's entries; with both tables there is one bit more, and a mask entry's index is offset by half
the cube (Mb.cubeBits, Mb.cubeOff, Mb.idxJ). An entry's index in its own table is
OnBytes/Slice/BlkCross.lean's Mb.idx.

A message's sample, seed and answer, has a type that hangs on the format alone (SmpT).

The seeds of a sending: one joint seed, of which each member reads a prefix (seeds1 for a sending of
one message; sigOK, seedsOK for the two messages whose seeds are drawn in one round). The number of
joint seeds that give one member's seed is written out as a power.

Main definitions: Mb.rbM, rbZ, pbM, pbZ, mainBits, maskBits, both, cubeBits, cubeOff, idxJ; MbAt,
MbAt.bits, stdAt, omAt, SmpT, padErr, seedCnt, seeds1, sigOK, seedsOK.

Statements, as definitions of type Prop: padErr_stmt, seeds1_fair, seedsOK_fair, seed_cnt_eq.

Not claimed. NONE OF THE FOUR STATEMENTS IS PROVED HERE. That the sample map has the library's
property, or that a list is bounded. That the cube's numbers, the index and the pad's place are the
program's. The count for the round with two members against the closed arithmetic is not stated.
-/
import OnBytes.Slice.BlkCross
import OnBytes.Slice.KeySmpRead

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

namespace Mb
variable (M : Mb)
/-- The bits of a main row's number. -/
def rbM : ℕ := ceilLog2 M.nM
/-- The bits of a mask row's number. -/
def rbZ : ℕ := ceilLog2 M.nZ
/-- The bits of a place in a main row. -/
def pbM : ℕ := ceilLog2 M.C.l
/-- The bits of a place in a mask row. -/
def pbZ : ℕ := ceilLog2 M.Z.l
/-- The bits of an index of the main table; 0 if there is none. -/
def mainBits : ℕ := if 0 < M.nM then M.rbM + M.pbM else 0
/-- The bits of an index of the mask table; 0 if there is none. -/
def maskBits : ℕ := if 0 < M.nZ then M.rbZ + M.pbZ else 0
/-- The message has both tables. -/
def both : Bool := decide (0 < M.nM) && decide (0 < M.nZ)
/-- The coordinates of the message's cube. -/
def cubeBits : ℕ := if M.both then max M.mainBits M.maskBits + 1 else M.mainBits + M.maskBits
/-- Where the mask table begins on the cube. -/
def cubeOff : ℕ := if M.both then 2 ^ (M.cubeBits - 1) else 0
/-- An entry's index on the cube, through its index in its own table. -/
def idxJ (j : M.cd.J) : ℕ :=
  match M.idx M.rbM M.rbZ j with
  | (.main, n) => n
  | (.mask, n) => M.cubeOff + n
end Mb

/-- What a message's oracle message is made of, beside its format: the pad's entry, and a bound on
its lists. -/
structure MbAt (M : Mb) where
  padJ : M.cd.J
  L : ℕ
/-- The coordinates of the message's cube. -/
@[reducible] def MbAt.bits {M : Mb} (_ : MbAt M) : ℕ := M.cubeBits
/-- The library's data of a standard oracle message, at a message's format. -/
@[reducible] noncomputable def stdAt (M : Mb) (A : MbAt M) : StdM GE M.Ps where
  Cm := M.cd
  Dt := {j // j ≠ A.padJ}
  place := (splitAt A.padJ).symm
  μ := Fin M.cubeBits
  plc := fun j t => (M.idxJ j.1).testBit t.val
  B := GEˣ
  b := Units.val
  e := M.e
/-- **A sent message as an oracle message of the library.** -/
@[reducible] noncomputable def omAt (M : Mb) (A : MbAt M) : OMsg GE := (stdAt M A).om
/-- A message's sample: seed and answer. It hangs on the format alone. -/
abbrev SmpT (M : Mb) : Type := ((Fin M.cubeBits → GE) × GEˣ) × (Unit → GE)
example (M : Mb) (A : MbAt M) : (omAt M A).Smp = SmpT M := rfl
/-- The number of the row with a pad, at m coordinates and the factors other than 0, in closed
arithmetic. -/
noncomputable def padErr (m : ℕ) : ℕ :=
  max (m * Fintype.card GE ^ (m - 1) * (Fintype.card GE - 1)) (Fintype.card GE ^ m)
/-- The count of a seed round for one member, in closed arithmetic. c: the joint point's
coordinates. bits: the member's. L: a bound on its lists. -/
noncomputable def seedCnt (c bits L : ℕ) : ℕ :=
  Fintype.card GE ^ (c - bits) * (L.choose 2 * padErr bits)
/-- STATEMENT, NOT PROVED HERE. The sample map's number is the closed arithmetic. -/
def padErr_stmt : Prop := ∀ (M : Mb) (A : MbAt M), (omAt M A).Z.err = padErr M.cubeBits

/-! ## The seeds of a sending -/

/-- **The seeds of a SEND of one message**: the joint seed has c coordinates and a factor; the
member reads the first bits. The number of joint seeds for one seed of the member is written out. -/
@[reducible] noncomputable def seeds1 (M : Mb) (A : MbAt M) (c : ℕ) :
    (Sig.one (omAt M A)).Seeds :=
  { D := (Fin c → GE) × GEˣ, sd := fun _ => cutPt c A.bits,
    mult := fun _ => Fintype.card GE ^ (c - A.bits) }

/-- **The signature of O and K**, the two messages whose seeds are drawn in one round. false: O.
true: K. -/
@[reducible] noncomputable def sigOK (MO MK : Mb) (AO : MbAt MO) (AK : MbAt MK) : Sig GE :=
  { O := Bool, om := fun b => if b then omAt MK AK else omAt MO AO }

/-- **Their seeds**: both read a prefix of ONE point, and the same factor. -/
@[reducible] noncomputable def seedsOK (MO MK : Mb) (AO : MbAt MO) (AK : MbAt MK) (c : ℕ) :
    (sigOK MO MK AO AK).Seeds :=
  { D := (Fin c → GE) × GEˣ
    sd := fun b => match b with | false => cutPt c AO.bits | true => cutPt c AK.bits
    mult := fun b => match b with
      | false => Fintype.card GE ^ (c - AO.bits) | true => Fintype.card GE ^ (c - AK.bits) }

/-- STATEMENT, NOT PROVED HERE. The prefix is fair, where the member's bits are no more than the
joint point's. -/
def seeds1_fair : Prop := ∀ (M : Mb) (A : MbAt M) (c : ℕ), A.bits ≤ c → (seeds1 M A c).Fair
/-- STATEMENT, NOT PROVED HERE. The same for the two members of one round. -/
def seedsOK_fair : Prop := ∀ MO MK AO AK (c : ℕ), AO.bits ≤ c → AK.bits ≤ c →
  (seedsOK MO MK AO AK c).Fair
/-- STATEMENT, NOT PROVED HERE. The library's count is the closed arithmetic. -/
def seed_cnt_eq : Prop := ∀ (M : Mb) (A : MbAt M) (c : ℕ),
  ldSendFamErr (Sig.one (omAt M A)) (seeds1 M A c) (fun _ => A.L) = seedCnt c A.bits A.L

end OnBytes.Slice
