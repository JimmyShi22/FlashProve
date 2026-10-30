-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLayerTables.lean: the three computed tables against digests in parameter files.

A parameter file can state the digests of the tables (lines tsilu, tsig, trope). The C++ verifier
computes the tables itself and refuses a file whose digests are not those of its own tables. The
digests that are spelled out here are the three of a small configuration's file
(OnBytes/Model/TestConfig.lean) and the rotary table's of a full-size one. The C++ verifier accepts
both files; no test here runs it. The tables that OnBytes/Model/LayerTables.lean computes in whole
numbers must have these digests.

What this shows: equality of all entries at these numbers (eg 8, smax 4095, the gate's clamp, theta0
10000, dh 128, 64 tokens), up to a collision of the hash; and the same for the rotary table of a
full-size configuration (theta0 500000, 1024 tokens), whose two other tables are the same as here.
It shows nothing for other numbers.

This file is not part of the compiled program.
-/
import OnBytes.Model.LayerTables
import OnBytes.Model.Config

namespace OnBytes.Model.Layer.Test

/-- Words of 32 bits as bytes, the lowest byte first. -/
def bytesOf (w : Array Nat) : ByteArray :=
  w.foldl
    (fun b x => (((b.push x.toUInt8).push (x / 2 ^ 8).toUInt8).push (x / 2 ^ 16).toUInt8).push
      (x / 2 ^ 24).toUInt8)
    (ByteArray.emptyWithCapacity (4 * w.size))

/-- exp(c / 256) for c = 0 to 32768, in fixed-point. -/
def X8 : Array Nat := expPowers 8 32768

-- A few entries that are known by hand. SILU is 0 at 0; far to the left it is 0, far to the right
-- the clamp. The sigmoid at 0 is a half. 1 / 3 is the floating-point number
-- 6004799503160661 / 2^54, and 3 is exact. Further down: the angle 0 has the cosine 1 and the
-- sine 0.
#guard siluWord 8 4095 X8 32768 == 4096
#guard siluWord 8 4095 X8 0 == 4096
#guard siluWord 8 4095 X8 65535 == 4096 + 4095
#guard sigmoidAt X8 32768 == 16 * 2048
#guard roundD 1 3 == (6004799503160661, 2 ^ 54)
#guard roundD 3 1 == (3 * 2 ^ 51 * 2 ^ 0, 2 ^ 51)

/-- True if the fraction x has the value n. -/
def isWhole (x : Nat × Nat) (n : Nat) : Bool := x.1 == n * x.2

-- Two ties: 2^53 + 1 lies between 2^53 and 2^53 + 2, and 2^53 + 3 between 2^53 + 2 and 2^53 + 4.
-- Each goes to the neighbour whose 53 bits end in 0: the first down, the second up.
#guard isWhole (roundD (2 ^ 53 + 1) 1) (2 ^ 53)
#guard isWhole (roundD (2 ^ 53 + 3) 1) (2 ^ 53 + 4)

/-- The two tables of the gate at the small configuration's numbers. -/
def gate : Array Nat × Array Nat := gateTables 8 4095 true true

/-- The rotary table at the small configuration's numbers. -/
def rope : Array Nat := ropeTable 12 10000 128 6

#guard rope.getD 0 0 == 4096 + 4096
#guard rope.getD (64 * 64) 0 == 4096

#guard tableDigest (bytesOf gate.1) == bytesOf
  #[2048398297, 192427613, 2862900154, 2853881485, 2797826050, 1420723544, 3686369553, 2593882461]

#guard tableDigest (bytesOf gate.2) == bytesOf
  #[1965976300, 2359599336, 2246761285, 2426172242, 3869868832, 310049175, 339407438, 2601410768]

#guard tableDigest (bytesOf rope) == bytesOf
  #[2232934348, 2156588140, 3599599331, 498649753, 3675316650, 2999201840, 1537898906, 2900737701]

/-- The rotary table at the numbers of a full-size configuration: 1024 tokens, theta0 500000. -/
def ropeFull : Array Nat := ropeTable 12 500000 128 10

#guard tableDigest (bytesOf ropeFull) == bytesOf
  #[786409086, 1563166184, 1100635208, 2272768750, 1260813977, 3744463197, 3300849996, 4050797957]

end OnBytes.Model.Layer.Test
