-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadNorm.lean: THE OUTPUT HEAD'S OWN ROUNDS: the final norm. Root and reciprocal
are the part Norm.lean, called for one norm; here stand what the final norm has of its own: the
rounding of the stream times the reciprocal, and the clamp. Definitions with code; no theorem.

WHAT IT IS ABOUT, in integers, at EVERY position t. str: the residual stream; R: the reciprocal.
  aw[k]  = floor((str[k] R + 2^(KF-1)) / 2^KF)        act[k] = aw[k] clamped to -2047 .. 2047
act is what the head goes on from (Head.lean).

HOW. The prover has committed to aw, to the rounding's remainder and to act. The rounding and the
clamp are facts on ranges and a table: keys, handed to the head's lookup. One of them holds the
product str R, which is not linear: normed, a sumcheck at the lookup's point zt, ties it to R and to
the stream. With the part's 26 it leaves 29 forms; it asks for seven reads and opens no oracle.

-/
import Johnson.Desc.Kinds.Norm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.FinalNorm

open OnBytes (E)
open Norm (lt ls d lPd T S2 pV squares products)

/-! ## Public, and what comes in -/

/-- T = 2^lt positions. d features, in blocks of 2^ls. MF, KF, epsF: the norm's two shifts and its
epsilon. -/
class Sizes where (lt ls d MF KF epsF : Nat)
export Sizes (MF KF epsF)

/-- The part's sizes: one norm. -/
instance [s : Sizes] : Norm.Sizes :=
  { lt := s.lt, ls := s.ls, d := s.d, NI := 1, MF := fun _ => s.MF, epsF := fun _ => s.epsF }
variable [Sizes]

/-- Four keys. The lookup shows that each, at each entry and position, is a row of its table. -/
inductive Key | remLow | remHigh | clamp | digits
/-- A key's number. -/
def Key.idx : Key → Nat
  | .remLow => 0 | .remHigh => 1 | .clamp => 2 | .digits => 3

/-- From the head's lookup: zt, its point on the positions, and zl, on a block's features. For a key
k: ew k x, the public weight of entry x (the equality weight of its column); ewh k i, that of block
i; wsum k, the sum of all ew k x. -/
class In where
  (zt zl : Point)
  (ew ewh : Key → Nat → E)
  wsum : Key → E
export In (zt zl ew ewh wsum)
variable [In]

/-! ## Hear: behind the part's rounds -/

/-- A sumcheck at zt of the reciprocal times the weighted stream; its end values are these two. -/
class Heard where normed : Sum
export Heard (normed)

/-- THE ROUNDS, and the verifier on them. -/
def hear : Hear Heard := do
  let normed ← sumcheck zt 2
  pure { normed }

/-- The same line as data. -/
def rounds : List Round := sumcheck.rounds lt 2
variable [Norm.Heard] [Heard]

/-! ## Reads: committed behind the head's rounds -/

/-- The matrices that are read: the stream (five limbs a feature), act (two), the row. -/
inductive Matrix | stream | act | row
/-- The seven reads: three are the part's. -/
inductive Read
  | streamAtSquares | streamAtNormed | actAtKeys | rowAtKeys | rowAtPV | rowAtProducts | rowAtNormed

/-- Which matrix a read sums, and under which weights. -/
def Read.of : Read → Matrix × Weights
  | .streamAtSquares => (.stream, Norm.Read.streams.weights)
  | .streamAtNormed  => (.stream, .long (eq zl) (eq normed.r))
  | .actAtKeys       => (.act,    .short (eq zt))
  | .rowAtKeys       => (.row,    .short (eq zt))
  | .rowAtPV         => (.row,    Norm.Read.rowsAtPV.weights)
  | .rowAtProducts   => (.row,    Norm.Read.rowsAtProducts.weights)
  | .rowAtNormed     => (.row,    .short (eq normed.r))

/-- Entry i of a read, as a variable of a form. wide: entry i of the head's read, at (zl, zt), of
the matrix that holds aw from feature 0 on and the remainder's high part from feature 2 d on, two
limbs each. -/
class Reads where
  entry : Read → Nat → Form
  wide : Nat → Form
export Reads (entry wide)

/-- The part's reader: limb l of the stream begins at feature l d; the row's digits at feature 0. -/
instance [x : Reads] : Norm.Reads :=
  { limb := fun _ l k => x.entry .streamAtSquares (l * d / S2 + k),
    cell := fun r _ j => x.entry (if r matches .rowsAtPV then .rowAtPV else .rowAtProducts) j }
variable [Reads]

/-! ## Claims: each form must be 0 -/

/-- str R, summed under the weights of the key remLow. Its end values are R and the weighted
stream. -/
def normedForms : List Form :=
  [normed.left ((normed.end_ 0).shown * (normed.end_ 1).shown),
   (normed.end_ 0).var
     - (OnBytes.Desc.First.P6.Row.ofDigits fun j => entry .rowAtNormed j + off1).R,
   (normed.end_ 1).var
     - ∑ i < d / S2, ∑ l < 5, (256 ^ l * ewh .remLow i) • entry .streamAtNormed (l * d / S2 + i)]

/-- All 29. -/
def forms : List Form := Norm.forms ++ normedForms

/-! ## The four keys, for the head's lookup -/

/-- Two limbs of the head's wide matrix from feature f0 on, under a key's weights. -/
def wideAt (k : Key) (f0 : Nat) : Form :=
  ∑ i < d / S2, ∑ l < 2, (256 ^ l * ewh k i) • wide ((f0 + l * d) / S2 + i)
/-- act of feature k through a read of act. -/
def actAt (x : Nat → Form) (k : Nat) : Form := x k + (256 : Nat) • x (d + k)

/-- A key's entries, summed at the lookup's point. In integers, at entry x and position t:
  remLow   str R + 2^(KF-1) - 2^KF aw - 2^16 rem: 16 bits: so aw is the rounded quotient.
  remHigh  2^(32-KF) rem: 16 bits: so the remainder is below 2^KF.
  clamp    (aw + 32768) + 2^28 (act + 2048) is a row of the clamp's table.
  digits   mul j * (digit j of the row): 8 bits: so each digit is below 256 / mul j.
more: the digits that the head has laid behind the norm's 99 in the same row. -/
def key (more : Nat) : Key → Form
  | .remLow  => normed.claimed.var
                  + wsum .remLow * ((2 ^ (KF - 1) : Nat) - (off2 * 2 ^ 16 : Nat) : E)
                  - (2 ^ KF : Nat) • wideAt .remLow 0 - (2 ^ 16 : Nat) • wideAt .remLow (2 * d)
  | .remHigh => (2 ^ (32 - KF) : Nat) • (off2 * wsum .remHigh + wideAt .remHigh (2 * d))
  | .clamp   => wideAt .clamp 0
                  + (2 ^ 28 : Nat) • (∑ k < d, ew .clamp k • actAt (entry .actAtKeys) k)
                  + wsum .clamp * (2 ^ 15 + 2 ^ 39 : Nat)
  | .digits  => ∑ j < NR + more, (mul j * ew .digits j) • (entry .rowAtKeys j + off1)

end VerifiableInference.Desc.Kinds.FinalNorm
