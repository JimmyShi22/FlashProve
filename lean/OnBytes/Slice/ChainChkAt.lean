-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainChkAt.lean: the checker on bytes `chainChk` as a plain function of a function on
byte strings, and the oracle on bit strings at which that plain function is the checker's answer.

OnBytes/Slice/OneWorldChain.lean has the checker `chainChk` as a computation that asks an oracle on
bit strings. Its answer at a fixed oracle g is `(chainChk ..).det g`. This file writes the checker's
text a second time, with the library's strict reader at the hash that a function O on byte strings
induces in the place of the reader that asks, and proves that the two give one answer. It serves
tests: as observed, Lean's evaluator is slow at an oracle on bit strings and quick at a function on
byte strings.

Main definitions.
 `chainChkAt O`      the checker's text at the function O: `pre`, the tests on the roots' lengths
                     and on the limits, the strict reader at the hash that `Tie.pinned O` induces,
                     and `chainPost`.
 `bitsOf O`          the oracle on bit strings that is made from O as `Run.oBits` is made from the
                     format's oracle.
Main theorems.
 `chainChk_det`      at every oracle g the checker's answer is `chainChkAt (Run.oB (g ()))`.
 `bitsOf_oracle`     `bitsOf Fmt.oracle` is `Run.oBits`.
 `HO_pinned_bitsOf`  for O with answers of 32 bytes, the hash that the oracle `bitsOf O` induces,
                     with the one string pinned, is the hash that O induces, with that string
                     pinned.
 `chainChk_bitsOf`   for such O the checker's answer at `bitsOf O` is `chainChkAt O`.
 `chainChk_oBits`    the checker's answer at `Run.oBits` is `chainChkAt Fmt.oracle`.

What is not claimed. Nothing on soundness, and no probability: every oracle is fixed. Equations
between two answers; both may be "no". That the checker says yes on anything is not shown here
(a test that is not in this library tests it). As functions on all byte strings `Run.oB (bitsOf O
())` and O may differ; they agree at the strings of the hash's calls. BLAKE2b's digest of the
parameter bytes is a plain value in both forms. The checker is not the program, which is the Lean
port built from OnBytes/, not the C++ verifier; the program does not call any function of this file.

-/
import OnBytes.Slice.OneWorldChain
import Run.ParserHashProofs

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Compile Compile.Batch _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf withinX pinned readAskR readAskR_det)

variable {γ : Type} (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)

/-- **The checker's text at a function O on byte strings**: `chainChk` with the library's strict
reader, in the identity monad, at the hash that `Tie.pinned O S0.base.params` induces, in the place
of the reader that asks. A plain function; it asks no oracle. The program does not call it. -/
def chainChkAt (O : ByteArray → ByteArray)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    Option (LinkOut 256 ((xdOf S0 stm).L dec)) :=
  match pre x with
  | none => none
  | some (r0, r1, b, i, fin) =>
    if r0.size = 32 ∧ r1.size = 32 ∧ withinX (reStated S0 (stm r0 r1)) = true then
      chainPost S0 stm dec r0 r1 fin
        (Fmt.readChainX (m := Id) (Fmt.HO (pinned O S0.base.params)) (reStated S0 (stm r0 r1)) []
          b i)
    else none

/-- **At every oracle g on bit strings the checker's answer is its plain form at the function on
byte strings that g induces.** An equation between two answers; both may be "no". Nothing on
soundness; no probability. -/
theorem chainChk_det (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (x : γ) (g : Fam (rom 256)) :
    (chainChk S0 stm dec pre x).det g = chainChkAt S0 stm dec (oB (g ())) pre x := by
  unfold chainChk chainChkAt
  cases pre x with
  | none => rfl
  | some p =>
    obtain ⟨r0, r1, b, i, fin⟩ := p
    dsimp only
    by_cases hc : r0.size = 32 ∧ r1.size = 32 ∧ withinX (reStated S0 (stm r0 r1)) = true
    · rw [if_pos hc, if_pos hc, OComp.det_bind, readAskR_det]
      rfl
    · rw [if_neg hc, if_neg hc]
      rfl

/-- The oracle on bit strings that is made from a function O on byte strings: a bit string is turned
into bytes by the library's one-to-one `Run.toBytes`, and O's answer into a digest. A bit string
that is no whole number of bytes, or whose first byte is 4, goes behind the escape byte 4. Of O's
answer the first 256 bits are taken, whatever its length. -/
def bitsOf (O : ByteArray → ByteArray) : Fam (rom 256) := fun _ s => bytesToDig (O (toBytes s))

/-- Made from the format's oracle, it is the library's `Run.oBits`. -/
theorem bitsOf_oracle : bitsOf Fmt.oracle = oBits := rfl

/-- For O with answers of 32 bytes: the hash that `bitsOf O` induces, with the string of the call on
`params` pinned, is the hash that O induces, with that string pinned. The two functions on byte
strings agree at the strings of the hash's calls, whose first byte is not the escape of
`Run.toBytes`. -/
theorem HO_pinned_bitsOf (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (params : ByteArray) :
    Fmt.HO (pinned (oB (bitsOf O ())) params) = Fmt.HO (pinned O params) := by
  funext n t i st bs
  have hq : ∀ half : UInt8, half = 0 ∨ half = 1 →
      oB (bitsOf O ()) (Fmt.oStr half n t i st bs) = O (Fmt.oStr half n t i st bs) := by
    intro half hh
    show digToBytes (bytesToDig (O (toBytes (bytesToBits (Fmt.oStr half n t i st bs))))) = _
    rw [toBytes_plain _ (plain_oStr half n t i st bs hh), bitsToBytes_bytesToBits,
      digToBytes_bytesToDig _ (hO _)]
  have hp : ∀ half : UInt8, half = 0 ∨ half = 1 →
      pinned (oB (bitsOf O ())) params (Fmt.oStr half n t i st bs) =
        pinned O params (Fmt.oStr half n t i st bs) := by
    intro half hh
    unfold pinned
    rw [hq half hh]
  unfold Fmt.HO
  rw [hp 0 (Or.inl rfl), hp 1 (Or.inr rfl)]

/-- **For O with answers of 32 bytes, the checker's answer at the oracle `bitsOf O` is its plain
form at O.** Nothing on soundness; no probability. -/
theorem chainChk_bitsOf (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))) (x : γ) :
    (chainChk S0 stm dec pre x).det (bitsOf O) = chainChkAt S0 stm dec O pre x := by
  rw [chainChk_det]
  unfold chainChkAt
  rw [HO_pinned_bitsOf O hO]

/-- The checker's answer at `Run.oBits`, the library's oracle on bit strings that is made from the
format's hash, is its plain form at the format's oracle. -/
theorem chainChk_oBits (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (x : γ) : (chainChk S0 stm dec pre x).det oBits = chainChkAt S0 stm dec Fmt.oracle pre x :=
  chainChk_bitsOf S0 stm dec Fmt.oracle Fmt.size_oracle pre x

end OnBytes.Slice
