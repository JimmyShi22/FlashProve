-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Tidy.lean: RULES ON BYTES THAT MAKE ANY BYTE COINS (ByteCoins,
OnBytes/Prover/Print/Coins.lean) MEET CoinsPrint (OnBytes/Prover/Print/Owed.lean) BY MAKE.

Main names.
  fitBytes n b    b if it has n bytes; else its first n bytes, zero bytes where it has none: n
    bytes.
  one32, offZero  a written value of 32 bytes (the byte 1, then zero bytes); b if it passes the
    format's test runOk (it is not 32 zero bytes), else one32.
  fitPath n l     l if it has n entries; else its first n, the all-false digest where it has none.
  ByteCoins.tidy salt s bc   the three run values by fitBytes 32 and offZero; each leaf's own bytes
    by fitBytes salt; the place modulo 2 ^ s.logLeaves; the siblings by fitPath; the place's bytes
    by fitBytes s.saltBytes. The filling body is kept.
  coinsPrint_tidy   salt ≤ 64 → CoinsPrint (bc.tidy salt s) salt s: at every bc.
  tidy_of_print     byte coins that meet CoinsPrint are left as they are.

THE RULES ARE NOT ONE TO ONE: several byte coins have one tidy form.
WHICH DEFAULT IS WRITTEN, AND AT WHICH TEST's FAILURE: fitBytes n b: where b.size ≠ n: b's first n
bytes, A ZERO BYTE where b has none · offZero b: where Fmt.runOk b fails (32 zero bytes): THE
CONSTANT one32 · fitPath n l: where l.length ≠ n: l's first n entries, THE ALL-FALSE DIGEST where l
has none · the place: its remainder modulo 2 ^ s.logLeaves. SO A TIDIED VALUE IS NOT THE RAW VALUE
wherever one of these tests fails; where all pass it is (tidy_of_print).

Limits. Rules on bytes and lengths alone. Nothing on how any program draws its bytes, and nothing is
said of their distribution. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Iop (Dig)
open TypedOracleCompiler.Iop (BatchProtocolWithLeafBody)

def fitBytes (n : ℕ) (b : ByteArray) : ByteArray :=
  if b.size = n then b else ⟨Array.ofFn (n := n) fun i => b.get! i.val⟩

theorem size_fitBytes (n : ℕ) (b : ByteArray) : (fitBytes n b).size = n := by
  unfold fitBytes
  split
  · assumption
  · exact Array.size_ofFn

theorem fitBytes_of_size {n : ℕ} {b : ByteArray} (h : b.size = n) : fitBytes n b = b := if_pos h

def one32 : ByteArray := ⟨Array.ofFn (n := 32) fun i => if i.val = 0 then 1 else 0⟩

def offZero (b : ByteArray) : ByteArray := if _root_.Fmt.runOk b = true then b else one32

theorem runOk_offZero (b : ByteArray) : _root_.Fmt.runOk (offZero b) = true := by
  unfold offZero
  split
  · assumption
  · decide +kernel

theorem size_offZero {b : ByteArray} (h : b.size = 32) : (offZero b).size = 32 := by
  unfold offZero
  split
  · exact h
  · exact Array.size_ofFn

theorem offZero_of_ok {b : ByteArray} (h : _root_.Fmt.runOk b = true) : offZero b = b := if_pos h

def fitPath (n : ℕ) (l : List (Dig 256)) : List (Dig 256) :=
  if l.length = n then l else (l ++ List.replicate n fun _ => false).take n

theorem length_fitPath (n : ℕ) (l : List (Dig 256)) : (fitPath n l).length = n := by
  unfold fitPath
  split
  · assumption
  · rw [List.length_take, List.length_append, List.length_replicate]
    omega

theorem fitPath_of_length {n : ℕ} {l : List (Dig 256)} (h : l.length = n) : fitPath n l = l :=
  if_pos h

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- **The tidy form of byte coins.** -/
def ByteCoins.tidy (salt : ℕ) (s : Params.LinBindingShape) (bc : ByteCoins L) : ByteCoins L where
  run1 := offZero (fitBytes 32 bc.run1)
  run2 := offZero (fitBytes 32 bc.run2)
  run3 := offZero (fitBytes 32 bc.run3)
  leaf := fun i b k j => fitBytes salt (bc.leaf i b k j)
  pad := bc.pad
  place := bc.place % 2 ^ s.logLeaves
  slotPath := fitPath s.logLeaves bc.slotPath
  slotSalt := fitBytes s.saltBytes bc.slotSalt

/-- **At every byte coins the tidy form meets CoinsPrint.** -/
theorem coinsPrint_tidy (salt : ℕ) (s : Params.LinBindingShape) (bc : ByteCoins L)
    (h : salt ≤ 64) : CoinsPrint (bc.tidy salt s) salt s where
  fit :=
    { run1 := size_offZero (size_fitBytes 32 _)
      run2 := size_offZero (size_fitBytes 32 _)
      run3 := size_offZero (size_fitBytes 32 _)
      leaf := fun _ _ _ _ => size_fitBytes salt _
      place := Nat.mod_lt _ (Nat.two_pow_pos _)
      slotPath := length_fitPath _ _
      slotSalt := size_fitBytes _ _ }
  salt64 := h
  ok1 := runOk_offZero _
  ok2 := runOk_offZero _
  ok3 := runOk_offZero _

/-- Byte coins that meet CoinsPrint are left as they are. -/
theorem tidy_of_print {salt : ℕ} {s : Params.LinBindingShape} {bc : ByteCoins L}
    (h : CoinsPrint bc salt s) : bc.tidy salt s = bc := by
  obtain ⟨r1, r2, r3, lf, pd, pl, sp, ss⟩ := bc
  have e1 : offZero (fitBytes 32 r1) = r1 := by
    rw [fitBytes_of_size h.fit.run1]
    exact offZero_of_ok h.ok1
  have e2 : offZero (fitBytes 32 r2) = r2 := by
    rw [fitBytes_of_size h.fit.run2]
    exact offZero_of_ok h.ok2
  have e3 : offZero (fitBytes 32 r3) = r3 := by
    rw [fitBytes_of_size h.fit.run3]
    exact offZero_of_ok h.ok3
  have e4 : (fun i b k j => fitBytes salt (lf i b k j)) = lf :=
    funext fun i => funext fun b => funext fun k => funext fun j =>
      fitBytes_of_size (h.fit.leaf i b k j)
  have e5 : pl % 2 ^ s.logLeaves = pl := Nat.mod_eq_of_lt h.fit.place
  have e6 : fitPath s.logLeaves sp = sp := fitPath_of_length h.fit.slotPath
  have e7 : fitBytes s.saltBytes ss = ss := fitBytes_of_size h.fit.slotSalt
  show (⟨offZero (fitBytes 32 r1), offZero (fitBytes 32 r2), offZero (fitBytes 32 r3),
    fun i b k j => fitBytes salt (lf i b k j), pd, pl % 2 ^ s.logLeaves, fitPath s.logLeaves sp,
    fitBytes s.saltBytes ss⟩ : ByteCoins L) = _
  rw [e1, e2, e3, e4, e5, e6, e7]

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.fitBytes
#print axioms OnBytes.Prover.Print.size_fitBytes
#print axioms OnBytes.Prover.Print.fitBytes_of_size
#print axioms OnBytes.Prover.Print.one32
#print axioms OnBytes.Prover.Print.offZero
#print axioms OnBytes.Prover.Print.runOk_offZero
#print axioms OnBytes.Prover.Print.size_offZero
#print axioms OnBytes.Prover.Print.offZero_of_ok
#print axioms OnBytes.Prover.Print.fitPath
#print axioms OnBytes.Prover.Print.length_fitPath
#print axioms OnBytes.Prover.Print.fitPath_of_length
#print axioms OnBytes.Prover.Print.ByteCoins.tidy
#print axioms OnBytes.Prover.Print.coinsPrint_tidy
#print axioms OnBytes.Prover.Print.tidy_of_print
