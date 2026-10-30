-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/StrInj.lean: the pieces of which the format's string of a call is made are one to one.

The format makes every hash as one call with six fields (`Fmt.OQ`, Fmt/Rules23.lean), and a call has
a string (`Run.strOf`, Run/CodingFn.lean). A call of a chain holds bytes that are made of a message,
a word for kind, work and the call's number, and a nonce (`Run.roundBytes`), or of a digest, a
statement and a run's value (`Run.firstBytes`). Here each of these makers is shown to be one to one,
under the bounds that it needs. No file, no chain and no typed query occurs here.

Main names:
  `strOf_inj`: two calls in the domain of the format's hash, with halves 0 or 1, that have one
    string are one call. From `Fmt.oStr_inj` (Fmt/Rules23Laws.lean).
  `bitsToBytes_inj`, `digToBytes_inj`: bit strings of whole bytes; digests.
  `u64n_inj`: numbers below 2 ^ 64.
  `blockNo_inj`, `half_call_inj`, `ofNat_half_inj`: which block of a row a typed block is; a block's
    number from its half and its call.
  `roundBytes_inj`: at one kind and one number of bits of work: the message, the call's number and
    the nonce. The message needs no bound: the two words are the last sixteen bytes.
  `firstBytes_inj`: the digest, the statement, the run's value.
  `rowForm_inj`, `firstForm_inj`: two forms of a call, as records; equal calls have equal parts.
  `word_cancel`, `whole_of_len`, `map_digToBytes_inj`, `kwcTo_some`: small tools.

Limits: tools alone. Nothing on any hash. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Run.CodingFn
import Run.CodingBitsLaws
import Run.CodingPage160
import Run.CodingPage162
import Fmt.Rules23Laws
import Fmt.Rules23In

set_option autoImplicit false

namespace OnBytes.K.Arm
open _root_.Run

/-- Two calls in the domain, with halves 0 or 1, that have one string are one call. -/
theorem strOf_inj {c c' : Fmt.OQ} (hh : c.half = 0 ∨ c.half = 1) (hh' : c'.half = 0 ∨ c'.half = 1)
    (hd : Fmt.hDom c.number c.tree c.index c.start c.bytes = true)
    (hd' : Fmt.hDom c'.number c'.tree c'.index c'.start c'.bytes = true)
    (e : strOf c = strOf c') : c = c' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Fmt.oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ hh hh' hd hd' e
  cases c
  cases c'
  simp only [Fmt.OQ.mk.injEq]
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- Bit strings of whole bytes. -/
theorem bitsToBytes_inj {a b : List Bool} (ha : whole a = true) (hb : whole b = true)
    (e : bitsToBytes a = bitsToBytes b) : a = b := by
  rw [← bytesToBits_bitsToBytes a ha, e, bytesToBits_bitsToBytes b hb]

/-- Digests. -/
theorem digToBytes_inj {d d' : Iop.Dig 256} (e : digToBytes d = digToBytes d') : d = d' := by
  have h := congrArg bytesToBits e
  rw [bits_digToBytes, bits_digToBytes] at h
  rw [← digOf_ofFn d, h, digOf_ofFn]

/-- Numbers below 2 ^ 64. -/
theorem u64n_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (e : Fmt.u64n x = Fmt.u64n y) :
    x = y := by
  rw [← Fmt.wordAt_u64n x hx, e, Fmt.wordAt_u64n y hy]

/-- Two strings that begin with a word each: the words are equal, and the rests. -/
theorem word_cancel {x y : Nat} {a b : ByteArray} (e : Fmt.u64n x ++ a = Fmt.u64n y ++ b) :
    Fmt.u64n x = Fmt.u64n y ∧ a = b :=
  Fmt.append_cancel _ _ _ _ ((Fmt.size_u64n x).trans (Fmt.size_u64n y).symm) e

/-- A bit string of 8 n bits is of whole bytes. -/
theorem whole_of_len {l : List Bool} {n : Nat} (h : l.length = 8 * n) : whole l = true :=
  (whole_iff l).2 ⟨n, h⟩

/-- Lists of digests. -/
theorem map_digToBytes_inj {l l' : List (Iop.Dig 256)}
    (e : l.map digToBytes = l'.map digToBytes) : l = l' :=
  List.map_injective_iff.2 (fun _ _ h => digToBytes_inj h) e

/-- Which block of the format's row a typed block is. -/
theorem blockNo_inj (w K : Nat) : Function.Injective (blockNo w K) := by
  intro j j' e
  apply Fin.ext
  have h1 := j.isLt
  have h2 := j'.isLt
  unfold blockNo at e
  split_ifs at e <;> omega

/-- A block's number from its half and its call. -/
theorem half_call_inj {b b' : Nat} (h : b % 2 = b' % 2) (h' : b / 2 = b' / 2) : b = b' := by
  omega

/-- The byte of a half. -/
theorem ofNat_half_inj {b b' : Nat} (e : UInt8.ofNat (b % 2) = UInt8.ofNat (b' % 2)) :
    b % 2 = b' % 2 := by
  have h := congrArg UInt8.toNat e
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h
  omega

/-- **The bytes of a call of a round**, at one kind and one number of bits of work. -/
theorem roundBytes_inj {msg msg' : ByteArray} {kind w c c' nonce nonce' v v' : Nat}
    (hv : kwcTo kind w c = some v) (hv' : kwcTo kind w c' = some v') (hn : nonce < 2 ^ 64)
    (hn' : nonce' < 2 ^ 64) (e : roundBytes msg kind w c nonce = roundBytes msg' kind w c' nonce') :
    msg = msg' ∧ c = c' ∧ nonce = nonce' := by
  unfold roundBytes at e
  have hs := congrArg ByteArray.size e
  simp only [ByteArray.size_append, Fmt.size_u64n] at hs
  obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _
    (by simp only [ByteArray.size_append, Fmt.size_u64n]; omega) e
  obtain ⟨e3, e4⟩ := Fmt.append_cancel _ _ _ _ (by omega) e1
  refine ⟨e3, ?_, u64n_inj hn hn' e2⟩
  unfold kwcTo at hv hv'
  split_ifs at hv hv' with h1 h2
  have := u64n_inj (by omega) (by omega) e4
  omega

/-- **The bytes of the call that makes a chain's first value.** -/
theorem firstBytes_inj {pd pd' st st' : ByteArray} {salt salt' : List Bool}
    (hp : pd.size = pd'.size) (hs : st.size < 2 ^ 64) (hs' : st'.size < 2 ^ 64)
    (hw : whole salt = true) (hw' : whole salt' = true)
    (e : firstBytes pd st salt = firstBytes pd' st' salt') :
    pd = pd' ∧ st = st' ∧ salt = salt' := by
  unfold firstBytes at e
  simp only [ByteArray.append_assoc] at e
  obtain ⟨e1, e⟩ := Fmt.append_cancel _ _ _ _ hp e
  obtain ⟨e2, e⟩ := word_cancel e
  obtain ⟨e3, e⟩ := Fmt.append_cancel _ _ _ _ (u64n_inj hs hs' e2) e
  obtain ⟨_, e⟩ := word_cancel e
  refine ⟨e1, e3, ?_⟩
  have e0 : Fmt.u64n 0 = Fmt.u64n 0 ++ ByteArray.empty := ByteArray.append_empty.symm
  by_cases h : salt.isEmpty = true <;> by_cases h' : salt'.isEmpty = true
  · rw [List.isEmpty_iff.1 h, List.isEmpty_iff.1 h']
  · rw [if_pos h, if_neg h', e0] at e
    have := u64n_inj (by decide) (by decide) (word_cancel e).1
    omega
  · rw [if_neg h, if_pos h', e0] at e
    have := u64n_inj (by decide) (by decide) (word_cancel e).1
    omega
  · rw [if_neg h, if_neg h'] at e
    exact bitsToBytes_inj hw hw' (word_cancel e).2

/-! ## Two forms of a call -/

/-- **A call of the form in which a round's block is asked**: half and call from the block's number;
the chain's value as the start; the bytes of a call of a round. At one kind, one number of bits of
work and one order of the blocks. n, n': the calls' numbers. -/
theorem rowForm_inj {n n' lab lab' idx idx' kind work nonce nonce' ow K v v' : Nat}
    {ρ ρ' : List Bool} {msg msg' : ByteArray} {j j' : Fin (K + 1)}
    (hρ : whole ρ = true) (hρ' : whole ρ' = true)
    (hv : kwcTo kind work (blockNo ow K j / 2) = some v)
    (hv' : kwcTo kind work (blockNo ow K j' / 2) = some v')
    (hn : nonce < 2 ^ 64) (hn' : nonce' < 2 ^ 64)
    (e : (⟨UInt8.ofNat (blockNo ow K j % 2), n, lab, idx, bitsToBytes ρ,
        roundBytes msg kind work (blockNo ow K j / 2) nonce⟩ : Fmt.OQ) =
      ⟨UInt8.ofNat (blockNo ow K j' % 2), n', lab', idx', bitsToBytes ρ',
        roundBytes msg' kind work (blockNo ow K j' / 2) nonce'⟩) :
    lab = lab' ∧ idx = idx' ∧ ρ = ρ' ∧ msg = msg' ∧ nonce = nonce' ∧ j = j' := by
  simp only [Fmt.OQ.mk.injEq] at e
  obtain ⟨a1, _, a3, a4, a5, a6⟩ := e
  obtain ⟨b1, b2, b3⟩ := roundBytes_inj hv hv' hn hn' a6
  exact ⟨a3, a4, bitsToBytes_inj hρ hρ' a5, b1, b3,
    blockNo_inj ow K (half_call_inj (ofNat_half_inj a1) b2)⟩

/-- **A call of the form in which a chain's first value is made.** h, n, t, s: half, number, tree
and start, whatever they are. -/
theorem firstForm_inj {h h' : UInt8} {n n' t t' lab lab' : Nat} {s s' pd pd' stm stm' : ByteArray}
    {run run' : List Bool} (hp : pd.size = pd'.size) (hs : stm.size < 2 ^ 64)
    (hs' : stm'.size < 2 ^ 64) (hw : whole run = true) (hw' : whole run' = true)
    (e : (⟨h, n, t, lab, s, firstBytes pd stm run⟩ : Fmt.OQ) =
      ⟨h', n', t', lab', s', firstBytes pd' stm' run'⟩) :
    lab = lab' ∧ pd = pd' ∧ stm = stm' ∧ run = run' := by
  simp only [Fmt.OQ.mk.injEq] at e
  obtain ⟨_, _, _, a4, _, a6⟩ := e
  exact ⟨a4, firstBytes_inj hp hs hs' hw hw' a6⟩

/-- If `kwcTo` gives a value, there is a v with `kwcTo kind w c = some v`. -/
theorem kwcTo_some {kind w c : Nat} (h : (kwcTo kind w c).isSome = true) :
    ∃ v, kwcTo kind w c = some v := Option.isSome_iff_exists.1 h

end OnBytes.K.Arm
