-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.CompressThm
import Run.Blake2b.LoadThm
import Run.Blake2b.ResumeThm
/-!
# The fast whole function equals the plain definition's

`blake2b_eq_spec`: (blake2b key data outlen).data = Spec.blake2b key.data data.data outlen, for
1 ≤ outlen ≤ 64 and a key of at most 64 bytes. `blake2b_eq_spec_all`: the same for all arguments:
outside that range both sides are empty.

The method: `At S T` says that a state S of Spec.lean and a state T of Compress.lean have the same
chaining value and the same counter, that no flag is set and that last_node is 0. Sections 1 to 4
follow it through blake2b_update's loop, blake2b_update and blake2b_final.

What "#print axioms" reports for blake2b_eq_spec_all: propext, Classical.choice and Quot.sound.
There is no sorry and no axiom of ours.
Source. filled, rest and closed write out again steps of Spec.blake2b_update and Spec.blake2b_final
(Spec.lean); so do the statements of at_step, update_small, update_big, set_lastblock_eq and
final_unfold and some terms inside proofs; the statements of spec_key, spec_small, spec_big and
spec_empty write out the arms of state (Hash.lean). These follow, at one remove, what the two files
name as their source.
Spec.lean's head says (its lines 7 and 8, copied here):
Adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the BLAKE2 reference source code package,
Copyright 2012 Samuel Neves, taken under CC0 1.0 Universal.
Hash.lean's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
-/
namespace Run.Blake2b

/- Kept from unfolding while Lean checks this file; no statement changes. -/
attribute [local irreducible] Spec.blake2b_compress

/-! ## 1. One block -/

/-- A state of Spec.lean and a state of Compress.lean have the same chaining value and the same
counter, no flag is set in either, and last_node is 0. -/
structure At (S : Spec.blake2b_state) (T : State) : Prop where
  h : S.h = T.h.arr
  t0 : S.t0 = T.t0
  t1 : S.t1 = T.t1
  f0 : S.f0 = 0
  f1 : S.f1 = 0
  g0 : T.f0 = 0
  g1 : T.f1 = 0
  node : S.last_node = 0

/-- Add 128 to the counter and compress a block that is not the last. -/
theorem at_step {S : Spec.blake2b_state} {T : State} (a : At S T) (block : Array UInt8) :
    At (Spec.blake2b_compress (Spec.blake2b_increment_counter S (128 : Nat).toUInt64) block)
      (compress (incrementCounter T 128) (MessageBlock.ofBytes ⟨block⟩ 0)) := by
  obtain ⟨c0, c1⟩ := increment_at S T (128 : Nat).toUInt64 a.t0 a.t1
  refine ⟨?_, ?_, ?_, ?_, ?_, a.g0, a.g1, ?_⟩
  · exact compress_h (Spec.blake2b_increment_counter S (128 : Nat).toUInt64) block
      (incrementCounter T 128) a.h c0 c1 (a.f0.trans a.g0.symm) (a.f1.trans a.g1.symm)
  · rw [compress_t0]
    exact c0
  · rw [compress_t1]
    exact c1
  · rw [compress_f0]
    exact a.f0
  · rw [compress_f1]
    exact a.f1
  · rw [compress_last_node]
    exact a.node

/-- A block cut out of the middle of an array. -/
theorem ofBytes_extract (pin : Array UInt8) (a : Nat) (h : a + 128 ≤ pin.size) :
    MessageBlock.ofBytes ⟨pin.extract a (a + 128)⟩ 0 = MessageBlock.ofBytes ⟨pin⟩ a := by
  apply ofBytes_congr
  intro j hj
  have hc : j < min (a + 128) pin.size - a := by omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, Nat.zero_add]
  rw [if_pos hc]

/-! ## 2. The loop of blake2b_update -/

/-- One more block in front of a run of blocks. -/
theorem updateBlocks_front (pin : Array UInt8) (off n : Nat) (T : State) :
    updateBlocks (fun j => MessageBlock.ofBytes ⟨pin⟩ (off + 128 * j)) (n + 1) 0 T =
      updateBlocks (fun j => MessageBlock.ofBytes ⟨pin⟩ (off + 128 + 128 * j)) n 0
        (compress (incrementCounter T 128) (MessageBlock.ofBytes ⟨pin⟩ off)) := by
  rw [updateBlocks_succ]
  have s := updateBlocks_shift (fun j => MessageBlock.ofBytes ⟨pin⟩ (off + 128 * j)) 1 n 0
    (compress (incrementCounter T 128) (MessageBlock.ofBytes ⟨pin⟩ off))
  show updateBlocks (fun j => MessageBlock.ofBytes ⟨pin⟩ (off + 128 * j)) n (1 + 0)
    (compress (incrementCounter T 128) (MessageBlock.ofBytes ⟨pin⟩ (off + 128 * 0))) = _
  rw [Nat.mul_zero, Nat.add_zero off, s]
  refine updateBlocks_congr _ _ _ (fun j _ _ => ?_)
  show MessageBlock.ofBytes ⟨pin⟩ (off + 128 * (1 + j)) = MessageBlock.ofBytes ⟨pin⟩ (off + 128 + 128 * j)
  rw [show off + 128 * (1 + j) = off + 128 + 128 * j from by omega]

/-- The loop compresses all whole blocks but leaves the last 1 to 128 bytes. -/
theorem while_eq (pin : Array UInt8) :
    ∀ (bound : Nat) (S : Spec.blake2b_state) (off len : Nat) (T : State),
      At S T → len ≤ bound → off + len ≤ pin.size →
      ∃ S', Spec.blake2b_update_while pin bound S off len =
          (S', off + 128 * ((len - 1) / 128), len - 128 * ((len - 1) / 128)) ∧
        At S' (updateBlocks (fun j => MessageBlock.ofBytes ⟨pin⟩ (off + 128 * j)) ((len - 1) / 128) 0 T) ∧
        S'.buf = S.buf ∧ S'.buflen = S.buflen ∧ S'.outlen = S.outlen := by
  intro bound
  induction bound with
  | zero =>
    intro S off len T a hb _
    have e : (len - 1) / 128 = 0 := by omega
    refine ⟨S, ?_, ?_, rfl, rfl, rfl⟩
    · rw [e, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
      rfl
    · rw [e]
      exact a
  | succ bound ih =>
    intro S off len T a hb hp
    by_cases hl : 128 < len
    · obtain ⟨S', w, a', b1, b2, b3⟩ := ih _ (off + 128) (len - 128) _
        (at_step a (pin.extract off (off + 128))) (by omega) (by omega)
      have e : (len - 1) / 128 = (len - 128 - 1) / 128 + 1 := by omega
      rw [e]
      generalize (len - 128 - 1) / 128 = n at w a' ⊢
      have hl' : len > Spec.BLAKE2B_BLOCKBYTES := hl
      refine ⟨S', ?_, ?_, b1.trans (compress_buf _ _), b2.trans (compress_buflen _ _),
        b3.trans (compress_outlen _ _)⟩
      · rw [Spec.blake2b_update_while, if_pos hl']
        show Spec.blake2b_update_while pin bound
          (Spec.blake2b_compress (Spec.blake2b_increment_counter S (128 : Nat).toUInt64)
            (pin.extract off (off + 128))) (off + 128) (len - 128) = _
        rw [w, show off + 128 + 128 * n = off + 128 * (n + 1) from by omega,
          show len - 128 - 128 * n = len - 128 * (n + 1) from by omega]
      · rw [updateBlocks_front, ← ofBytes_extract pin off (by omega)]
        exact a'
    · have e : (len - 1) / 128 = 0 := by omega
      have hl' : ¬ len > Spec.BLAKE2B_BLOCKBYTES := hl
      refine ⟨S, ?_, ?_, rfl, rfl, rfl⟩
      · rw [Spec.blake2b_update_while, if_neg hl', e, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
      · rw [e]
        exact a

/-! ## 3. blake2b_update -/

/-- What blake2b_final needs to know of a state: chaining value, counter, and what its buffer holds.
The buffer's first `S.buflen` bytes are the bytes of `pin` from `from_` on. -/
structure Holds (S : Spec.blake2b_state) (T : State)
    (pin : Array UInt8) (from_ len n : Nat) : Prop where
  at_ : At S T
  size : S.buf.size = 128
  buflen : S.buflen = len
  le : len ≤ 128
  outlen : S.outlen = n
  bytes : ∀ j, j < len → S.buf.getD j 0 = pin.getD (from_ + j) 0

theorem update_empty (S : Spec.blake2b_state) (pin : Array UInt8) (h : pin.size = 0) :
    Spec.blake2b_update S pin = S := by
  have h0 : ¬ pin.size > 0 := by omega
  unfold Spec.blake2b_update
  dsimp only
  rw [if_neg h0]

/-- At most as many bytes as the buffer has room for: they are copied into the buffer. -/
theorem update_small (S : Spec.blake2b_state) (pin : Array UInt8)
    (h0 : 0 < pin.size) (h : ¬ 128 - S.buflen < pin.size) :
    Spec.blake2b_update S pin =
      { S with
        buf := Spec.memcpy S.buf S.buflen pin 0 pin.size, buflen := S.buflen + pin.size } := by
  have h0' : pin.size > 0 := h0
  have h' : ¬ pin.size > Spec.BLAKE2B_BLOCKBYTES - S.buflen := h
  unfold Spec.blake2b_update
  dsimp only
  rw [if_pos h0', if_neg h']

/-- The state after blake2b_update has filled the buffer and compressed it. -/
def filled (S : Spec.blake2b_state) (pin : Array UInt8) : Spec.blake2b_state :=
  Spec.blake2b_compress
    (Spec.blake2b_increment_counter
      { S with buflen := 0, buf := Spec.memcpy S.buf S.buflen pin 0 (128 - S.buflen) }
      (128 : Nat).toUInt64)
    (Spec.memcpy S.buf S.buflen pin 0 (128 - S.buflen))

/-- The last two lines of blake2b_update: what is left goes into the buffer. -/
def rest (pin : Array UInt8) (w : Spec.blake2b_state × Nat × Nat) : Spec.blake2b_state :=
  { w.1 with buf := Spec.memcpy w.1.buf w.1.buflen pin w.2.1 w.2.2, buflen := w.1.buflen + w.2.2 }

/-- More bytes than the buffer has room for. -/
theorem update_big (S : Spec.blake2b_state) (pin : Array UInt8) (h : 128 - S.buflen < pin.size) :
    Spec.blake2b_update S pin =
      rest pin (Spec.blake2b_update_while pin (pin.size - (128 - S.buflen)) (filled S pin)
        (0 + (128 - S.buflen)) (pin.size - (128 - S.buflen))) := by
  have h0' : pin.size > 0 := by omega
  have h' : pin.size > Spec.BLAKE2B_BLOCKBYTES - S.buflen := h
  unfold Spec.blake2b_update
  dsimp only
  rw [if_pos h0', if_pos h']
  rfl

/-- The small case, from an empty buffer. -/
theorem holds_small {S : Spec.blake2b_state} {T : State} {outlen : Nat} (a : At S T)
    (hs : S.buf.size = 128) (hb : S.buflen = 0) (ho : S.outlen = outlen) (pin : Array UInt8)
    (h0 : 0 < pin.size) (h128 : pin.size ≤ 128) :
    Holds (Spec.blake2b_update S pin) T pin 0 pin.size outlen := by
  rw [update_small S pin h0 (by omega)]
  refine ⟨⟨a.h, a.t0, a.t1, a.f0, a.f1, a.g0, a.g1, a.node⟩, ?_, ?_, h128, ho, ?_⟩
  · show (Spec.memcpy S.buf S.buflen pin 0 pin.size).size = 128
    rw [size_memcpy S.buf S.buflen pin 0 pin.size (by omega) (by omega), hs]
  · show S.buflen + pin.size = pin.size
    omega
  · intro j hj
    show (Spec.memcpy S.buf S.buflen pin 0 pin.size).getD j 0 = _
    have := getD_memcpy_in S.buf S.buflen pin 0 pin.size j (by omega) (by omega) hj
    rw [hb, Nat.zero_add] at this
    rw [hb, Nat.zero_add]
    exact this

/-- The big case. m is the block that goes through the buffer. -/
theorem holds_big {S : Spec.blake2b_state} {T : State} {outlen : Nat} (a : At S T)
    (hs : S.buf.size = 128) (hb : S.buflen ≤ 128) (ho : S.outlen = outlen) (pin : Array UInt8)
    (hbig : 128 - S.buflen < pin.size) (m : MessageBlock)
    (hm : MessageBlock.ofBytes ⟨Spec.memcpy S.buf S.buflen pin 0 (128 - S.buflen)⟩ 0 = m) (off len : Nat)
    (hoff : off = 128 - S.buflen) (hlen : len = pin.size - off) :
    Holds (Spec.blake2b_update S pin)
      (updateBlocks (fun j => MessageBlock.ofBytes ⟨pin⟩ (off + 128 * j)) ((len - 1) / 128) 0
        (compress (incrementCounter T 128) m))
      pin (off + 128 * ((len - 1) / 128)) (len - 128 * ((len - 1) / 128)) outlen := by
  have a0 : At
      { S with buflen := 0, buf := Spec.memcpy S.buf S.buflen pin 0 (128 - S.buflen) } T :=
    ⟨a.h, a.t0, a.t1, a.f0, a.f1, a.g0, a.g1, a.node⟩
  have a1 : At (filled S pin) (compress (incrementCounter T 128) m) := by
    rw [← hm]
    exact at_step a0 _
  obtain ⟨S', w, a', b1, b2, b3⟩ := while_eq pin len (filled S pin) off len _ a1 (Nat.le_refl _)
    (by omega)
  have hbuf : S'.buf.size = 128 := by
    rw [b1]
    unfold filled
    rw [compress_buf]
    show (Spec.memcpy S.buf S.buflen pin 0 (128 - S.buflen)).size = 128
    rw [size_memcpy S.buf S.buflen pin 0 (128 - S.buflen) (by omega) (by omega), hs]
  have hbl : S'.buflen = 0 := by
    rw [b2]
    unfold filled
    rw [compress_buflen]
    rfl
  have hout : S'.outlen = outlen := by
    rw [b3]
    unfold filled
    rw [compress_outlen]
    exact ho
  rw [update_big S pin hbig, Nat.zero_add, ← hoff, ← hlen, w]
  refine ⟨⟨a'.h, a'.t0, a'.t1, a'.f0, a'.f1, a'.g0, a'.g1, a'.node⟩, ?_, ?_, by omega, hout, ?_⟩
  · show (Spec.memcpy S'.buf S'.buflen pin (off + 128 * ((len - 1) / 128))
      (len - 128 * ((len - 1) / 128))).size = 128
    rw [size_memcpy S'.buf S'.buflen pin (off + 128 * ((len - 1) / 128))
      (len - 128 * ((len - 1) / 128)) (by omega) (by omega), hbuf]
  · show S'.buflen + (len - 128 * ((len - 1) / 128)) = len - 128 * ((len - 1) / 128)
    omega
  · intro j hj
    show (Spec.memcpy S'.buf S'.buflen pin _ _).getD j 0 = _
    have := getD_memcpy_in S'.buf S'.buflen pin (off + 128 * ((len - 1) / 128))
      (len - 128 * ((len - 1) / 128)) j (by omega) (by omega) hj
    rw [hbl, Nat.zero_add] at this
    rw [hbl]
    exact this

/-! ## 4. blake2b_final -/

theorem set_lastblock_eq (S : Spec.blake2b_state) (h : S.last_node = 0) :
    Spec.blake2b_set_lastblock S = { S with f0 := 0xffffffffffffffff } := by
  have hc : ¬ (S.last_node != 0) = true := by
    rw [h]
    decide
  unfold Spec.blake2b_set_lastblock
  dsimp only
  rw [if_neg hc]

/-- The state after blake2b_final's call of blake2b_compress. -/
def closed (S : Spec.blake2b_state) : Spec.blake2b_state :=
  let S2 := Spec.blake2b_set_lastblock (Spec.blake2b_increment_counter S S.buflen.toUInt64)
  Spec.blake2b_compress { S2 with buf := Spec.memset S2.buf S2.buflen 0 (128 - S2.buflen) }
    (Spec.memset S2.buf S2.buflen 0 (128 - S2.buflen))

theorem final_unfold (S : Spec.blake2b_state) (outlen : Nat) (h1 : ¬ outlen < S.outlen)
    (h2 : Spec.blake2b_is_lastblock S = false) :
    Spec.blake2b_final S outlen =
      some (((List.range 8).foldl
        (fun (buffer : Array UInt8) i => Spec.store64 buffer (8 * i) (closed S).h[i]!)
        (Array.replicate 64 0)).extract 0 (closed S).outlen) := by
  have h2' : ¬ Spec.blake2b_is_lastblock S = true := by
    rw [h2]
    exact Bool.false_ne_true
  unfold Spec.blake2b_final
  dsimp only
  rw [if_neg h1, if_neg h2']
  rfl

/-- blake2b_final on a state whose buffer holds the end of pin. -/
theorem final_holds {S : Spec.blake2b_state} {T : State} {pin : Array UInt8}
    {from_ len outlen : Nat} (H : Holds S T pin from_ len outlen) (hend : pin.size ≤ from_ + len) :
    Spec.blake2b_final S outlen =
      some ((finalBlock T (MessageBlock.ofBytes ⟨pin⟩ from_) len).h.bytes64.data.extract 0 outlen) := by
  have hl : Spec.blake2b_is_lastblock S = false := by
    unfold Spec.blake2b_is_lastblock
    rw [H.at_.f0]
    rfl
  obtain ⟨c0, c1⟩ := increment_at S T S.buflen.toUInt64 H.at_.t0 H.at_.t1
  have hblk : MessageBlock.ofBytes ⟨Spec.memset S.buf S.buflen 0 (128 - S.buflen)⟩ 0 =
      MessageBlock.ofBytes ⟨pin⟩ from_ := by
    apply ofBytes_congr
    intro j hj
    rw [Nat.zero_add, H.buflen]
    by_cases hjl : j < len
    · rw [getD_memset_before S.buf len 0 (128 - len) j (by have := H.le; have := H.size; omega) hjl,
        H.bytes j hjl]
    · have e := getD_memset_in S.buf len 0 (128 - len) (j - len)
        (by have := H.le; have := H.size; omega) (by omega)
      rw [show len + (j - len) = j from by omega] at e
      rw [e, getD_of_ge (by omega)]
  have e1 : closed S = Spec.blake2b_compress
      { Spec.blake2b_increment_counter S S.buflen.toUInt64 with
        f0 := 0xffffffffffffffff, buf := Spec.memset S.buf S.buflen 0 (128 - S.buflen) }
      (Spec.memset S.buf S.buflen 0 (128 - S.buflen)) := by
    unfold closed
    rw [set_lastblock_eq (Spec.blake2b_increment_counter S S.buflen.toUInt64) H.at_.node]
    rfl
  have key := compress_h
    { Spec.blake2b_increment_counter S S.buflen.toUInt64 with
      f0 := 0xffffffffffffffff, buf := Spec.memset S.buf S.buflen 0 (128 - S.buflen) }
    (Spec.memset S.buf S.buflen 0 (128 - S.buflen))
    (setLastblock (incrementCounter T S.buflen.toUInt64)) H.at_.h c0 c1 rfl
    (H.at_.f1.trans H.at_.g1.symm)
  have hh : (closed S).h = (finalBlock T (MessageBlock.ofBytes ⟨pin⟩ from_) len).h.arr := by
    rw [e1, key, hblk, H.buflen]
    rfl
  have ho : (closed S).outlen = outlen := by
    rw [e1, compress_outlen]
    exact H.outlen
  rw [final_unfold S outlen (by rw [H.outlen]; exact Nat.lt_irrefl _) hl, hh, store_eq, ho]

/-! ## 5. The whole function -/

theorem at_first (keylen outlen : Nat) : At (firstSpec keylen outlen) (firstState keylen outlen) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Zeros after the end of an array do not change a block. -/
theorem ofBytes_pad (key : Array UInt8) (n : Nat) :
    MessageBlock.ofBytes ⟨key ++ Array.replicate n 0⟩ 0 = MessageBlock.ofBytes ⟨key⟩ 0 := by
  apply ofBytes_congr
  intro j _
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.getElem?_replicate]
  grind

/-- With a key: the key's block, filled up with zeros, goes first. -/
theorem spec_key (key data : Array UInt8) (outlen : Nat) (k0 : key.size > 0) (hk : key.size ≤ 64) :
    (Spec.blake2b_final (Spec.blake2b_update (Spec.blake2b_update (firstSpec key.size outlen)
      (key ++ Array.replicate (128 - key.size) 0)) data) outlen).getD #[] =
      (if data.size > 0 then
        message (fun j => MessageBlock.ofBytes ⟨data⟩ (128 * j)) data.size
          (updateBlocks (fun _ => MessageBlock.ofBytes ⟨key⟩ 0) 1 0 (firstState key.size outlen))
      else
        finalBlock (firstState key.size outlen) (MessageBlock.ofBytes ⟨key⟩ 0) 128).h.bytes64.data.extract
        0 outlen := by
  have hp : (key ++ Array.replicate (128 - key.size) 0).size = 128 := by
    rw [Array.size_append, Array.size_replicate]
    omega
  have K := holds_small (outlen := outlen) (at_first key.size outlen) (Array.size_replicate ..) rfl
    rfl (key ++ Array.replicate (128 - key.size) 0) (by omega) (by omega)
  rw [hp] at K
  generalize Spec.blake2b_update (firstSpec key.size outlen)
    (key ++ Array.replicate (128 - key.size) 0) = U at K ⊢
  by_cases d0 : data.size > 0
  · rw [if_pos d0]
    have hm : MessageBlock.ofBytes ⟨Spec.memcpy U.buf U.buflen data 0 (128 - U.buflen)⟩ 0 =
        MessageBlock.ofBytes ⟨key⟩ 0 := by
      rw [← ofBytes_pad key (128 - key.size)]
      apply ofBytes_congr
      intro j hj
      rw [K.buflen, Nat.zero_add,
        getD_memcpy_before U.buf 128 data 0 (128 - 128) j
          (by have := K.size; omega) (by omega) hj,
        K.bytes j hj, Nat.zero_add]
    have D := holds_big K.at_ K.size (by have := K.buflen; omega) K.outlen data
      (by have := K.buflen; omega) _ hm 0 data.size (by have := K.buflen; omega) (by omega)
    rw [final_holds D (by omega), message_eq, updateBlocks_one]
    simp only [Nat.zero_add, Option.getD_some]
  · rw [if_neg d0, update_empty _ data (by omega), final_holds K (by omega), ofBytes_pad,
      Option.getD_some]

/-- Without a key, a message of 1 to 128 bytes. -/
theorem spec_small (data : Array UInt8) (outlen : Nat) (d0 : 0 < data.size)
    (d128 : data.size ≤ 128) :
    (Spec.blake2b_final (Spec.blake2b_update (firstSpec 0 outlen) data) outlen).getD #[] =
      (message (fun j => MessageBlock.ofBytes ⟨data⟩ (128 * j)) data.size
        (firstState 0 outlen)).h.bytes64.data.extract 0 outlen := by
  have D := holds_small (outlen := outlen) (at_first 0 outlen) (Array.size_replicate ..) rfl rfl
    data d0 d128
  rw [message_eq, final_holds D (by omega), show (data.size - 1) / 128 = 0 from by omega]
  simp only [updateBlocks_zero, Option.getD_some, Nat.mul_zero, Nat.sub_zero]

/-- Without a key, a message of more than 128 bytes. -/
theorem spec_big (data : Array UInt8) (outlen : Nat) (d128 : ¬ data.size ≤ 128) :
    (Spec.blake2b_final (Spec.blake2b_update (firstSpec 0 outlen) data) outlen).getD #[] =
      (message (fun j => MessageBlock.ofBytes ⟨data⟩ (128 * j)) data.size
        (firstState 0 outlen)).h.bytes64.data.extract 0 outlen := by
  have hm : MessageBlock.ofBytes ⟨Spec.memcpy (firstSpec 0 outlen).buf (firstSpec 0 outlen).buflen data 0
               (128 - (firstSpec 0 outlen).buflen)⟩ 0 = MessageBlock.ofBytes ⟨data⟩ 0 := by
    apply ofBytes_congr
    intro j hj
    exact getD_memcpy_in (Array.replicate 128 0) 0 data 0 128 j
      (by rw [Array.size_replicate]; omega) (by omega) hj
  have D := holds_big (outlen := outlen) (at_first 0 outlen) (Array.size_replicate ..)
    (Nat.zero_le _) rfl data (by show 128 - 0 < data.size; omega) _ hm 128 (data.size - 128) rfl rfl
  rw [message_eq, final_holds D (by omega)]
  have e : (data.size - 1) / 128 = (data.size - 128 - 1) / 128 + 1 := by omega
  have f := updateBlocks_front data 0 ((data.size - 128 - 1) / 128) (firstState 0 outlen)
  simp only [Nat.zero_add] at f
  rw [e, f, Option.getD_some]
  rw [show data.size - 128 - 128 * ((data.size - 128 - 1) / 128) =
      data.size - 128 * ((data.size - 128 - 1) / 128 + 1) from by omega,
    show 128 + 128 * ((data.size - 128 - 1) / 128) =
      128 * ((data.size - 128 - 1) / 128 + 1) from by omega]

/-- Without a key, the empty message. -/
theorem spec_empty (data : Array UInt8) (outlen : Nat) (d0 : ¬ 0 < data.size) :
    (Spec.blake2b_final (Spec.blake2b_update (firstSpec 0 outlen) data) outlen).getD #[] =
      (message (fun j => MessageBlock.ofBytes ⟨data⟩ (128 * j)) data.size
        (firstState 0 outlen)).h.bytes64.data.extract 0 outlen := by
  have Z : Holds (firstSpec 0 outlen) (firstState 0 outlen) data 0 0 outlen :=
    ⟨at_first 0 outlen, Array.size_replicate .., rfl, Nat.zero_le _, rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rw [message_eq, update_empty _ data (by omega), final_holds Z (by omega),
    show data.size = 0 from by omega]
  simp only [Option.getD_some, Nat.zero_sub, Nat.zero_div, Nat.mul_zero, Nat.sub_zero,
    updateBlocks_zero]

/-- The plain definition's digest is the first outlen bytes of the chaining value of the fast
function's last state. -/
theorem spec_eq_state (key data : Array UInt8) (outlen : Nat) (h1 : 1 ≤ outlen) (h64 : outlen ≤ 64)
    (hk : key.size ≤ 64) :
    Spec.blake2b key data outlen = (state ⟨key⟩ ⟨data⟩ outlen).h.bytes64.data.extract 0 outlen := by
  have sk : (ByteArray.mk key).size = key.size := rfl
  have sd : (ByteArray.mk data).size = data.size := rfl
  have g1 : ¬ (outlen = 0 ∨ outlen > Spec.BLAKE2B_OUTBYTES) := by
    show ¬ (outlen = 0 ∨ outlen > 64)
    omega
  have g2 : ¬ key.size > Spec.BLAKE2B_KEYBYTES := by
    show ¬ key.size > 64
    omega
  unfold Spec.blake2b state
  dsimp only
  rw [if_neg g1, if_neg g2, sk, sd]
  by_cases k0 : key.size > 0
  · rw [if_pos k0, if_pos k0, init_key_eq outlen key h1 h64 k0 hk]
    exact spec_key key data outlen k0 hk
  · rw [if_neg k0, if_neg k0, init_eq outlen h1 h64, show key.size = 0 from by omega]
    by_cases d0 : 0 < data.size
    · by_cases d128 : data.size ≤ 128
      · exact spec_small data outlen d0 d128
      · exact spec_big data outlen d128
    · exact spec_empty data outlen d0

/-- The fast BLAKE2b computes the plain definition's BLAKE2b: for 1 ≤ outlen ≤ 64 and a key of at
most 64 bytes, the range in which the reference implementation returns a digest. -/
theorem blake2b_eq_spec (key data : ByteArray) (outlen : Nat) (h1 : 1 ≤ outlen)
    (h64 : outlen ≤ 64) (hk : key.size ≤ 64) :
    (blake2b key data outlen).data = Spec.blake2b key.data data.data outlen := by
  rw [blake2b_inside key data outlen h1 h64 hk, spec_eq_state key.data data.data outlen h1 h64 hk]
  unfold ChainingValue.bytes
  rw [ByteArray.data_extract]

/-- Outside that range both return no bytes. -/
theorem spec_outside (key data : Array UInt8) (outlen : Nat)
    (h : ¬ (1 ≤ outlen ∧ outlen ≤ 64 ∧ key.size ≤ 64)) :
    Spec.blake2b key data outlen = #[] := by
  unfold Spec.blake2b
  dsimp only
  by_cases g1 : outlen = 0 ∨ outlen > Spec.BLAKE2B_OUTBYTES
  · rw [if_pos g1]
  · have g2 : key.size > Spec.BLAKE2B_KEYBYTES := by
      have : ¬ (outlen = 0 ∨ outlen > 64) := g1
      show key.size > 64
      omega
    rw [if_neg g1, if_pos g2]

/-- For all arguments. -/
theorem blake2b_eq_spec_all (key data : ByteArray) (outlen : Nat) :
    (blake2b key data outlen).data = Spec.blake2b key.data data.data outlen := by
  by_cases h : 1 ≤ outlen ∧ outlen ≤ 64 ∧ key.size ≤ 64
  · exact blake2b_eq_spec key data outlen h.1 h.2.1 h.2.2
  · rw [blake2b_outside key data outlen h, spec_outside key.data data.data outlen h]
    rfl

end Run.Blake2b
