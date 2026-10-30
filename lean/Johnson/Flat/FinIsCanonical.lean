-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/FinIsCanonical.lean: WHAT THE LAST TEST's YES SAYS OF THE TOKEN: where the first chain's last test
(`S.finAsked`, Johnson/Desc/First/State.lean) says yes at the asked reply AS THE PROGRAM READS IT OFF THE REPLY FILE's
BYTES, what was heard (`S.heard`, Johnson/Desc/First/StateHeard.lean) is the typed instance's reply token as an element of
the extension field (`replyOf`, Johnson/Flat/LinksAt.lean); and that element names one token.

Why. The proof file's hypothesis on soundness wants of a description "the last test compares what was heard with what is
asked" (`FileDescription.Hears.fins`, Johnson/Desc/Sound/FoldHeard.lean), with "what is asked" read off the TYPED instance
(`replyOf`, Johnson/Flat/LinksAt.lean). The description's instance holds BYTES: its asked reply is
"the first 32-bit word of the reply file, as a number, as an element". Between the two lie: bytes to words; a word to a number; a
number to an element.

Main names.
  `askedReplyOf y`: the asked reply as the program reads it: the text of the description's harness's `Inst.asked`, to the letter.
  `asked_of_replyBytes`: at the reply file that says a typed instance it is `replyOf` of that instance. ONE PREMISE: the
    vocabulary has at most 2^32 tokens (a cast's bound: a token is written as one 32-bit word).
  `fin_is_canonical`: THE ROW: the last test's yes there gives: what was heard is `some (replyOf x)`. IT SPEAKS OF BYTES MADE OF THE TYPED INSTANCE
    (`replyBytesOf x`), not of the file that a program reads: the right subject for its caller (`Hears.fins` at typed requests); two ties to the harness are
    named under Limits.
  `fins_of_bytes`: the same along any map from instances to bytes that is the reply file's at a typed instance: the form in
    which `Hears.fins` asks it.
  `askedReplyOf_c0`, `askedReplyOf_eq_iff`: THE ASKED SIDE, OF THE FILE's FIRST WORD, NO PREMISE: the asked element's first word is the file's first
    32-bit word (0 where there is none); two files have one asked element just where they have one first word. SO THE EMPTY FILE, A FILE OF ONE TO THREE
    BYTES AND EVERY FILE THAT BEGINS WITH THE WORD 0 ALL ASK THE TOKEN 0 (`askedReplyOf_empty`: a control): only the harness's test on the instance
    (okInst) fences that, and no theorem here speaks of it. (A fence "the file has one word" would not cure it: five to seven bytes give one word too, and a word that is no token stays: two readers.) `ofNat_wraps`: a control: on NUMBERS the map
    wraps at the prime (n and n + p give one element): the bound is had here by type.
  `c0_ofNat`, `replyOf_inj`: under the same premise two instances with one `replyOf` have one reply token: so "heard = asked"
    pins the token, not a residue class of tokens.

NO PREMISE OF CANONICITY, AND WHY NONE IS NEEDED. The last test compares RAW WORDS (the type E derives its decidable equality: three
words each): a heard element whose words are not below the prime is not equal to `ofNat n`, whose words are: the test refuses it. That
every word of a view is below the prime is asked by the three runs (`viewWordsBelowPrime`), not by the last test, and is not spent here.

THE TWO SILLY MEMBERS. A last test that says yes to all: the law is false of it (at a record that heard nothing). One that says no to
all: the law holds for nothing. The law is of `S.finAsked`'s own text.
Every "there is", walked: none.

Limits. Over State.lean (the proof beneath, `S.heard_of_finAsked`, is typed so that it also stands at a further conjunct).
`askedReplyOf` IS A SECOND WRITING of `ProofFile.Inst.asked` (Johnson/Desc/ProofFile/Pub.lean:149, with y for x.y), one line of the harness. The tie between the two
stands at the full size's instances: `asked_instOf` (Johnson/LLT25R/BackAtPure.lean:57, by rfl). NO THEOREM STATES IT AT EVERY INSTANCE OF THE HARNESS. THE MAP
from the top's typed requests to the harness's instances is `LPFD.Full.instanceAsPlainRecord` (Johnson/Desc/Laid/ProofFull.lean:51), with `instPartsOf`
(Johnson/Top/Fire/Code/Vals/FastFull.lean:429): it lays y := `replyBytesOf x.val`, so hy in `fins_of_bytes` is paid by rfl. `Hears.fins` takes no fence: so the road is the
description pulled back along that map, not the harness's own instances. THE REQUEST's SECOND ARM (a request that covers more positions
than the last: the reply is then asked to be 0) is not here: it wants the third conjunct that another version of `S.finAsked` has. The small size's requests:
general in P: nothing is special to a size. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.StateHeard
import Johnson.Flat.EarlyApart
import Johnson.Flat.LinksAt
import OnBytes.K.ReplyToken

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open Inst.Model OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.Desc.First (S)

/-- The asked reply, as the program reads it off the reply file's bytes. -/
def askedReplyOf (y : ByteArray) : E := ofNat ((words32 y).getD 0 0).toNat

/-- **At the reply file that says a typed instance, the asked reply is the instance's reply token as an
element.** -/
theorem asked_of_replyBytes {P : Params} (x : Instance' P) (hV : P.V ≤ 2 ^ 32) :
    askedReplyOf (replyBytesOf x) = replyOf x := by
  unfold askedReplyOf replyBytesOf
  rw [words32_bytesOfWords]
  have e : (replyWordsOf x).getD 0 0 = UInt32.ofNat x.y.val := rfl
  rw [e, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (lt_of_lt_of_le x.y.isLt hV)]
  rfl

/-- **The row.** Where the last test says yes at the asked reply as the program reads it, what was heard
is the instance's reply token as an element. -/
theorem fin_is_canonical {P : Params} (x : Instance' P) (hV : P.V ≤ 2 ^ 32) (s : S)
    (h : s.finAsked (askedReplyOf (replyBytesOf x)) = true) : s.heard = some (replyOf x) := by
  rw [asked_of_replyBytes x hV] at h
  exact S.heard_of_finAsked _ s h

/-- The same along a map from instances to bytes, AT ONE b whose bytes are the reply file's of a typed instance. (At
B := the harness's own instances, whose reply file is any bytes, hy fails at some b: the empty file: `replyBytesOf` always
gives four bytes. It is meant at typed instances, where it is paid by rfl.) -/
theorem fins_of_bytes {P : Params} {B : Type} (yOf : B → ByteArray) (val : B → Instance' P) (b : B)
    (hy : yOf b = replyBytesOf (val b)) (hV : P.V ≤ 2 ^ 32) (s : S)
    (h : s.finAsked (askedReplyOf (yOf b)) = true) : s.heard = some (replyOf (val b)) := by
  rw [hy] at h
  exact fin_is_canonical (val b) hV s h

/-- The first word of a number below the prime, as an element, is that number. -/
theorem c0_ofNat {y : ℕ} (hy : y < pW.toNat) : (ofNat y).c0.toNat = y :=
  OnBytes.K.token_of_reply (plain := #[ofNat y]) (got := ofNat y) rfl (beq_self_eq_true _) hy

/-- **THE ASKED SIDE IS CANONICAL IN THE FILE's FIRST WORD**: the asked element's first word IS the file's first
32-bit word, as a number: no premise: a 32-bit word is below the prime. -/
theorem askedReplyOf_c0 (y : ByteArray) :
    (askedReplyOf y).c0.toNat = ((words32 y).getD 0 0).toNat :=
  c0_ofNat (lt_trans ((words32 y).getD 0 0).toNat_lt (by decide))

/-- Two reply files have one asked element just where they have one first word. -/
theorem askedReplyOf_eq_iff (y y' : ByteArray) :
    askedReplyOf y = askedReplyOf y' ↔ (words32 y).getD 0 0 = (words32 y').getD 0 0 := by
  constructor
  · intro h
    have e := congrArg (fun t : E => t.c0.toNat) h
    simp only [askedReplyOf_c0] at e
    exact UInt32.toNat_inj.1 e
  · intro h
    unfold askedReplyOf
    rw [h]

/-- A CONTROL: the first word alone is read: the empty file asks the token 0. -/
theorem askedReplyOf_empty : askedReplyOf ByteArray.empty = ofNat 0 := by decide +kernel

/-- A CONTROL: WHY THE BYTES MATTER: on numbers the map into the field wraps: n and n + p give one element.
So a last test that is handed "the asked NUMBER as an element" is canonical on the asked side only under a
bound on that number; read off one 32-bit word the bound holds by type. -/
theorem ofNat_wraps (n : ℕ) : ofNat (n + pW.toNat) = ofNat n := by
  unfold ofNat fOfNat
  rw [Nat.add_mod_right]

/-- **The element names one token.** -/
theorem replyOf_inj {P : Params} (hV : P.V ≤ 2 ^ 32) (x x' : Instance' P)
    (h : replyOf x = replyOf x') : x.y = x'.y := by
  have hp : (2 : ℕ) ^ 32 < pW.toNat := by decide
  have b : ∀ z : Instance' P, z.y.val < pW.toNat := fun z =>
    lt_trans (lt_of_lt_of_le z.y.isLt hV) hp
  have e : (ofNat x.y.val).c0.toNat = (ofNat x'.y.val).c0.toNat :=
    congrArg (fun t : E => t.c0.toNat) h
  rw [c0_ofNat (b x), c0_ofNat (b x')] at e
  exact Fin.ext e

end OnBytes.Flat

#print axioms OnBytes.Flat.asked_of_replyBytes
#print axioms OnBytes.Flat.fin_is_canonical
#print axioms OnBytes.Flat.fins_of_bytes
#print axioms OnBytes.Flat.replyOf_inj
#print axioms OnBytes.Flat.askedReplyOf_c0
#print axioms OnBytes.Flat.askedReplyOf_eq_iff
#print axioms OnBytes.Flat.ofNat_wraps
#print axioms OnBytes.Flat.askedReplyOf_empty
