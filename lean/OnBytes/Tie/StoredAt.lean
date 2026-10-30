-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredAt.lean: a chain that opens stored tables, read at the hash that any function on
byte strings induces, and the compiled verifier of the library's theory under the same function.

OnBytes/Tie/StoredMain.lean leads from "the program's reader has read the chain and the decision
says yes" to "the compiled verifier accepts what was read", with the format's own hash, BLAKE2b, on
both sides. Its core, `stored_core`, holds for every function O on byte strings that has answers of
32 bytes and whose hash of the parameter bytes is the format's digest of them. This file states the
rest of that road for every such O. "The program" is the Lean port built from OnBytes/, not the C++
verifier.

Main definitions.
 `readInAt O`           the text of `readIn` (OnBytes/Chain/Session.lean) with the library's strict
                        reader at the hash `Fmt.HO O` in the place of the program's reader. The
                        program does not call it.
 `CompiledAcceptsXAt O`  the text of `CompiledAcceptsX` with O in the place of `Fmt.oracle`.
Main theorems.
 `compiledAcceptsX_iff`  `CompiledAcceptsX` is `CompiledAcceptsXAt Fmt.oracle`.
 `readInAt_oracle`       within `smallFX`, `readInAt Fmt.oracle` is `readIn`.
 `digestAt_oracle`       `Fmt.oracle` meets `DigestAt` for parameter bytes within the hash's domain
                        (`Fmt.hDom`: here, at most 2^32 - 144 bytes).
 `stored_compiled_at`, `readInAtX_compiled`   if the reader at O has read the chain and the decision
                        says yes on its view, the compiled verifier under the typed oracle functions
                        that O induces accepts what was read.

The hypotheses are those of `stored_compiled` without `smallFX`, and two on O: its answers have 32
bytes, and `DigestAt O S`: the hash that O induces gives, on the parameter bytes, the format's own
digest of them.

What is not claimed. Nothing on soundness, and no probability. `DigestAt O S` fixes O at one string.
A function drawn uniformly among those with answers of 32 bytes meets it with chance 2^-256: for
such a function the two main theorems say nothing as they stand. That the reader at O reads any
file, for any O other than `Fmt.oracle`, is not proved; a test shows one file of a made-up example
read at one other function (a test that is not in this library). The typed oracle functions that a
random O induces are not shown to be random typed oracles: they answer every typed query without a
call with zeros, and the map from typed queries to strings is not shown to be one to one
(Run/CodingFn.lean). A constant `stm` meets the hypothesis on the statement, and then the typed
first query does not read the roots; the root of a table that the chain does not open is free (head
of OnBytes/Tie/StoredMain.lean). How many strings the reader at O asks O for is not said here
(OnBytes/Tie/CostX.lean, AskX.lean). No property of BLAKE2b is used or claimed. Nothing on the C++
verifier or on machine code. What the head of OnBytes/Tie/StoredMain.lean does not claim is not
claimed here.

-/
import OnBytes.Tie.StoredMain

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- The hash that O induces gives, on the parameter bytes of S, the format's own digest of these
bytes. It is a condition on O at one string. -/
def DigestAt (O : ByteArray → ByteArray) (S : Fmt.SpecX) : Prop :=
  Fmt.HO O 169 0 1 Fmt.zero32 S.base.params = Fmt.paramsDigest S.base.params

/-- The format's own oracle meets `DigestAt`, for parameter bytes within the hash's domain. -/
theorem digestAt_oracle (S : Fmt.SpecX)
    (hd : Fmt.hDom 169 0 1 Fmt.zero32 S.base.params = true) : DigestAt Fmt.oracle S :=
  Fmt.HO_oracle 169 0 1 Fmt.zero32 S.base.params hd

/-- Reads the chain with the description S that begins at byte i of b, at the hash that O induces.
No decision is taken. The program does not call this function: it is `readIn` with the library's
strict reader at `Fmt.HO O` in the place of the program's reader. -/
def readInAt (O : ByteArray → ByteArray) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    InSession ChainRead := fun s =>
  match Fmt.readChainX (m := Id) (Fmt.HO O) S s.seen b i with
  | none => none
  | some (o, j) => some (⟨o, viewOf S o, j⟩, ⟨o.seen⟩)

/-- What `readInAt O` returns is what the strict reader reads at the hash that O induces, and its
view. -/
theorem readInAt_read (O : ByteArray → ByteArray) (S : Fmt.SpecX) (b : ByteArray) (i : Nat)
    (s s' : Session) (r : ChainRead) (e : readInAt O S b i s = some (r, s')) :
    Fmt.readChainX (m := Id) (Fmt.HO O) S s.seen b i = some (r.out, r.next) ∧
      r.view = Fmt.viewX S r.out := by
  unfold readInAt at e
  cases hx : Fmt.readChainX (m := Id) (Fmt.HO O) S s.seen b i with
  | none =>
    rw [hx] at e
    cases e
  | some x =>
    rw [hx] at e
    cases e
    exact ⟨rfl, viewOf_eq S x.1⟩

/-- Within `smallFX` the reader at `Fmt.oracle` is the program's reader. -/
theorem readInAt_oracle (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s : Session)
    (hsm : smallFX S b = true) : readInAt Fmt.oracle S b i s = readIn S b i s := by
  unfold readInAt readIn
  rw [readChainX_HO S s.seen b i hsm, readChain_eq]
  cases Fmt.readChainX (m := Id) Fmt.formatHash S s.seen b i with
  | none => rfl
  | some x => rfl

/-- "The compiled verifier accepts what was read", under the typed oracle functions that O induces.
It is `CompiledAcceptsX` with O in the place of `Fmt.oracle`. -/
def CompiledAcceptsXAt (O : ByteArray → ByteArray) (S : Fmt.SpecX)
    (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (r0 r1 : ByteArray)
    (o : Fmt.ChainOut) : Prop :=
  ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec).up,
    toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
      (xdOf S stm).xs dec o = some π ∧
    (verifyOneProtocol (lam := 256) (K := (xdOf S stm).K + 1) (L := (xdOf S stm).L dec)
      (256 + 8 * S.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec).up
      (wqX (xdOf S stm).C (xdOf S stm).K (chalP S.base.plan.field (xdOf S stm).K) (xdOf S stm).ds
        (xdOf S stm).a (xdOf S stm).xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPX (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec
        (fun _ _ p => (p.val, [])) (fun _ => some ()))
      (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
      (famX (xdOf S stm) dec O ((xdOf S stm).K + 1)) = true

/-- `CompiledAcceptsX` is the case `Fmt.oracle`. -/
theorem compiledAcceptsX_iff (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (r0 r1 : ByteArray) (o : Fmt.ChainOut) :
    CompiledAcceptsX S stm dec r0 r1 o ↔ CompiledAcceptsXAt Fmt.oracle S stm dec r0 r1 o :=
  Iff.rfl

/-- A chain that opens stored tables, read by the strict reader at the hash that O induces, at any
byte and under any record of vertices, and on which the decision is yes. Then the compiled verifier
under the typed oracle functions that O induces accepts what was read. The hypotheses: O's answers
have 32 bytes; `DigestAt O S`; r0 and r1 have 32 bytes; the description is within the limits
(`withinX`); its statement is `stm r0 r1`; the statement's item of every table that is opened holds
that table's root, r0 for item 0 and r1 for item 1. Nothing on soundness. For a function O that does
not meet `DigestAt O S` nothing is said. -/
theorem stored_compiled_at (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32) (hw : withinX S = true)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : DigestAt O S) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O) S seen b i = some (o, j))
    (hdec : dec (Fmt.viewX S o) = true) : CompiledAcceptsXAt O S stm dec r0 r1 o := by
  unfold withinX at hw
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
  obtain ⟨⟨hok, hn⟩, honce⟩ := hw
  obtain ⟨π, t1, t2⟩ := stored_core S stm dec O hO r0 r1 h0 h1 hok hn honce hst hroot hpd seen b i
    o j e hdec
  exact ⟨π, t1, (thin_verify Unit Unit 256 _ ((xdOf S stm).L dec)
    (famX (xdOf S stm) dec O ((xdOf S stm).K + 1)) Unit _ _ 256 .link _ _ _ _
    (fun _ => none) (fun s => some (.inl s)) 0 _ () π).symm.trans t2⟩

/-- The same for a chain that `readInAt O` has read in a session, and on whose view a decision says
yes. -/
theorem readInAtX_compiled (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32) (hw : withinX S = true)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : DigestAt O S) (s : Session) (b : ByteArray) (i : ℕ) (r : ChainRead) (s' : Session)
    (e : readInAt O S b i s = some (r, s')) (hdec : dec r.view = true) :
    CompiledAcceptsXAt O S stm dec r0 r1 r.out := by
  obtain ⟨t1, t2⟩ := readInAt_read O S b i s s' r e
  rw [t2] at hdec
  exact stored_compiled_at O hO S stm dec r0 r1 h0 h1 hw hst hroot hpd s.seen b i r.out r.next t1
    hdec

end OnBytes.Tie
