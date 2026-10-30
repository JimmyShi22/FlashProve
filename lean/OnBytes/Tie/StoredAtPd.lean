-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredAtPd.lean: what the strict reader has read at the hash of any function O, and the
decision accepts, the compiled verifier accepts under the typed oracle functions that O induces;
with the digest of the parameter bytes as an argument.

OnBytes/Tie/StoredAt.lean has that for a function O whose hash gives the format's own digest on the
parameter bytes (`DigestAt`). Here pd is any byte string, O's hash gives pd on these bytes
(`DigestAtPd`), and the typed oracle functions are `famXPd` at pd (OnBytes/Tie/FamPd.lean). Every O
meets `DigestAtPd` at its own value (`digestAtPd_self`): so nothing is asked of O but answers of 32
bytes. pd is then no second freedom: it is O's answer at one string. The typed oracle functions
`famXPd … pd O` then depend on O twice: through its answers, and through pd in the string of the
first query.

Main definitions: `DigestAtPd`, `CompiledAcceptsXAtPd`.
Main theorems: `stored_compiled_atPd`, `readInAtX_compiledPd`; `digestAt_iff_pd`,
`compiledAcceptsXAt_iff_pd`: StoredAt's two definitions are the case of the format's own digest.

What is not claimed. What the head of OnBytes/Tie/StoredAt.lean does not claim, but for its two
sentences on `DigestAt`. Nothing on soundness; no probability.

-/
import OnBytes.Tie.StoredAt
import OnBytes.Tie.StoredPd

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- The hash that O induces gives pd on the parameter bytes of S. A condition on O at one string. -/
def DigestAtPd (O : ByteArray → ByteArray) (S : Fmt.SpecX) (pd : ByteArray) : Prop :=
  Fmt.HO O 169 0 1 Fmt.zero32 S.base.params = pd

/-- `DigestAt` is the case of the format's own digest. -/
theorem digestAt_iff_pd (O : ByteArray → ByteArray) (S : Fmt.SpecX) :
    DigestAt O S ↔ DigestAtPd O S (Fmt.paramsDigest S.base.params) := Iff.rfl

/-- Every O meets it at its own value. -/
theorem digestAtPd_self (O : ByteArray → ByteArray) (S : Fmt.SpecX) :
    DigestAtPd O S (Fmt.HO O 169 0 1 Fmt.zero32 S.base.params) := rfl

/-- "The compiled verifier accepts what was read", under the typed oracle functions that O induces.
It is `CompiledAcceptsXAt` with pd in the place of the format's digest of the parameter bytes. -/
def CompiledAcceptsXAtPd (pd : ByteArray) (O : ByteArray → ByteArray) (S : Fmt.SpecX)
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
      (famXPd (xdOf S stm) dec pd O ((xdOf S stm).K + 1)) = true

/-- `CompiledAcceptsXAt` is the case of the format's own digest. -/
theorem compiledAcceptsXAt_iff_pd (O : ByteArray → ByteArray) (S : Fmt.SpecX)
    (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (r0 r1 : ByteArray)
    (o : Fmt.ChainOut) :
    CompiledAcceptsXAt O S stm dec r0 r1 o ↔
      CompiledAcceptsXAtPd (Fmt.paramsDigest S.base.params) O S stm dec r0 r1 o := by
  unfold CompiledAcceptsXAt CompiledAcceptsXAtPd
  rw [famX_eq_pd]
  rfl

/-- A chain that opens stored tables, read by the strict reader at the hash that O induces, at any
byte and under any record of vertices, and on which the decision is yes. Then the compiled verifier
under the typed oracle functions that O induces accepts what was read. The hypotheses: O's answers
have 32 bytes; `DigestAtPd O S pd`; r0 and r1 have 32 bytes; the description is within the limits
(`withinX`); its statement is `stm r0 r1`; the statement's item of every table that is opened holds
that table's root, r0 for item 0 and r1 for item 1. Nothing on soundness. For a function O that does
not meet `DigestAtPd O S pd` nothing is said. -/
theorem stored_compiled_atPd (pd : ByteArray) (O : ByteArray → ByteArray) (hO : ∀ s,
    (O s).size = 32)
    (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32) (hw : withinX S = true)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : DigestAtPd O S pd) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O) S seen b i = some (o, j))
    (hdec : dec (Fmt.viewX S o) = true) : CompiledAcceptsXAtPd pd O S stm dec r0 r1 o := by
  unfold withinX at hw
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
  obtain ⟨⟨hok, hn⟩, honce⟩ := hw
  obtain ⟨π, t1, t2⟩ := stored_corePd S stm dec pd O hO r0 r1 h0 h1 hok hn honce hst hroot hpd seen
      b i
    o j e hdec
  exact ⟨π, t1, (thin_verify Unit Unit 256 _ ((xdOf S stm).L dec)
    (famXPd (xdOf S stm) dec pd O ((xdOf S stm).K + 1)) Unit _ _ 256 .link _ _ _ _
    (fun _ => none) (fun s => some (.inl s)) 0 _ () π).symm.trans t2⟩

/-- The same for a chain that `readInAt O` has read in a session, and on whose view a decision says
yes. -/
theorem readInAtX_compiledPd (pd : ByteArray) (O : ByteArray → ByteArray) (hO : ∀ s,
    (O s).size = 32)
    (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32) (hw : withinX S = true)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : DigestAtPd O S pd) (s : Session) (b : ByteArray) (i : ℕ) (r : ChainRead) (s' : Session)
    (e : readInAt O S b i s = some (r, s')) (hdec : dec r.view = true) :
    CompiledAcceptsXAtPd pd O S stm dec r0 r1 r.out := by
  obtain ⟨t1, t2⟩ := readInAt_read O S b i s s' r e
  rw [t2] at hdec
  exact stored_compiled_atPd pd O hO S stm dec r0 r1 h0 h1 hw hst hroot hpd s.seen b i r.out r.next
      t1
    hdec

end OnBytes.Tie
