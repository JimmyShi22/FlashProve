-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/FrontSetPub.lean: the set of ALL requests' early parts (`FrontSet`,
Johnson/Top/FrontSet.lean) at the very spelling that the makers' page lays for a proof file's first
chain: the pair "the item `request`, the request file's bytes" of an instance that holds the public
input (`HoldsPub.req2`, Johnson/Maker/Page/ReqBoth.lean); and what the page's laws ask of that
spelling, proved at it from what is asked below.

THE LETTERS MEET; THIS IS NO TIE.

AT WHICH FORMAT. The page lays TWO strings of a request in the first chain's statement only in the
format in which that statement also holds the request file's words. In the format before it the
statement holds the item alone, and this file speaks of no program of that format.

Why. The laws on a proof file's silent rounds (`silentProof_laws`,
OnBytes/Maker/Page/FitSilent.lean) ask that the page's two strings are one to one on the typed
instances that pass a test. Johnson/Flat/FrontSetOwnAt.lean has a set with every instance at the
spelling "(a letter, the request file's bytes of enc x)". The makers' tops lay another term for the
same letter: `H.req2 x` := (the item of the public input of x, that input's request file). A
`FrontSet` is indexed by its spelling, so the one does not serve the other without an equation of
functions. Here the set is made at `H.req2` itself, from one premise more, `hpub`: the request file
of the public input of x is the request file that says enc x. No cast.

  `FrontSet.ownPub H hpub`   the set, at sp := `H.req2`.
  `FrontSet.has_ownPub`      it has every instance.
  `hreq_ownPub`              the page's two strings are one to one on what passes its test: the
                             premise `hreq` of `silentProof_laws`, in that theorem's own words.
  `silentLaws_ownPub`        so: the laws on a proof file's silent rounds, at that spelling and
                             test, at every function h and all chains c.
  `holdsWords`, `hpub_holdsWords`   at three fixed public files the record that holds, for x, the
                             request file that says enc x: `hpub` by definition.

`silentLaws_ownPub` goes by `silentProof_laws`, whose premise speaks of the pair, and not by
`silentProof_laws_words`, whose premise speaks of the second strings alone: `FrontSet.hreq` is
stated of the pair, and no law of that record is stated of the second halves at the typed instances.

What is asked, by name: hT, hV', hV (the window below 2 ^ 32; the vocabulary at most 2 ^ 32 and not
empty); henc (enc is one to one); he (the interface's early part is "the reply laid 0"); isR, one,
self (a test that lets the fixed record alone through); hpub; and H, a record with one law
(`early_same`: the early part holds the same parameter file, scale file and request file;
`HoldsPub`, Johnson/Maker/Page/ReqPub.lean). The type of L has not been searched for laws. None
speaks of a hash function. The one-to-one law beneath is `early_of_requestBytes`
(Johnson/Flat/EarlyApart.lean).

Not claimed. The premises at any interface. That the second string of any program's statement is the
request file of the call's instance. The two bounds on the strings' sizes. That the item, the first
string, says anything: nothing is asked of it. A FIXED HASH STANDS IN THAT STRING: `H.reqX x` is the
program's item of x's files (`itemPub`, Johnson/Maker/Page/ReqPub.lean; `Proof.requestItem`), which
holds values of the programs' second hash function, a fixed public function; no law on any hash is
asked or shown. Nothing on soundness.


-/
import Johnson.Flat.FrontSetOwnAt
import Johnson.Maker.Page.ReqBoth
import OnBytes.Maker.Page.FitSilent

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open Iop Inst.Model OnBytes.Flat
open _root_.Run (HId)
open OnBytes.Maker OnBytes.Maker.Page
open Johnson.Session (HoldsPub holdsBytes)

variable {I X : Type} {L : HolographicProtocol I X} {r₀ : L.Rec} {P : Params} (hT : P.T < 2 ^ 32)
  (hV' : P.V ≤ 2 ^ 32) (hV : 0 < P.V) (enc : X → Instance' P) (henc : Function.Injective enc)
  (he : ∀ x, enc (L.early x) = withoutReply hV (enc x))
  (isR : L.Rec → Bool) (one : ∀ r, isR r = true → r = r₀) (self : isR r₀ = true)
  (H : HoldsPub X L.early) (hpub : ∀ x, (H.pub x).request = requestBytesOf (enc x))

/-- **The set of ALL early parts, at the makers' own spelling.** -/
def FrontSet.ownPub : FrontSet L H.req2 r₀ :=
  FrontSet.ownRaw hT hV' hV enc henc he (fun _ => true) isR one self
    fun x y _ _ _ _ e => (hpub x).symm.trans ((congrArg Prod.snd e).trans (hpub y))

/-- **It has every instance.** The set is formed from the premises that the head lists. -/
theorem FrontSet.has_ownPub (i : X) :
    (FrontSet.ownPub hT hV' hV enc henc he isR one self H hpub).Has i :=
  FrontSet.has_ownRaw hT hV' hV enc henc he (fun _ => true) isR one self _ i rfl

/-- **The page's two strings are one to one on what passes the set's test.** The set is formed from
the premises that the head lists. -/
theorem hreq_ownPub (z z' : L.XC)
    (a : (FrontSet.ownPub hT hV' hV enc henc he isR one self H hpub).okX z = true)
    (b : (FrontSet.ownPub hT hV' hV enc henc he isR one self H hpub).okX z' = true)
    (e : reqOf (L := L) H.req2 z = reqOf (L := L) H.req2 z') : z = z' :=
  (FrontSet.ownPub hT hV' hV enc henc he isR one self H hpub).hreq z z' a b e

/-- **The laws on a proof file's silent rounds, at the makers' own spelling and the set's test.**
The set is formed from the premises that the head lists. -/
theorem silentLaws_ownPub (h : HId) (c : OnBytes.Params.ProofChains)
    (tl : Dig 256 → List E → List (Dig 256)) :
    SilentLaws (silentProof h c (reqOf (L := L) H.req2))
      (fFrontP tl (reqOf (L := L) H.req2)
        (FrontSet.ownPub hT hV' hV enc henc he isR one self H hpub).okX) (fJoin tl) fSeam :=
  silentProof_laws h c (reqOf (L := L) H.req2) _
    (hreq_ownPub hT hV' hV enc henc he isR one self H hpub) tl

/-! ## The record at three fixed public files -/

include he in
/-- The early part of an instance has the instance's request file. Under hV, he. -/
theorem requestBytes_early (x : X) :
    requestBytesOf (enc (L.early x)) = requestBytesOf (enc x) := by
  rw [he]
  exact requestBytesOf_withoutReply hV (enc x)

/-- At three fixed public files: x holds the request file and the reply file that say enc x. -/
def holdsWords (pol lay KL : ByteArray) : HoldsPub X L.early :=
  holdsBytes pol lay KL (fun x => requestBytesOf (enc x)) (fun x => replyBytesOf (enc x))
    (requestBytes_early hV enc he)

/-- `hpub` there, by definition. -/
theorem hpub_holdsWords (pol lay KL : ByteArray) (x : X) :
    ((holdsWords hV enc he pol lay KL).pub x).request = requestBytesOf (enc x) := rfl

end OnBytes.K.Arm.ProofFront

#print axioms OnBytes.K.Arm.ProofFront.FrontSet.has_ownPub
#print axioms OnBytes.K.Arm.ProofFront.hreq_ownPub
#print axioms OnBytes.K.Arm.ProofFront.silentLaws_ownPub
#print axioms OnBytes.K.Arm.ProofFront.hpub_holdsWords
