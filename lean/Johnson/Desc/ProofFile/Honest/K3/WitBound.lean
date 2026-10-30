-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitBound.lean: the reader of the input at the lookups, with another
term at the head's lookup, in which what is made of the instance is bound once in front of the two
functions on keys and bits; and the theorems that it is the same reader. Definitions with code, and
theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md. In this file: the reader of the input at a site is the field `wit` of
`Fill` (Honest/K3/LotRow.lean): of the chain's input and the challenges heard, the keys and bits
that the lookup's row is given. The head's public data is a value of `OnBytes.Ends.H.PubH`.

Why. In `ownSources` (Honest/K3/WitOwner.lean) the head's public data `pubH x` stands inside
`fun theta n =>` and `fun u j =>`. At `tiedOwnSources` it is `headPub X (req x).1 (req x).2`, and at
a proof file's instance `req` is `reqAt Z` (Honest/K3/WitReq.lean), which reads the request. A
program that evaluates the term as it stands can make all this anew for every key and every bit.

What is defined.
  `ownSourcesBound`: the text of `ownSources` with `let P := pubH x` and the cells' reader in front
    of the head's two functions. The other five fields are `ownSources`' own.
  `sourcesAtBound`: `sourcesAt` (Honest/K3/LotFilled.lean) over it, with `let q := req x` in front
    of `headPub`: one reading of the instance for both of its halves.
  `boundWit`: the reader at a site: `fastAsk` where the site names the round that samples the matrix
    (as `fastWit`, Honest/K3/LotInstFast.lean), the filling's reader over `sourcesAtBound`
    elsewhere.

What is shown.
  `ownSourcesBound_eq`, `sourcesAtBound_eq`: they are `ownSources` and `sourcesAt`: by `rfl`.
  `boundWit_fast`: `boundWit` is `fastWit`; `boundWit_eq`: so it is the filling's own reader, at
    every site.

Imported. Honest/K3/LotInstFast.lean and what stands beneath it.

Users. Honest/K3/LotInstKeepBound.lean, Honest/K3/Tab/TabALaw.lean, Honest/K3/Tab/TabGLaw.lean and
Honest/K3/Tab/TabHLaw.lean import this file. Meant for the lot of rows that pass their tables on
(Honest/K3/LotKeep.lean): its letter `wit`.

Limits. The equations say that the terms are equal, not how long either takes: that the public data
is made once at an application of the reader is a matter of how a program evaluates the term. It is
still made anew at every application of the reader to the challenges heard. On the layers' and
attention's calls nothing is exchanged.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotInstFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {W₀ Rc Xi Tr : Type}

/-- `ownSources` with the head's public data and the cells' reader bound in front of the head's two
functions. -/
def ownSourcesBound (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr :=
  { ownSources X cells weights pubH with
    head := fun x C W =>
      let P := pubH x
      let cell := ownH X C.cell W.entry (linkH X)
      ⟨fun theta n => OnBytes.Ends.H.keyH P cell theta n,
       fun u j => OnBytes.Ends.H.bitsH P.h P.L.fs cell (u * 32 + j)⟩ }

/-- It is `ownSources`. -/
theorem ownSourcesBound_eq (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) :
    ownSourcesBound X cells weights pubH = ownSources X cells weights pubH := rfl

/-- `sourcesAt` over `ownSourcesBound`. -/
def sourcesAtBound (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) : Sources W₀ Xi Tr :=
  ownSourcesBound Z.p.X cells weights fun x =>
    let q := req x
    headPub Z.p.X q.1 q.2

/-- It is `sourcesAt`. -/
theorem sourcesAtBound_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) :
    sourcesAtBound cells weights req Z = sourcesAt cells weights req Z := rfl

/-- The reader of the input at a site: `fastAsk` where the site names the round that samples the
matrix, the filling's reader over `sourcesAtBound` elsewhere. -/
def boundWit (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    Local W₀ Rc Xi Tr → Ask :=
  match s.rng with
  | some r => fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard
  | none => (fastFill (Rc := Rc) (sourcesAtBound cells weights req Z)).wit s

/-- It is `fastWit`. -/
theorem boundWit_fast (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    boundWit (Rc := Rc) cells weights req Z s = fastWit cells weights req Z s := rfl

/-- **It is the filling's own reader, at every site.** -/
theorem boundWit_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    boundWit (Rc := Rc) cells weights req Z s =
      (fastFill (Rc := Rc) (sourcesAt cells weights req Z)).wit s :=
  (boundWit_fast cells weights req Z s).trans (fastWit_eq cells weights req Z s)

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.ownSourcesBound_eq
#print axioms ProofFile.Honest.K3.sourcesAtBound_eq
#print axioms ProofFile.Honest.K3.boundWit_fast
#print axioms ProofFile.Honest.K3.boundWit_eq
