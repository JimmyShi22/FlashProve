-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/OraclePages.lean: the page's data for a run of the compiled verifier of a key file or
of a proof file on real bytes. Definitions alone.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

The family of typed oracle functions of such a run is meant to be `gJ P O`
(OnBytes/Maker/Page/Frame.lean): O at the string `codeJ P o q j` of a typed query and a block; zeros
where the page P writes no string (a hole). O is a function on the format's strings, an argument of
`proofPage` and `keyPage`. This file makes P; no line of its code names `gJ`.

Main names:
  `pageRun`: a page whose four spellings "taken from elsewhere" write nothing.
  `proofPage`, `keyPage`: a proof file's and a key file's data of the page: `fillJ` at
    `silentProof` and at `silentKey`, the parameters' digests made by the format's hash over O.

Limits: this file holds no statement.
Holes. At `pageRun` the four spellings write nothing. So a chain query under the entry file's tag
and a query to the spare oracle have no string, and a leaf has one only where `leaf` gives a call.
sR is the number of bytes of the salt of a leaf of the request tree: such a leaf has a string only
at 256 + 8 sR + 64 bits, so at another sR than the file's every one of them is a hole. A chain query
of the seeds stands under the key file's tag: at such a page it is spelt by the key file's rows, if
at all, and not as the seeds' own call. So far what hangs on `pageRun` and its letters. The holes of
OnBytes/Maker/Page/Frame.lean stand as well (fbw; the slot value under the entry file's tag; a head
f2 with an instance; a round out of range; every block but the tail's at a chain's first query),
and so does its word that `gJ` is no one-to-one coding. Under `gJ` a query without a string is
answered by zeros, and nothing here refuses it.
Letters. cfg, sR, leaf and the two files' data are the caller's: nothing here says that they are
those of a given file. All letters of `proofPage` and `keyPage` are the caller's too. The O in them
and the O in `gJ P O` are two letters: nothing here lays them equal. The data hang on O (the
parameters' digests are made over it): so a statement on `gJ P O` for one page P and all O does not
speak of a page made here, which turns with O. req is free: nothing asks that it spells the
instance or is one to one; at a first query without an instance the request's bytes are empty.
The read-back. Where rd returns nothing, or a plain part of another round than the query names, or
the half of a round's pair that sends nothing, the message and the three statements are empty, the
two run values are the empty string and the nonce is 0; a string can still be written there. That
rd reads back what the verifier's embedding writes is said nowhere here.
Nothing on soundness.

-/
import OnBytes.Maker.Page.Fill
import OnBytes.Maker.Page.Silent
import OnBytes.Maker.Page.Trees

set_option autoImplicit false

namespace Johnson.RunOne

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run
open _root_.Run.PQ (CK)
open _root_.Compile.Joined (JoinMsg)
open OnBytes OnBytes.Maker OnBytes.Maker.Page

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- A page for a run: the four spellings that are taken from elsewhere write nothing. -/
def pageRun (cfg : ByteArray) (sR : ℕ) (key : FileJ L .test) (proof : FileJ L .onl)
    (leaf : LeafIn L → Option Fmt.OQ) : PageJ L K where
  cfg := cfg
  key := key
  proof := proof
  sR := sR
  leaf := leaf
  link := fun _ => none
  seeds := fun _ => none
  leafX := fun _ => none
  other := fun _ => none

/-- A proof file's data of the page, under any tag t (no string holds the tag). rd: from the
interface's plain parts under t to the file's own; req: from an instance, two strings: the value of
the statement's item "request", then the request file's bytes (`silentProof`,
OnBytes/Maker/Page/Silent.lean). After `proofM` (Johnson/Maker/Page/At.lean).
-/
def proofPage {t : Tag} (C : CK) (D : WholeD) (tF : FrontMsg (List E))
    (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray)
    (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))
    (O : ByteArray → ByteArray) (c : Params.ProofChains) (req : X → ByteArray × ByteArray) :
    FileJ L t :=
  fillJ C D tF tJ t3 rd (silentProof (Fmt.HO O) c req)

/-- A key file's data of the page, under any tag t. After `keyM` (Johnson/Maker/Page/At.lean). -/
def keyPage {t : Tag} (C : CK) (D : WholeD) (tF : FrontMsg (List E))
    (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray)
    (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))
    (O : ByteArray → ByteArray) (k : Params.KeyChains) : FileJ L t :=
  fillJ C D tF tJ t3 rd (silentKey (Fmt.HO O) k X)

end Johnson.RunOne
