-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/ProofAt.lean: what a run of the compiled verifier of the proof file's slot is handed,
at the small size, with the rounds' data bound once: the letters, the description, the hollow
carrier, the wire record, the page, and the proof string made of the parsed proof file (the outside
parser's output). No reader of the proof file, no report and no runner stand here.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why the data are an argument. Ds p (Johnson/RunOne/Closed.lean) costs the planner's dry runs at
every evaluation. Everything in the section At takes the data and the three values beside them as
arguments: a caller binds Ds p, tF p, tJ p, rn p once and hands them on. At these values the carrier
is Closed's own (LAt_Ls).

  Letters, lettersAt   the claim, made of the user's own files (claimOf, in Letters.lean beside this
                       file: its plan is the answer of the planner's twin over the format's hash
                       at O), and the table that the entry file names, which is the prover's
  sRof, sbOf           the bytes of a salt: of the binding tree's leaves; of an opening
  DscAt, LAt, wqAt     the description, the hollow carrier, the wire record
  rdP                  the read-back under the proof file's tag
  pageB                the page: sR and the leaves' spelling are arguments
  pageP                pageB for a run of the three chains alone: the leaves write nothing (no chain
                       of a proof file asks them)
  pageV                pageB for a run with the part behind the chains: sR is sRof, the leaves are
                       spelt (leafOf id)
  answersC, frontC     the parsed proof file's answers as a table's; what the front round sends
  stringC              the proof string of a parsed proof file (Carrier.File.toBPrfAt)
  knOf                 the number of blocks but one at which a run is made

Whose each input is. The user's: the parameter file, the layout, the scales, the request, the reply
(in these runs, where whoever starts a run supplies the two as the user's claim). The prover's: the
entry file, of which the table's root and answers are read, untested here; and the parsed proof
file, the stored copy's number in it too (frontC): no test here holds that number. The caller's: the
hash O and Kn. NO INPUTS: the commitment ID, the key file, the entry's number: a yes of a run over
these values says nothing on which commitment the table belongs to.

Under which oracle functions. A page serves the family gJ P O (OnBytes/Maker/Page/Frame.lean) alone:
O at the string that the page writes for a typed query, zeros where it writes none. That family is
no encoding in the theorems' sense. The request's item (reqS; claimOf) is made by the format's
second hash function, a fixed function, not by O, as are the planner's own tests and digests on the
public files (publicOf): so whether claimOf returns, and part of the plan that it returns, hang on
that fixed function at every O. All of these read the user's public files and request, none the
prover's bytes.

To be minded. No query under the tag "test" can be typed at this carrier: its protocol under that
tag has no round, so a chain query there has no plain part to hold. The test of a record's seeds
asks such queries: it is not and cannot be run here. Here the record's seeds are drawn by the
verifier's side over the hash, under the table's name (recFormed, Johnson/RunOne/ProofGround.lean);
its answers are the entry file's. No law ties this to the seeds' test.
Under pageP a verifier that asks a leaf gets no string: a guarded run says no to every proof string
there, the honest one too. The binding tree's shape in stringC is the plan's; sRof is its number of
salt bytes, and depthReq (Johnson/RunOne/Closed.lean) its depth. The binding tree is the tree that
other files call the request tree.

Limits. Definitions, and three equations by unfolding. The hollow carrier is the carrier of no
theorem. The tool that wrote the parsed proof file is untrusted, and nothing here tests what it
wrote but its form. Nothing on soundness.


-/
import Johnson.RunOne.Closed
import Johnson.RunOne.Letters
import Johnson.RunOne.OraclePages
import OnBytes.Maker.SilentParts
import OnBytes.Maker.CarrierTyping

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.RunOne

open OnBytes OnBytes.Maker OnBytes.Maker.Page OnBytes.Flat
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (JoinMsg)
open _root_.Run
open _root_.Run.PQ (CK View)

/-- The letters of a proof file's run: the claim, made of the user's own files (claimOf,
Johnson/RunOne/Letters.lean), and the table that the entry file names, which is the prover's. -/
structure Letters extends Claim where
  /-- the table that the entry file names: the prover's -/
  further : Params.TableName
  /-- the user's parameter file -/
  pol : ByteArray
  /-- the user's file of scales -/
  KL : ByteArray
  /-- the user's request file -/
  request : ByteArray
  /-- the user's reply file -/
  y : ByteArray

/-- The letters at the user's five files and the entry file. -/
def lettersAt (O : ByteArray → ByteArray) (pol lay KL request y ent : ByteArray) :
    Except String Letters := do
  let c ← claimOf O pol lay KL request y
  match TieK.furtherOf c.p.chains.link ent with
  | some further =>
    pure { c with further := further, pol := pol, KL := KL, request := request, y := y }
  | none => throw "No table could be read off the entry file."

/-- The bytes of a salt of the binding tree's leaves. -/
def sRof (A : Letters) : ℕ := A.p.chains.proof.first.binding.saltBytes

/-- The bytes of a salt of an opening. -/
def sbOf (A : Letters) : ℕ := A.p.chains.proof.first.given.plan.salt

/-- The parsed proof file's answers as a table's. -/
def answersC (k : Carrier.File) : List E := k.answers.map E.ofTriple

/-- What the front round sends: these answers, and the parsed proof file's number of the stored
copy. -/
def frontC (k : Carrier.File) : FrontMsg (List E) := frontOf (answersC k) k.copy

/-- The number of blocks but one at which a run is made: what is asked for, and at least what the
rounds of the data need: with fewer blocks a round's draws would be cut short, and the run would
part from the programs by our own fault. -/
def knOf (D : WholeD) (Kn : ℕ) : ℕ := max Kn (blocksT .two (D.ds₁ ++ (D.ds₂ ++ D.ds₃)))

section At
variable (D : WholeD) (tF₀ : FrontMsg (List E)) (tJ₀ : JoinMsg (List E) ByteArray)
  (rn₀ : Yp → View → View → View → Bool) (Kn : ℕ)

/-- The description at data that are bound once. -/
abbrev DscAt := wholeDesc Cs D tF₀ tJ₀ ByteArray.empty sil rn₀

/-- The hollow carrier there. early: what of an instance is written first. -/
abbrev LAt (early : Yp → Yp) : BatchProtocolWithLeafBody Unit Yp :=
  hollow (DscAt D tF₀ tJ₀ rn₀).batch (0, []) early none

/-- The wire record there. -/
def wqAt : ProtocolQueryLayout 256 (Kn + 1) (DscAt D tF₀ tJ₀ rn₀).batch :=
  wqWhole Cs Kn (chalP .two Kn) D tF₀ tJ₀ ByteArray.empty sil rn₀

/-- The read-back under the proof file's tag: the plain parts are the file's own, by unfolding. -/
def rdP (early : Yp → Yp) (w : PBt (LAt D tF₀ tJ₀ rn₀ early) .onl) :
    Option (PlainPart (chainsOf Cs D tF₀ tJ₀ ByteArray.empty).sh
      (chainsOf Cs D tF₀ tJ₀ ByteArray.empty).ann) := some w

/-- **The page.** The key file's rows are never asked: no query under their tag can be typed at
this carrier. sR: the bytes of a salt of the binding tree's leaves. leaf: the leaves' spelling. The
first chain's statement reads the request's item and the request file's bytes off the instance in
the typed query (reqS, Johnson/RunOne/Closed.lean, at the user's parameter file and scales). -/
def pageB (O : ByteArray → ByteArray) (A : Letters) (sR : ℕ)
    (leaf : LeafIn (LAt D tF₀ tJ₀ rn₀ (earlyS A.p)) → Option Fmt.OQ) :
    PageJ (LAt D tF₀ tJ₀ rn₀ (earlyS A.p)) (Kn + 1) :=
  pageRun A.p.cfg sR
    (keyPage Cs D tF₀ tJ₀ ByteArray.empty (fun _ => none) O A.p.chains.key)
    (fillJ Cs D tF₀ tJ₀ ByteArray.empty (rdP D tF₀ tJ₀ rn₀ (earlyS A.p))
      (silentProof (Fmt.HO O) A.p.chains.proof (reqS A.pol A.KL)))
    leaf

/-- The page's data of the proof file, by unfolding. -/
theorem pageB_proof (O : ByteArray → ByteArray) (A : Letters) (sR : ℕ)
    (leaf : LeafIn (LAt D tF₀ tJ₀ rn₀ (earlyS A.p)) → Option Fmt.OQ) :
    (pageB D tF₀ tJ₀ rn₀ Kn O A sR leaf).proof =
      fillJ Cs D tF₀ tJ₀ ByteArray.empty (rdP D tF₀ tJ₀ rn₀ (earlyS A.p))
        (silentProof (Fmt.HO O) A.p.chains.proof (reqS A.pol A.KL)) := rfl

/-- The page for a run of the three chains alone: the leaves write nothing. -/
def pageP (O : ByteArray → ByteArray) (A : Letters) (sR : ℕ) :
    PageJ (LAt D tF₀ tJ₀ rn₀ (earlyS A.p)) (Kn + 1) :=
  pageB D tF₀ tJ₀ rn₀ Kn O A sR fun _ => none

/-- The page's data of the proof file, by unfolding. -/
theorem pageP_proof (O : ByteArray → ByteArray) (A : Letters) (sR : ℕ) :
    (pageP D tF₀ tJ₀ rn₀ Kn O A sR).proof =
      fillJ Cs D tF₀ tJ₀ ByteArray.empty (rdP D tF₀ tJ₀ rn₀ (earlyS A.p))
        (silentProof (Fmt.HO O) A.p.chains.proof (reqS A.pol A.KL)) := rfl

/-- **The page for a run with the part behind the chains.** -/
def pageV (O : ByteArray → ByteArray) (A : Letters) :
    PageJ (LAt D tF₀ tJ₀ rn₀ (earlyS A.p)) (Kn + 1) :=
  pageB D tF₀ tJ₀ rn₀ Kn O A (sRof A) (leafOf (L := LAt D tF₀ tJ₀ rn₀ (earlyS A.p)) id)

/-- **The proof string of a parsed proof file.** The configuration's digest and the binding tree's
shape are the plan's. none: the file's four fields on the binding tree do not fit the shape; or an
entry of trees has a number that is no tree's of the data (File.treesFit); or the first chain's last
round, the seal, is not bare; or a tree's chain in the file is not the data's; or the plain parts of
one of the three chains do not type (Carrier.File.toBPrfAt, OnBytes/Maker/CarrierTyping.lean). -/
def stringC (A : Letters) (kc : Carrier.File) :
    Option (OneProtocolProof 256 (DscAt D tF₀ tJ₀ rn₀).batch) :=
  kc.toBPrfAt Cs D tF₀ tJ₀ ByteArray.empty sil rn₀ A.p.cfg A.p.chains.proof.first.binding
    (frontC kc) ⟨answersC kc, kc.run2⟩ kc.run3

end At

/-- At the closed values the carrier is Closed's own. -/
theorem LAt_Ls (p : Model.Verify.Planned) :
    LAt (Ds p) (tF p) (tJ p) (rn p) (earlyS p) = Ls p := rfl

end Johnson.RunOne

#print axioms Johnson.RunOne.pageB_proof
#print axioms Johnson.RunOne.pageP_proof
#print axioms Johnson.RunOne.LAt_Ls
