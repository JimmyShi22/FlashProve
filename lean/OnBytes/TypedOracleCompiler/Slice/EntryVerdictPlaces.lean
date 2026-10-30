-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictPlaces.lean: a second form, for evaluation, of the closed check of an
entry file. It has the same value as the first form on all arguments.

That this form is faster, that it comes home, or that it says yes on anything is a fact of a run,
and this head reports none.

What this file states, assumes and does not show, its terms and its limits in full: the comment on
`runEntryFullQ_eq`.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictRun
import OnBytes.TypedOracleCompiler.Run.LaxPlaces

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open TypedOracleCompiler.Run.Thin (PlaceOK PlaceOKS)

/-- The four laws at the wire of the trivial round: it has no position. -/
theorem placeOK_wire0S (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    PlaceOK (wire0S C K chal) where
  at0 := fun _ _ _ h => by cases h
  atJ := fun _ _ _ h => by cases h
  back0 := fun p => p.elim
  backJ := fun p => p.elim

/-- The four laws at the wire of a round of the description. -/
theorem placeOK_wireS (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD) :
    PlaceOK (wireS C K chal d) where
  at0 := fun _ _ _ h => by cases h
  atJ := fun k j p h => ⟨rfl, place_posAtT d.trees k j p h⟩
  back0 := fun _ h => by cases h
  backJ := fun p _ => posAtT_place d.trees p

/-- The four laws at all rounds of the description. -/
theorem placeOKS_wiresSL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List RD, PlaceOKS (SL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds)
  | [] => trivial
  | d :: ds => ⟨placeOK_wireS C K chal d, placeOKS_wiresSL C K chal ds⟩

end TypedOracleCompiler.Run.PQ

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE bodyS)
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run.Thin (verifyLXLQ verifyLXLQ_eq PlaceOKS)
open TypedOracleCompiler.Run.EntryPageSafe (gOf gOf_oracle toBytesT)
open OnBytes.Tie (EntryGround linkAtCfg AskedE)
open OnBytes.Slice (s0Of seedEntry seedOfDrawnC)
open OnBytes.Slice.Shapes (Cfg scAt)

section
variable {X : Type} (D : XD) (dec : X → View → Bool) {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D)
    (early : X → X)
  (Tf : Unit → InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- The four laws at the link's wire, at every list of external positions. -/
theorem placeOKS_wqXL (L : List (Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a))) :
    PlaceOKS (PSXE D dec).S (PSXE D dec).ann (wqXL D dec L).sh :=
  ⟨PQ.placeOK_wire0S D.C D.K _, PQ.placeOKS_wiresSL D.C D.K _ D.ds⟩

/-- `laxEL` over `verifyLXLQ`. -/
def laxELQ (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) : Bool :=
  verifyLXLQ (fun _ => LXE (Bd := Bd) D early (Tf ())) F id (memX D.a) early none .link
    (PSXE D dec) (wqXL D dec []).sh (wqXL D dec) (ix2 (2 ^ D.a)) (lstX D dec) E.emb
    (embPXE D early (Tf ())) some B.embE 0 cms x π

/-- It is `laxEL`. -/
theorem laxELQ_eq
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) :
    laxELQ D dec B E early Tf F cms x π = laxEL D dec B E early Tf F cms x π :=
  verifyLXLQ_eq (fun _ => LXE (Bd := Bd) D early (Tf ())) F id (memX D.a) early none .link
    (PSXE D dec) (wqXL D dec []).sh (wqXL D dec) (placeOKS_wqXL D dec) (ix2 (2 ^ D.a))
    (lstX D dec) E.emb (embPXE D early (Tf ())) some B.embE 0 cms x π

end

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- `entryPartO` over `laxELQ`. -/
def entryPartOQ (c : ByteArray) (hc : c.size = 32) (pd : Dig 256) (a : AskedE)
    (O : ByteArray → ByteArray) : Bool :=
  pinsFit (entryXD G c) G.q.link.table &&
    match assembleS (entryXD G c)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
    | none => false
    | some π =>
      cmpEL (entryXD G c) (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)
          (seedOfDrawnC G.q.link.table.cubeBits G.q.link.table.answers)
          (EntryRunTop.famOfO (entryXD G c) hc (d1Run G.q.link.table.cubeBits
            G.q.link.table.answers)
            G.q.link.table pd O)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] 0
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2 &&
        laxELQ (entryXD G c) _ (bodyS (entryXD G c).a (entryXD G c).base.plan.salt)
          (ownES (entryXD G c) (hok c hc))
          (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (fun _ => TSE (entryXD G c) (seedEntry G.q.link.table.cubeBits G.q.link.table.answers))
          (EntryRunTop.famOfO (entryXD G c) hc (d1Run G.q.link.table.cubeBits
            G.q.link.table.answers)
            G.q.link.table pd O)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root]
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a) π

/-- It is `entryPartO`: on all arguments. -/
theorem entryPartOQ_eq (c : ByteArray) (hc : c.size = 32) (pd : Dig 256) (a : AskedE)
    (O : ByteArray → ByteArray) :
    entryPartOQ G hok c hc pd a O = entryPartO G hok c hc pd a O := by
  unfold entryPartOQ entryPartO
  simp only [laxELQ_eq]
  rfl

/-- `verifyEntryO` over `entryPartOQ`. -/
def verifyEntryOQ (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) : Bool :=
  let b₀ := O (toBytesT (scAt cfg))
  let c := _root_.Run.digToBytes (_root_.Run.digS b₀)
  let b₁ := O (toBytesT (s0Of (G.bytesAt c)))
  entryPartOQ G hok c (_root_.Run.size_digToBytes _) (_root_.Run.digS b₁) a O

/-- It is `verifyEntryO`: on all arguments. -/
theorem verifyEntryOQ_eq (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    verifyEntryOQ G hok cfg a O = verifyEntryO G hok cfg a O := by
  unfold verifyEntryOQ verifyEntryO
  simp only [entryPartOQ_eq]

/-- The second form for a run, at the full size. -/
def runEntryFullQ (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) : Bool :=
  askedFit OnBytes.Tie.recordGround.q.link.table a &&
    verifyEntryOQ OnBytes.Tie.recordGround record_ok cfg a O

/-- The second form for a run, at the small example. -/
def runEntrySmallQ (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) : Bool :=
  askedFit OnBytes.Tie.smallRecordGround.q.link.table a &&
    verifyEntryOQ OnBytes.Tie.smallRecordGround small_record_ok cfg a O

/-- At the full size the second form for a run is the first: on all arguments.

This file states: `runEntryFullQ cfg a O = runEntryFull cfg a O` and the like at the small example
(`runEntryFullQ_eq`, `runEntrySmallQ_eq`), for every value cfg of the three public files, every
parsed entry file a and every hash function O on bytes. So the second forms are the closed checks
`verifyEntryFull` and `verifyEntrySmall` (OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean) at the function
`gOf O` (`runEntryFullQ_check`, `runEntrySmallQ_check`), and at the format's own hash
(`runEntryFullQ_oracle`, `runEntrySmallQ_oracle`). The second forms are the first forms' text over
`verifyLXLQ` (OnBytes/TypedOracleCompiler/Run/LaxPlaces.lean), which makes each tree's checks along the leaves that
are read and not along all leaves.

It assumes: no hypothesis in the six statements named; their variables are cfg, a and (but in the
two at the format's hash) O. The general forms (`entryPartOQ_eq`, `verifyEntryOQ_eq`) have the
record G : `EntryGround` of the entry file's parameters as a variable and carry the check's own
hypothesis hok; `entryPartOQ_eq` asks also that the digest c has 32 bytes (hc). The four laws that
LaxPlaces.lean asks are proved here for the entry file's protocol
(`placeOKS_wqXL`), from two lemmas of OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean.

It does not show: that the second form is faster, that it ends, or that it says yes on anything. An
evaluation that gives true is no proof in Lean: whoever passes from it to the closed check trusts
Lean's evaluator or compiler and its runtime. No bound, no probability, nothing on soundness.
Nothing more of the closed check than OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean shows: by that file's
own limits it takes the roots, the answers and the seeds out of the parsed value, does not look at
the commitment ID, and does not refuse all that a strict reading of the file refuses. Nothing more
of `verifyLXLQ` than OnBytes/TypedOracleCompiler/Run/LaxPlaces.lean shows. The stand-alone program for the entry
file's part (OnBytes/ShellOf/EntryProg.lean), which the Lean verifier program `verify-on-bytes` does
not call, and `evaluate_entryExtraFull_oracle`, `evaluate_entryExtraSmall_oracle`
(Johnson/Top/Pub/FrontWithEntry.lean) name the first form, not this one. The limits in full, for
every statement of this file: below.

Terms: lean/GLOSSARY.md. In the comments of this file "paid" means proved, here or in the
files imported, a "wire" or "wiring" is the data that numbers a round's positions and trees, a
"place" is a leaf's number in its tree, "comes home" means that an evaluation ends, a "run" is
an evaluation by Lean's evaluator or of compiled code, and the "lax verifier" is `verifyLX`
(OnBytes/TypedOracleCompiler/Run/LaxThin.lean), an evaluable form of the compiled verifier `verifyB` of the
compiler under OnBytes/TypedOracleCompiler/. Where a comment of this file names the head of a file, read with
it the comment to which that head points.

THE LIMITS.

OnBytes/TypedOracleCompiler/Slice/EntryVerdictPlaces.lean: a second form for a run of the closed check of an entry
file, without the walk over all leaves of the own trees. It is the first form on all arguments.

Statements with their proofs, and definitions with code. `runEntryFull` and `runEntrySmall`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean) call the lax verifier along short lists (`laxEL`,
OnBytes/TypedOracleCompiler/Slice/EntryVerdictShort.lean), which walks every leaf of every own tree and searches at
each the set of positions read. Here the same text stands over `verifyLXLQ`
(OnBytes/TypedOracleCompiler/Run/LaxPlaces.lean), which goes, tree by tree, along the places of the read positions
alone.

Main names:
  `placeOK_wire0S`, `placeOK_wireS`, `placeOKS_wiresSL` (namespace `TypedOracleCompiler.Run.PQ`): the four
    laws that LaxPlaces.lean asks of a wire hold of the description's own wires. No condition.
  `placeOKS_wqXL`: so they hold at the link's wire `(wqXL D dec L).sh`, for all D, dec and L: here
    the condition of `verifyLXLQ_eq` is paid.
  `laxELQ`, `laxELQ_eq`: `laxEL` over `verifyLXLQ`; it is `laxEL`.
  `entryPartOQ`, `verifyEntryOQ`; `entryPartOQ_eq`, `verifyEntryOQ_eq`: `entryPartO` and
    `verifyEntryO` over `laxELQ`; they are these.
  `runEntryFullQ`, `runEntrySmallQ` cfg a O : Bool; `runEntryFullQ_eq`, `runEntrySmallQ_eq`: they
    are `runEntryFull` and `runEntrySmall`, on all arguments, with no premise.
    `runEntryFullQ_check`, `runEntrySmallQ_check`: so they are the closed checks at `gOf O`.
    `runEntryFullQ_oracle`, `runEntrySmallQ_oracle`: at the format's oracle on bytes they are the
    closed checks at the realised oracle on bit strings.

Limits.
  1. Equations of values. That this form is faster, that it comes home, or that it says yes on
     anything is a fact of a run, and this head reports none.
  2. All that the heads of EntryVerdictRun.lean and LaxPlaces.lean do not claim. No bound is joined
     here. No probability stands here. Nothing on soundness.
  3. A run's answer true is no proof in Lean of `runEntryFullQ cfg a O = true`: whoever passes from
     it, by the equations here, to the closed check trusts Lean's evaluator or compiler and its
     runtime, here also on `Finset.sort`, `Finset.image` and `Finset.filter` (`placesAt`).
  4. The program's kit names `runEntryFull` and `runEntrySmall`, not these forms
     (OnBytes/ShellOf/EntryProg.lean). The text of `entryPartO` and `verifyEntryO` is copied
     here: if that text turns, the equations here do not build until the copy follows.
-/
theorem runEntryFullQ_eq (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    runEntryFullQ cfg a O = runEntryFull cfg a O :=
  congrArg (askedFit OnBytes.Tie.recordGround.q.link.table a && ·)
    (verifyEntryOQ_eq _ _ cfg a O)

/-- At the small example the second form for a run is the first: on all arguments. -/
theorem runEntrySmallQ_eq (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    runEntrySmallQ cfg a O = runEntrySmall cfg a O :=
  congrArg (askedFit OnBytes.Tie.smallRecordGround.q.link.table a && ·)
    (verifyEntryOQ_eq _ _ cfg a O)

/-- So at the full size it is the closed check at the function made of O. -/
theorem runEntryFullQ_check (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    runEntryFullQ cfg a O = verifyEntryFull cfg a (gOf O) :=
  (runEntryFullQ_eq cfg a O).trans (runEntryFull_eq cfg a O)

/-- So at the small example it is the closed check at the function made of O. -/
theorem runEntrySmallQ_check (cfg : Cfg) (a : AskedE) (O : ByteArray → ByteArray) :
    runEntrySmallQ cfg a O = verifyEntrySmall cfg a (gOf O) :=
  (runEntrySmallQ_eq cfg a O).trans (runEntrySmall_eq cfg a O)

/-- At the format's oracle on bytes, at the full size, it is the closed check at the realised oracle
on bit strings. -/
theorem runEntryFullQ_oracle (cfg : Cfg) (a : AskedE) :
    runEntryFullQ cfg a _root_.Fmt.oracle = verifyEntryFull cfg a _root_.Run.oBits := by
  rw [runEntryFullQ_check, gOf_oracle]

/-- At the format's oracle on bytes, at the small example, it is the closed check at the realised
oracle on bit strings. -/
theorem runEntrySmallQ_oracle (cfg : Cfg) (a : AskedE) :
    runEntrySmallQ cfg a _root_.Fmt.oracle = verifyEntrySmall cfg a _root_.Run.oBits := by
  rw [runEntrySmallQ_check, gOf_oracle]

end TypedOracleCompiler.Slice

#print axioms TypedOracleCompiler.Slice.laxELQ_eq
#print axioms TypedOracleCompiler.Slice.runEntryFullQ_eq
#print axioms TypedOracleCompiler.Slice.runEntrySmallQ_eq
#print axioms TypedOracleCompiler.Slice.runEntryFullQ_check
#print axioms TypedOracleCompiler.Slice.runEntrySmallQ_check
#print axioms TypedOracleCompiler.Slice.runEntryFullQ_oracle
#print axioms TypedOracleCompiler.Slice.runEntrySmallQ_oracle
