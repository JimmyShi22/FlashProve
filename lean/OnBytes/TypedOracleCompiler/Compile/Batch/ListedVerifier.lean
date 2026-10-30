-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean: the compiled verifier of one slot in a form that goes
along lists of leaves and of positions, where OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean's verifyOneProtocol
walks all 2 ^ depth leaves of every tree and all positions of the external oracles. Definitions.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. After the chain, verifyOneProtocol makes two walks. The strict format (proofHasStrictFormat) asks at every leaf of
every tree, and at every position of the external oracles: if an opening stands here, is the
position read, and has the salt its length? The checks (forestsOf) ask at every leaf and position:
is it read? and take the opening there. At a stored table of great depth these walks are long.

What is done. The caller hands over four things: two lists, and two functions that return lists.
  own, listed: where openings of the argument string can stand: for each round, each of its two
    components and each tree the leaves; and the positions of the external oracles. They hang on
    the string alone. THEY MUST HOLD EVERY PLACE AT WHICH AN OPENING STANDS, READ OR NOT: the strict
    format is there to refuse an opening at a place that is not read.
  mkRd, mkRdE: what is read: mkRd as a function of the instance, the verifier's messages and the
    plain parts, mkRdE of the first two: the read leaves, rising, tree by tree; and the read
    positions of the external oracles in the wire's order.
The bodies of the definitions here call neither Q.loc.reads nor Q.loc.extReads: no set of read
positions is made. Whether a leaf is read is asked of the list of read leaves of its tree.
The wiring comes in pieces (sh, wl, nOpen, maxDepth) and not as one record ProtocolQueryLayout: that record holds
the external oracles' wiring WireE, whose field all is the list of all positions, and compiled Lean
builds a record's fields when it builds the record (by reading; not measured here).
wl : WireELess (ListedExt.lean) is that wiring less the list.

Main definitions. strictBBL, forestsOfL, afterFL, afterBOL, verifyBSL: proofHasStrictFormat, forestsOf, afterF,
checkPrunedOpenings, verifyOneProtocol with strictSBL (ListedStrict.lean), forestsBL (ListedForests.lean), strictExtL and
forestExtL (ListedExt.lean) in the place of strictSB, forestsB, strictExt and forestExt.

Still carried as data: each round's wire record WireRB holds pt : Round.IsPoint, whose field finPos
is the list of all positions of the round's trees, built when the record is built. Of pt the
verifier reads ofSyms and zero alone (mkTr). That list is not cured here.

Limits. THAT verifyBSL IS verifyOneProtocol IS NOT SHOWN IN THIS FILE: ListedVerifierLaws.lean shows it,
under premises on the four things. Where these fail, verifyBSL can say yes where verifyOneProtocol says no.
At a place that own or listed leave out, the strict format tests no opening: not that its tree has a
root, not that the place is read, not the salt's length; at empty lists no opening is tested. At
mkRd or mkRdE that leave out a read place, that place is not checked, even if no opening stands
there; where they hold a place that is not read, an opening there passes as read. So all four are
to be made in Lean on the verifier's side, with a proof, and never taken from a parser.
Nothing on time or memory is a theorem. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedStrict
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedForests
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- For each round: the lists of leaves of the trees of the shared component, and of the slot's. -/
abbrev Leaves : Type := List (List (List ℕ) × List (List ℕ))

/-- proofHasStrictFormat along the places at which openings can stand. rd, rdE: the leaves and the positions
read. -/
def strictBBL (sMT sFS : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (depthReq : ℕ) (π : OneProtocolProof lam Q)
    (own : Leaves) (listed : List E.Pos) (rd : Leaves) (rdE : List E.Pos)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : Bool :=
  haveI := wl.dec
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ RootsOfChain.count Q.loc.shape rts) &&
    strictSBL sMT Q.loc.shape Q.ann sh rts π.opens own rd &&
    strictExtL sMT (fun p => rdE.contains p) π.ext listed &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty) &&
    (ph.slotVal.isSome || π.rsalt.isEmpty)

/-- forestsOf along the leaves and positions read. -/
def forestsOfL {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embE : E.Sym → Body L) (cms : List (Dig lam)) (π : OneProtocolProof lam Q) (rd : Leaves)
    (rdE : List E.Pos) (rts : RootsOfChain lam Q.loc.shape) : Option (List (Forest lam L)) :=
  match forestsBL Q.loc.shape Q.ann sh embS rts π.opens rd,
    forestExtL wl embE cms π.ext rdE with
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- afterF with the wiring in pieces. -/
def afterFL {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann)
    (wl : WireELess E) (depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    TypedOracleComputation lam K L Bool :=
  (runForests Fs s).bind fun ok =>
  (reqPart depthReq π ph).bind fun okr =>
  pure (ok && okr && Q.loc.accept x (wl.build fun p => (π.ext p).map Opening.sym)
    (mkTr Q.loc.shape Q.ann sh rts π.plains ρ π.opens))

/-- checkPrunedOpenings at forestsOfL. -/
def afterBOL {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann)
    (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (rd : Leaves)
    (rdE : List E.Pos) (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    TypedOracleComputation lam K L Bool :=
  match forestsOfL Q sh wl embS embE cms π rd rdE rts with
  | some Fs =>
      if (flatF Fs).length ≤ nOpen ∧
          (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ maxDepth)) then
        afterFL Q sh wl depthReq x π ρ rts ph Fs (readsF Fs)
      else pure false
  | none => pure false

/-- **The verifier along the lists**: the chain; the strict format; then afterBOL. The wiring comes
in pieces: sh, wl, nOpen, maxDepth. -/
def verifyBSL (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (own : Leaves) (listed : List E.Pos)
    (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos) : TypedOracleComputation lam K L Bool :=
  (recomputeChain t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann sh embP 0 .first π.roots π.plains).bind
    fun r =>
    match r with
    | none => pure false
    | some (ρ, rts, ph) =>
      let rd := mkRd x ρ (effPlains Q.loc.shape Q.ann rts π.plains)
      let rdE := mkRdE x ρ
      if strictBBL sMT sFS Q sh wl depthReq π own listed rd rdE rts ph then
        afterBOL Q sh wl nOpen maxDepth embS embE depthReq cms x π rd rdE ρ rts ph
      else pure false

end TypedOracleCompiler.Compile.Batch
