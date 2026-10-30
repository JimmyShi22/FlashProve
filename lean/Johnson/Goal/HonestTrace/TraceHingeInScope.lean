-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/TraceHingeInScope.lean

Conditional lemmas for public files in the goals' scope. At a served request, Cb.Lkp.MidP holds at
the 25 lookups of the calls with keys and bits read by the matrices' labels in theTrace X i x;
wherever a trace that meets TraceHinge (Johnson/HonestTrace/TraceHinge.lean) is there, the same
holds at that trace; and an instance that is true under the policy at the files' parameters is
served.
This file states no goal.

Main definitions and theorems:
* "PublicInScope Z pp lay X": the three premises on the public files as one structure: Z is in the
  goals' scope; the goals' reader returns pp at Z; publicOf returns X.
* "servesAt_of_true": under PublicInScope: Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x gives
  ServesAt X i x.
* "TrueAtInput pp instOf i ξ": instOf reads off ξ an instance that is true under the policy at pp's
  scales and policy. "trueAtInput_of_trace": under PublicInScope and TraceHinge: where trace i ξ is
  there, TrueAtInput pp instOf i ξ.
* "midPAtReaders_in_scope": in scope, at a served request: MidPAtReaders X (cellOf X (theTrace X i
  x)) (entryOf i) x. "midPAtReaders_of_true": the same from Policy.IsTrueUnder.
* "midPAtReaders_of_traceHinge": under PublicInScope and TraceHinge: where trace w₀ ξ = some ω,
  instOf reads off ξ an instance x with MidPAtReaders X (cellOf X ω) (entryOf w₀) x.
* "readers_eq_in_scope": in scope, at a served request: fromG, fromA and fromH at the readers cellOf
  X (theTrace X i x) and entryOf i are cellMW, cellZ and readH at the lists of theTrace X i x and
  i.mat, as functions.

Limits. These are conditional lemmas, and short: each is at most TraceHinge, a rewriting, and
theorems of Johnson/HonestTrace/FromCells.lean, Johnson/Goal/HonestTrace/FromCellsInScope.lean or
Johnson/Goal/HonestTrace/FullInScope.lean. WHAT IS READ OF AN INPUT IS THAT ITS TRACE IS THERE: no
statement of this file says that a trace is there at any input. Policy.IsTrueUnder stands here at
every instance x; no statement of this file names requestOfTokens, so that the instance is the one
built of a prompt and an output without padding is a matter of instOf, a parameter here. No theorem
of this file shows PublicInScope of any Z; see its docstring. That the X of another file's public
part is publicOf's return at files in scope is not shown here; for Zp.p.X of the description's
public part Zp the three premises are the fields scope, reads and pubOne of P5J.AtMg
(Johnson/P5J/AtMg.lean), of which the side library has a member at VerifierAndGoals.storedPublicFiles (headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean); neither is imported here. On names: readers_eq_in_scope says
that this library's reading by labels is its reading by numbers; that the verifier's plans bear
these labels is planName_ff_in_scope, planName_att_in_scope and planName_head_in_scope
(Johnson/Goal/HonestTrace/FullInScope.lean), not called here; fromG, fromA and fromH read a borrowed
matrix at the borrower's number and label, and that a reader which asks by the owner's number, the
owner's label and a first column reads the same is not shown here. The keys are the library's keyG,
keyA and keyH: nothing is said here on the format's own wording of the keys. All is at the full
size.

Not claimed: anything on a prover, on what a verifier accepts, or on a property of the protocol.

-/
import Johnson.HonestTrace.TraceHinge
import Johnson.Goal.HonestTrace.FromCellsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model.Verify (publicOf)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {i : Cm.Idx} {x : Instance ppref}

/-- **The three premises on the public files, as one structure.** No theorem of this file shows it
of any Z. At the stored files VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap the fields scope and reads are theorems
(VerifierAndGoals.filesRead, Johnson/Goal/Files/FilesReadProof.lean). That publicOf returns at VerifierAndGoals.storedPublicFiles,
at lay := some VerifierAndGoals.storedPublicFiles.lay, is a theorem of the side library AtFullSide
(publicOf_zFull_returns, AtFullSide/Planner/PublicReturns.lean). Johnson/Goal/Meaning/ScopeRun.lean
checks the three by an evaluation too ("#guard allThree storedPublicFiles"; by three_of_allThree,
Johnson/Goal/Meaning/HeadCondExample.lean, the three hold, at lay := some Z.lay, wherever that test
accepts). VerifierAndGoals.storedPublicFiles is a term of Ladder/Stored.lean; its weights are synthetic. No theorem of
this file calls any of these. -/
structure PublicInScope (Z : VerifierAndGoals.PublicFiles) (pp : ScalesAndPolicy) (lay : Option ByteArray)
    (X : Model.Verify.Public) : Prop where
  /-- Z is in the goals' scope -/
  scope : VerifierAndGoals.InScope Z = true
  /-- the goals' reader returns pp at Z -/
  reads : VerifierAndGoals.readFiles Z = .ok pp
  /-- publicOf returns X at Z's parameter file and scale file -/
  pub : publicOf Z.pol Z.KL lay = .ok X

/-- Under PublicInScope: an instance that is true under the policy at the files' parameters (pp's
scales and policy) is served. At every instance x: that x is built of a prompt and an output without
padding is not asked. By servesAt_iff_in_scope, which goes both ways. -/
theorem servesAt_of_true (B : PublicInScope Z pp lay X)
    (V : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) : ServesAt X i x :=
  (servesAt_iff_in_scope B.scope B.reads B.pub i x).2 V

/-- "True under the policy" at an input: the reader finds an instance, and that instance is true
under the policy at the files' parameters. -/
def TrueAtInput {Xi : Type} (pp : ScalesAndPolicy) (instOf : Xi → Option (Instance ppref)) (i : Cm.Idx)
    (ξ : Xi) : Prop :=
  ∃ x, instOf ξ = some x ∧ Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x

/-- Under PublicInScope and TraceHinge: where the trace is there, the input is true under the
policy. So a statement "wherever the trace is there" speaks of such inputs alone. The converse is
not shown here. -/
theorem trueAtInput_of_trace {Xi : Type} (B : PublicInScope Z pp lay X)
    {trace : Cm.Idx → Xi → Option Tr} {instOf : Xi → Option (Instance ppref)}
    (G : TraceHinge X trace instOf) {ξ : Xi} {ω : Tr} (h : trace i ξ = some ω) :
    TrueAtInput pp instOf i ξ := by
  obtain ⟨x, hx, Sv, -⟩ := G i ξ ω h
  exact ⟨x, hx, (servesAt_iff_in_scope B.scope B.reads B.pub i x).1 Sv⟩

/-- In scope, at a served request: MidPAtReaders at the readers cellOf X (theTrace X i x) and
entryOf i. It is midP_layers_cells_in_scope, midP_att_cells_in_scope and midP_head_cells_in_scope
(Johnson/Goal/HonestTrace/FromCellsInScope.lean) as one statement. -/
theorem midPAtReaders_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) :
    MidPAtReaders X (cellOf X (theTrace X i x)) (entryOf i) x :=
  fun θ al => ⟨fun _ hg => midP_layers_cells_in_scope hZ hR h Sv hg θ al,
    fun _ hg => midP_att_cells_in_scope hZ hR h Sv hg θ al,
    midP_head_cells_in_scope hZ hR h Sv θ al⟩

/-- The same from "true under the policy" at the files' parameters. -/
theorem midPAtReaders_of_true (B : PublicInScope Z pp lay X)
    (V : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) :
    MidPAtReaders X (cellOf X (theTrace X i x)) (entryOf i) x :=
  midPAtReaders_in_scope B.scope B.reads B.pub (servesAt_of_true B V)

/-- Under PublicInScope and TraceHinge: where trace w₀ ξ = some ω, instOf reads off ξ an instance x,
and MidPAtReaders holds at the readers cellOf X ω and entryOf w₀ and at x. -/
theorem midPAtReaders_of_traceHinge {Xi : Type} (B : PublicInScope Z pp lay X)
    {trace : Cm.Idx → Xi → Option Tr} {instOf : Xi → Option (Instance ppref)}
    (G : TraceHinge X trace instOf) {w₀ : Cm.Idx} {ξ : Xi} {ω : Tr} (h : trace w₀ ξ = some ω) :
    ∃ x, instOf ξ = some x ∧ MidPAtReaders X (cellOf X ω) (entryOf w₀) x := by
  obtain ⟨x, hx, Sv, rfl⟩ := G w₀ ξ ω h
  exact ⟨x, hx, midPAtReaders_in_scope B.scope B.reads B.pub Sv⟩

/-- **The reading by labels is the reading by numbers**, in scope, at a served request, as
functions, at all 25 sub-proofs: an equation of readers. By it MidPAtReaders at these readers is the
conclusion of midP_in_scope, after rewriting. By fromG_cellOf, fromA_cellOf and fromH_cellOf
(Johnson/HonestTrace/FromCells.lean) under namesFit_theTrace. -/
theorem readers_eq_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) :
    (∀ g < 12, fromG X (cellOf X (theTrace X i x)) (entryOf i) g =
        Alg.cellMW (theTrace X i x (2 * g)) i.mat) ∧
      (∀ g < 12, fromA X (cellOf X (theTrace X i x)) g = L5.cellZ (theTrace X i x (2 * g + 1))) ∧
      fromH X (cellOf X (theTrace X i x)) (entryOf i) = Hd.readH (theTrace X i x 24) i.mat :=
  have N := namesFit_theTrace hZ hR h Sv
  ⟨fun _ hg => fromG_cellOf N i hg, fun _ hg => fromA_cellOf N hg, fromH_cellOf N i⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.servesAt_of_true
#print axioms OnBytes.HonestTrace.trueAtInput_of_trace
#print axioms OnBytes.HonestTrace.midPAtReaders_in_scope
#print axioms OnBytes.HonestTrace.midPAtReaders_of_true
#print axioms OnBytes.HonestTrace.midPAtReaders_of_traceHinge
#print axioms OnBytes.HonestTrace.readers_eq_in_scope
