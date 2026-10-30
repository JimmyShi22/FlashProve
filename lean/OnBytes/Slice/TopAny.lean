-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/TopAny.lean: from "the compiled verifier accepts" to a statement on traces, for every
description of a chain that opens two stored tables.

OnBytes/Tie/StoredMain.lean proves that the compiled verifier of one slot accepts what the program's
reader and decision accept (`CompiledAcceptsX`). OnBytes/Slice/LinkClause.lean and Experiment.lean
prove what follows when the compiled Link verifier of a whole wiring accepts. This file proves that
the two verifiers are equal for every description D and decision dec, and joins the two halves.

Main definitions: `wireTo`, `reAnn`, `WkAny`, `asLink`, `SoundLAny`, `theRunAny`, `badAny`,
`LgBehind`.
Main theorems: `psofX_up`, `okgAny`, `vls_any`, `experiment_any`; on the named set of
bad traces `badAny_rare`, `badAny_mono`, `badAny_stable`, `badAny_run`; the statement on traces
`top_any`, `compiled_top`, `session_top`.
Asked: the protocol made from D and dec is round-by-round sound for a language Lg with error counts
εL; no round asks for more than 64 bits of work; the test `Run.PQ.okX` on the stored openings.

Limits, a line each: the first four of the last three theorems, the others of every theorem here.
 With large counts they are true and empty: they say something only with `badAny_rare` at the same
 counts and a small e.
 The hypothesis on the trace is membership, not order: which trace to take is the reader's duty.
 No theorem gives a trace with an accepted run's queries outside the named set.
 Whether a list with BLAKE2b's answers shows one of the set's three events no theorem says.
 No bound on the probability that a false file is accepted: `experiment_any` and the bound on the
 set speak of random typed oracles, the verifier's yes of BLAKE2b.
 Not claimed: that the hypothesis of soundness holds for a language of interest; that one set serves
 all entry files; that the typed first query reads the roots; that the roots are the right ones (no
 key is checked); anything on what the two strings decode to.
In full, with the three events of the named set: OnBytes/Slice/README.md, "TopAny.lean".
-/
import OnBytes.Slice.Top
import OnBytes.Tie.EntryFile
import Run.PlanQXDoorProofs
import Run.PlanQXLawsProofs
import Run.M1RunTieP

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ
open scoped ENNReal

/-! ## The same data under an equal marking -/

section
variable {Y : Type} {E : ExtSpec} {lam K : ℕ}

/-- A wiring, carried along an equation between two batch protocols. -/
def wireTo {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) : ProtocolQueryLayout lam K Q' := h ▸ w

/-- The library's laws of a wiring go along. -/
theorem wireTo_okg {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) (hw : w.OKG) :
    (wireTo h w).OKG := by
  subst h
  exact hw

/-- The wire of the outside strings is not touched. -/
theorem wireTo_ext {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) :
    (wireTo h w).ext = w.ext := by
  subst h
  rfl

/-- The bound on depths is not touched. -/
theorem wireTo_maxDepth {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) :
    (wireTo h w).maxDepth = w.maxDepth := by
  subst h
  rfl

/-- A proof string under another marking of the same protocol. No field of a proof string reads
the marking, so the fields are the same. -/
def reAnn {loc : InteractiveOracleProof Y E} {A : RoundSplits loc.shape} (A' : RoundSplits loc.shape) (π : OneProtocolProof lam ⟨loc, A⟩) :
    OneProtocolProof lam ⟨loc, A'⟩ :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path⟩

/-- Carrying a proof string along the equation gives the same string. -/
theorem reAnn_eq {loc : InteractiveOracleProof Y E} {A A' : RoundSplits loc.shape} (h : A = A') (π : OneProtocolProof lam ⟨loc, A⟩) :
    (congrArg (BatchInteractiveOracleProof.mk loc) h ▸ π : OneProtocolProof lam ⟨loc, A'⟩) = reAnn A' π := by
  subst h
  rfl

/-- A plain part, carried along an equation between two markings of one shape. -/
def pbTo {s : Shape} {A A' : RoundSplits s} (e : A = A') (z : PlainPart s A) : PlainPart s A' := e ▸ z

/-- A plain part of the first round stays, if the first round's marking stays. -/
theorem pbTo_inl {r : Round} {s : Shape} (a : RAnn r) {A A' : RoundSplits s} (e : A = A')
    (h : ((a, A) : RoundSplits (r :: s)) = (a, A')) (x : a.P0 ⊕ a.Pj) :
    pbTo (s := r :: s) (A := (a, A)) (A' := (a, A')) h (Sum.inl x) = Sum.inl x := by
  subst e
  rfl

/-- A plain part of a later round is carried along the equation of the later rounds. -/
theorem pbTo_inr {r : Round} {s : Shape} (a : RAnn r) {A A' : RoundSplits s} (e : A = A')
    (h : ((a, A) : RoundSplits (r :: s)) = (a, A')) (q : PlainPart s A) :
    pbTo (s := r :: s) (A := (a, A)) (A' := (a, A')) h (Sum.inr q) = Sum.inr (pbTo e q) := by
  subst e
  rfl

/-- The compiled verifier of one slot does not change when the marking is replaced by an equal
one and wiring, string and the map on plain parts are carried along. -/
theorem verifyBS_ann {I X : Type} {L : BatchProtocol I X} (sMT sFS : ℕ) (t : Tag) (loc : InteractiveOracleProof Y E)
    (A A' : RoundSplits loc.shape) (h : A = A') (wq : ProtocolQueryLayout lam K ⟨loc, A⟩)
    (embS : (p : OPos loc.shape) → OSym loc.shape p → Body L)
    (embP : PlainPart loc.shape A → PlainPart (shapeOf L t) (annOf L t))
    (embP' : PlainPart loc.shape A' → PlainPart (shapeOf L t) (annOf L t))
    (hP : ∀ z, embP z = embP' (pbTo h z))
    (xin : Y → Option X) (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam ⟨loc, A⟩) :
    verifyOneProtocol sMT sFS t ⟨loc, A⟩ wq embS embP xin embE depthReq cms x π =
      verifyOneProtocol sMT sFS t ⟨loc, A'⟩ (wireTo (congrArg (BatchInteractiveOracleProof.mk loc) h) wq) embS embP' xin embE
        depthReq cms x (reAnn A' π) := by
  subst h
  have hE : embP = embP' := funext hP
  subst hE
  rfl

end

/-! ## The protocol of a description -/

/-- The protocol that is made from a description carries the marking "all rounds local". -/
theorem psofX_up (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : View → Bool) :
    (skeletonOverBothExternalStrings C ds a xs dec).up = BatchInteractiveOracleProof.ofProto (skeletonOverBothExternalStrings C ds a xs dec).up.loc :=
  congrArg (BatchInteractiveOracleProof.mk (skeletonOverBothExternalStrings C ds a xs dec).up.loc) (Twin.allLo_eq (SOf C ds))

/-- The library's map on plain parts of the rounds of a description is the carrying along the
equation between the two markings. -/
theorem embPL_eq (C : CK) : ∀ (ds : List RD) (q : PlainPart (uL C ds) (Twin.allLo (SL C ds))),
    embPL C ds q = pbTo (Twin.allLo_eq (SL C ds)) q
  | [], q => q.elim
  | _ :: ds, .inl x => (pbTo_inl _ (Twin.allLo_eq (SL C ds)) _ x).symm
  | _ :: ds, .inr q =>
    (congrArg Sum.inr (embPL_eq C ds q)).trans (pbTo_inr _ (Twin.allLo_eq (SL C ds)) _ q).symm

/-- The same for the whole shape, with the round in front. -/
theorem embPX_eq (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : View → Bool)
    (z : PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds))) :
    embPX (I := Unit) (RI := Unit) C ds a xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()) z =
      pbTo (Twin.allLo_eq (SOf C ds)) z := by
  cases z with
  | inl x => exact (pbTo_inl _ (Twin.allLo_eq (SL C ds)) _ x).symm
  | inr q =>
    exact (congrArg Sum.inr (embPL_eq C ds q)).trans
      (pbTo_inr _ (Twin.allLo_eq (SL C ds)) _ q).symm

/-- The whole wiring, for every description: Link's is the protocol's; Test and Batch have no
rounds. -/
def WkAny (D : XD) (dec : View → Bool) : QueryLayout 256 (D.L dec) :=
  WkX (D.K + 1) (wireTo (psofX_up D.C D.ds D.a D.xs dec)
    (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec))

/-- The whole wiring obeys the library's laws. Asked: the two conditions on the description. -/
theorem okgAny (D : XD) (dec : View → Bool)
    (hwork : (rds D.base).all (fun d => decide (d.entry.work ≤ 64)) = true)
    (hokx : okX D.ds D.a D.xs = true) : (WkAny D dec).OKG :=
  okgWkX D.C D.ds D.a D.xs dec (D.K + 1) _
    (wireTo_okg _ _ (wqX_okg D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec dec
      (okX_own D.ds D.a D.xs hokx) (M1RunTieP.okgOf D.base dec hwork)))
    (wireTo_ext _ _)
    (le_of_le_of_eq (le_max_right (maxDepth D.ds) D.a) (wireTo_maxDepth
      (psofX_up D.C D.ds D.a D.xs dec)
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)).symm)

/-- A typed string of the protocol as a Link string of the interface: the same fields. -/
def asLink (D : XD) (dec : View → Bool) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) :
    OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (D.L dec).link) :=
  reAnn _ π

/-- The compiled verifier of one slot, at the protocol, wiring and maps of a description, is the
compiled Link verifier of the whole wiring. -/
theorem vls_any (D : XD) (dec : View → Bool) (sMT : ℕ) (cm cm' : Dig 256)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) :
    verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) sMT 256 .link
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
      (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π
    = vLS (WkAny D dec) sMT 256 cm cm' (asLink D dec π) :=
  verifyBS_ann (L := D.L dec) sMT 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up.loc
    (Twin.allLo (SOf D.C D.ds)) (RoundSplits.allLocal (Twin.up (SOf D.C D.ds)))
    (Twin.allLo_eq (SOf D.C D.ds)) (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())) id
    (embPX_eq D.C D.ds D.a D.xs dec) (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π

/-! ## From the one hypothesis to the statement on traces, for every description -/

section
variable (D : XD) (dec : View → Bool)

/-- The one hypothesis. The protocol that is made from the description D and the decision dec is
round-by-round sound for the language Lg, with error counts that are each, as a share of the round's
challenge values, at most e. -/
def SoundLAny (Lg : Unit → (twoExternalStrings (D.L dec).wordLength (D.L dec).Symbol).Str → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ εL : Err (D.L dec).link.shape, Err.Below εL εs ∧ (D.L dec).link.Sound Lg εL

/-- The compiled Link verifier on a typed proof string under two roots given as bytes. -/
def theRunAny (r0 r1 : ByteArray) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) :
    TypedOracleComputation 256 (WkAny D dec).K (D.L dec) Bool :=
  vLS (WkAny D dec) (256 + 8 * D.base.plan.salt) 256 (bytesToDig r0) (bytesToDig r1)
    (asLink D dec π)

/-- What the library's run function evaluates after reader and typing is the compiled Link
verifier, with its typed queries answered by BLAKE2b on the format's strings. -/
theorem vx_any (r0 r1 : ByteArray) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) :
    VX D dec r0 r1 π = (theRunAny D dec r0 r1 π).det (famX D dec _root_.Fmt.oracle (D.K + 1)) :=
  (vx_eq D dec r0 r1 π).trans
    (congrArg (OComp.det (famX D dec _root_.Fmt.oracle (D.K + 1)))
      (vls_any D dec (256 + 8 * D.base.plan.salt) (bytesToDig r0) (bytesToDig r1) π))

/-- The named set of bad traces at the wiring of a description, made from error counts εL of the
protocol: a clash in a hash tree, a clash in a chain, or a lucky step (`linkBad`,
OnBytes/Slice/LinkClause.lean). The two other protocols of the interface have no rounds. -/
def badAny (εL : Err (D.L dec).link.shape) : Tc (WkAny D dec) → Prop :=
  linkBad (WkAny D dec) () εL () (fun _ _ _ => true)

variable {D dec}

/-- The named set is closed under adding queries. -/
theorem badAny_mono (εL : Err (D.L dec).link.shape) (tr tr' : Tc (WkAny D dec))
    (h : badAny D dec εL tr) : badAny D dec εL (tr ++ tr') :=
  linkBad_mono (WkAny D dec) () εL () (fun _ _ _ => true) tr tr' h

/-- Outside the named set what is read off a trace under an announced root never changes. -/
theorem badAny_stable (εL : Err (D.L dec).link.shape) (tr tr' : Tc (WkAny D dec)) (cm : Dig 256)
    (hB : ¬ badAny D dec εL (tr ++ tr')) (hann : Announced (WkAny D dec) tr cm) :
    extEnc (WkAny D dec) tr cm = extEnc (WkAny D dec) (tr ++ tr') cm :=
  linkBad_stable (WkAny D dec) () εL () (fun _ _ _ => true) tr tr' cm hB hann

variable (hwork : (rds D.base).all (fun d => decide (d.entry.work ≤ 64)) = true)
variable (hokx : okX D.ds D.a D.xs = true)
include hwork hokx

/-- The compiler's conclusion at the protocol and wiring of a description. -/
theorem linkAt_any (Lg : Unit → (twoExternalStrings (D.L dec).wordLength (D.L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (h : SoundLAny D dec Lg εs) : LinkAt (WkAny D dec) Lg εs :=
  let ⟨εL, hb, hs⟩ := h
  linkAt (WkAny D dec) Lg εs () εL () (fun _ _ _ => true) trivial hb trivial (fun _ _ => trivial) hs
    (psofX_local D.C D.ds D.a D.xs dec) (okgAny D dec hwork hokx)

/-- Under the typed random oracles an algorithm with at most t queries reaches the named set with
probability at most t e + 2 t^2 / 2^256, if every error count, as a share of its round's challenge
values, is at most e. -/
theorem badAny_rare (εL : Err (D.L dec).link.shape) (εs : ℝ≥0∞) (hb : Err.Below εL εs) (β : Type)
    (A : TypedOracleComputation 256 (WkAny D dec).K (D.L dec) β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | badAny D dec εL o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  linkBad_rare (WkAny D dec) () εL () (fun _ _ _ => true) εs trivial hb trivial
    (fun _ _ => trivial) (okgAny D dec hwork hokx) β A t hA

/-- A yes of the compiled Link verifier under any fixed oracle functions, and the named set. If
a trace holds the run's queries with these functions' answers and shows none of the three events,
the language holds of the two strings that are read off it under the two roots. Asked: the protocol
is round-by-round sound for the language with the error counts that the set is made from. Nothing is
asked on the size of the counts: with large counts the statement is true and empty. It says
something only together with `badAny_rare` at the same counts and a small e. In full:
OnBytes/Slice/README.md, "TopAny.lean". -/
theorem badAny_run (Lg : Unit → (twoExternalStrings (D.L dec).wordLength (D.L dec).Symbol).Str → Prop)
    (εL : Err (D.L dec).link.shape) (hs : (D.L dec).link.Sound Lg εL)
    (g : Fam (spec 256 (WkAny D dec).K (D.L dec))) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) (hv : (theRunAny D dec r0 r1 π).det g = true)
    (tr : Tc (WkAny D dec)) (hsub : trail g (theRunAny D dec r0 r1 π) ⊆ tr)
    (hB : ¬ badAny D dec εL tr) :
    Lg () (extEnc (WkAny D dec) tr (bytesToDig r0), extEnc (WkAny D dec) tr (bytesToDig r1)) :=
  linkBad_run (WkAny D dec) (okgAny D dec hwork hokx) Lg () εL () (fun _ _ _ => true) hs
    (psofX_local D.C D.ds D.a D.xs dec) g _ _ _ _ (asLink D dec π) hv tr hsub hB

/-- The experiment in one world, at the protocol and wiring of a description. -/
theorem experiment_any (Lg : Unit → (twoExternalStrings (D.L dec).wordLength (D.L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (h : SoundLAny D dec Lg εs) (A : TypedOracleComputation 256 (WkAny D dec).K (D.L dec) (LinkOut 256 (D.L dec)))
    (t : ℕ) (hA : A.QueryBound t) :
    pr (linkExp (WkAny D dec) (256 + 8 * D.base.plan.salt) 256 A).withTrace.law
        (linkWin (WkAny D dec) Lg) ≤
      ((t + tVQB (WkAny D dec).Lk (WkAny D dec).depthReq : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + tVQB (WkAny D dec).Lk (WkAny D dec).depthReq + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  link_experiment (WkAny D dec) (okgAny D dec hwork hokx) Lg εs (linkAt_any hwork hokx Lg εs h) _ _
    A t hA

omit hwork hokx in
/-- The bytes. A file that the library's run function accepts: the copy's root; the typed string
that reader and typing give; the compiled verifier's yes under BLAKE2b on the format's strings. -/
theorem accepted_any (r0 file : ByteArray) (h : runEntry D dec r0 file = .accepted) :
    ∃ r1 rest π, readHead file = some (r1, rest) ∧
      (_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (D.atR r0 r1) rest).bind
        (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) = some π ∧
      (theRunAny D dec r0 r1 π).det (famX D dec _root_.Fmt.oracle (D.K + 1)) = true := by
  obtain ⟨r1, rest, π, hr, hπ, hv⟩ := runEntry_accepted D dec r0 file h
  exact ⟨r1, rest, π, hr, hπ, (vx_any D dec r0 r1 π).symm.trans hv⟩

/-- The statement on traces for a file that the library's run function accepts, of the named
set. If the protocol is round-by-round sound for Lg with the error counts εL, then for every
accepted file and every trace that holds the compiled verifier's queries with BLAKE2b's answers and
shows none of the three events of `badAny D dec εL`, Lg holds of the two strings that are read off
the trace. See OnBytes/Slice/README.md, "TopAny.lean", for what this does not say, for the size of
the counts and for which trace to take. -/
theorem top_any (Lg : Unit → (twoExternalStrings (D.L dec).wordLength (D.L dec).Symbol).Str → Prop)
    (εL : Err (D.L dec).link.shape) (hs : (D.L dec).link.Sound Lg εL) :
    ∀ r0 file, runEntry D dec r0 file = .accepted →
      ∃ r1 rest π, readHead file = some (r1, rest) ∧
        (_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (D.atR r0 r1) rest).bind
          (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) = some π ∧
        ∀ tr : Tc (WkAny D dec),
          trail (famX D dec _root_.Fmt.oracle (D.K + 1)) (theRunAny D dec r0 r1 π) ⊆ tr →
          ¬ badAny D dec εL tr →
          Lg () (extEnc (WkAny D dec) tr (bytesToDig r0),
            extEnc (WkAny D dec) tr (bytesToDig r1)) := by
  intro r0 file ha
  obtain ⟨r1, rest, π, hr, hπ, hv⟩ := accepted_any r0 file ha
  exact ⟨r1, rest, π, hr, hπ, badAny_run hwork hokx Lg εL hs _ r0 r1 π hv⟩

end

/-! ## From "the compiled verifier accepts" to the statement on traces -/

open OnBytes.Tie (xdOf withinX CompiledAcceptsX smallFX readInX_compiled entrySpec entryStatement
  entry_check_compiled)

section
variable (D : XD) (dec : View → Bool)

/-- What is said of a typed string π under the roots r0 and r1, given a set Bad of traces. The
compiled Link verifier of the whole wiring says yes on π, with its typed queries answered by BLAKE2b
on the format's strings. For every trace outside Bad that holds this run's queries and answers, Lg
holds of the two strings that are read off the trace under the two roots. The theorems below have it
at the named set `badAny`. -/
def LgBehind (Bad : Tc (WkAny D dec) → Prop)
    (Lg : Unit → (twoExternalStrings (D.L dec).wordLength (D.L dec).Symbol).Str → Prop) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) : Prop :=
  (theRunAny D dec r0 r1 π).det (famX D dec Fmt.oracle (D.K + 1)) = true ∧
  ∀ tr : Tc (WkAny D dec),
    trail (famX D dec Fmt.oracle (D.K + 1)) (theRunAny D dec r0 r1 π) ⊆ tr → ¬ Bad tr →
    Lg () (extEnc (WkAny D dec) tr (bytesToDig r0), extEnc (WkAny D dec) tr (bytesToDig r1))

end

/-- "The compiled verifier accepts what was read" is a yes of the compiled Link verifier of the
whole wiring, on the string that the library's typing makes from what was read. -/
theorem compiled_run (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (r0 r1 : ByteArray) (o : Fmt.ChainOut)
    (h : CompiledAcceptsX S stm dec r0 r1 o) :
    ∃ π, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
        (xdOf S stm).xs dec o = some π ∧
      (theRunAny (xdOf S stm) dec r0 r1 π).det
        (famX (xdOf S stm) dec Fmt.oracle ((xdOf S stm).K + 1)) = true :=
  let ⟨π, hty, hπ⟩ := h
  ⟨π, hty, (congrArg (OComp.det (famX (xdOf S stm) dec Fmt.oracle ((xdOf S stm).K + 1)))
    (vls_any (xdOf S stm) dec (256 + 8 * S.base.plan.salt) (bytesToDig r0) (bytesToDig r1)
      π)).symm.trans hπ⟩

/-- From "the compiled verifier accepts what was read" to the language, of the named set, under
the one hypothesis with its error counts εL. The set does not depend on roots and chain. See
OnBytes/Slice/README.md, "TopAny.lean", for what this does not say, for the size of the counts and
for which trace to take. -/
theorem compiled_top (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool)
    (hwork : (rds (xdOf S stm).base).all (fun d => decide (d.entry.work ≤ 64)) = true)
    (hokx : okX (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S stm).L dec).wordLength ((xdOf S stm).L dec).Symbol).Str → Prop)
    (εL : Err ((xdOf S stm).L dec).link.shape) (hs : ((xdOf S stm).L dec).link.Sound Lg εL) :
    ∀ r0 r1 o, CompiledAcceptsX S stm dec r0 r1 o →
      ∃ π, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
          (xdOf S stm).xs dec o = some π ∧
        LgBehind (xdOf S stm) dec (badAny (xdOf S stm) dec εL) Lg r0 r1 π := by
  intro r0 r1 o ha
  obtain ⟨π, hty, hv⟩ := compiled_run S stm dec r0 r1 o ha
  exact ⟨π, hty, hv, badAny_run hwork hokx Lg εL hs _ r0 r1 π hv⟩

/-! ## The two conditions on the description follow from the limits test -/

/-- In a list of rounds that meets the format's conditions on rounds, no round asks for more than 64
bits of work. -/
private theorem work_of_roundsOk (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
      Fmt.roundsOk P noRand firstTree after sent rs = true → ∀ r ∈ rs, r.entry.work ≤ 64
  | [], _, _, _, _, hr => absurd hr List.not_mem_nil
  | r₀ :: rs, after, sent, h, r, hr => by
    rw [Fmt.roundsOk, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hr with rfl | hr'
    · -- The bound is one of the conditions on a single round.
      have h1 := h.1
      simp only [Fmt.Round.ok, Bool.and_eq_true, decide_eq_true_eq] at h1
      omega
    · exact work_of_roundsOk P noRand firstTree rs _ _ h.2 r hr'

/-- The entry of each round in the library's form is the entry of one of the format's rounds. -/
private theorem entry_of_rdsFrom (S : Fmt.Spec) :
    ∀ (rs : List Fmt.Round) (sent : Nat),
      ∀ d ∈ rdsFrom S sent rs, ∃ r ∈ rs, d.entry = r.entry
  | [], _, _, hd => absurd hd List.not_mem_nil
  | r :: rs, sent, d, hd => by
    rw [rdsFrom] at hd
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact ⟨r, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨r', hr', e⟩ := entry_of_rdsFrom S rs _ d hd'
      exact ⟨r', List.mem_cons.mpr (Or.inr hr'), e⟩

/-- A chain's description within the library's limits asks in no round for more than 64 bits of
work. -/
theorem work_of_ok (S : Fmt.Spec) (h : PQ.ok S = true) :
    (rds S).all (fun d => decide (d.entry.work ≤ 64)) = true := by
  -- The limits hold the format's conditions, and these hold the conditions on the rounds.
  have hS : S.ok = true := by
    simp only [PQ.ok, Bool.and_eq_true] at h
    exact h.1.1.1.1
  have hr : Fmt.roundsOk S.plan S.rand.isNone S.firstTree false 0 S.rounds = true := by
    cases hq : Fmt.roundsOk S.plan S.rand.isNone S.firstTree false 0 S.rounds with
    | true => rfl
    | false => simp [Fmt.Spec.ok, hq] at hS
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨r, hrs, e⟩ := entry_of_rdsFrom S S.rounds 0 d hd
  rw [decide_eq_true_eq, e]
  exact work_of_roundsOk _ _ _ S.rounds _ _ hr r hrs

/-- The limits test holds the library's limits, at every function for the statement: none of the
limits reads the statement's function. -/
theorem within_ok (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (hw : withinX S = true) : (xdOf S stm).ok = true := by
  unfold withinX at hw
  simp only [Bool.and_eq_true] at hw
  exact hw.1.1

/-- Within the limits test no round asks for more than 64 bits of work. -/
theorem within_work (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (hw : withinX S = true) :
    (rds (xdOf S stm).base).all (fun d => decide (d.entry.work ≤ 64)) = true := by
  have h := within_ok S stm hw
  unfold XD.ok at h
  simp only [Bool.and_eq_true] at h
  exact work_of_ok _ h.1.1

/-- Within the limits test the openings of the stored tables pass the library's test on them. -/
theorem within_okx (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (hw : withinX S = true) : okX (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs = true := by
  have h := within_ok S stm hw
  unfold XD.ok at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-! ## From what the program has accepted to the statement on traces -/

/-- From a chain that a session of the program has read, and on whose view the decision says yes,
to the language. The chain opens two stored tables with the roots r0 and r1, its description is
within the limits test, and file and description are within the bounds `smallFX`. Under the one
hypothesis with its error counts εL: the typing makes a string from what the session has read, and
`LgBehind` holds of it at the named set. See OnBytes/Slice/README.md, "TopAny.lean", for what this
does not say, for the size of the counts and for which trace to take. -/
theorem session_top (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (hw : withinX S = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S stm).L dec).wordLength ((xdOf S stm).L dec).Symbol).Str → Prop)
    (εL : Err ((xdOf S stm).L dec).link.shape) (hs : ((xdOf S stm).L dec).link.Sound Lg εL) :
    ∀ r0 r1 : ByteArray, r0.size = 32 → r1.size = 32 → S.base.statement = stm r0 r1 →
      (∀ t ∈ S.stored.flatten,
        Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0)) →
      ∀ (s : Session) (b : ByteArray) (i : ℕ), smallFX S b = true →
      ∀ (r : ChainRead) (s' : Session), readIn S b i s = some (r, s') → dec r.view = true →
      ∃ π, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
          (xdOf S stm).xs dec r.out = some π ∧
        LgBehind (xdOf S stm) dec (badAny (xdOf S stm) dec εL) Lg r0 r1 π :=
  fun r0 r1 s0 s1 hst hroot s b i hsm r s' e hdec =>
    compiled_top S stm dec (within_work S stm hw) (within_okx S stm hw) Lg εL hs r0 r1 r.out
      (readInX_compiled S stm dec r0 r1 s0 s1 hw hst hroot s b i hsm r s' e hdec)

/-- From a yes of the program's check of an entry file to the language. The parameters, the first
table's name and the further table's name fix the description S and the block whose decision the
program takes (`entrySpec`). S is within the limits test. Asked: the one hypothesis with its error
counts εL, at the protocol made from S and that decision. For every file within the bounds `smallFX`
on which the check says yes with that further table: the reader `readIn` reads a chain under S from
some byte offset j of the file (not shown to be the one `Entry.check` used), the typing makes a
string from what was read, and `LgBehind` holds of it at the named set, under the two tables' roots.
The further table's name is in the file, and the named set is made from a description that holds it:
see OnBytes/Slice/README.md, "TopAny.lean", also for the size of the counts and for which trace to
take. -/
theorem check_top (params : ByteArray) (p : Params.Link) (hp : Params.Link.read params = some p)
    (first further : Params.TableName) (block : Blk Unit) (S : Fmt.SpecX)
    (hS : entrySpec p first further = some (block, S)) (hw : withinX S = true)
    (h0 : first.root.size = 32)
    (Lg : Unit → (twoExternalStrings ((xdOf S (entryStatement first further)).L
                    (block.decides (Entry.start p))).wordLength ((xdOf S (entryStatement first further)).L
                             (block.decides (Entry.start p))).Symbol).Str → Prop)
    (εL : Err ((xdOf S (entryStatement first further)).L
      (block.decides (Entry.start p))).link.shape)
    (hs : ((xdOf S (entryStatement first further)).L
      (block.decides (Entry.start p))).link.Sound Lg εL) :
    ∀ file : ByteArray, Entry.check params first file = .ok further → smallFX S file = true →
      ∃ (j : ℕ) (r : ChainRead) (s' : Session) (π : _),
        readIn S file j Session.start = some (r, s') ∧
        toBPrfX S.base.plan.salt S.base.cfg (xdOf S (entryStatement first further)).C
          (xdOf S (entryStatement first further)).ds (xdOf S (entryStatement first further)).a
          (xdOf S (entryStatement first further)).xs (block.decides (Entry.start p)) r.out =
            some π ∧
        LgBehind (xdOf S (entryStatement first further)) (block.decides (Entry.start p))
          (badAny (xdOf S (entryStatement first further)) (block.decides (Entry.start p)) εL) Lg
          first.root further.root π := by
  have h4 := compiled_top S (entryStatement first further)
    (block.decides (Entry.start p)) (within_work S _ hw) (within_okx S _ hw) Lg εL hs
  intro file hc hsm
  obtain ⟨p', block', S', j, r, s', hp', hS', hrd, himp⟩ :=
    entry_check_compiled params first further file hc
  -- the check has read the same parameters, so it has made the same description and block
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  obtain ⟨rfl, rfl⟩ : block = block' ∧ S = S' := Prod.mk.inj (Option.some.inj (hS.symm.trans hS'))
  obtain ⟨π, hty, hL⟩ := h4 _ _ _ (himp hw hsm h0)
  exact ⟨j, r, s', π, hrd, hty, hL⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.verifyBS_ann
#print axioms OnBytes.Slice.psofX_up
#print axioms OnBytes.Slice.okgAny
#print axioms OnBytes.Slice.vls_any
#print axioms OnBytes.Slice.linkAt_any
#print axioms OnBytes.Slice.experiment_any
#print axioms OnBytes.Slice.accepted_any
#print axioms OnBytes.Slice.badAny_mono
#print axioms OnBytes.Slice.badAny_stable
#print axioms OnBytes.Slice.badAny_rare
#print axioms OnBytes.Slice.badAny_run
#print axioms OnBytes.Slice.top_any
#print axioms OnBytes.Slice.compiled_top
#print axioms OnBytes.Slice.within_work
#print axioms OnBytes.Slice.within_okx
#print axioms OnBytes.Slice.session_top
#print axioms OnBytes.Slice.check_top
