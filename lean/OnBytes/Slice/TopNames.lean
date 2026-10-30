-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/TopNames.lean: one named set of bad traces for all statements of a chain.


OnBytes/Slice/TopAny.lean names, for a description, a decision and error counts, a set of bad traces
(`badAny`) outside which a yes of the compiled verifier means that the language holds. That set is
made from the description. A description holds the chain's statement, the statement of an entry's
chain holds the two tables' roots, and the further table's root is in the file. This file shows
that the set at one statement serves all statements.

Why this holds. The named set is made from the protocol, the wiring and the error counts. Protocol
and wiring are made from the description's field, rounds, first tree's number and openings of stored
tables, and not from its statement (`Run.rds_congr`, Run/PlanPullM1.lean, for the rounds in the
library's form). The statement enters the typed oracle functions that BLAKE2b induces, and nothing
else. The statement on traces holds for a run under any typed oracle functions (`badAny_run`,
OnBytes/Slice/TopAny.lean).

The types. The protocols of two descriptions that differ in the statement alone are equal. While the
rounds are a variable they are not equal by evaluation. So the typed string and the oracle functions
are carried along the equation (`accept_to`). The theorems speak of typed oracle functions g that
are equal, by `HEq`, to a family that `famX` gives: g is the family that BLAKE2b induces at the
description with the true statement, at the type that belongs to the description from which the set
is made.

Main definitions: `reStated`, `LgUnder`.
Main theorems.
 `stated_top`      one named set for a description with any statement, and any function that gives
                   the statement's bytes from the roots.









Not claimed.
 All that OnBytes/Slice/README.md, "TopAny.lean", does not claim.
 Whether a given list with BLAKE2b's
 answers shows one of the set's three events no theorem says. Nothing is asked here on the size of
 the counts: with large counts the statements are true and empty, and they say something only
 together with `badAny_rare` at the same counts and a small e. Which trace to take is the reader's
 duty, as that page says.
 Nothing on the table with its record: the key holds the record's answers and seeds, which depend
 on the table's name, and the decision may read them.
 That the limits test holds at every statement if it holds at one. It is a hypothesis for each pair
 of names, and can be evaluated.
-/
import OnBytes.Slice.TopAny
import Run.PlanPullM1

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ
open scoped ENNReal
open OnBytes.Tie (xdOf inFile withinX CompiledAcceptsX smallFX entrySpec entryStatement
  entry_check_compiled)

/-! ## A description with another statement -/

/-- A description with another statement. -/
def reStated (S : Fmt.SpecX) (x : ByteArray) : Fmt.SpecX :=
  ⟨{ S.base with statement := x }, S.stored⟩

/-! ## The run under any typed oracle functions -/

/-- What is said of a typed string π under the roots r0 and r1 and the typed oracle functions g,
given a set Bad of traces. The compiled Link verifier of the whole wiring says yes on π under g.
For every trace outside Bad that holds this run's queries and answers, Lg holds of the two strings
that are read off the trace under the two roots. At the functions that BLAKE2b induces this is
`LgBehind`. The theorems below have it at the named set `badAny`. -/
def LgUnder (D : XD) (dec : View → Bool) (Bad : Tc (WkAny D dec) → Prop)
    (Lg : Unit → (twoExternalStrings (D.L dec).wordLength (D.L dec).Symbol).Str → Prop)
    (g : Fam (spec 256 (WkAny D dec).K (D.L dec))) (r0 r1 : ByteArray)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) : Prop :=
  (theRunAny D dec r0 r1 π).det g = true ∧
  ∀ tr : Tc (WkAny D dec), trail g (theRunAny D dec r0 r1 π) ⊆ tr → ¬ Bad tr →
    Lg () (extEnc (WkAny D dec) tr (bytesToDig r0), extEnc (WkAny D dec) tr (bytesToDig r1))

/-- A yes of the compiled verifier of one slot, carried along an equation between two lists of
rounds. The number of blocks is a function Kf of the rounds. Typed string and typed oracle functions
go along; of the functions this is said by an equation between terms of two types. -/
theorem accept_to (C : CK) (Kf : List RD → ℕ) (chal : ∀ K e k, (Fin K → Dig 256) → C.Ch e k)
    (a : ℕ) (xs : List XO) (dec : View → Bool) (ds ds' : List RD) (hds : ds' = ds)
    (salt : ℕ) (cfg : ByteArray) (sMT : ℕ) (cm cm' : Dig 256) (o : Fmt.ChainOut)
    (g' : Fam (spec 256 (Kf ds' + 1) (Lu C ds' a xs dec)))
    (π' : OneProtocolProof 256 (skeletonOverBothExternalStrings C ds' a xs dec).up) (hty : toBPrfX salt cfg C ds' a xs dec o = some π')
    (hv : (verifyOneProtocol (lam := 256) (K := Kf ds' + 1) (L := Lu C ds' a xs dec) sMT 256 .link
      (skeletonOverBothExternalStrings C ds' a xs dec).up (wqX C (Kf ds') (chal (Kf ds')) ds' a xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPX C ds' a xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
      (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π').det g' = true) :
    ∃ (π : OneProtocolProof 256 (skeletonOverBothExternalStrings C ds a xs dec).up) (g : Fam (spec 256 (Kf ds + 1) (Lu C ds a xs dec))),
      toBPrfX salt cfg C ds a xs dec o = some π ∧ HEq g g' ∧
      (verifyOneProtocol (lam := 256) (K := Kf ds + 1) (L := Lu C ds a xs dec) sMT 256 .link
        (skeletonOverBothExternalStrings C ds a xs dec).up (wqX C (Kf ds) (chal (Kf ds)) ds a xs dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embPX C ds a xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) (fun s => some (.inl s)) 0 [cm, cm'] () π).det g = true := by
  subst hds
  exact ⟨π', g', hty, HEq.rfl, hv⟩

/-- One named set for all statements. S is within the limits test. Asked: the one hypothesis
with its error counts εL, at the protocol made from S and dec. The named set is the one at S, stm₀
and εL: it does not depend on the statement x, the function stm, the roots and the chain. If the
compiled verifier accepts what was read at the description S with the statement x, then the typing
at S makes a string from what was read, and `LgUnder` holds of it at that set and at the typed
oracle functions that BLAKE2b induces for the description with the statement x. For the size of the
counts and for which trace to take see OnBytes/Slice/README.md, "TopAny.lean". -/
theorem stated_top (S : Fmt.SpecX) (stm₀ : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (hw : withinX S = true)
    (Lg : Unit → (twoExternalStrings ((xdOf S stm₀).L dec).wordLength ((xdOf S stm₀).L dec).Symbol).Str → Prop)
    (εL : Err ((xdOf S stm₀).L dec).link.shape) (hs : ((xdOf S stm₀).L dec).link.Sound Lg εL) :
    ∀ (x : ByteArray) (stm : ByteArray → ByteArray → ByteArray) (r0 r1 : ByteArray)
      (o : Fmt.ChainOut), CompiledAcceptsX (reStated S x) stm dec r0 r1 o →
      ∃ π g, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm₀).C (xdOf S stm₀).ds
          (xdOf S stm₀).a (xdOf S stm₀).xs dec o = some π ∧
        HEq g (famX (xdOf (reStated S x) stm) dec Fmt.oracle ((xdOf (reStated S x) stm).K + 1)) ∧
        LgUnder (xdOf S stm₀) dec (badAny (xdOf S stm₀) dec εL) Lg g r0 r1 π := by
  have hwork := within_work S stm₀ hw
  have hokx := within_okx S stm₀ hw
  intro x stm r0 r1 o ha
  obtain ⟨π', hty', hv'⟩ := ha
  obtain ⟨π, g, hty, hg, hv⟩ := accept_to (ckP S.base.plan.field)
    (kMax fun e k => (bsRound S.base.plan.field e k).b) (fun K => chalP S.base.plan.field K)
    (xdOf S stm₀).a (xdOf S stm₀).xs dec (rds (inFile S.base)) (rds (inFile (reStated S x).base))
    (_root_.Run.rds_congr _ _ rfl rfl) S.base.plan.salt S.base.cfg (256 + 8 * S.base.plan.salt)
    (bytesToDig r0) (bytesToDig r1) o (famX (xdOf (reStated S x) stm) dec Fmt.oracle _) π' hty' hv'
  have hrun : (theRunAny (xdOf S stm₀) dec r0 r1 π).det g = true :=
    (congrArg (OComp.det g) (vls_any (xdOf S stm₀) dec (256 + 8 * S.base.plan.salt)
      (bytesToDig r0) (bytesToDig r1) π)).symm.trans hv
  exact ⟨π, g, hty, hg, hrun, badAny_run hwork hokx Lg εL hs g r0 r1 π hrun⟩





end OnBytes.Slice

#print axioms OnBytes.Slice.stated_top
