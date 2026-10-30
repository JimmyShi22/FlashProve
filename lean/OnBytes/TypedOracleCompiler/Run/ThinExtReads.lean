-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
TWO: OnBytes/TypedOracleCompiler/Run/ThinExtReads.lean: THE LIBRARY's FILE OF THE SAME NAME SAID AGAIN OVER
OnBytes/TypedOracleCompiler (a list of trees a round; a leaf's body a parameter of the interface). It is the third
of the three later run forms of the evaluable verifier: verifyPX, with its tie verifyPX_eq to
OnBytes/TypedOracleCompiler's verifyPR, and thin_ext: verifyPX at the mask of a one-to-one numbering =
(OnBytes/TypedOracleCompiler's verifyOneProtocol ..).det g.
TURNED WITH THE ROAD, as strictP | afterP in ThinDefs.lean: strictPX (one conjunct more, the last:
no string behind the slot's value where the chain has not joined), afterPX (it hands π.rsalt to
reqPartB).
WHAT IS SAID AGAIN AS TEXT: forestsOfX, verifyPX; Spec.verifyPX_eq, verifyPX_eq; Spec.thin_ext,
thin_ext. Nothing had to be turned for the list of trees: the external oracles' wiring (WireE) is
the library's own in OnBytes/TypedOracleCompiler too.
WHAT IS LEFT TO THE LIBRARY's OWN MODULE (imported beside; it stands on no turned type): maskOf,
testBit_maskOf, maskBit, maskBit_eq, idx2, idx2_inj.
WHAT IS NOT SAID. The walk over ALL positions of the external oracles (we.all), twice, stays: the
test at each is a look at a bit, the walk is no shorter. The head below is the library's, kept.

Run/ThinExtReads.lean: the evaluable form of the compiled verifier with a fast test "is this
position of the external oracles read?": verifyPX. Definitions, statements
(Run.Thin.Spec.verifyPX_eq, thin_ext) and proofs. For protocols with external oracles of real sizes.

Why. Run/ThinReads.lean's verifyPR walks all positions of the external oracles twice (the strict
format; the checks) and asks at each "is it read?" by a search in the finite set of the positions
read: the work is (positions) times (reads). Here the set is turned once into one number (bit "idx
p" for each member p), and the test is a look at a bit. ("Thin" in names: the evaluable form,
Run/ThinDefs.lean.)

Sources.  Run/ThinDefs.lean's strictP; Run/ThinReads.lean's forestsOfR, afterPR, verifyPR.

1. What the file contains.
     maskOf idx R         The number. testBit_maskOf: its bit i is set exactly if some member has
                          idx = i.
     maskBit idx m p      The test: the bit "idx p" of the number m. maskBit_eq: for idx one to one,
                          at m := maskOf idx R, it is membership in R.
     strictPX, forestsOfX, afterPX, verifyPX mk tst ..
                          The four functions named under Sources with, for the external oracles, in
                          the place of membership in the set: mk : Finset E.Pos → M (what is made of
                          the set, once; it is handed on as a value) and tst : M → E.Pos → Bool (the
                          test).
     idx2 n, idx2_inj     The numbering of the positions of two strings of length n (Iop's twoExternalStrings):
                          the first string's, then the second's.
   Why two functions and not one test "Finset E.Pos → E.Pos → Bool": a function of two arguments
   that begins "let m := ..; fun p => .." is compiled as one function of both, and makes m anew at
   every p.
2. What is checked when the file compiles.  Only the types and the proofs.
3. Theorems.
     verifyPX_eq          If tst (mk R) p is membership of p in R, for all R, p: verifyPX mk tst ..
                          = verifyPR ..
     thin_ext             For idx one to one: verifyPX (fun _ => L) g (maskOf idx) (maskBit idx)
                          L.early L.late .. = (Compile.Batch.verifyOneProtocol .. P.up ..).det g. There is no
                          other hypothesis.
4. What is not claimed. Nothing on time: what was measured is written down nowhere in this
development. Nothing on a protocol or on the conditions on a wiring. NO STATEMENT ON SOUNDNESS
FOLLOWS.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.ThinExtReads
import OnBytes.TypedOracleCompiler.Run.ThinReads

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin
export _root_.Run.Thin (maskOf testBit_maskOf maskBit maskBit_eq idx2 idx2_inj)

/-! ### The verifier -/

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ()))) {Y : Type}
  {E : ExtSpec} {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)

def strictPX (sMT sFS : ℕ) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  haveI := wq.decO
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ cntP P.S rts) &&
    sSP sMT P.S P.ann wq.sh rts (fun p => decide (p ∈ R)) π.opens &&
    sExtP sMT wq.ext (tst (mk Re)) π.ext &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty) &&
    (ph.slotVal.isSome || π.rsalt.isEmpty)

def forestsOfX (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    Option (List (Forest lam (Lf ()))) :=
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match forestsR Lf P.S P.ann wq.sh embS rts R π.opens,
        forestExtP Lf wq.ext embE cms (tst (mk Re)) π.ext with
  | some a, some b => some (a ++ b)
  | _, _ => none

def afterPX (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfX Lf mk tst P wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatP Lf Fs).length ≤ wq.nOpen ∧
          (flatP Lf Fs).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot
            π.path π.rsalt ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- THE VERIFIER, WITH A TEST OF ITS OWN FOR THE EXTERNAL ORACLES' POSITIONS. -/
def verifyPX (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if strictPX mk tst sMT sFS P wq depthReq x π ρ rts ph then
      afterPX Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph
    else false

def Spec.verifyPX_eq : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ()))) (Y : Type)
      (E : ExtSpec) (M : Type) (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool) (early : X → X)
      (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
      (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
      (x : Y) (π : OneProtocolProof lam P.up),
    (∀ R p, tst (mk R) p = true ↔ p ∈ R) →
    verifyPX Lf g mk tst early late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyPR Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π

theorem verifyPX_eq : Spec.verifyPX_eq := by
  intro I X lam K Lf g Y E M mk tst early late sMT sFS t P wq embS embP xin embE depthReq cms x π h
  letI : DecidableEq E.Pos := wq.ext.dec
  have e : ∀ R, tst (mk R) = fun p => decide (p ∈ R) := fun R =>
    funext fun p => Bool.eq_iff_iff.2 ((h R p).trans decide_eq_true_iff.symm)
  unfold verifyPX verifyPR strictPX afterPX afterPR forestsOfX forestsOfR strictP
  simp only [e]
  rfl

def Spec.thin_ext : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K L)) (Y : Type) (E : ExtSpec)
      (idx : E.Pos → ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    Function.Injective idx →
    verifyPX (fun _ => L) g (maskOf idx) (maskBit idx) L.early L.late sMT sFS t P wq embS embP
        xin embE depthReq cms x π =
      (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g

theorem thin_ext : Spec.thin_ext := fun I X lam K L g Y E idx sMT sFS t P wq embS embP xin embE
    depthReq cms x π hi =>
  letI : DecidableEq E.Pos := wq.ext.dec
  (verifyPX_eq I X lam K (fun _ => L) g Y E ℕ (maskOf idx) (maskBit idx) L.early L.late sMT sFS t P
      wq embS embP xin embE depthReq cms x π (fun R p => maskBit_eq idx hi R p)).trans
    (thin_reads I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π)

end TypedOracleCompiler.Run.Thin
