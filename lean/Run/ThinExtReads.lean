-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinExtReads.lean: the evaluable form of the compiled verifier with a fast test "is this
position of the external oracles read?": `verifyPX`. Definitions, statements
(`Run.Thin.Spec.verifyPX_eq`, `Run.Thin.Spec.thin_ext`) and proofs. For protocols with external
oracles of real sizes.

The external oracles (`ExtSpec`, Iop/InteractiveOracleProof.lean) are strings that are fixed before the protocol
starts; the positions read in them are the finite set `P.extReads x ρ`.

Why. Run/ThinReads.lean's `verifyPR` walks the list `wq.ext.all` of the external oracles' positions
twice and asks "is it read?", in the checks at each position of the list, in the strict format where
an opening stands, by a search in the finite set of the positions read: the work is (positions)
times (reads). Here the set is turned, once for each of the two walks, into one number (bit `idx p`
for each member p), and the test is a look at a bit. ("Thin" in names: the evaluable form,
Run/ThinDefs.lean.)

Sources. Run/ThinDefs.lean's `strictP`; Run/ThinReads.lean's `forestsOfR`, `afterPR`, `verifyPR`.

1. What the file contains.
     `maskBit_eq`: for idx one to one, at `m := maskOf idx R`, `maskBit idx m p` is membership in R.
     `strictPX`, `forestsOfX`, `afterPX`, `verifyPX mk tst ..`: The four functions named under
       Sources with, for the external oracles, in the place of membership in the set:
       `mk : Finset E.Pos → M` (what is made of the set, once in `strictPX` and once in
       `forestsOfX`; it is handed on as a value) and `tst : M → E.Pos → Bool` (the test).
   Why two functions and not one test `Finset E.Pos → E.Pos → Bool`: a function of two arguments
   that begins "let m := ..; fun p => .." is compiled as one function of both, and makes m anew at
   every p.
2. What is checked when the file compiles. Only the types and the proofs.
3. Theorems.
     `verifyPX_eq`: If `tst (mk R) p` is membership of p in R, for all R, p:
       `verifyPX mk tst .. = verifyPR ..`
     `thin_ext`: For idx one to one:
       `verifyPX (fun _ => L) g (maskOf idx) (maskBit idx) L.early L.late ..` is
       `(Compile.Batch.verifyOneProtocol .. P.up ..).det g`. There is no other hypothesis beside whatever the
       arguments hold as proofs.
4. What is not claimed. Nothing on time: what was measured is written down nowhere in Run/ or Fmt/.
   Nothing on a protocol or on the conditions on a wiring. No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ThinReads

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

/-! ### A finite set as one number -/

/-- The number with bit `idx p` set for each member p of R. -/
def maskOf {α : Type} (idx : α → ℕ) (R : Finset α) : ℕ := R.fold (· ||| ·) 0 fun p => 2 ^ idx p

theorem testBit_maskOf {α : Type} [DecidableEq α] (idx : α → ℕ) (i : ℕ) (R : Finset α) :
    (maskOf idx R).testBit i = true ↔ ∃ p ∈ R, idx p = i := by
  unfold maskOf
  induction R using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.fold_insert ha, Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq, Finset.mem_insert, exists_eq_or_imp]

/-- The test: a look at a bit. -/
def maskBit {α : Type} (idx : α → ℕ) (m : ℕ) (p : α) : Bool := m.testBit (idx p)

theorem maskBit_eq {α : Type} [DecidableEq α] (idx : α → ℕ) (hi : Function.Injective idx)
    (R : Finset α) (p : α) :
    maskBit idx (maskOf idx R) p = true ↔ p ∈ R := by
  unfold maskBit
  rw [testBit_maskOf]
  exact ⟨fun ⟨q, hq, e⟩ => hi e ▸ hq, fun h => ⟨p, h, rfl⟩⟩

/-- The positions of two strings of length n (`twoExternalStrings`, Iop/InteractiveOracleProof.lean), numbered. -/
def idx2 (n : ℕ) : Fin n ⊕ Fin n → ℕ := Sum.elim (fun q => q.val) fun q => n + q.val

theorem idx2_inj (n : ℕ) : Function.Injective (idx2 n) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Fin.ext h)
  · exact absurd h (by have := a.isLt; show a.val ≠ n + b.val; omega)
  · exact absurd h (by have := b.isLt; show n + a.val ≠ b.val; omega)
  · exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel h))

/-! ### The verifier -/

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X) (g : Fam (spec lam K (Lf ()))) {Y : Type}
  {E : ExtSpec} {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)

def strictPX (sMT sFS : ℕ) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  haveI := wq.decO
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ cntP P.S rts) &&
    sSP sMT P.S P.ann wq.sh rts (fun p => decide (p ∈ R)) π.opens &&
    sExtP sMT wq.ext (tst (mk Re)) π.ext &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty)

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
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot π.path ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- The verifier, with a test of its own for the external oracles' positions. -/
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
  ∀ (I X : Type) (lam K : ℕ) (Lf : Unit → BatchProtocol I X) (g : Fam (spec lam K (Lf ()))) (Y : Type)
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
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (spec lam K L)) (Y : Type) (E : ExtSpec)
      (idx : E.Pos → ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    Function.Injective idx →
    verifyPX (fun _ => L) g (maskOf idx) (maskBit idx) L.early L.late sMT sFS t P wq embS embP
        xin embE depthReq cms x π =
      (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g

theorem thin_ext : Spec.thin_ext := fun I X lam K L g Y E idx sMT sFS t P wq embS embP xin embE depthReq cms x π hi =>
  letI : DecidableEq E.Pos := wq.ext.dec
  (verifyPX_eq I X lam K (fun _ => L) g Y E ℕ (maskOf idx) (maskBit idx) L.early L.late sMT sFS t P
      wq embS embP xin embE depthReq cms x π (fun R p => maskBit_eq idx hi R p)).trans
    (thin_reads I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π)

end Run.Thin
