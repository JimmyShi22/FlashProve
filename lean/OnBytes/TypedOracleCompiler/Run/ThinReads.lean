-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
TWO: OnBytes/TypedOracleCompiler/Run/ThinReads.lean: THE LIBRARY's FILE OF THE SAME NAME SAID AGAIN OVER OnBytes/TypedOracleCompiler
(a list of trees a round; a leaf's body a parameter of the interface). It is the second of the three
later run forms of the evaluable verifier: verifyPR, with its tie verifyPR_eq to OnBytes/TypedOracleCompiler's
verifyPB, and thin_reads: verifyPR = (OnBytes/TypedOracleCompiler's verifyOneProtocol ..).det g.
WHAT IS TURNED: forestsR alone, and as OnBytes/TypedOracleCompiler's forestsP is turned against the library's: where
the library checks "the tree" of a component (optP at one depth and one root, then one forest),
OnBytes/TypedOracleCompiler goes tree by tree through the component's lists of depths and of roots (treesP from tree
0 on) and makes the forests of all of them (forestsTP). The set of the round's own positions, R0, is
made once a round and serves all trees of both components. forestsR_eq's statement and proof stand
as text.
TURNED WITH THE ROAD: afterPR (it hands π.rsalt to reqPartB).
WHAT IS SAID AGAIN AS TEXT: forestsR_eq; forestsOfR, verifyPR; forestsOfR_eq, afterPR_eq;
Spec.verifyPR_eq, verifyPR_eq; Spec.thin_reads, thin_reads.
WHAT IS LEFT TO THE LIBRARY's OWN MODULE (imported beside; it stands on no turned type): headR,
tailR, mem_headR, mem_tailR.
WHAT IS NOT SAID. THE MEASURE IN THE HEAD BELOW IS THE LIBRARY's, OF THE LIBRARY's FUNCTIONS. How a
set of positions read is MADE (P.reads) is the protocol's own cost: this form splits the set after
it is made. The head below is the library's, kept.

Run/ThinReads.lean: the evaluable form of the compiled verifier with the set of positions read split
round by round: verifyPR. Definitions, two statements (Run.Thin.Spec.verifyPR_eq, thin_reads) and
their proofs.

verifyPR = verifyPB (Run/ThinBits.lean), and so = (Compile.Batch.verifyOneProtocol ..).det g, without a
hypothesis. ("Thin" in names: the evaluable form, Run/ThinDefs.lean.)

Why. Measured at a protocol of thirty rounds with trees of depths 15, 14, 14 and 221 positions read:
of 50.6 s of verifyPB 41.8 s went into the checks of the openings (forestsOfP). The library's text
asks "is p read?" at each of the 2^depth places of each tree, and each such question compares p with
all positions read, each of them a value under as many "Sum.inr" as rounds stand before its own.

What is done. As the recursion goes down the rounds, the set is split: headR R, the positions of the
first round, as that round's own positions; tailR R, those of the later rounds. A round's places are
then compared with that round's own positions alone.

Sources. Run/ThinBits.lean's verifyPB, whose binders verifyPR has word for word; Run/ThinDefs.lean's
forestsP.

1. What the file contains. headR, tailR; forestsR (forestsP with the set in the place of the test);
forestsOfR, afterPR, verifyPR.
2. What is checked when the file compiles.  Only the types and the proofs.
3. Theorems.
     forestsR_eq     (∀ p, isRead p = true ↔ p ∈ R) → forestsR .. R f = forestsP .. isRead f
     verifyPR_eq     verifyPR = verifyPB at all arguments
     thin_reads      verifyPR (fun _ => L) g L.early L.late .. = (verifyOneProtocol .. P.up ..).det g
4. What is not claimed. How fast it runs: that is a matter of measurement. The strict format's test
is left as it is (it asks "is p read?" only where an opening stands). NO STATEMENT ON SOUNDNESS
FOLLOWS.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.ThinReads
import OnBytes.TypedOracleCompiler.Run.ThinBitsTieProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin
export _root_.Run.Thin (headR tailR mem_headR mem_tailR)

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X)

/-- forestsP, with the set of positions read in the place of the test, split round by round.
TWO: tree by tree, as OnBytes/TypedOracleCompiler's forestsP -/
def forestsR :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → OSym (up S) p → Body (Lf ())) → RootsOfChain lam (up S) → Finset (OPos (up S)) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Forest lam (Lf ())))
  | [], _, _, _, _, _, _ => some []
  | r :: S, (_, A), (w, W), emb, (rt, rts), R, f =>
      haveI : DecidableEq r.Pos := w.pt.decPos
      let R0 : Finset r.Pos := headR (α := r.Pos) (β := OPos (up S)) R
      match treesP Lf r w.posAt0 (fun p => emb (.inl p))
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []),
        treesP Lf r w.posAtJ (fun p => emb (.inl p))
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []),
        forestsR S A W (fun p => emb (.inr p)) rts
          (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => f (.inr p)) with
      | some a, some b, some c =>
          some (forestsTP Lf w.pr0 a ++ (forestsTP Lf w.prJ b ++ c))
      | _, _, _ => none

theorem forestsR_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (emb : (p : OPos (up S)) → OSym (up S) p → Body (Lf ())) (rts : RootsOfChain lam (up S))
        (R : Finset (OPos (up S))) (isRead : OPos (up S) → Bool)
        (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      (∀ p, isRead p = true ↔ p ∈ R) →
      forestsR Lf S A W emb rts R f = forestsP Lf S A W emb rts isRead f
  | [], _, _, _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), emb, (rt, rts), R, isRead, f, h => by
      letI : DecidableEq r.Pos := w.pt.decPos
      have h0 : (fun p : r.Pos =>
            @decide (p ∈ headR (α := r.Pos) (β := OPos (up S)) R)
              (@Finset.decidableMem _ w.pt.decPos p _)) =
          fun p => isRead (.inl p) := by
        funext p
        exact Bool.eq_iff_iff.2 ⟨fun hh =>
            (h (.inl p)).2 ((mem_headR R p).1 (of_decide_eq_true hh)),
          fun hh => decide_eq_true ((mem_headR R p).2 ((h (.inl p)).1 hh))⟩
      have ih := forestsR_eq S A W (fun p => emb (.inr p)) rts
        (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => isRead (.inr p)) (fun p => f (.inr p))
        (fun p => by rw [mem_tailR]; exact h (.inr p))
      simp only [forestsR, forestsP, h0, ih]
      rfl

variable (g : Fam (typedOracleFamily lam K (Lf ()))) {Y : Type} {E : ExtSpec}

def forestsOfR (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    Option (List (Forest lam (Lf ()))) :=
  haveI := wq.ext.dec
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match forestsR Lf P.S P.ann wq.sh embS rts R π.opens,
        forestExtP Lf wq.ext embE cms (fun p => decide (p ∈ Re)) π.ext with
  | some a, some b => some (a ++ b)
  | _, _ => none

def afterPR (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfR Lf P wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatP Lf Fs).length ≤ wq.nOpen ∧
          (flatP Lf Fs).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot
            π.path π.rsalt ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- THE VERIFIER, THE SET OF POSITIONS READ SPLIT ROUND BY ROUND. -/
def verifyPR (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if strictP sMT sFS P wq depthReq x π ρ rts ph then
      afterPR Lf g P wq embS embE depthReq cms x π ρ rts ph
    else false

theorem forestsOfR_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    forestsOfR Lf P wq embS embE cms x π ρ rts = forestsOfP Lf P wq embS embE cms x π ρ rts := by
  letI : DecidableEq (OPos (up P.S)) := wq.decO
  have h := forestsR_eq Lf P.S P.ann wq.sh embS rts (P.reads x ρ (effsP P.S P.ann rts π.plains))
    (fun p => decide (p ∈ P.reads x ρ (effsP P.S P.ann rts π.plains))) π.opens
    (fun p => decide_eq_true_iff)
  unfold forestsOfR forestsOfP
  dsimp only
  rw [h]
  rfl

theorem afterPR_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    afterPR Lf g P wq embS embE depthReq cms x π ρ rts ph =
      afterPB Lf g P wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterPR afterPB
  rw [forestsOfR_eq]
  rfl

def Spec.verifyPR_eq : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ()))) (Y : Type)
      (E : ExtSpec) (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
      (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
      (x : Y) (π : OneProtocolProof lam P.up),
    verifyPR Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyPB Lf g early late sMT sFS t P wq embS embP xin embE depthReq cms x π

theorem verifyPR_eq : Spec.verifyPR_eq := by
  intro I X lam K Lf g Y E early late sMT sFS t P wq embS embP xin embE depthReq cms x π
  unfold verifyPR verifyPB
  simp only [afterPR_eq]
  rfl

def Spec.thin_reads : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K L)) (Y : Type) (E : ExtSpec)
      (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
      (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up),
    verifyPR (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g

theorem thin_reads :
    Spec.thin_reads := fun I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π =>
  (verifyPR_eq I X lam K (fun _ => L) g Y E L.early L.late sMT sFS t P wq embS embP xin
      embE depthReq cms x π).trans
    (thin_bits I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π)

end TypedOracleCompiler.Run.Thin
