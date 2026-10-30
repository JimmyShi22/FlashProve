-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinReads.lean: the evaluable form of the compiled verifier with the set of positions read split
round by round: `verifyPR`. Definitions, two statements (`Run.Thin.Spec.verifyPR_eq`,
`Run.Thin.Spec.thin_reads`) and their proofs.

`verifyPR` equals `verifyPB` (Run/ThinBits.lean) at all arguments, and so, at `fun _ => L`,
`L.early`, `L.late`, it equals `(Compile.Batch.verifyOneProtocol ..).det g`, without a hypothesis beside
whatever the arguments hold as proofs. (`L.early`: what of an instance is written into a chain's
first query; `id`: the whole; `BatchProtocol.early`, Iop/Batch.lean.) (`L.late`: the round into whose query
the whole instance is written; `none`: no such round; `BatchProtocol.late`, Iop/Batch.lean.) ("Thin" in names:
the evaluable form, Run/ThinDefs.lean.) `Compile.Batch.verifyOneProtocol` (Compile/Batch/Verifier.lean) is
the compiled verifier of one slot of a batch protocol: on one argument string it recomputes the
Fiat-Shamir hash chain, tests the string's format, checks the Merkle openings and, if the chain has
joined, the path in the request tree, and runs the protocol's `accept`. It is written as a tree of
oracle queries (`OComp`); `OComp.det g` (Rom/Cache.lean) is the result of the run under the oracle
functions g in which every coin toss yields 0. The positions read are the positions in the prover's
oracles, of all rounds together, that the protocol's verifier reads: the finite set `P.reads x ρ ..`
(`PS.reads`, Run/TwinDefs.lean).

Why. Measured at a protocol of thirty rounds with trees of depths 15, 14, 14 and 221 positions read:
of 50.6 s of `verifyPB` 41.8 s went into the checks of the openings (`forestsOfP`). The library's
definition asks "is p read?" at each of the 2^depth places of each tree, and each such question
compares p with all positions read, each of them a value under as many `Sum.inr` as there are rounds
before its own.

What is done. As the recursion goes down the rounds, the set is split: `headR R`, the positions of
the first round, as that round's own positions; `tailR R`, those of the later rounds. A round's
places are then compared with that round's own positions alone.

1. What the file contains. `headR`, `tailR`; `forestsR`; `forestsOfR`, `afterPR`, `verifyPR`.
2. What is checked when the file compiles. Only the types and the proofs.
3. Theorems. `forestsR_eq`, `verifyPR_eq`, and
     `thin_reads`: `verifyPR (fun _ => L) g L.early L.late .. = (verifyOneProtocol .. P.up ..).det g`

Notation:
  `sMT`, `sFS`: the length of the salt of a leaf, and of the salt of a chain
    (Compile/Batch/Verifier.lean);
  `P`: the skeleton of a batch protocol (`PS`, Run/TwinDefs.lean);
  `P.up`: the batch protocol of the skeleton `P` (`PS.up`, Run/TwinDefs.lean);
  `embS`, `embP`, `embE`: how symbols and plain parts are written into queries (`verifyB`,
    Compile/Batch/Verifier.lean);
  `xin`: a map; `xin x` is `recomputeChain`'s `x`, the whole instance (Compile/Batch/Verifier.lean);
  `depthReq`: depth of the request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `cms`: the external roots (`verifyB`, Compile/Batch/Verifier.lean).

4. What is not claimed. How fast it runs: that is a matter of measurement. The strict format's test
   is left as it is (it asks "is p read?" only where an opening stands). No statement on soundness
   follows.

Sources. Run/ThinBits.lean's `verifyPB`, whose binders `verifyPR` has word for word;
Run/ThinDefs.lean's `forestsP`.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ThinBitsTieProofs

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

/-- The members of R of the form `Sum.inl a`, as members of α. -/
def headR {α β : Type} (R : Finset (α ⊕ β)) : Finset α :=
  R.filterMap Sum.getLeft? fun a a' b h h' => by
    rw [Option.mem_def, Sum.getLeft?_eq_some_iff] at h h'
    rw [h, h']

/-- The members of R of the form `Sum.inr b`, as members of β. -/
def tailR {α β : Type} (R : Finset (α ⊕ β)) : Finset β :=
  R.filterMap Sum.getRight? fun a a' b h h' => by
    rw [Option.mem_def, Sum.getRight?_eq_some_iff] at h h'
    rw [h, h']

theorem mem_headR {α β : Type} (R : Finset (α ⊕ β)) (a : α) : a ∈ headR R ↔ Sum.inl a ∈ R := by
  unfold headR
  rw [Finset.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Sum.getLeft?_eq_some_iff] at h
    rwa [← h]
  · exact fun h => ⟨_, h, rfl⟩

theorem mem_tailR {α β : Type} (R : Finset (α ⊕ β)) (b : β) : b ∈ tailR R ↔ Sum.inr b ∈ R := by
  unfold tailR
  rw [Finset.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Sum.getRight?_eq_some_iff] at h
    rwa [← h]
  · exact fun h => ⟨_, h, rfl⟩

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)

/-- `forestsP` (Run/ThinDefs.lean), with the set of positions read in the place of the test, split
round by round. -/
def forestsR :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → OSym (up S) p → Body (Lf ())) → RootsOfChain lam (up S) → Finset (OPos (up S)) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Forest lam (Lf ())))
  | [], _, _, _, _, _, _ => some []
  | r :: S, (_, A), (w, W), emb, (rt, rts), R, f =>
      haveI : DecidableEq r.Pos := w.pt.decPos
      let R0 : Finset r.Pos := headR (α := r.Pos) (β := OPos (up S)) R
      match optP Lf r w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)),
        optP Lf r w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)),
        forestsR S A W (fun p => emb (.inr p)) rts
          (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => f (.inr p)) with
      | some a, some b, some c =>
          some (splitP Lf w.pr0
              ⟨w.depth0, fun _ => rt.1.join.getD default, a.map fun c => (0, c)⟩ ++
            (splitP Lf w.prJ ⟨w.depthJ, fun _ => rt.2.join.getD default, b.map fun c => (0, c)⟩ ++
              c))
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

variable (g : Fam (spec lam K (Lf ()))) {Y : Type} {E : ExtSpec}

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
        runForestsB Lf g Fs (readsP Lf Fs) && reqPartB Lf g depthReq π.rtreq π.slot π.path ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- The verifier, the set of positions read split round by round. -/
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
  ∀ (I X : Type) (lam K : ℕ) (Lf : Unit → BatchProtocol I X) (g : Fam (spec lam K (Lf ()))) (Y : Type)
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
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (g : Fam (spec lam K L)) (Y : Type) (E : ExtSpec)
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

end Run.Thin
