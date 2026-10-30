-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinDefs.lean: the evaluable form of the compiled verifier: `verifyP`, a plain function that
Lean's evaluator can run at rounds with very many possible verifier messages. Definitions only.

The compiled verifier is the verifier of the non-interactive argument that the library's compiler
makes of an interactive oracle protocol: Merkle trees for the oracles, a hash chain for the
challenges (`Compile.Batch.verifyOneProtocol`); proof of work is tested where the protocol's `accept` tests
it. The compiled verifier is defined as a tree of oracle queries over typed protocols. This file
writes it again as a function that computes the same verdict at given oracle functions g ("thin" in
names); later forms, each proved equal to the one before, run at real sizes (part 4). That at
`Lf := fun _ => L`, `L.early`, `L.late` it is `(Compile.Batch.verifyOneProtocol .. P.up ..).det g` is stated
in Run/ThinTie.lean and proved in Run/ThinTieProofs.lean.

Why it is needed. A round (`Iop.Round`) carries `Fintype Chal` as data: at run time, the list of all
verifier messages. The interface holds its protocols' shapes, so their rounds. Compiled Lean is
strict: whatever is handed over as a value is built. Observed, with a trace in a round's instance:
whether an argument that stands in a function's types alone is built depends on what the compiler
made of that function (inlined or not, recursive or not, in which file); no rule could be relied on.

The principle of this file. No function here has a parameter, explicit or implicit, of type `Round`,
`Shape`, `InteractiveOracleProof`, `BatchInteractiveOracleProof` or `BatchProtocol`. In their place stand `RS`, `List RS`, `PS`
(Run/TwinDefs.lean: a round with its instance behind a function of `Unit`), and the interface behind
a function of `Unit`, an explicit argument `Lf`; the types are written at `Lf ()`. A closure is
handed on and never called, so there is nothing to build.

Sources. The library's texts (Compile/Batch/Verifier.lean), with the trees of queries replaced by
their values at oracle functions g, as in Run/VerifyDet.lean and Run/TwinDet.lean.

1. What the file contains.
     `verifyP` and its helpers.
   Taken from the library as they stand: `actOf`, `takeRt`, `Head.withLate`, `Phase.slotVal`,
   `climbF`, `strictExt`, the walk for pruned openings (Hash/Octopus.lean, Hash/OctopusFacts.lean),
   which have no such parameter; projections and constructors of records, some of which have a
   round, a protocol or the interface as an implicit parameter by Lean's signatures (for instance,
   in that order, `WireRB`, Iop/BatchWire.lean; `OneProtocolProof`, Compile/Batch/Verifier.lean; `FbIn`,
   Compile/Batch/Oracles.lean).
   One thing more is done for speed and changes no value: the sets of positions read are made once
   (a "let" in front), not anew at each of the 2^depth places that the format's test and the checks
   walk.
2. What is checked when the file compiles. Only the types.
3. Theorems. None in this file.
4. What is not claimed. Nothing else is faster here than in `verifyOneProtocol`. That a run ends at a round
   with very many verifier messages is shown by a test (Run/ThinGuard.lean), not here. That
   `verifyP` itself is what runs on proof files of real sizes: it is not. The run functions use
   later forms, each proved equal to the one before: `verifyPB` (Run/ThinBits.lean: the trees' walks
   on digests as data, so that the oracle is asked once a vertex), `verifyPR` (Run/ThinReads.lean:
   the set of positions read split round by round) and, with external oracles, `verifyPX`
   (Run/ThinExtReads.lean: a fast test for their positions; equal if that test is membership in the
   set).

Terms: lean/GLOSSARY.md.
-/
import Run.TwinDefs
import Compile.MerkleList
import Hash.OctopusFacts

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocol I X)

/-! ### Forests -/

def splitP (pr : Bool) (F : Forest lam (Lf ())) : List (Forest lam (Lf ())) :=
  if pr then [F] else F.cs.map fun e => ⟨F.depth, F.treeRoot, [e]⟩
def idxP (F : Forest lam (Lf ())) : List ℕ := F.cs.map fun e => e.1 * 2 ^ F.depth + e.2.j
def needP (F : Forest lam (Lf ())) : ℕ := Octopus.need F.depth (idxP Lf F)
def readsOneP (F : Forest lam (Lf ())) : List (Dig lam) :=
  Octopus.reads F.depth (F.cs.map fun e => (e.1 * 2 ^ F.depth + e.2.j, e.2.path))
def flatP (Fs : List (Forest lam (Lf ()))) : List (Check lam (Lf ())) :=
  Fs.flatMap fun F => F.cs.map Prod.snd
def readsP (Fs : List (Forest lam (Lf ()))) : List (Dig lam) := Fs.flatMap (readsOneP Lf)
def wellP (c : Check lam (Lf ())) : Bool :=
  decide (c.path.length = c.depth) && decide (c.j < 2 ^ c.depth)

/-! ### The checks of one component of one round -/

def compP (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    List ℕ → Option (List (Check lam (Lf ())))
  | [] => some []
  | j :: js =>
      match posAt j with
      | some p =>
          if isRead p then
            match f p, compP r posAt depth emb rt isRead f js with
            | some op, some cs => some (⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ :: cs)
            | _, _ => none
          else compP r posAt depth emb rt isRead f js
      | none => compP r posAt depth emb rt isRead f js

def optP (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body (Lf ())) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Option (List (Check lam (Lf ()))) :=
  match rt with
  | none => some []
  | some c => compP Lf r posAt depth emb c isRead f (List.range (2 ^ depth))

def forestsP :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → OSym (up S) p → Body (Lf ())) → RootsOfChain lam (up S) → (OPos (up S) → Bool) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Forest lam (Lf ())))
  | [], _, _, _, _, _, _ => some []
  | r :: S, (_, A), (w, W), emb, (rt, rts), isRead, f =>
      match optP Lf r w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        optP Lf r w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
          (fun p => isRead (.inl p)) (fun p => f (.inl p)),
        forestsP S A W (fun p => emb (.inr p)) rts
          (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
      | some a, some b, some c =>
          some (splitP Lf w.pr0
              ⟨w.depth0, fun _ => rt.1.join.getD default, a.map fun c => (0, c)⟩ ++
            (splitP Lf w.prJ ⟨w.depthJ, fun _ => rt.2.join.getD default, b.map fun c => (0, c)⟩ ++
              c))
      | _, _, _ => none

def extWP {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    List E.Pos → Option (List (ℕ × Check lam (Lf ())))
  | [] => some []
  | p :: ps =>
      if isRead p then
        match g p, extWP we emb cms isRead g ps with
        | some op, some cs =>
          some ((we.which p,
                ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
                  cms.getD (we.which p) default, we.depth⟩) :: cs)
        | _, _ => none
      else extWP we emb cms isRead g ps

def forestExtP {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    Option (List (Forest lam (Lf ()))) :=
  (extWP Lf we emb cms isRead g we.all).map fun cs =>
    splitP Lf we.pr ⟨we.depth, fun t => cms.getD t default, cs⟩

/-! ### The local transcript -/

def rootP (r : RS) (a : RAnn r.up) (rt : RtC lam × RtC lam) (p : r.Pos) : Bool :=
  if a.own p then rt.2.join.isSome else rt.1.join.isSome

def effP (r : RS) (a : RAnn r.up) (rt : RtC lam × RtC lam) (pl : r.Plain) : r.Plain :=
  a.plain.symm (if rt.1.isSome then (a.plain pl).1 else (a.plain r.dPlain).1,
    if rt.2.isSome then (a.plain pl).2 else (a.plain r.dPlain).2)

def effsP : (S : List RS) → RoundSplits (up S) → RootsOfChain lam (up S) → Plains (up S) → Plains (up S)
  | [], _, _, _ => ()
  | r :: S, (a, A), (rt, rts), (pl, pls) => (effP r a rt pl, effsP S A rts pls)

def trP :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → RootsOfChain lam (up S) → Plains (up S) →
    Rho (up S) → ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Tr (up S)
  | [], _, _, _, _, _, _ => ()
  | r :: S, (a, A), (w, W), (rt, rts), (pl, pls), (c, ρ), f =>
      ((w.pt.ofSyms fun p => match rootP r a rt p, f (.inl p) with
          | true, some op => op.sym
          | _, _ => w.pt.zero p, effP r a rt pl), c, trP S A W rts pls ρ fun p => f (.inr p))

/-! ### The strict format -/

def cntP : (S : List RS) → RootsOfChain lam (up S) → ℕ
  | [], _ => 0
  | _ :: S, (rt, rts) => rt.1.join.toList.length + rt.2.join.toList.length + cntP S rts

def sCompP (sMT : ℕ) (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : Bool :=
  (List.range (2 ^ depth)).all fun j => match posAt j with
    | none => true
    | some p => match f p with
      | none => true
      | some op => hasRoot && isRead p && decide (op.salt.length = sMT)

def sSP (sMT : ℕ) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A → RootsOfChain lam (up S) →
    (OPos (up S) → Bool) → ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Bool
  | [], _, _, _, _, _ => true
  | r :: S, (_, A), (w, W), (rt, rts), isRead, f =>
      sCompP sMT r w.posAt0 w.depth0 rt.1.join.isSome
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      sCompP sMT r w.posAtJ w.depthJ rt.2.join.isSome
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) &&
      sSP sMT S A W rts (fun p => isRead (.inr p)) (fun p => f (.inr p))

/-! ### At oracle functions -/

variable (g : Fam (spec lam K (Lf ())))

def nodeP (a b : Dig lam) : Dig lam := g OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits)
def rnodeP (a b : Dig lam) : Dig lam := g OracleName.rnode ((List.ofFn a, List.ofFn b) : Bits × Bits)

def chainP (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    (PlainPart (up S) A → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) → ℕ → Phase lam → List (Dig lam) →
    Plains (up S) → Option (Rho (up S) × RootsOfChain lam (up S) × Phase lam)
  | [], _, _, _, _, ph, _, _ => some ((), (), ph)
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.hasJ rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (OracleName.fb t)
                  (⟨i, h.withLate (if late = some i then x else none), rt,
                    embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam (Lf ()) t)
              (chainP early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2)
          | none => none
      | some (.one h false next) =>
          match takeRt w.has0 rts with
          | some (rt, rts') =>
              let ans : (Fin K → Dig lam) × Dig lam :=
                g (OracleName.fb t) (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam (Lf ()) t)
              (chainP early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                  (next (List.ofFn ans.2)) rts' pls).map
                fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2)
          | none => none
      | some (.join ρ) =>
          match takeRt w.hasJ rts with
          | some (rtj, rts1) =>
              match takeRt w.has0 rts1 with
              | some (rt0, rts') =>
                  let c : Dig lam :=
                    g (OracleName.g t) (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam (Lf ()) t)
                  let ans : (Fin K → Dig lam) × Dig lam :=
                    g (OracleName.fb t)
                      (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                        embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam (Lf ()) t)
                  (chainP early late t cms x salt rtreq S A W (fun z => embP (.inr z)) (i + 1)
                      (.shr (List.ofFn ans.2) c) rts' pls).map
                    fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2)
              | none => none
          | none => none
      | none => none

def runForestP (F : Forest lam (Lf ())) (s : List (Dig lam)) : Bool :=
  ((Octopus.upN F.depth (idxP Lf F)).zip
      (Octopus.octF (nodeP Lf g) F.depth (idxP Lf F)
        (F.cs.map fun e => (g OracleName.leaf e.2.inp : Dig lam)) s)).all
    fun m => decide (m.2 = F.treeRoot m.1)

def runForestsP : List (Forest lam (Lf ())) → List (Dig lam) → Bool
  | [], _ => true
  | F :: Fs, s => runForestP Lf g F (s.take (needP Lf F)) && runForestsP Fs (s.drop (needP Lf F))

def reqCheckP (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (c : Dig lam) :
    Bool :=
  if path.length = depthReq ∧ slot < 2 ^ depthReq then
    decide (climbF (rnodeP Lf g) path slot (g OracleName.rleaf (List.ofFn c : Bits) : Dig lam) = rtreq)
  else false

def reqPartP (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam)) (ph : Phase lam) :
    Bool :=
  match ph.slotVal with
  | none => true
  | some c => reqCheckP Lf g depthReq rtreq slot path c

/-! ### The verifier -/

variable {Y : Type} {E : ExtSpec}

def sExtP (sMT : ℕ) (we : WireE E) (isRead : E.Pos → Bool)
    (f : E.Pos → Option (Opening lam E.Sym)) : Bool :=
  strictExt sMT we isRead f

def strictP (sMT sFS : ℕ) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  haveI := wq.decO
  haveI := wq.ext.dec
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ cntP P.S rts) &&
    sSP sMT P.S P.ann wq.sh rts (fun p => decide (p ∈ R)) π.opens &&
    sExtP sMT wq.ext (fun p => decide (p ∈ Re)) π.ext &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty)

def forestsOfP (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    Option (List (Forest lam (Lf ()))) :=
  haveI := wq.decO
  haveI := wq.ext.dec
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match forestsP Lf P.S P.ann wq.sh embS rts (fun p => decide (p ∈ R)) π.opens,
        forestExtP Lf wq.ext embE cms (fun p => decide (p ∈ Re)) π.ext with
  | some a, some b => some (a ++ b)
  | _, _ => none

def afterP (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  match forestsOfP Lf P wq embS embE cms x π ρ rts with
  | some Fs =>
      if (flatP Lf Fs).length ≤ wq.nOpen ∧
          (flatP Lf Fs).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
        runForestsP Lf g Fs (readsP Lf Fs) && reqPartP Lf g depthReq π.rtreq π.slot π.path ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | none => false

/-- The verifier. -/
def verifyP (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) =>
    if strictP sMT sFS P wq depthReq x π ρ rts ph then
      afterP Lf g P wq embS embE depthReq cms x π ρ rts ph
    else false

end Run.Thin
