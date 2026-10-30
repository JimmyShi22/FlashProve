-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/LessWire.lean: the verifier along the lists (ListedVerifier.lean,
verifyBSL) over a lesser wire record, which holds no list of a round's positions. Definitions. The
equations are in LessWireLaws.lean.

Why. A round's wire record WireRB (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) holds pt : Round.IsPoint
(Iop/Shape.lean), whose field finPos : Fintype r.Pos is data: the list of all positions of the
round's trees. Compiled Lean builds a record's fields when it builds the record. The verifier never
reads that list: of a wire record recomputeChain, rootAt, mkTr, strictSBL and forestsBL read ten things, and
the cut to the lists (ListedCut.lean, keptR) reads an eleventh, place.

What is done. WireRL holds these eleven things. chainBX, rootAtX, mkTrX, strictSBX, forestsBX are
recomputeChain, rootAt, mkTr (Verifier.lean), strictSBL (ListedStrict.lean) and forestsBL
(ListedForests.lean), word for word, over it; strictBBX, forestsOfX, afterFX, afterBOX, verifyBSX
are ListedVerifier.lean's strictBBL, forestsOfL, afterFL, afterBOL, verifyBSL with these. lessR and
lessS say what is left of a full record: they are for statements; a run builds a WireRL outright.
After OnBytes/RunA/ListedOwnDefs.lean, which does the like (WireRLess) for the library's own wire
record.

Limits. Nothing on time or memory is a theorem. Nothing on soundness.
The program does not import this file.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- What the verifier reads of a round's wire record. -/
structure WireRL (lam K : ℕ) (r : Round) where
  ofSyms : ((p : r.Pos) → r.Sym p) → r.Orc
  zero : (p : r.Pos) → r.Sym p
  depth0 : List ℕ
  depthJ : List ℕ
  tree : r.Pos → ℕ
  /-- read by the cut to the lists alone (ListedCut.lean, keptR) -/
  place : r.Pos → ℕ
  posAt0 : ℕ → ℕ → Option r.Pos
  posAtJ : ℕ → ℕ → Option r.Pos
  chal : (Fin K → Dig lam) → r.Chal
  pr0 : Bool
  prJ : Bool

def WireSL (lam K : ℕ) : Shape → Type
  | [] => Unit
  | r :: s => WireRL lam K r × WireSL lam K s

/-- What is left of a round's wire record. For statements. -/
def lessR {r : Round} {a : RAnn r} (w : WireRB lam K r a) : WireRL lam K r :=
  ⟨w.pt.ofSyms, w.pt.zero, w.depth0, w.depthJ, w.tree, w.place, w.posAt0, w.posAtJ, w.chal, w.pr0,
    w.prJ⟩

/-- The same for a list of rounds. For statements. -/
def lessS : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → WireSL lam K s
  | [], _, _ => ()
  | _ :: s, (_, A), (w, W) => (lessR w, lessS s A W)

/-- the records of the rounds of s, then those of u -/
def WireSL.app : {s u : Shape} → WireSL lam K s → WireSL lam K u → WireSL lam K (s ++ u)
  | [], _, _, V => V
  | _ :: _, _, (w, W), V => (w, WireSL.app W V)

/-- recomputeChain over the lesser records. -/
def chainBX (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    (s : Shape) → (A : RoundSplits s) → WireSL lam K s → (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ →
    Phase lam → List (Dig lam) → Plains s → TypedOracleComputation lam K L (Option (Rho s × RootsOfChain lam s × Phase lam))
  | [], _, _, _, _, ph, _, _ => pure (some ((), (), ph))
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) =>
      match actOf cms (x.map L.early) salt a.kind ph with
      | some (.one h true next) =>
          match takeRt w.depthJ.length rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h.withLate (lateInstancePart L i x), rt,
                  embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)
              let r ← chainBX t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2))
          | none => pure none
      | some (.one h false next) =>
          match takeRt w.depth0.length rts with
          | some (rt, rts') => do
              let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
              let r ← chainBX t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts' pls
              pure (r.map fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2))
          | none => pure none
      | some (.join ρ) =>
          match takeRt w.depthJ.length rts with
          | some (rtj, rts1) =>
              match takeRt w.depth0.length rts1 with
              | some (rt0, rts') => do
                  let c ← askTypedOracle (L := L) (K := K) (OracleName.g t)
                    (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t)
                  let ans ← askTypedOracle (L := L) (K := K) (OracleName.fb t)
                    (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                      embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)
                  let r ← chainBX t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                    (.shr (List.ofFn ans.2) c) rts' pls
                  pure (r.map fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2))
              | none => pure none
          | none => pure none
      | none => pure none

/-- rootAt over a lesser record. -/
def rootAtX {r : Round} (a : RAnn r) (w : WireRL lam K r) (rt : RtC lam × RtC lam) (p : r.Pos) :
    Bool :=
  if a.own p then ((rt.2.getD [])[w.tree p]?).isSome else ((rt.1.getD [])[w.tree p]?).isSome

/-- mkTr over the lesser records. -/
def mkTrX : (s : Shape) → (A : RoundSplits s) → WireSL lam K s → RootsOfChain lam s → Plains s → Rho s →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → Tr s
  | [], _, _, _, _, _, _ => ()
  | _ :: s, (a, A), (w, W), (rt, rts), (pl, pls), (c, ρ), f =>
      ((w.ofSyms fun p => match rootAtX a w rt p, f (.inl p) with
          | true, some op => op.sym
          | _, _ => w.zero p, effPlain a rt pl), c, mkTrX s A W rts pls ρ fun p => f (.inr p))

/-- strictSBL over the lesser records. -/
def strictSBX (sMT : ℕ) :
    (s : Shape) → WireSL lam K s → RootsOfChain lam s →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → Leaves → Leaves → Bool
  | [], _, _, _, _, _ => true
  | _ :: s, (w, W), (rt, rts), f, own, rd =>
      strictTreesL sMT w.posAt0 w.depth0 (rt.1.getD []) (fun p => f (.inl p))
        (rd.headD ([], [])).1 (own.headD ([], [])).1 &&
      strictTreesL sMT w.posAtJ w.depthJ (rt.2.getD []) (fun p => f (.inl p))
        (rd.headD ([], [])).2 (own.headD ([], [])).2 &&
      strictSBX sMT s W rts (fun p => f (.inr p)) own.tail rd.tail

/-- forestsBL over the lesser records. -/
def forestsBX :
    (s : Shape) → WireSL lam K s →
    ((p : OPos s) → OSym s p → Body L) → RootsOfChain lam s →
    ((p : OPos s) → Option (Opening lam (OSym s p))) → Leaves → Option (List (Forest lam L))
  | [], _, _, _, _, _ => some []
  | _ :: s, (w, W), emb, (rt, rts), f, rd =>
      match checksTreesL w.posAt0 (fun p => emb (.inl p))
          (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []) (rd.headD ([], [])).1,
        checksTreesL w.posAtJ (fun p => emb (.inl p))
          (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []) (rd.headD ([], [])).2,
        forestsBX s W (fun p => emb (.inr p)) rts (fun p => f (.inr p)) rd.tail with
      | some a, some b, some c => some (forestsT w.pr0 a ++ (forestsT w.prJ b ++ c))
      | _, _, _ => none

/-- strictBBL over the lesser records. -/
def strictBBX (sMT sFS : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sl : WireSL lam K Q.loc.shape) (wl : WireELess E) (depthReq : ℕ) (π : OneProtocolProof lam Q)
    (own : Leaves) (listed : List E.Pos) (rd : Leaves) (rdE : List E.Pos)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : Bool :=
  haveI := wl.dec
  decide (π.salt.length = sFS) && decide (π.roots.length ≤ RootsOfChain.count Q.loc.shape rts) &&
    strictSBX sMT Q.loc.shape sl rts π.opens own rd &&
    strictExtL sMT (fun p => rdE.contains p) π.ext listed &&
    decide (π.slot < 2 ^ depthReq) && (ph.slotVal.isSome || π.path.isEmpty) &&
    (ph.slotVal.isSome || π.rsalt.isEmpty)

/-- forestsOfL over the lesser records. -/
def forestsOfX {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sl : WireSL lam K Q.loc.shape) (wl : WireELess E)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embE : E.Sym → Body L) (cms : List (Dig lam)) (π : OneProtocolProof lam Q) (rd : Leaves)
    (rdE : List E.Pos) (rts : RootsOfChain lam Q.loc.shape) : Option (List (Forest lam L)) :=
  match forestsBX Q.loc.shape sl embS rts π.opens rd,
    forestExtL wl embE cms π.ext rdE with
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- afterFL over the lesser records. -/
def afterFX {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (sl : WireSL lam K Q.loc.shape)
    (wl : WireELess E) (depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    TypedOracleComputation lam K L Bool :=
  (runForests Fs s).bind fun ok =>
  (reqPart depthReq π ph).bind fun okr =>
  pure (ok && okr && Q.loc.accept x (wl.build fun p => (π.ext p).map Opening.sym)
    (mkTrX Q.loc.shape Q.ann sl rts π.plains ρ π.opens))

/-- afterBOL over the lesser records. -/
def afterBOX {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (sl : WireSL lam K Q.loc.shape)
    (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (rd : Leaves)
    (rdE : List E.Pos) (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    TypedOracleComputation lam K L Bool :=
  match forestsOfX Q sl wl embS embE cms π rd rdE rts with
  | some Fs =>
      if (flatF Fs).length ≤ nOpen ∧
          (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ maxDepth)) then
        afterFX Q sl wl depthReq x π ρ rts ph Fs (readsF Fs)
      else pure false
  | none => pure false

/-- **The verifier along the lists, over the lesser records.** -/
def verifyBSX (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sl : WireSL lam K Q.loc.shape) (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (own : Leaves) (listed : List E.Pos)
    (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos) : TypedOracleComputation lam K L Bool :=
  (chainBX t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann sl embP 0 .first π.roots π.plains).bind
    fun r =>
    match r with
    | none => pure false
    | some (ρ, rts, ph) =>
      let rd := mkRd x ρ (effPlains Q.loc.shape Q.ann rts π.plains)
      let rdE := mkRdE x ρ
      if strictBBX sMT sFS Q sl wl depthReq π own listed rd rdE rts ph then
        afterBOX Q sl wl nOpen maxDepth embS embE depthReq cms x π rd rdE ρ rts ph
      else pure false

end TypedOracleCompiler.Compile.Batch
