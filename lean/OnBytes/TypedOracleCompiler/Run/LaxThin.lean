-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LaxThin.lean: an evaluable form of the lax compiled verifier: verifyLX; and the tie:
it is (verifyB t P.up wq …).det g. General in a skeleton P : Twin.PS and its wiring. Definitions
that compute; equations. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.
Why. The four run forms verifyP | verifyPB | verifyPR | verifyPX mirror verifyOneProtocol (the strict
format's test; forests). Wanted thrice: a yes by evaluation on a real entry file; the entry's large
tie; the proof file's join.
The form has all three cures of the later run forms at once, and ThinDefs' principle (no parameter
of type Round, Shape, InteractiveOracleProof, BatchInteractiveOracleProof or BatchProtocolWithLeafBody; the interface behind a function of Unit):
  checksR Lf S A W emb rts R f  checksB over the skeleton's rounds: each component's checks by
      ThinDefs' optP (tree by tree); the set of positions read split round by round (ThinReads'
      headR | tailR)
  extLP Lf we emb cms isRead f  checksExt's text, the interface behind Lf
  runCheckB Lf g c  one check, climbed alone, on bits (ThinBits' rule: a digest that has been
      computed is data): the leaf's answer as bits; the path's digests as bits; nodeB; compared with
      the root's bits
  afterLX Lf g mk tst P wq …  afterB's clauses in afterB's order; for the external positions
      ThinExtReads' mk | tst (the set turned once into a value; the test a look at it)
  verifyLX Lf g mk tst early late t P wq embS embP xin embE depthReq cms x π  chainP as it is, then
      afterLX
  checksR_eq, extLP_eq, runCheckB_eq, chainP_det, afterLX_eq
  lax_thin  (∀ R p, tst (mk R) p = true ↔ p ∈ R) → verifyLX (fun _ => L) g mk tst L.early L.late t P
      wq embS embP xin embE depthReq cms x π = (verifyB t P.up wq embS embP xin embE depthReq cms x
      π).det g
  lax_ext  for idx one to one: the same at maskOf idx | maskBit idx: no other hypothesis
  chainP_det  the chain alone: (recomputeChainOfProof t P.up wq embP xin cms x π).det g = chainP (fun _ => L) g
      L.early L.late … (chainT_eq, twd_chain, thin_chain joined)
No flag pr0 | prJ | pr is read: a wiring serves as it lies.
What is not said. That an evaluator brings it home at any size: a file of this project that is not
in this library tries it. chainP's deep
recursion stays. How the set of positions read is made is the protocol's own cost.
checksExt walks all positions of the external oracles, once. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.LaxDet
import OnBytes.TypedOracleCompiler.Run.ThinExtReads

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X)

/-! ### The checks -/

/-- checksB over the skeleton, the set of positions read split round by round -/
def checksR :
    (S : List RS) → (A : RoundSplits (up S)) → RoundsQueryLayout lam K (up S) A →
    ((p : OPos (up S)) → OSym (up S) p → Body (Lf ())) → RootsOfChain lam (up S) → Finset (OPos (up S)) →
    ((p : OPos (up S)) → Option (Opening lam (OSym (up S) p))) → Option (List (Check lam (Lf ())))
  | [], _, _, _, _, _, _ => some []
  | r :: S, (_, A), (w, W), emb, (rt, rts), R, f =>
      haveI : DecidableEq r.Pos := w.pt.decPos
      let R0 : Finset r.Pos := headR (α := r.Pos) (β := OPos (up S)) R
      match optP Lf r w.posAt0 w.depth0 (fun p => emb (.inl p)) (rt.1.getD [])
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)),
        optP Lf r w.posAtJ w.depthJ (fun p => emb (.inl p)) (rt.2.getD [])
          (fun p => decide (p ∈ R0)) (fun p => f (.inl p)),
        checksR S A W (fun p => emb (.inr p)) rts
          (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => f (.inr p)) with
      | some a, some b, some c => some (a ++ b ++ c)
      | _, _, _ => none

/-- checksExt's text -/
def extLP {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    List E.Pos → Option (List (Check lam (Lf ())))
  | [] => some []
  | p :: ps =>
      if isRead p then
        match f p, extLP we emb cms isRead f ps with
        | some op, some cs =>
          some (⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
                cms.getD (we.which p) default, we.depth⟩ :: cs)
        | _, _ => none
      else extLP we emb cms isRead f ps

variable (g : Fam (typedOracleFamily lam K (Lf ())))

/-- One check, climbed alone, on bits. -/
def runCheckB (c : Check lam (Lf ())) : Bool :=
  decide (climbF (nodeB Lf g) (c.path.map List.ofFn) c.j
      (List.ofFn (g OracleName.leaf c.inp : Dig lam)) = List.ofFn c.root)

/-! ### The verifier -/

variable {Y : Type} {E : ExtSpec} {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)

/-- what follows the chain: afterB's clauses -/
def afterLX (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Bool :=
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match checksR Lf P.S P.ann wq.sh embS rts R π.opens,
        extLP Lf wq.ext embE cms (tst (mk Re)) π.ext wq.ext.all with
  | some a, some b =>
      if (a ++ b).length ≤ wq.nOpen ∧
          (a ++ b).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
        (a ++ b).all (runCheckB Lf g) && reqPartB Lf g depthReq π.rtreq π.slot π.path π.rsalt ph &&
          P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
            (trP P.S P.ann wq.sh rts π.plains ρ π.opens)
      else false
  | _, _ => false

/-- THE LAX VERIFIER, EVALUABLE. -/
def verifyLX (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Bool :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => false
  | some (ρ, rts, ph) => afterLX Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph

/-! ### The ties -/

section
variable (L : BatchProtocolWithLeafBody I X)

theorem checksR_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (emb : (p : OPos (up S)) → OSym (up S) p → Body L) (rts : RootsOfChain lam (up S))
        (R : Finset (OPos (up S))) (isRead : OPos (up S) → Bool)
        (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      (∀ p, isRead p = true ↔ p ∈ R) →
      checksR (fun _ => L) S A W emb rts R f = checksB (up S) A W emb rts isRead f
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
      have ih := checksR_eq S A W (fun p => emb (.inr p)) rts
        (tailR (α := r.Pos) (β := OPos (up S)) R) (fun p => isRead (.inr p)) (fun p => f (.inr p))
        (fun p => by rw [mem_tailR]; exact h (.inr p))
      simp only [checksR, checksB, h0, ih, optP_eq]
      split
      · rename_i a' b' c' ha hb hc
        simp only [ha, hb, hc]
      · rename_i hn
        split
        · rename_i a' b' c' ha hb hc
          exact (hn a' b' c' ha hb hc).elim
        · rfl

theorem extLP_eq {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    ∀ ps : List E.Pos, extLP (fun _ => L) we emb cms isRead f ps =
      TypedOracleCompiler.Compile.Batch.checksExt we emb cms isRead f ps
  | [] => rfl
  | p :: ps => by
      simp only [extLP, TypedOracleCompiler.Compile.Batch.checksExt, extLP_eq we emb cms isRead f ps]
      split_ifs
      · split
        · rename_i op cs ha hb
          simp only [ha, hb]
        · rename_i hn
          split
          · rename_i op cs ha hb
            exact (hn op cs ha hb).elim
          · rfl
      · rfl

variable (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))

theorem runCheckB_eq (c : Check lam L) : runCheckB (fun _ => L) g c = runCheckF g c := by
  unfold runCheckB runCheckF
  rw [climbF_map List.ofFn (nodeP (fun _ => L) g) (nodeB (fun _ => L) g)
      (nodeB_ofFn (fun _ => L) g), decide_ofFn]
  rfl

variable {Y : Type} {E : ExtSpec}

/-- The chain alone: three ties joined. -/
theorem chainP_det (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    (recomputeChainOfProof t P.up wq embP xin cms x π).det g =
      chainP (fun _ => L) g L.early L.late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
        .first π.roots π.plains := by
  rw [← chainQT_eq]
  exact (twd_chain I X lam K L g L.early L.late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots
      π.plains).trans
    (thin_chain I X lam K L g L.early L.late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
        .first π.roots
      π.plains).symm

variable {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)

theorem afterLX_eq (h : ∀ R p, tst (mk R) p = true ↔ p ∈ R) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    afterLX (fun _ => L) g mk tst P wq embS embE depthReq cms x π ρ rts ph =
      afterBF g P.up wq embS embE depthReq cms x π ρ rts ph := by
  letI : DecidableEq E.Pos := wq.ext.dec
  letI : DecidableEq (OPos (up P.S)) := wq.decO
  have e : ∀ R, tst (mk R) = fun p => decide (p ∈ R) := fun R =>
    funext fun p => Bool.eq_iff_iff.2 ((h R p).trans decide_eq_true_iff.symm)
  have he : effsP P.S P.ann rts π.plains = effPlains (up P.S) P.ann rts π.plains :=
    (effsP_eq P.S P.ann rts π.plains).trans (effPlainsT_eq lam P.S P.ann rts π.plains)
  have ht : trP P.S P.ann wq.sh rts π.plains ρ π.opens = mkTr (up P.S) P.ann wq.sh rts
      π.plains ρ π.opens :=
    (trP_eq P.S P.ann wq.sh rts π.plains ρ π.opens).trans
        (mkTrT_eq lam K P.S P.ann wq.sh rts π.plains ρ π.opens)
  have hc := checksR_eq L P.S P.ann wq.sh embS rts (P.reads x ρ
      (effPlains (up P.S) P.ann rts π.plains))
    (fun p => decide (p ∈ P.reads x ρ (effPlains (up P.S) P.ann rts π.plains))) π.opens
    (fun p => decide_eq_true_iff)
  have hb : runCheckB (fun _ => L) g = runCheckF g := funext (runCheckB_eq L g)
  have hr : reqPartB (fun _ => L) g depthReq π.rtreq π.slot π.path π.rsalt ph = reqPartF g
      depthReq π ph :=
    (reqPartB_eq (fun _ => L) g depthReq π.rtreq π.slot π.path π.rsalt ph).trans
        (reqPartP_eq L g depthReq π ph)
  unfold afterLX afterBF
  dsimp only
  rw [he, hc, e, extLP_eq, hb, hr, ht]
  split
  · rename_i a b ha hb'
    simp only [ha, hb']
    rfl
  · rename_i hn
    split
    · rename_i a b ha hb'
      exact (hn a b ha hb').elim
    · rfl

/-- THE TIE. -/
theorem lax_thin (h : ∀ R p, tst (mk R) p = true ↔ p ∈ R) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    verifyLX (fun _ => L) g mk tst L.early L.late t P wq embS embP xin embE depthReq cms x π =
      (verifyB t P.up wq embS embP xin embE depthReq cms x π).det g := by
  unfold verifyLX verifyB
  rw [OComp.det_bind, chainP_det]
  cases chainP (fun _ => L) g L.early L.late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some r =>
    exact (afterLX_eq L g mk tst h P wq embS embE depthReq cms x π _ _ _).trans
      (afterB_det g P.up wq embS embE depthReq cms x π _ _ _).symm

/-- At the mask of a one-to-one numbering: no other hypothesis. -/
theorem lax_ext (idx : E.Pos → ℕ) (hi : Function.Injective idx) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    verifyLX (fun _ => L) g (maskOf idx) (maskBit idx) L.early L.late t P wq embS embP xin embE
        depthReq cms x π =
      (verifyB t P.up wq embS embP xin embE depthReq cms x π).det g :=
  letI : DecidableEq E.Pos := wq.ext.dec
  lax_thin L g (maskOf idx) (maskBit idx) (fun R p => maskBit_eq idx hi R p) t P wq embS embP xin
      embE depthReq cms x π

end

end TypedOracleCompiler.Run.Thin
