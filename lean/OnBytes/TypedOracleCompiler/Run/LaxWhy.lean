-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LaxWhy.lean: which clause of the evaluable lax verifier (Run/LaxThin.lean: verifyLX)
says no: whyLX; and: whyLX … = .yes exactly if verifyLX … = true. A tool for tests on damaged
strings: a "no" alone does not say what refused. General in a skeleton P. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.
Why. In a test on damaged strings, a result "refused" does not by itself say which clause refused.
  Why  chain (chainP refuses: by its text (Run/ThinDefs.lean:182-226) only where the string has too
      few roots or the phase allows no act: it tests no work) | own (a read position of an own tree
      has no opening) | ext (the like, external) | few (more checks than nOpen) | formed (a check is
      not well formed, or deeper than maxDepth) | walks (a climb does not end in its root) | req
      (the request tree) | accept (the local verifier's decision) | yes
  afterWhy, whyLX  afterLX's and verifyLX's texts, each "false" replaced by the name of the clause,
      in afterB's order: the first clause that fails is named
  afterWhy_yes, whyLX_yes
What is not said. That the clause named is the only one that fails. That the order of the names is
afterLX's is by copying, checked by no theorem: only ".yes ↔ true" is proved. A typing that gives no
string is before this function: the caller's to name. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.LaxThin

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

/-- which clause says no -/
inductive Why where
  | chain | own | ext | few | formed | walks | req | accept | yes
  deriving DecidableEq, Repr

variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ())))
  {Y : Type} {E : ExtSpec} {M : Type} (mk : Finset E.Pos → M) (tst : M → E.Pos → Bool)

def afterWhy (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) : Why :=
  let R := P.reads x ρ (effsP P.S P.ann rts π.plains)
  let Re := P.extReads x ρ
  match checksR Lf P.S P.ann wq.sh embS rts R π.opens,
        extLP Lf wq.ext embE cms (tst (mk Re)) π.ext wq.ext.all with
  | none, _ => .own
  | some _, none => .ext
  | some a, some b =>
      if (a ++ b).length ≤ wq.nOpen then
        if (a ++ b).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) then
          if (a ++ b).all (runCheckB Lf g) then
            if reqPartB Lf g depthReq π.rtreq π.slot π.path π.rsalt ph then
              if P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
                  (trP P.S P.ann wq.sh rts π.plains ρ π.opens) then .yes
              else .accept
            else .req
          else .walks
        else .formed
      else .few

/-- Which clause says no. -/
def whyLX (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) : Why :=
  match chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => .chain
  | some (ρ, rts, ph) => afterWhy Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph

theorem afterWhy_yes (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ())) (embE : E.Sym → Body (Lf ()))
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    afterWhy Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph = .yes ↔
      afterLX Lf g mk tst P wq embS embE depthReq cms x π ρ rts ph = true := by
  unfold afterWhy afterLX
  dsimp only
  cases checksR Lf P.S P.ann wq.sh embS rts (P.reads x ρ (effsP P.S P.ann rts π.plains)) π.opens
      with
  | none => simp
  | some a =>
    cases extLP Lf wq.ext embE cms (tst (mk (P.extReads x ρ))) π.ext wq.ext.all with
    | none => simp
    | some b =>
      dsimp only
      by_cases h1 : (a ++ b).length ≤ wq.nOpen
      · by_cases h2 : (a ++ b).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) = true
        · have h12 : (a ++ b).length ≤ wq.nOpen ∧
              (a ++ b).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) = true :=
                  ⟨h1, h2⟩
          rw [if_pos h1, if_pos h2, if_pos h12]
          cases (a ++ b).all (runCheckB Lf g) <;>
            cases reqPartB Lf g depthReq π.rtreq π.slot π.path π.rsalt ph <;>
            cases P.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
              (trP P.S P.ann wq.sh rts π.plains ρ π.opens) <;> simp
        · have h12 : ¬ ((a ++ b).length ≤ wq.nOpen ∧
              (a ++ b).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) = true) :=
                  fun h => h2 h.2
          rw [if_pos h1, if_neg h2, if_neg h12]
          simp
      · have h12 : ¬ ((a ++ b).length ≤ wq.nOpen ∧
            (a ++ b).all (fun c => wellP Lf c && decide (c.depth ≤ wq.maxDepth)) = true) :=
                fun h => h1 h.1
        rw [if_neg h1, if_neg h12]
        simp

theorem whyLX_yes (early : X → X) (late : Option ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body (Lf ()))
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (xin : Y → Option X) (embE : E.Sym → Body (Lf ())) (depthReq : ℕ) (cms : List (Dig lam))
    (x : Y) (π : OneProtocolProof lam P.up) :
    whyLX Lf g mk tst early late t P wq embS embP xin embE depthReq cms x π = .yes ↔
      verifyLX Lf g mk tst early late t P wq embS embP xin embE depthReq cms x π = true := by
  unfold whyLX verifyLX
  cases chainP Lf g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0 .first
      π.roots π.plains with
  | none => simp
  | some r => exact afterWhy_yes Lf g mk tst P wq embS embE depthReq cms x π _ _ _

end TypedOracleCompiler.Run.Thin
