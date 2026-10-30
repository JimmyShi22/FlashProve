-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryJudgeRun.lean: THE ENTRY's JUDGE WHOLE (judgeRunEL, Slice/JudgeE.lean: the
seeds' chain under each outer root, compared with the instance's seeds; then the lax verifier) AS
ONE CLOSED, EVALUABLE TERM: runJE; AND THE TIE: runJE … = true EXACTLY IF assembleE GIVES out AND
(judgeRunEL … out).det F = true.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. Wanted: "the judge's first half in front (the seeds' two chains by chainP at T's skeleton; the
comparison): runJE : Bool with runJE_eq".
  chainB_detP           the road's chain over a skeleton's rounds, under oracle functions, is the
    evaluable chainP: (recomputeChain t cms x salt rtreq (up S) A W embP i ph rts pls).det g = chainP (fun _
    => L) g L.early L.late t cms x salt rtreq S A W embP i ph rts pls  (Run/LaxThin.lean's
    chainP_det, at any S, A, W)
  seedChain D early e F c     [ITS PLAIN PARTS ARE WRITTEN AT THE SKELETON's ROUNDS ((s0 C).dPlain,
    (roundS C d).dPlain, ()): SeedsT.lean's plainsT says ".up.dPlain": one value by definition, BUT
    EVALUATED IT BUILDS THE ROUND, WITH THE LIST OF ALL ITS VERIFIER MESSAGES: ToyEntry's first run
    ended "out of memory" in seedChain] the seeds' protocol's chain at the one fixed string (no
    salt, no root, the plain parts plainsT: each round's default), under the tag of Test and the one
    outer root c: chainP at the skeleton SOf D.C [dSeed e]
  cmpG, cmpT_det_ch     the comparisons over any way to run the chain under one root; cmpT
    (Slice/JudgeE.lean) under oracle functions is that (general in W, Ex, ZT)
  cmpE … l i s          for each root of l: that chain; a no if it refuses or if sOf of what it
    draws is not the value number i, i + 1, … of s
  cmpE_eq               it is (cmpT (testXE …) [] default [] (plainsT …) (seedOfE D e sOf) (pack2 S)
    l i s).det F
  runJE D dec B E d₁-free: early e sOf F r0 r1 x o : Bool     cmpE at [dig r0, dig r1], then
    runE
  runJE_eq          runJE … = true ↔ ∃ out, assembleEZ … r0 r1 x o = some out ∧ (judgeRunEL (ZXE
    …) (testXE …) [] default [] (plainsT …) (seedOfE D e sOf) (pack2 S) out).det F = true
THE LETTERS ARE THOSE OF EntryAt.base (Slice/EntryDelivers.lean): T := TSE D e; wT := wTSE D e; eT |
pT := embST | prjST; saltT := []; rtT := default; rootsT := []; plainsT := SeedsT.lean's plainsT D.C
(dSeed e) (oneExternalString (2 ^ D.a) SgX); at e := seedEntry lg s, sOf := seedOfDrawn lg s, early := earlyTwo
d₁ it is the part's own judge's run.
WHAT IS NOT SAID. That it comes home at a size; any family; the typing's asking half. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRun
import OnBytes.TypedOracleCompiler.Slice.EntryXRun

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf)
open _root_.Run.PQ (View SgX)
open _root_.Run (bytesToDig)
open _root_.Run.Twin (RS)
open TypedOracleCompiler.Run.Thin (chainP thin_chain)
open TypedOracleCompiler.Run.Twin (chainT_eq twd_chain)

/-- The road's chain over a skeleton's rounds, under oracle functions, is chainP. -/
theorem chainB_detP {I X : Type} {lam K : ℕ} (L : BatchProtocolWithLeafBody I X)
    (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L)) (t : Tag)
    (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) (S : List RS)
    (A : RoundSplits (_root_.Run.Twin.up S)) (W : RoundsQueryLayout lam K (_root_.Run.Twin.up S) A)
    (embP : PlainPart (_root_.Run.Twin.up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
    (rts : List (Dig lam)) (pls : Plains (_root_.Run.Twin.up S)) :
    (recomputeChain t cms x salt rtreq (_root_.Run.Twin.up S) A W embP i ph rts pls).det g =
      chainP (fun _ => L) g L.early L.late t cms x salt rtreq S A W embP i ph rts pls := by
  rw [← chainT_eq]
  exact (twd_chain I X lam K L g L.early L.late t cms x salt rtreq S A W embP i ph rts pls).trans
    (thin_chain I X lam K L g L.early L.late t cms x salt rtreq S A W embP i ph rts pls).symm

/-- the comparisons, over any way to run the chain under one root -/
def cmpG {lam : ℕ} {R S Sd : Type} [DecidableEq S] (ch : Dig lam → Option R) (val : R → S)
    (get : Sd → ℕ → S) :
    List (Dig lam) → ℕ → Sd → Bool
  | [], _, _ => true
  | c :: l, i, s =>
    match ch c with
    | some y => if val y = get s i then cmpG ch val get l (i + 1) s else false
    | none => false

/-- cmpT's comparisons under oracle functions, given the chain's value under each root -/
theorem cmpT_det_ch {I A Sd S : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L}
    {Ex : ExtRd L} [DecidableEq S]
    (ZT : Written W) (saltT : Bits) (rtT : Dig lam) (rootsT : List (Dig lam))
        (plainsT : Plains ZT.P.shape)
    (seedOf : Rho ZT.P.shape → S) (Pk : Pack Ex.k S Sd)
        (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam W.K L))
    (ch : Dig lam → Option (Rho ZT.P.shape × RootsOfChain lam ZT.P.shape × Phase lam))
    (hch : ∀ c, (ZT.chainT saltT rtT rootsT plainsT [c]).det F = ch c) :
    ∀ (l : List (Dig lam)) (i : ℕ) (s : Sd),
      (cmpT ZT saltT rtT rootsT plainsT seedOf Pk l i s).det F = cmpG ch
          (fun y => seedOf y.1) Pk.get l i s
  | [], _, _ => rfl
  | c :: l, i, s => by
      show (((ZT.chainT saltT rtT rootsT plainsT [c]).bind fun z =>
        match z with
        | some y => if seedOf y.1 = Pk.get s i then
            cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s else OComp.pure false
        | none => OComp.pure false).det F) = _
      rw [OComp.det_bind, hch c]
      unfold cmpG
      cases ch c with
      | none => rfl
      | some y =>
        dsimp only
        split_ifs
        · exact cmpT_det_ch ZT saltT rtT rootsT plainsT seedOf Pk F ch hch l (i + 1) s
        · rfl

variable {A S : Type} [DecidableEq S] (D : XD) (dec : A × (S × S) → View → Bool) {Bd : Type}
    (B : BodyD Bd) (E : OwnE Bd D)
  (early : A × (S × S) → A × (S × S)) (e : _root_.Fmt.Entry) (sOf : List _root_.Fmt.Drawn → S)

/-- the seeds' chain under one outer root -/
def seedChain (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (TSE D e)))) (c : Dig 256) :
    Option (Rho (TSE D e).shape × RootsOfChain 256 (TSE D e).shape × Phase 256) :=
  chainP (fun _ => LXE (Bd := Bd) D early (TSE D e)) F early none .test [c] none [] default
      (SOf D.C [dSeed e])
    (_root_.Run.Twin.allLo (SOf D.C [dSeed e])) (wTSE D e).sh id 0 .first []
    ((PQ.s0 D.C).dPlain, (PQ.roundS D.C (dSeed e)).dPlain, ())

/-- the comparisons -/
def cmpE (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (TSE D e))))
    :
    List (Dig 256) → ℕ → S × S → Bool :=
  cmpG (seedChain D early e F) (fun y => seedOfE D e sOf y.1) (pack2 S).get

theorem cmpE_eq (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (TSE D e))))
    (l : List (Dig 256)) (i : ℕ) (s : S × S) :
    (cmpT (Ex := ext2R (LXE (Bd := Bd) D early (TSE D e)))
      (testXE D B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) [] default []
      (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)) (seedOfE D e sOf) (pack2 S) l i s).det F = cmpE D
          early e sOf F l i s :=
  cmpT_det_ch (Ex := ext2R (LXE (Bd := Bd) D early (TSE D e)))
    (testXE D B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) [] default []
    (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)) (seedOfE D e sOf) (pack2 S) F
        (seedChain D early e F)
    (fun c => chainB_detP (LXE (Bd := Bd) D early (TSE D e)) F .test [c] none [] default
        (SOf D.C [dSeed e])
      (_root_.Run.Twin.allLo (SOf D.C [dSeed e])) (wTSE D e).sh id 0 .first []
          (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)))
    l i s

/-- The judge's run, evaluable. -/
def runJE (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (TSE D e)))) (r0 r1 : ByteArray)
    (x : A × (S × S)) (o : _root_.Fmt.ChainOut) : Bool :=
  cmpE D early e sOf F [bytesToDig r0, bytesToDig r1] 0 x.2 && runE D dec B E early
      (fun _ => TSE D e) F r0 r1 x o

/-- The tie. -/
theorem runJE_eq (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (TSE D e))))
    (r0 r1 : ByteArray) (x : A × (S × S)) (o : _root_.Fmt.ChainOut) :
    runJE D dec B E early e sOf F r0 r1 x o = true ↔
      ∃ out, assembleEZ D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _) r0 r1 x
          o = some out ∧
        (judgeRunEL (ZXE D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))
          (testXE D B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) [] default []
          (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)) (seedOfE D e sOf) (pack2 S) out).det
              F = true := by
  unfold runJE
  rw [Bool.and_eq_true, runE_eq D dec B E early (TSE D e) (wTSE D e) (embST D.C e _)
      (prjST D.C e _)]
  constructor
  · rintro ⟨h1, out, ho, hv⟩
    refine ⟨out, ho, (judgeRunEL_det (testXE D B E early (TSE D e) (wTSE D e) (embST D.C e _)
        (prjST D.C e _)) [] default []
      (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)) (seedOfE D e sOf) (pack2 S)
      (ZXE D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) F out).2 ⟨?_, hv⟩⟩
    refine (cmpE_eq D B E early e sOf F _ 0 out.2.1.2).trans ?_
    rw [assembleE_roots ho, assembleE_x ho]
    exact h1
  · rintro ⟨out, ho, hj⟩
    obtain ⟨h1, hv⟩ := (judgeRunEL_det (testXE D B E early (TSE D e) (wTSE D e) (embST D.C e _)
        (prjST D.C e _)) [] default []
      (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)) (seedOfE D e sOf) (pack2 S)
      (ZXE D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) F out).1 hj
    refine ⟨?_, out, ho, hv⟩
    have h2 := (cmpE_eq D B E early e sOf F _ 0 out.2.1.2).symm.trans h1
    rw [assembleE_roots ho, assembleE_x ho] at h2
    exact h2

end TypedOracleCompiler.Slice
