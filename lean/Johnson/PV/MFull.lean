-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MFull.lean: FOR DvOf AT THE FULL SIZE (Johnson/Top/Fire/Code/VerifyVAtD.lean)
  AND FOR Johnson/Top/Fire/Code/Vals/DvFull.lean:
  VALUES WITH CODE FOR THE LETTERS t · cfg · shape · pl0 · pl1 · m, AND THE FAST FAMILY.
No «noncomputable» stands here.
IMPORTS (every definition with code, by Lean's environment):
  Johnson/PV/CutAll · Johnson/PV/FamCut · Johnson/PV/MvAny · Johnson/PV/MvAt.




W4M.WriteSide (Johnson/PV/MvAny.lean) IS Rom.ImplV TO THE LETTER (blocks · rng · code); here its
  three fields are laid into Rom.ImplV.
STILL ARGUMENTS: K · h₀ k c' (read for the six pd alone, which dK dP overwrite: any values with
  code: e.g. Fmt.HO Fmt.oracle, G.k, G.c) · sp okS (the front set's; for a rehearsal: okS := fun _
  => true) · r₀ (THE SAME TERM AS DvOf's r₀) · c · sR · dK dP
(from the public reading pub8: cfg8 · key8 · prf8 as bytes) · linkF ( THE ENTRY FILE's CHAIN
  QUERIES' STRINGS: NO VALUE WITH CODE IS LAID HERE:
  a stand-in
«fun _ => none» sends every chain query of the entry file behind the escape: THE ENTRY's ARM THEN
  SAYS NO) · bk (LAID: bkF sX serL: backL2 (OnBytes/TypedOracleCompiler/Run/ArmBack.lean) at the library's
  serialisers: the text of backOfFull (declared nowhere in this library); sX, serL: arguments).
seed := recSeedK recT recLg recS (K + 1) ‹(seedBS recLg recS).b ≤ K + 1›
  (OnBytes/Flat/RecordSeed.lean:30): not laid here.



-/
import Johnson.Top.Fire.Code.VerifyVAtD
import Johnson.PV.MvPrep
import Johnson.Flat.SerArmAt
import Johnson.Top.Pub.ArmPublicTopFull
import OnBytes.TypedOracleCompiler.Run.ArmBack

set_option autoImplicit false
set_option maxRecDepth 40000

namespace PV.MFull
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub VerifiableInference.OnPublicFiles
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (lk : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX))
  (aL : RoundSplits (LvOf DK DP runK runP rK rP depthReq early lk).link.shape) (salt : ℕ)

/-- The interface. -/
abbrev carF := carrierV (LvOf DK DP runK runP rK rP depthReq early lk) (List Bool)
  (aTOf DK DP runK runP rK rP depthReq early lk) aL

/-- A W4M.WriteSide (Johnson/PV/MvAny.lean), as a Rom.ImplV. -/
def toImplV {S : OSpec} {lam : ℕ} (w : W4M.WriteSide S lam) : ImplV S lam := ⟨w.blocks, w.rng,
    w.code⟩

/-- The serialiser of the key file's plain parts. -/
def serKF : Ser (PBt (carF DK DP runK runP rK rP depthReq early lk aL) .test) :=
  serWhole (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (serFront (Ser.list serE3)) (serJoin (Ser.list serE3) serBytes) serBytes

/-! ## The record's wire's five letters (and the sixth) -/

/-- t. -/
def tF : Tag := .test

/-- cfg, at the configuration's digest c (32 bytes). -/
def cfgF (c : ByteArray) : List (Dig 256) := TypedOracleCompiler.Run.SeedVals.cfgL c

/-- shape: the tables' shape as the first seed query holds it. -/
def shapeF : Bits := pubShapeTopFull

/-- pl0 = pl1: the plain part of the seeds' two queries. -/
def plF : PlainPart (shapeOf (carF DK DP runK runP rK rP depthReq early lk aL) .test) (annOf (carF DK DP
           runK runP rK rP depthReq early lk aL) .test) :=
  TypedOracleCompiler.Run.SeedVals.plainFirst _ _ _ _

/-! ## m, and the fast family -/

variable (K : ℕ) (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains)
  (sp : X → ByteArray × ByteArray) (okS : X → Bool) (r₀ : RecFull) (c : ByteArray) (sR : ℕ)
  (linkF : FbIn 256 (carF DK DP runK runP rK rP depthReq early lk aL) .link × Fin (K + 1 + 1) →
      Option (List Bool)) (dK dP : Pd3)
  (bk : AllPts 256 (K + 1) (carF DK DP runK runP rK rP depthReq early lk aL) → List Bool) (O :
      ByteArray → ByteArray)

/-- The serialiser of the proof file's plain parts. -/
def serPF : Ser (PBt (carF DK DP runK runP rK rP depthReq early lk aL) .onl) :=
  serWhole (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
    (serFront (Ser.list serE3)) (serJoin (Ser.list serE3) serBytes) serBytes

/-- **bk: THE TOTAL CODE's put BEHIND THE ESCAPE**: backL2 at the library's serialisers (the text of
  backOfFull). sX: a serialiser of the instances; serL: one of the entry file's plain parts (at the
  written link: serLinkOf (ckP .two) ds). backOfFull, serLinkOf: declared nowhere in the library. -/
def bkF (sX : Ser X) (serL : Ser (PBt (carF DK DP runK runP rK rP depthReq early lk aL) .link)) :
    AllPts 256 (K + 1) (carF DK DP runK runP rK rP depthReq early lk aL) → List Bool :=
  (TypedOracleCompiler.Run.ArmBack.backL2 (carF DK DP runK runP rK rP depthReq early lk aL) (Ser.prod
              (Ser.option sX) (Ser.prod serRecFull serRecFull))
    _root_.Compile.serBits
    (fun t => match t with
      | .link => serL
      | .test => serKF DK DP runK runP rK rP depthReq early lk aL
      | .onl => serPF DK DP runK runP rK rP depthReq early lk aL) (K + 1)).put

/-- **THE VALUE FOR m.** sp: the request's two strings; okS: the front set's test on an instance;
  r₀: THE SAME RECORD AS DvOf's r₀; c: the configuration's digest; sR: the bytes of the request
  tree's salt; dK dP: the six chains'
parameters' digests; linkF: the entry file's chain queries' strings; bk: the total code's put behind
  the escape. -/
def mF : ImplV (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early lk aL)) 256 :=
  toImplV (W4M.mAt (L := carF DK DP runK runP rK rP depthReq early lk aL) (K := K) (ckP .two) (DK.at
      frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map sp).getD default)
    (fun z => (match z.1 with
      | some x => okS x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    frS.P.v c sR (Equiv.refl (List Bool)) (plF DK DP runK runP rK rP depthReq early lk aL) (serKF DK
        DP runK runP rK rP depthReq early lk aL) pubShapeTopFull (pubRestTopFull c) linkF (8 * salt)
        dK dP bk)

/-- **THE FAST FAMILY**: by W4M.famAt_reads it is what mF reads out of the hash function gOf O. -/
def famF : Fam (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early lk aL)) :=
  W4M.famAt (L := carF DK DP runK runP rK rP depthReq early lk aL) (K := K) (ckP .two) (DK.at
      frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map sp).getD default)
    (fun z => (match z.1 with
      | some x => okS x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    frS.P.v c sR (Equiv.refl (List Bool)) (plF DK DP runK runP rK rP depthReq early lk aL) (serKF DK
        DP runK runP rK rP depthReq early lk aL) pubShapeTopFull (pubRestTopFull c) linkF (8 * salt)
        dK dP bk O

/-- **THE FAST FAMILY IS WHAT mF READS OUT OF THE HASH FUNCTION gOf O**: point by point; no premise.
  (W4M.famAt_reads at these letters.) -/
theorem famF_reads (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 (carF DK DP runK runP rK rP
                    depthReq early lk aL) o) :
    famF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP bk O o
        q =
      ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP
          bk).rng o).symm fun j =>
        TypedOracleCompiler.Run.PageRun.gOf O () ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k
                    c' sp okS r₀ c sR linkF dK dP bk).code o q j) :=
  W4M.famAt_reads ..

/-- **THE FAST FAMILY IN THE FORM FOR A LONG EVALUATION** (W4M.famAtL, Johnson/PV/MvAtL.lean): a
  chain answer keeps as many delayed values as the round needs, and the last; under the proof file's
  tag what is kept does not hold the query; the tests are read
along the data. e: THE ESCAPE's STRING AS ONE CONSTANT: bk := fun _ => e (): the shouting stub. AT
  THE FULL SIZE, AND AT THE SHEET's K, THIS IS THE FORM TO RUN: a chain keeps every answer to its
  end. -/
def famFL (e : Unit → List Bool) : Fam (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early
                 lk aL)) :=
  W4M.famAtL (L := carF DK DP runK runP rK rP depthReq early lk aL) (K := K) (ckP .two) (DK.at
      frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map sp).getD default)
    (fun z => (match z.1 with
      | some x => okS x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    frS.P.v c sR (Equiv.refl (List Bool)) (plF DK DP runK runP rK rP depthReq early lk aL) (serKF DK
        DP runK runP rK rP depthReq early lk aL) pubShapeTopFull (pubRestTopFull c) linkF (8 * salt)
        dK dP e O

/-- **IT IS WHAT mF, AT bk := fun _ => e (), READS OUT OF THE HASH FUNCTION gOf O**: point by point;
  no premise. -/
theorem famFL_reads (e : Unit → List Bool) (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 (carF
                    DK DP runK runP rK rP depthReq early lk aL) o) :
    famFL DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP O e o
        q =
      ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP (fun
          _ => e ())).rng o).symm fun j =>
        TypedOracleCompiler.Run.PageRun.gOf O () ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k
                    c' sp okS r₀ c sR linkF dK dP (fun _ => e ())).code o q j) :=
  W4M.famAtL_reads ..

/-- **WHAT OF THE FAST FAMILY DOES NOT HANG ON THE QUERY, AS A VALUE** (W4M.Prep,
  Johnson/PV/MvPrep.lean): the page, both tests, the record «once a query». A CALLER BINDS IT ONCE
  (let pr := prepF …) AND HANDS ON famFP … pr e: so that the page is made once, and not,
as it may be under famF | famFL handed on with the query left open, at every query. -/
def prepF : W4M.Prep (carF DK DP runK runP rK rP depthReq early lk aL) (K + 1) :=
  W4M.prepAt (L := carF DK DP runK runP rK rP depthReq early lk aL) (K := K) (ckP .two) (DK.at
      frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map sp).getD default)
    (fun z => (match z.1 with
      | some x => okS x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    frS.P.v c sR (Equiv.refl (List Bool)) (plF DK DP runK runP rK rP depthReq early lk aL) (serKF DK
        DP runK runP rK rP depthReq early lk aL) pubShapeTopFull (pubRestTopFull c) linkF (8 * salt)
        dK dP

/-- **THE FAST FAMILY AT A PREPARED VALUE.** The hint under the key file's tag is
  W4M.hintK: it covers the seeds' two queries (at a smaller hint the record's seed can read
  95 | 140 blocks beyond it: each hashed anew for every bit). -/
def famFP (pr : W4M.Prep (carF DK DP runK runP rK rP depthReq early lk aL) (K + 1)) (e : Unit → List
    Bool) : Fam (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early lk aL)) :=
  W4M.famPrep pr e O (W4M.hintK (K + 1) (DK.at frS.P.T.a)) (Johnson.RunOne.Lite.needAt (DP.at
      frS.P.T.a))

/-- **AT prepF IT IS famFL.** -/
theorem famFP_is (e : Unit → List Bool) :
    famFP DK DP runK runP rK rP depthReq early lk aL K O (prepF DK DP runK runP rK rP depthReq early
        lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP) e =
      famFL DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP O e
          :=
  (W4M.famPrep_hint _ e O _ _ (Johnson.RunOne.Lite.needAt (DK.at frS.P.T.a))
      (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a))).trans rfl

/-- **SO IT IS WHAT mF, AT bk := fun _ => e (), READS OUT OF gOf O.** -/
theorem famFP_reads (e : Unit → List Bool) (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : domOf 256 (carF
                    DK DP runK runP rK rP depthReq early lk aL) o) :
    famFP DK DP runK runP rK rP depthReq early lk aL K O (prepF DK DP runK runP rK rP depthReq early
        lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP) e o q =
      ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK dP (fun
          _ => e ())).rng o).symm fun j =>
        TypedOracleCompiler.Run.PageRun.gOf O () ((mF DK DP runK runP rK rP depthReq early lk aL salt K h₀ k
                    c' sp okS r₀ c sR linkF dK dP (fun _ => e ())).code o q j) :=
  (congrFun (congrFun (famFP_is DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀
      c sR linkF dK dP O e) o) q).trans
    (famFL_reads DK DP runK runP rK rP depthReq early lk aL salt K h₀ k c' sp okS r₀ c sR linkF dK
        dP O e o q)

end PV.MFull
