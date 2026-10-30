-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/JudgeOffRun.lean: what the judge of OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean computes under
a family of oracle functions; and, at the key's frame with the seeds' protocol
(OnBytes/TypedOracleCompiler/Slice/Plain3XSeeds.lean), in terms of two typed queries.

A part owes that the judge's run, under the oracle functions that a page reads off the one oracle,
says yes wherever the checker on bytes does (`fit`, OnBytes/TypedOracleCompiler/Slice/Part.lean). This file brings
the judge's run under a family F to three things: F's answers at the seeds' protocol's two queries;
a comparison; the compiled verifier's own value under F.
 - `judgeVal`, `judgeOffRun_det`: for any written batch protocol and any written second protocol:
   the run's value under F is: no, if the second protocol's chain refuses under F; no, if `seedOf`
   of its verifier's messages is not the instance's second part; else the strict compiled verifier's
   value under F;
 - `chainT_seeds_det`: at the key's frame the second protocol's chain under F has the value that
   `chainAt_seeds_det` (OnBytes/TypedOracleCompiler/Slice/SeedsRun.lean) states, at the queries `q0S`, `q1S` under
   the tag of Test with plain parts as they are;
 - `seedUnderF`: the value that the judge compares: `sOf` of the format's record of what the wiring
   makes of F's answer at `q1S`, at the link of F's answer at `q0S`;
 - `x3_run_det`: the judge's run at the key's frame under F says yes exactly if `seedUnderF` is the
   instance's second part and the strict compiled verifier says yes under F.

Main definitions: `judgeVal`, `seedUnderF`.
Main theorems: `judgeOffRun_det`, `chainT_seeds_det`, `x3_run_det`.

Not claimed. No page, no checker, no fit. That `seedUnderF` at a page's family is a program's seed
is not said here. Nothing on the compiled verifier's own value. Nothing on soundness. The sibling: a
second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.


Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3XSeeds
import OnBytes.TypedOracleCompiler.Slice.SeedsRun

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section
variable {I A Sd : Type} [DecidableEq Sd] {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L}
  (Z : WrittenB W) (ZT : Written W) (saltT : Bits) (rtT : Dig lam) (rootsT : List (Dig lam))
  (plainsT : Plains ZT.P.shape) (seedOf : Rho ZT.P.shape → Sd) (sMT sFS : ℕ)

/-- The judge's value, from the chain's value z and the compiled verifier's value v: no, if the
chain has refused; no, if the value that it yields is not x2; else v. -/
def judgeVal (x2 : Sd) (v : Bool) :
    Option (Rho ZT.P.shape × RootsOfChain lam ZT.P.shape × Phase lam) → Bool
  | some y => if seedOf y.1 = x2 then v else false
  | none => false

/-- The judge's run under a family F of oracle functions: `judgeVal` of the second protocol's
chain's value under F and the strict compiled verifier's value under F. -/
theorem judgeOffRun_det (F : Fam (typedOracleFamily lam W.K L)) (o : BatchOut Z) :
    (judgeOffRun Z ZT saltT rtT rootsT plainsT seedOf sMT sFS o).det F =
      judgeVal ZT seedOf o.2.1.2 ((Z.verifierS sMT sFS o.1 o.2.1 o.2.2).det F)
        ((ZT.chainT saltT rtT rootsT plainsT [o.1]).det F) := by
  unfold judgeOffRun
  rw [OComp.det_bind]
  cases (ZT.chainT saltT rtT rootsT plainsT [o.1]).det F with
  | none => rfl
  | some y =>
    show (if seedOf y.1 = o.2.1.2 then Z.verifierS sMT sFS o.1 o.2.1 o.2.2
      else OComp.pure false).det F =
        if seedOf y.1 = o.2.1.2 then (Z.verifierS sMT sFS o.1 o.2.1 o.2.2).det F else false
    by_cases h : seedOf y.1 = o.2.1.2
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      rfl

end

variable {A Sd : Type} [DecidableEq Sd] (G : Stretches)
  (dec : A × Sd → PQ.View → PQ.View → PQ.View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones) (salt : ℕ) (d : Sd)
  (e : _root_.Fmt.Entry) (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX)

/-- The interface at the key's frame with the seeds' protocol as its Test. -/
abbrev LXs := Strings.strung (LX3 G dec (earlyWith d) (TS G e))

omit [DecidableEq Sd] in
/-- At the key's frame the seeds' protocol's chain at the fixed string computes, under F, what
`chainAt_seeds_det` states. -/
theorem chainT_seeds_det (F : Fam (typedOracleFamily 256 (K + 1) (LXs G dec d e))) (cms : List (Dig 256)) :
    ((testWritten G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
        (prjST G.C e _)).chainT [] default [] (plainsT G.C (dSeed e) _) cms).det F =
      some (((PQ.wire0S G.C K chal).chal
            (F (.fb .test) (q0S (L := LXs G dec d e) .test G.C e _ id cms)).1,
          (PQ.wireS G.C K chal (dSeed e)).chal
            (F (.fb .test) (q1S (L := LXs G dec d e) .test G.C e _ id
              (TypedOracleCompiler.Compile.Batch.link
                (F (.fb .test) (q0S (L := LXs G dec d e) .test G.C e _ id cms))))).1, ()),
        ((none, some []), (none, some []), ()),
        .loc (TypedOracleCompiler.Compile.Batch.link (F (.fb .test)
                  (q1S (L := LXs G dec d e) .test G.C e _ id (TypedOracleCompiler.Compile.Batch.link
                    (F (.fb .test) (q0S (L := LXs G dec d e) .test G.C e _ id cms))))))) :=
  chainAt_seeds_det (L := LXs G dec d e) .test G.C e _ id K chal (we1 G.a) F cms

omit [DecidableEq Sd] in
/-- The value that the judge compares with the instance's second part, under F and the root cm. -/
def seedUnderF (sOf : List _root_.Fmt.Drawn → Sd) (F : Fam (typedOracleFamily 256 (K + 1) (LXs G dec d e)))
    (cm : Dig 256) : Sd :=
  seedOfS G e sOf ((PQ.wire0S G.C K chal).chal
      (F (.fb .test) (q0S (L := LXs G dec d e) .test G.C e _ id [cm])).1,
    (PQ.wireS G.C K chal (dSeed e)).chal
      (F (.fb .test) (q1S (L := LXs G dec d e) .test G.C e _ id
        (TypedOracleCompiler.Compile.Batch.link
          (F (.fb .test) (q0S (L := LXs G dec d e) .test G.C e _ id [cm]))))).1, ())

/-- The judge's run at the key's frame says yes under F exactly if the value drawn under F is the
instance's second part and the strict compiled verifier says yes under F. -/
theorem x3_run_det (sOf : List _root_.Fmt.Drawn → Sd) (sMT sFS : ℕ)
    (F : Fam (typedOracleFamily 256 (K + 1) (LXs G dec d e)))
    (out : BatchOut (ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e)
      (embST G.C e _) (prjST G.C e _))) :
    (judgeOffRun
        (ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        (testWritten G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _))
        [] default [] (plainsT G.C (dSeed e) _) (seedOfS G e sOf) sMT sFS out).det F = true ↔
      seedUnderF G dec K chal d e sOf F out.1 = out.2.1.2 ∧
        ((ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
          (prjST G.C e _)).verifierS sMT sFS out.1 out.2.1 out.2.2).det F = true := by
  have h3 := (judgeOffRun_det
    (ZXo G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _) (prjST G.C e _))
    (testWritten G dec K chal o salt d (TS G e) embE prjE (wTS G K chal e) (embST G.C e _)
      (prjST G.C e _))
    [] default [] (plainsT G.C (dSeed e) _) (seedOfS G e sOf) sMT sFS F out).trans
    (congrArg (judgeVal _ (seedOfS G e sOf) out.2.1.2 _)
      (chainT_seeds_det G dec K chal o salt d e embE prjE F [out.1]))
  refine Iff.trans (Eq.congr_left h3) ?_
  show (if seedUnderF G dec K chal d e sOf F out.1 = out.2.1.2 then _ else false) = true ↔ _
  by_cases h : seedUnderF G dec K chal d e sOf F out.1 = out.2.1.2
  · rw [if_pos h]
    exact ⟨fun h2 => ⟨h, h2⟩, fun h2 => h2.2⟩
  · rw [if_neg h]
    exact ⟨fun h2 => Bool.noConfusion h2, fun h2 => absurd h2.1 h⟩

end TypedOracleCompiler.Slice
