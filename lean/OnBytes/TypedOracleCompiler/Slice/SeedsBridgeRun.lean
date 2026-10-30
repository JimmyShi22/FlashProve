-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedsBridgeRun.lean: under the law on a page of
OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean, the value that the judge of OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean
compares with the seeds in its instance is the seed of the key's table under the oracle; so a yes of
the judge's run under the family read out of an oracle says that the instance's seeds are that seed.

OnBytes/TypedOracleCompiler/Slice/JudgeOffRun.lean writes the judge's run under a family F as one equivalence
(`x3_run_det`): the value drawn under F (`seedUnderF`) is the instance's second part, and the strict
compiled verifier says yes. `seedUnderF` is the seeds off what the wire makes of F's answer at the
drawing round's query, behind the link of F's answer at the first query. There the typed answer has
K + 1 blocks and a tail, so its implementation has two strings more than K a query
(`SeedRound.secondPS` at the successor of K); at a round without work the wire takes the first K.
`SeedsPage` is used at K + 1, `seedUnder_of_blocks` (OnBytes/Slice/SeedDrawn.lean) at K.

Main theorems.
 `seedUnderF_eq`        UNDER `SeedsPage`, at the library's kit `ckP .two`, its wire `chalP .two K`
                        and the entry `seedEntry lg s`: `seedUnderF` at the family read out of g is
                        the seed that `seedUnder lg s k g` gives.
 `x3_run_seed`          IF THE JUDGE'S RUN SAYS YES UNDER THE FAMILY READ OUT OF g, THE SEEDS IN ITS
                        INSTANCE ARE THE SEED UNDER g.

Asked: 0 < s; K is at least the number of blocks of the seeds' sampler; the implementation obeys
`SeedsPage` at the name of the key k and the two queries of the seeds' chain under the root.

Not claimed. NO IMPLEMENTATION IS SHOWN TO OBEY `SeedsPage`: no page with the seeds' tag is written.
That the root under which the chain runs is the key's root: `SeedsPage` names a key's name and a
root side by side, and whoever gives a page ties them (`firstPN_key`). The answers of the record:
nothing here. That the judge ever says yes. NOTHING ON SOUNDNESS IS SHOWN; no probability. What the
heads of SeedsBridge.lean and JudgeOffRun.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the
one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.SeedsBridge
import OnBytes.TypedOracleCompiler.Slice.JudgeOffRun

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP chalP digToBytes bytesToBits)
open OnBytes.Slice (seedBS seedOfDrawn roundDraws GE NZ seedEntry dsOf_seedEntry seedUnder
  seedUnder_of_blocks)

variable {An : Type} (lg s : ℕ) (G : Stretches)
  (dec : An × (Fin s → (Fin lg → GE) × NZ) → PQ.View → PQ.View → PQ.View → Bool)
  (K : ℕ) (d : Fin s → (Fin lg → GE) × NZ)

/-- UNDER THE LAW ON A PAGE, THE VALUE THAT THE JUDGE COMPARES WITH THE INSTANCE'S SEEDS IS THE
SEED UNDER THE ORACLE: at the library's kit and wire and the entry `seedEntry lg s`, in the family
that is read out of g through an implementation m that obeys `SeedsPage` at the name of the key k
and the two queries of the seeds' chain under the root cm. -/
theorem seedUnderF_eq (hs0 : 0 < s) (hK : (seedBS lg s).b ≤ K)
    (m : OracleCoding (typedOracleFamily 256 (K + 1) (LXs (atBlocks G) dec d (seedEntry lg s))) 256)
    (k : OnBytes.Tie.IdKey) (cm : Dig 256)
    (hp : SeedsPage m .test (OnBytes.Key.nameOf k.1 k.2.1 k.2.2)
      (q0S (L := LXs (atBlocks G) dec d (seedEntry lg s)) .test (ckP .two) (seedEntry lg s) _ id
        [cm])
      (q1S (L := LXs (atBlocks G) dec d (seedEntry lg s)) .test (ckP .two) (seedEntry lg s) _ id))
    (g : Fam (rom 256)) :
    some (seedUnderF (atBlocks G) dec K (chalP .two K) d (seedEntry lg s) (seedOfDrawn lg s)
      (readBlocks m g) cm) = seedUnder lg s k g :=
  (seedUnder_of_blocks lg s K (seedEntry lg s) (dsOf_seedEntry lg s hs0) hK k g
    (firstBlocks 256 (K + 1) K (fbAt m g .test
      (q1S (L := LXs (atBlocks G) dec d (seedEntry lg s)) .test (ckP .two) (seedEntry lg s) _ id
        (Batch.link (fbAt m g .test
          (q0S (L := LXs (atBlocks G) dec d (seedEntry lg s)) .test (ckP .two) (seedEntry lg s) _
            id [cm]))))).1)
    fun i => by
      have hi : i.val < K + 1 := Nat.lt_succ_of_lt i.isLt
      unfold firstBlocks
      rw [dif_pos hi]
      refine (hp.round g _ ⟨i.val, hi⟩).trans ?_
      rw [hp.first g]
      rfl).symm

/-- IF THE JUDGE'S RUN SAYS YES UNDER THE FAMILY READ OUT OF g, THE SEEDS IN ITS INSTANCE ARE THE
SEED UNDER g, under the law on a page at the name of a key k and the output's root: what the
join's clause on the record asks of the key's part, for the seed. -/
theorem x3_run_seed [DecidableEq (Fin s → (Fin lg → GE) × NZ)] (o : (atBlocks G).Ones) (salt : ℕ)
    (embE : PQ.SgX → List Bool) (prjE : List Bool → Option PQ.SgX) (hs0 : 0 < s)
    (hK : (seedBS lg s).b ≤ K) (sMT sFS : ℕ)
    (m : OracleCoding (typedOracleFamily 256 (K + 1) (LXs (atBlocks G) dec d (seedEntry lg s))) 256)
    (k : OnBytes.Tie.IdKey) (g : Fam (rom 256))
    (out : BatchOut (ZXo (atBlocks G) dec K (chalP .two K) o salt d
      (TS (atBlocks G) (seedEntry lg s)) embE prjE
      (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s)) (embST (ckP .two) (seedEntry lg s) _)
      (prjST (ckP .two) (seedEntry lg s) _)))
    (hp : SeedsPage m .test (OnBytes.Key.nameOf k.1 k.2.1 k.2.2)
      (q0S (L := LXs (atBlocks G) dec d (seedEntry lg s)) .test (ckP .two) (seedEntry lg s) _ id
        [out.1])
      (q1S (L := LXs (atBlocks G) dec d (seedEntry lg s)) .test (ckP .two) (seedEntry lg s) _ id))
    (h : (judgeOffRun
        (ZXo (atBlocks G) dec K (chalP .two K) o salt d (TS (atBlocks G) (seedEntry lg s)) embE
          prjE (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s))
          (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _))
        (testWritten (atBlocks G) dec K (chalP .two K) o salt d
          (TS (atBlocks G) (seedEntry lg s)) embE prjE
          (wTS (atBlocks G) K (chalP .two K) (seedEntry lg s))
          (embST (ckP .two) (seedEntry lg s) _) (prjST (ckP .two) (seedEntry lg s) _))
        [] default [] (plainsT (ckP .two) (dSeed (seedEntry lg s)) _)
        (seedOfS (atBlocks G) (seedEntry lg s) (seedOfDrawn lg s)) sMT sFS out).det
          (readBlocks m g) = true) :
    seedUnder lg s k g = some out.2.1.2 := by
  have h1 := ((x3_run_det (atBlocks G) dec K (chalP .two K) o salt d (seedEntry lg s) embE prjE
    (seedOfDrawn lg s) sMT sFS (readBlocks m g) out).1 h).1
  rw [← seedUnderF_eq lg s G dec K d hs0 hK m k out.1 hp g, h1]

end TypedOracleCompiler.Slice
