-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
The verifier's side of an input at the small size, as a function of the three public files.

`DvOf` (Johnson/Top/Fire/Code/VerifyVAtDS.lean) builds that input from about thirty arguments.
`dvSmallAt` fills in those that can be computed from the three public files `Z = ⟨pol, lay, KL⟩` and
leaves the rest as arguments. Nothing here is `noncomputable`: every definition has code and can be
evaluated. DvFull.lean is the same text at the full size.

Filled in:
  * the makers' data `GS Z := bigZSmall Z` (Johnson/Top/ArmsAtFilesSmall.lean). Where the planner
    refuses the three files, this is a stand-in of which nothing is assumed: ask `planOk Z` first,
    and let a run's print say what it answered.
  * off `GS Z`: the two starting records, the two depths and `early`.
  * the key file's and the proof file's decision: `runKSmall (GS Z)` and `runPSmall (GS Z)`
    (Johnson/Flat/WireAt.lean). These are the makers' decisions (OnBytes/Maker/), filled in for
    rehearsals. They are not the description's own decisions.
  * the entry file's five parts `lkS`, `aLS`, `wLS`, `embLS`, `prjLS` (Vals/EntryFive.lean).
  * `saltS Z`, the salt's length off the plan (40 bytes at the stored examples' files), and the
    parameters `pAt` of it (`⟨576, 256, 0, 0⟩` there).
  * the code of a key, of which the commitment ID is the hash: `PV.EncId.encS` at `cS Z`, the
    configuration's digest of the three public files. `encS_eq` (Vals/EncId.lean) says that it is
    the library's `encId`.
  * `buildReqAt sizesSmall`, which builds the instance.
Still arguments: `DK`, `DP`, `K`, `t`, `cfg`, `shape`, `pl0`, `pl1`, `num`, `seed`, `r₀`, `m`.

`DK` and `DP` are the rounds' data of the key file and of the proof file. They are arguments so that
either of two pairs can be passed: `dkLanded`, `dpLanded` come from dry runs of `verify-on-bytes`;
`dkPlan`, `dpPlan` are made of the plan alone. A run's print should not differ between the two.

Limits:
  * What is passed for the arguments decides what the value is. Nothing here ties them to each other
    or to `Z`.
  * `planOk` and `dataPlanOk` are tests that a caller must ask. No definition in this file asks
    them.
  * `dataPlanOk` asks the makers' tests at the depth that the plan gives (`DK.a`, `DP.a`).
    `WholeD.at` overwrites that depth and tests nothing, so of data read as `DK.at a` at another
    depth `a` a yes of `dataPlanOk` says nothing.
  * `pAt` rests on a reading of which parameters the verifier uses (see its comment). No theorem
    holds it.
  * This file has no theorem. What is known of its definitions is known by evaluation, not by proof:
    `planOk` has said yes at the stored examples' public files, at both sizes, and no at five
    altered inputs. `dataPlanOk` has said yes there, and no at three altered sets of public files at
    each size (the layout cut in half, the policy cut in half, an empty `KL`). In all three the plan
    is not made: no run is known in which the plan is made and a makers' test says no.
  * The text compiles and has been evaluated in rehearsals, though not by its writer.

Terms: lean/GLOSSARY.md.


-/
import Johnson.Top.Fire.Code.VerifyVAtDS
import Johnson.Top.ArmsAtFilesSmall
import Johnson.Top.Fire.Code.Vals.EntryFive
import Johnson.Flat.ClaimsTrue
import Johnson.Top.Fire.Code.Vals.EncId
import OnBytes.Params.Configure
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Small
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutDS
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open PV.EntryFive

/-- The instance's type at the small size. -/
abbrev XS : Type := ReqAt sizesSmall

/-- The makers' data, of the three public files. -/
def GS (Z : OnBytes.K.Pub) : FilesParameters XS RecSmall := OnBytes.K.ArmsAtFiles.bigZSmall Z

/-- Does the planner take the three public files? Where it does not, `GS` is a stand-in of which
  nothing is assumed. -/
def planOk (Z : OnBytes.K.Pub) : Bool :=
  match OnBytes.Flat.planOf Z with
  | .ok _ => true
  | .error _ => false

/-- The salt's length in bytes, off the plan. -/
def saltS (Z : OnBytes.K.Pub) : ℕ := (GS Z).k.oneTime.given.plan.salt

/-- The compiler's parameters. The verifier reads the first two alone, `sMT` and `sFS`
  (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean, LinkAns.lean), so the other two are 0. That these are the
  right two numbers is a reading of those files, held by no theorem; in one run a strict check of
  the stored examples' entry files said yes at them. -/
def pAt (salt : ℕ) : _root_.Compile.Params := ⟨256 + 8 * salt, 256, 0, 0⟩

/-- The configuration's digest of the three public files, as 256 bits. -/
def cS (Z : OnBytes.K.Pub) : Dig 256 :=
  _root_.Run.bytesToDig (OnBytes.Params.configurationDigest [Z.pol, Z.lay, Z.KL])

section At
variable (Z : OnBytes.K.Pub) (DK DP : WholeD) (K : ℕ)

set_option quotPrecheck false in
local notation "LVs" => LvOf DK DP (runKSmall (GS Z)) (runPSmall (GS Z)) (GS Z).rec₀ (GS Z).z₀.2
  (GS Z).depthReq (GS Z).early lkS
set_option quotPrecheck false in
local notation "ATs" => aTOf DK DP (runKSmall (GS Z)) (runPSmall (GS Z)) (GS Z).rec₀ (GS Z).z₀.2
  (GS Z).depthReq (GS Z).early lkS

/-- **The value, with the rounds' data as arguments.** -/
def dvSmallAt (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (carrierV LVs (List Bool) ATs aLS) t)
      (annOf (carrierV LVs (List Bool) ATs aLS) t))
    (num : ℕ → Plains (LVs).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LVs).Seed)
    (r₀ : (LVs).Rec)
    (m : ImplV (typedOracleFamily 256 (K + 1) (carrierV LVs (List Bool) ATs aLS)) 256) : InputV :=
  DvOf DK DP (runKSmall (GS Z)) (runPSmall (GS Z)) (GS Z).rec₀ (GS Z).z₀.2 (GS Z).depthReq
    (GS Z).k.oneTime.binding.logLeaves (GS Z).early lkS K (saltS Z) aLS (wLS K) (embLS (saltS Z))
    (prjLS (saltS Z)) t cfg shape pl0 pl1 num seed r₀ (pAt (saltS Z)) m
    (fun k => PV.EncId.encS (cS Z) k.cm k.rcd) (buildReqAt sizesSmall)

end At

/-- The rounds' data that come from dry runs of `verify-on-bytes` (`dataKSmall`, `dataPSmall`:
  Johnson/Flat/WireAt.lean). They are not made of the plan. Kept for the callers that name them;
  `dkPlan` and `dpPlan` below take their place. -/
def dkLanded (Z : OnBytes.K.Pub) : WholeD := dataKSmall (GS Z)
def dpLanded (Z : OnBytes.K.Pub) : WholeD := dataPSmall (GS Z)

/-! ## The rounds' data, made of the plan alone: no dry run of `verify-on-bytes` -/

/-- `(DK, DP, tK, tP)`: the two files' rounds' data, and what the makers' tests say at the key
  file's and at the proof file's written rounds. The data are `dataKAt` and `dataPAt`
  (Johnson/G/RoundsOfPlan.lean) at one `madeOf` of the three public files. These two functions do
  not refuse where the makers' tests say no: they return the data of three empty lists. So the tests
  are asked here by name, at the data's own depth. -/
def dataPlan (Z : OnBytes.K.Pub) : Except String (WholeD × WholeD × Bool × Bool) := do
  let m ← Johnson.G.OfPlan.madeOf Z.pol Z.lay Z.KL
  let (rk, rp) ← Johnson.G.OfPlan.roundsAt m
  let DK ← Johnson.G.OfPlan.dataKAt m
  let DP ← Johnson.G.OfPlan.dataPAt m
  pure (DK, DP, okAt DK.a (some rk), okAt DP.a (some rp))

/-- The data of three empty lists of rounds. What a file's decision says at them is not stated here.
  -/
def emptyD : WholeD := WholeD.of srS.P.T.a (OnBytes.Three.Whole.of [] [] [])

/-- The key file's rounds' data, made of the plan; `emptyD` where the plan is not made. -/
def dkPlan (Z : OnBytes.K.Pub) : WholeD :=
  match dataPlan Z with
  | .ok x => x.1
  | .error _ => emptyD

/-- The proof file's rounds' data, made of the plan; `emptyD` where the plan is not made. -/
def dpPlan (Z : OnBytes.K.Pub) : WholeD :=
  match dataPlan Z with
  | .ok x => x.2.1
  | .error _ => emptyD

/-- The plan is made, and the makers' tests say yes at both files' written rounds, at the depth that
  the plan gives. See the head's limits. -/
def dataPlanOk (Z : OnBytes.K.Pub) : Bool :=
  match dataPlan Z with
  | .ok x => x.2.2.1 && x.2.2.2
  | .error _ => false

end LPFD.Small

#print axioms LPFD.Small.GS
#print axioms LPFD.Small.planOk
#print axioms LPFD.Small.saltS
#print axioms LPFD.Small.pAt
#print axioms LPFD.Small.cS
#print axioms LPFD.Small.dvSmallAt
#print axioms LPFD.Small.dkLanded
#print axioms LPFD.Small.dpLanded
#print axioms LPFD.Small.dataPlan
#print axioms LPFD.Small.dkPlan
#print axioms LPFD.Small.dpPlan
#print axioms LPFD.Small.dataPlanOk
