-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/After.lean: the ten conditions of `AfterRuns` on what the compiled verifier of a
key file, and of a proof file, checks behind its three chains hold at the typing of a file that was
read.

`AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean) has ten fields: the first chain's seal, the openings'
form (four), the walks (four), the decision. OnBytes/Maker/Page/AfterOf.lean has the ten statements
(`after_read`) at the description and the wire record that OnBytes/Maker/ makes of a file's data.
Here they are laid into the record, at `fileKey` (Johnson/Maker/Written.lean) and `fileProofA`
(Johnson/Maker/WrittenA.lean).

  `afterRuns_key_of`, `afterRuns_proof_of`   **the ten fields**, for any oracle functions g that
      meet two records: `GRows` (OnBytes/Maker/Page/RunsTools.lean: how g answers the chains'
      queries) and `CodeOwes` (OnBytes/Maker/WalksOf.lean: how g answers at a vertex and a leaf, at
      the bodies in use).
    the seal      `sealAt_of_read` (OnBytes/Maker/Page/Runs.lean)
    the openings  `opened_read` (OnBytes/Maker/Page/Opened.lean), with `draws_of_read`
    the walks     `walks_of` (OnBytes/Maker/WalksOf.lean), with `PageOwes.readOwes`
    the decision  `accept_of_read` (OnBytes/Maker/Page/Accept.lean)

The premises, beside the two records on g.
  `PageOwes` (OnBytes/Maker/Page/Owes.lean): the reading, the parameters, tests on the data.
  The data W are made of the dry run's three lists of rounds.
  `typeFile` returns π at the reading r. It holds the test `sameTwice` (OnBytes/Maker/Tables.lean)
    that two openings of one place hold one column and salt.
  The three chains' values under g.
  The test on the three silent rounds' messages says yes; the file's decision says yes at all views
    that are as the views read but for the digests drawn.
  The first of the commitments is the digest of the root in item 0 of the second chain's statement.
None is shown here.

Not claimed. The fields of `Left` beside `after` (`laws`, `wire`, `fits`, `saltLen`, `slotLt`,
`pathLen`, `climb`): among them the climb in the request tree and the lengths of the salt and the
path, which the compiled verifier checks behind its chains too. Nothing on soundness (index binding
included), what a root fixes, opening-form binding, no two openings of a commitment, correctness of
extraction or whatever else names a committer or a prover.

-/
import Johnson.Maker.WrittenA
import OnBytes.Maker.Page.AfterOf
import OnBytes.TypedOracleCompiler.Joined.K.Left

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes OnBytes.Maker OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)
open OnBytes.TwoLaws (ViewAlike)
open _root_.Run _root_.Run.PQ Compile OnBytes.RunA TypedOracleCompiler.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch.Cms (Bodies)

section Proof
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (DK : WholeD) (W : Three.Whole)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))
  (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
  (b : Bodies (objF f a DK (WholeD.of a W) tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
    Bd) (r₀ : Seed × Ans)

variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : _root_.Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : _root_.Fmt.SpecX} {R₃' : Rounds} {S₃ : _root_.Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : _root_.Fmt.Rand} {R₃ : Rounds}

/-- the proof file, written, with r₀ in the record's place in the request -/
local notation "𝔉" => fileProofA f K a DK (WholeD.of a W) tFk tJk t3k tFp tJp t3p silK runK silP
  runP eL Z wL Bd depthReq depthReqT depthReqL b r₀
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (WholeD.at (WholeD.of a W) a) tFp tJp t3p

/-- **All ten fields at the proof file**, for oracle functions g that meet `GRows` and `CodeOwes`.
-/
theorem afterRuns_proof_of (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) _)) (sb : ℕ) (cfg :
                                 ByteArray)
    (O : PageOwes p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ g₁ l₁ x₁ n₁ R₃ a
      sb K f cfg) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (pF : TFp) (pJ : TJp) (p3 : T3p) (salt : ByteArray) (path : List ByteArray) (π : (𝔉).Prf)
    (h : typeFile (ckP f) a W tFp tJp t3p silP runP sb cfg pF pJ p3 salt path r = some π)
    (cms : List (Dig 256)) (x : X × (Seed × Ans)) (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂)
    (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π).det g = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a').det g = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a' b').det g = some e')
    (Gr : GRows (t := (𝔉).t) (C := ckP f) (K := K) (rF := plainRS TFp tFp) (rJ := plainRS TJp tJp)
      (r3 := plainRS T3p t3p) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc (ckP f) (WholeD.of a W) tFp tJp t3p silP runP) (𝔉).embP (𝔉).xin cms x π g
      _root_.Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out r.second.out
      (R₁.map (·.1)).dropLast)
    (CO : CodeOwes (ckP f) K a W tFp tJp t3p g (_root_.Fmt.HO _root_.Fmt.oracle) (𝔉).embS (𝔉).embE
      cfg sb)
    (hsil : silP x pF pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → runP x v₁ v₂ v₃ = true)
    (hc : ∀ root,
      _root_.Fmt.itemRoot (Params.Shared.statement p.table r.place.root) 0 = some root →
      cms.getD 0 default = bytesToDig root) :
    TypedOracleCompiler.Joined.K.AfterRuns (𝔉) g (256 + 8 * sb) cms x π (bytesToDig seal1) a' b' e' :=
  have H := after_read f K a W tFp tJp t3p silP runP g (𝔉).embS (𝔉).embE (𝔉).embP (𝔉).xin cms sb cfg
    O
    hW pF pJ p3 salt path π h x a' b' e' h₁ h₂ h₃ Gr CO hsil hrun hc
  { sealAt := H.1
    opened₁ := H.2.1.1
    opened₂ := H.2.1.2.1
    opened₃ := H.2.1.2.2.1
    openedE := H.2.1.2.2.2
    walk₁ := H.2.2.1.1
    walk₂ := H.2.2.1.2.1
    walk₃ := H.2.2.1.2.2.1
    walkE := H.2.2.1.2.2.2
    accept := H.2.2.2 }

end Proof

section Key
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (W : Three.Whole) (DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))
  (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
  (b : Bodies (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
    Bd)

variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : _root_.Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : _root_.Fmt.SpecX} {R₃' : Rounds} {S₃ : _root_.Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : _root_.Fmt.Rand} {R₃ : Rounds}

/-- the key file, written -/
local notation "𝔉" => fileKey f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP
  eL Z wL Bd depthReq depthReqT depthReqL b
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (WholeD.at (WholeD.of a W) a) tFk tJk t3k

/-- **All ten fields at the key file**, for oracle functions g that meet `GRows` and `CodeOwes`. -/
theorem afterRuns_key_of (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) _)) (sb : ℕ) (cfg : ByteArray)
    (O : PageOwes p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ g₁ l₁ x₁ n₁ R₃ a
      sb K f cfg) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (pF : TFk) (pJ : TJk) (p3 : T3k) (salt : ByteArray) (path : List ByteArray) (π : (𝔉).Prf)
    (h : typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg pF pJ p3 salt path r = some π)
    (cms : List (Dig 256)) (x : Seed × Ans) (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂)
    (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π).det g = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a').det g = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin cms x π a' b').det g = some e')
    (Gr : GRows (t := (𝔉).t) (C := ckP f) (K := K) (rF := plainRS TFk tFk) (rJ := plainRS TJk tJk)
      (r3 := plainRS T3k t3k) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc (ckP f) (WholeD.of a W) tFk tJk t3k silK runK) (𝔉).embP (𝔉).xin cms x π g
      _root_.Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out r.second.out
      (R₁.map (·.1)).dropLast)
    (CO : CodeOwes (ckP f) K a W tFk tJk t3k g (_root_.Fmt.HO _root_.Fmt.oracle) (𝔉).embS (𝔉).embE
      cfg sb)
    (hsil : silK x pF pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → runK x v₁ v₂ v₃ = true)
    (hc : ∀ root,
      _root_.Fmt.itemRoot (Params.Shared.statement p.table r.place.root) 0 = some root →
      cms.getD 0 default = bytesToDig root) :
    TypedOracleCompiler.Joined.K.AfterRuns (𝔉) g (256 + 8 * sb) cms x π (bytesToDig seal1) a' b' e' :=
  have H := after_read f K a W tFk tJk t3k silK runK g (𝔉).embS (𝔉).embE (𝔉).embP (𝔉).xin cms sb cfg
    O
    hW pF pJ p3 salt path π h x a' b' e' h₁ h₂ h₃ Gr CO hsil hrun hc
  { sealAt := H.1
    opened₁ := H.2.1.1
    opened₂ := H.2.1.2.1
    opened₃ := H.2.1.2.2.1
    openedE := H.2.1.2.2.2
    walk₁ := H.2.2.1.1
    walk₂ := H.2.2.1.2.1
    walk₃ := H.2.2.1.2.2.1
    walkE := H.2.2.1.2.2.2
    accept := H.2.2.2 }

end Key

end OnBytes.Maker.Page
