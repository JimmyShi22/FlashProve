-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/AfterG.lean: under the typed oracle functions that a page induces from the
realised oracle, the ten conditions of `AfterRuns` on what the compiled verifier of a key file, and
of a proof file, checks behind its three chains hold at the typing of a file that was read. The page
stands under premises that say what its family answers at the leaves (`LeafXAgrees`) and at the
chains' queries (`Speaks`); and the three chains' values are values under that family.

Johnson/Maker/Page/After.lean has the ten fields of `AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean) for
any oracle functions that meet `GRows` and `CodeOwes`. Here both are paid at `gJ P Fmt.oracle`
(OnBytes/Maker/Page/Frame.lean): `GRows` by OnBytes/Maker/Page/AtFiles.lean, `CodeOwes` by
OnBytes/Maker/Page/CodeAt.lean, at the bodies `bodiesF` (Johnson/EntryRec/BodiesAt.lean) with
`embStored` for the stored table's symbols.

  `afterRuns_proof_gJ`   the ten fields at `fileProofA` (Johnson/Maker/WrittenA.lean).
  `afterRuns_key_gJ`     the ten fields at `fileKey` (Johnson/Maker/Written.lean).

The premises.
  `PageOwes` (OnBytes/Maker/Page/Owes.lean), at the file's own public data: the reading, the
    parameters, tests on the data. The data W are made of the dry run's three lists of rounds.
  ON THE PAGE P: its digest is cfg; its field `leaf` reads a body as it is; `LeafXAgrees` at the
    bodies of the file's own symbols; its family answers the file's chain queries by the file's data
    as laid (`Speaks`, OnBytes/Maker/Page/Chains.lean), at the queries Q, and the file's own queries
    are such (`QuietAt`, OnBytes/Maker/Page/RowsAt.lean); a read-back rd of the plain parts.
  ON THE INTERFACE: two conditions on the round in which an instance is written (`late₁`, `late₃`);
    for a proof file, that the request's two strings come out of the typed instance (`hreq`).
  ON THE READING, beside `PageOwes`: the joining round's and the seam's messages; the table's root
    has 32 bytes; the value of the table's item has fewer than 2^64 bytes (`hz₀`: then the root in
    item 0 of the second chain's statement is the table's).
  NEITHER A TEST NOR A LAW OF THE READING: `typeFile` returns π at the reading r (it holds the test
    `sameTwice`, OnBytes/Maker/Tables.lean, that two openings of one place hold one column and
    salt); the test on the three silent rounds' messages says yes; the file's decision says yes at
    all views that are as the views read but for the digests.
  The three chains' values under `gJ P Fmt.oracle`, at the commitments that begin with the digest of
    the table's root.
None is shown here.

Not claimed. `gJ P O` is a function of the typed query, no one-to-one coding (the head of
OnBytes/Maker/Page/Frame.lean). The fields of `Left` beside `after` (`laws`, `wire`, `fits`,
`saltLen`, `slotLt`, `pathLen`, `climb`): among them the climb in the request tree and the lengths
of the salt and the path, which the compiled verifier checks behind its chains too. Nothing on
soundness (index binding included), what a root fixes, opening-form binding, no two openings of a
commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import Johnson.Maker.Page.After
import Johnson.EntryRec.BodiesAt
import OnBytes.Maker.Page.AtFiles
import OnBytes.Maker.Page.CodeAt
import OnBytes.Params.StatementLaws

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)
open OnBytes.TwoLaws (ViewAlike)
open _root_.Run _root_.Run.PQ Compile OnBytes.RunA TypedOracleCompiler.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch (PlainPart FbIn)
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open _root_.Compile.Joined (Chains JoinMsg)

section Proof
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (DK : WholeD) (W : Three.Whole)
  {TFk TJk T3k : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k)
  (tFp : FrontMsg (List E)) (tJp : JoinMsg (List E) ByteArray) (t3p : ByteArray)
  (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX))) (depthReq
                                     depthReqT depthReqL sb : ℕ)
  (r₀ : Seed × Ans)

variable {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : _root_.Fmt.SpecX}
  {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd}
  {S₂ : _root_.Fmt.SpecX} {R₃' : Rounds} {S₃ : _root_.Fmt.SpecX} {R₃ : Rounds}

/-- the typed oracles' carrier, with strings of bits for bodies -/
local notation "𝓛" => typedOracleCarrier
  (objF f a DK (WholeD.of a W) tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) (List Bool)
  (Chains.ann (chainsOf (ckP f) (WholeD.at DK a) tFk tJk t3k))
  eL.aL
/-- the bodies: a body is the leaf's own string of bits -/
local notation "𝒮" => bodiesF f a DK (WholeD.of a W) tFk tJk t3k tFp tJp t3p silK runK silP runP eL
  Z sb (embStored a sb) (prjStored a sb)
/-- the file, written -/
local notation "𝔉" => fileProofA f K a DK (WholeD.of a W) tFk tJk t3k tFp tJp t3p silK runK silP
  runP eL Z wL (List Bool) depthReq depthReqT depthReqL 𝒮 r₀
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (WholeD.at (WholeD.of a W) a) tFp tJp t3p

/-- **All ten fields at the proof file, under `gJ P Fmt.oracle`.** -/
theorem afterRuns_proof_gJ (cfg : ByteArray) (c : Params.ProofChains) (table : Params.TableName)
    (copy : ℕ) (request words : ByteArray)
    (block : Blk FirstEnd) (req : _ → ByteArray × ByteArray)
    (O : PageOwes (Proof.tailPublic c table) block (Proof.firstStart c.first) file i
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₃ a sb K f cfg)
    (hW : W = Three.Whole.of R₁ R₂ R₃)
    (P : PageJ 𝓛 (K + 1)) (hP : P.leaf = leafOf fun b : List Bool => b) (hPc : P.cfg = cfg)
    (hX₁ : ∀ q y, LeafXAgrees P (symb₁ (𝔉).embS (.inr q) y))
    (hX₂ : ∀ q y, LeafXAgrees P (symb₂ (𝔉).embS (.inr q) y))
    (hX₃ : ∀ q y, LeafXAgrees P (symb₃ (𝔉).embS (.inr q) y))
    (hXE : ∀ y, LeafXAgrees P ((𝔉).embE y))
    (rd : PBt 𝓛 (𝔉).t → Option (PlainPart (𝒞).sh (𝒞).ann)) (Q : FbIn 256 𝓛 (𝔉).t → Prop)
    (hrd : ∀ w, rd ((𝔉).embP w) = some w)
    (S : Speaks (gJ P _root_.Fmt.oracle) (𝔉).t
      (fillJ (ckP f) (WholeD.of a W) tFp tJp t3p rd (silentProof (_root_.Fmt.HO _root_.Fmt.oracle) c
        req))
      _root_.Fmt.oracle Q)
    (Qa : ∀ cms x salt rtreq ρ0 c' pF pJ p3, QuietAt (ckP f) (WholeD.of a W) tFp tJp t3p rd
      (silentProof (_root_.Fmt.HO _root_.Fmt.oracle) c req) Q (𝔉).embP cms x salt rtreq ρ0 c' pF pJ
        p3)
    (rest : List (Dig 256)) (x : X × (Seed × Ans))
    (hreq : ((((𝔉).xin x).map (𝓛).early).map req).getD default = (request, words)) (π : (𝔉).Prf)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers r = some pJ)
    (h3 : seamOf r = some p3) (salt : ByteArray) (path : List ByteArray)
    (h : typeFile (ckP f) a W tFp tJp t3p silP runP sb cfg (frontOf table.answers copy) pJ p3 salt
      path r = some π)
    (z₁ : table.root.size = 32)
    (late₁ : (𝔉).xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₁).length →
      (𝓛).late ≠ some (0 + 1 + n))
    (late₃ : (𝔉).xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₃).length →
      (𝓛).late ≠ some (0 + (𝒞).c₁.length + (𝒞).c₂.length + 1 + n))
    (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂) (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π).det
      (gJ P _root_.Fmt.oracle) = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a').det
      (gJ P _root_.Fmt.oracle) = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a' b').det
      (gJ P _root_.Fmt.oracle) = some e')
    (hsil : silP x (frontOf table.answers copy) pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → runP x v₁ v₂ v₃ = true)
    (hz₀ : (Params.tableValue table).size < 2 ^ 64) :
    TypedOracleCompiler.Joined.K.AfterRuns (𝔉) (gJ P _root_.Fmt.oracle) (256 + 8 * sb)
      (bytesToDig table.root :: rest) x π (bytesToDig seal1) a' b' e' := by
  have B₁ : BodyIs (fun b : List Bool => b) sb (ckP f) (WholeD.of a W).ds₁
      fun p => symb₁ (𝔉).embS (.inr p) :=
    (symb₁_whole (L := 𝓛) (𝒞) (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₁)
      (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₂) (RCode.none _ _ fun p => p)
      (scT sb (ckP f) (WholeD.of a W).ds₃)).symm ▸ bodyIs_scT sb (ckP f) _
  have B₂ : BodyIs (fun b : List Bool => b) sb (ckP f) (WholeD.of a W).ds₂
      fun p => symb₂ (𝔉).embS (.inr p) :=
    (symb₂_whole (L := 𝓛) (𝒞) (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₁)
      (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₂) (RCode.none _ _ fun p => p)
      (scT sb (ckP f) (WholeD.of a W).ds₃)).symm ▸ bodyIs_scT sb (ckP f) _
  have B₃ : BodyIs (fun b : List Bool => b) sb (ckP f) (WholeD.of a W).ds₃
      fun p => symb₃ (𝔉).embS (.inr p) :=
    (symb₃_whole (L := 𝓛) (𝒞) (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₁)
      (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₂) (RCode.none _ _ fun p => p)
      (scT sb (ckP f) (WholeD.of a W).ds₃)).symm ▸ bodyIs_scT sb (ckP f) _
  have hpg : pageFitB a sb W = true := by rw [hW]; exact O.page
  have hz₁ : r.place.root.size < 2 ^ 64 := by
    rw [(sizes_of_read O.read).1]
    omega
  obtain ⟨f₁, f₂, f₃, fE⟩ := pageFitB_spec hpg
  exact afterRuns_proof_of f K a DK W tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL
    (List Bool)
    depthReq depthReqT depthReqL 𝒮 r₀ (gJ P _root_.Fmt.oracle) sb cfg O hW _ pJ p3 salt path π h _ x
      a' b'
    e' h₁ h₂ h₃
    (rows_proof_value (ckP f) a tFp tJp t3p silP runP W hW c table copy request words block req
      O.wholeFits
      O.read
      O.spec₁ O.small rd Q (𝔉).embP hrd _ S Qa (𝔉).xin rest x hreq π pJ p3 hJ h3 sb cfg salt path h
        z₁
      late₁ late₃)
    (codeOwes_gJ (ckP f) a W tFp tJp t3p (𝔉).embS (𝔉).embE P _root_.Fmt.oracle (fun b : List Bool =>
      b) hP
      sb cfg hPc O.cfg32 B₁ B₂ B₃ (fun _ => rfl) f₁ f₂ f₃ fE hX₁ hX₂ hX₃ hXE)
    hsil hrun fun root hr => by
      have e : some table.root = some root :=
        (Params.Shared.statement_root0 table r.place.root hz₀ hz₁).symm.trans hr
      rw [← Option.some.inj e]
      rfl

end Proof

section Key
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (W : Three.Whole) (DP : WholeD)
  (tFk : FrontMsg (List E)) (tJk : JoinMsg (List E) ByteArray) (t3k : ByteArray)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silK : Seed × Ans → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX))) (depthReq
                                     depthReqT depthReqL sb : ℕ)

variable {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : _root_.Fmt.SpecX}
  {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd}
  {S₂ : _root_.Fmt.SpecX} {R₃' : Rounds} {S₃ : _root_.Fmt.SpecX} {R₃ : Rounds}

/-- the typed oracles' carrier, with strings of bits for bodies -/
local notation "𝓛" => typedOracleCarrier
  (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) (List Bool)
  (Chains.ann (chainsOf (ckP f) (WholeD.at (WholeD.of a W) a) tFk tJk t3k))
  eL.aL
/-- the bodies: a body is the leaf's own string of bits -/
local notation "𝒮" => bodiesF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL
  Z sb (embStored a sb) (prjStored a sb)
/-- the file, written -/
local notation "𝔉" => fileKey f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP
  runP eL Z wL (List Bool) depthReq depthReqT depthReqL 𝒮
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (WholeD.at (WholeD.of a W) a) tFk tJk t3k

/-- **All ten fields at the key file, under `gJ P Fmt.oracle`.** -/
theorem afterRuns_key_gJ (cfg : ByteArray) (k : Params.KeyChains) (table : Params.TableName)
    (O : PageOwes (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file i
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₃ a sb K f cfg)
    (hW : W = Three.Whole.of R₁ R₂ R₃)
    (P : PageJ 𝓛 (K + 1)) (hP : P.leaf = leafOf fun b : List Bool => b) (hPc : P.cfg = cfg)
    (hX₁ : ∀ q y, LeafXAgrees P (symb₁ (𝔉).embS (.inr q) y))
    (hX₂ : ∀ q y, LeafXAgrees P (symb₂ (𝔉).embS (.inr q) y))
    (hX₃ : ∀ q y, LeafXAgrees P (symb₃ (𝔉).embS (.inr q) y))
    (hXE : ∀ y, LeafXAgrees P ((𝔉).embE y))
    (rd : PBt 𝓛 (𝔉).t → Option (PlainPart (𝒞).sh (𝒞).ann)) (Q : FbIn 256 𝓛 (𝔉).t → Prop)
    (hrd : ∀ w, rd ((𝔉).embP w) = some w)
    (S : Speaks (gJ P _root_.Fmt.oracle) (𝔉).t
      (fillJ (ckP f) (WholeD.of a W) tFk tJk t3k rd (silentKey (_root_.Fmt.HO _root_.Fmt.oracle) k
        _))
      _root_.Fmt.oracle Q)
    (Qa : ∀ cms x salt rtreq ρ0 c' pF pJ p3, QuietAt (ckP f) (WholeD.of a W) tFk tJk t3k rd
      (silentKey (_root_.Fmt.HO _root_.Fmt.oracle) k _) Q (𝔉).embP cms x salt rtreq ρ0 c' pF pJ p3)
    (rest : List (Dig 256)) (x : Seed × Ans) (π : (𝔉).Prf) (copy : ℕ)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers r = some pJ)
    (h3 : seamOf r = some p3) (salt : ByteArray) (path : List ByteArray)
    (h : typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg (frontOf table.answers copy) pJ p3 salt
      path r = some π)
    (z₁ : table.root.size = 32)
    (late₁ : (𝔉).xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₁).length →
      (𝓛).late ≠ some (0 + 1 + n))
    (late₃ : (𝔉).xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₃).length →
      (𝓛).late ≠ some (0 + (𝒞).c₁.length + (𝒞).c₂.length + 1 + n))
    (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂) (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π).det
      (gJ P _root_.Fmt.oracle) = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a').det
      (gJ P _root_.Fmt.oracle) = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a' b').det
      (gJ P _root_.Fmt.oracle) = some e')
    (hsil : silK x (frontOf table.answers copy) pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → runK x v₁ v₂ v₃ = true)
    (hz₀ : (Params.tableValue table).size < 2 ^ 64) :
    TypedOracleCompiler.Joined.K.AfterRuns (𝔉) (gJ P _root_.Fmt.oracle) (256 + 8 * sb)
      (bytesToDig table.root :: rest) x π (bytesToDig seal1) a' b' e' := by
  have B₁ : BodyIs (fun b : List Bool => b) sb (ckP f) (WholeD.of a W).ds₁
      fun p => symb₁ (𝔉).embS (.inr p) :=
    (symb₁_whole (L := 𝓛) (𝒞) (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₁)
      (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₂) (RCode.none _ _ fun p => p)
      (scT sb (ckP f) (WholeD.of a W).ds₃)).symm ▸ bodyIs_scT sb (ckP f) _
  have B₂ : BodyIs (fun b : List Bool => b) sb (ckP f) (WholeD.of a W).ds₂
      fun p => symb₂ (𝔉).embS (.inr p) :=
    (symb₂_whole (L := 𝓛) (𝒞) (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₁)
      (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₂) (RCode.none _ _ fun p => p)
      (scT sb (ckP f) (WholeD.of a W).ds₃)).symm ▸ bodyIs_scT sb (ckP f) _
  have B₃ : BodyIs (fun b : List Bool => b) sb (ckP f) (WholeD.of a W).ds₃
      fun p => symb₃ (𝔉).embS (.inr p) :=
    (symb₃_whole (L := 𝓛) (𝒞) (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₁)
      (RCode.none _ _ fun p => p) (scT sb (ckP f) (WholeD.of a W).ds₂) (RCode.none _ _ fun p => p)
      (scT sb (ckP f) (WholeD.of a W).ds₃)).symm ▸ bodyIs_scT sb (ckP f) _
  have hpg : pageFitB a sb W = true := by rw [hW]; exact O.page
  have hz₁ : r.place.root.size < 2 ^ 64 := by
    rw [(sizes_of_read O.read).1]
    omega
  obtain ⟨f₁, f₂, f₃, fE⟩ := pageFitB_spec hpg
  exact afterRuns_key_of f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL
    (List Bool)
    depthReq depthReqT depthReqL 𝒮 (gJ P _root_.Fmt.oracle) sb cfg O hW _ pJ p3 salt path π h _ x a'
      b'
    e' h₁ h₂ h₃
    (rows_key_value (ckP f) a tFk tJk t3k silK runK W hW k table O.wholeFits O.read O.spec₁ O.small
      rd Q
      (𝔉).embP
      hrd _ S Qa (𝔉).xin rest x π copy pJ p3 hJ h3 sb cfg salt path h z₁ late₁ late₃)
    (codeOwes_gJ (ckP f) a W tFk tJk t3k (𝔉).embS (𝔉).embE P _root_.Fmt.oracle (fun b : List Bool =>
      b) hP
      sb cfg hPc O.cfg32 B₁ B₂ B₃ (fun _ => rfl) f₁ f₂ f₃ fE hX₁ hX₂ hX₃ hXE)
    hsil hrun fun root hr => by
      have e : some table.root = some root :=
        (Params.Shared.statement_root0 table r.place.root hz₀ hz₁).symm.trans hr
      rw [← Option.some.inj e]
      rfl

end Key

end OnBytes.Maker.Page
