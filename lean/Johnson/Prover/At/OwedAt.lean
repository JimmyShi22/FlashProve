-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/OwedAt.lean: two of the conditions under which a prover's strings can be printed,
paid at the input of the full size (`innerCompilerInputAtFullSize`, Johnson/Flat/Dec/TwoSizesAt.lean): what is
asked of a stored table, and the lengths of what is drawn.

Main names.
  `okF_symF`, `table_honestTab` (namespace `Johnson.Prover.At`)   the format's code word's symbol is
      a word below the prime; so a stored table of such code words (`honestTab`,
      OnBytes/Slice/Honest.lean) names each place, holds words below the prime, and has 2^v words in
      a column
  `tableOwes_honestTab`   `TableOwes` (OnBytes/Prover/Print/OuterKept.lean) at such a table, at
      leaves' salts of the form `leafSalt c (s j)` with c of 32 bytes and each s j of at most 64
      bytes
  `HonestEnc E`, `honestEnc_codingHonest`   a coding whose encoder gives such tables; the written
      honest side (`codingHonest`, OnBytes/Flat/CodingHonest.lean) is one
  `tableOwes_fullD` (namespace `VerifiableInference.OnPublicFiles`)   for all data: `TableOwes` at the
      object's own encoded index r.protocol.encodeIndex i ρ, if the coding is of that kind
  `honestEnc_the` (namespace `Meaning`)   the goals' description's coding is of that kind, at all
      public files
  `drawFit_fullD`   for all data: `DrawFit` (Johnson/Prover/All/Yes.lean) from coins of the bytes'
      form with `ByteCoins.Fit` (OnBytes/Prover/Print/Coins.lean) at the three request depths
  `drawFit_tOf` (namespace `FlashProve`)   its call at the letters S of one set of public files

Kin in the library. `Johnson.Pack.ok_hornerF`, `ok_symF`
(Johnson/Pack/TabMeets.lean [not in this library]) say what
`okF_symF` says. That file stands on two more of its kind;
nothing here imports it. The eight lines rest on the same `Fmt.Fld.ok_add` (Fmt/FieldE.lean).

Limits. That a committer's salts have the form `leafSalt c (s j)` at the configuration's digest c
that is drawn, and that a prover's coins are of the bytes' form, are premises. That the number of
the copy in a draw is below 2^64 is a condition on the draw which nothing here can show: a draw is a
letter. Nothing here says that a verifier says yes. Nothing on soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.WiresAt
import Johnson.Prover.All.Yes
import OnBytes.Prover.Print.OuterKept
import OnBytes.Flat.CodingHonest
import OnBytes.Flat.TableNumbers
import Johnson.Goal.Description.AtBound
import Johnson.Goal.Conditions.DepthsAtDescriptionDataAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.At
open OnBytes.Slice OnBytes.Flat OnBytes.Maker
open _root_.Run (leafSalt)
open OnBytes.Prover.Print (TableOwes saltFrom_leafSalt)

/-! ## A stored table of the format's code words -/

theorem ok_hornerF (z : UInt64) (cs : List UInt64) :
    Fmt.Fld.two.ok (Fmt.M1.hornerF z cs) = true := by
  cases cs with
  | nil =>
    show Fmt.Fld.two.ok 0 = true
    decide
  | cons c l => exact Fmt.Fld.ok_add _ _ _

/-- The format's code word's symbol is a word below the prime. -/
theorem okF_symF (C : Fmt.M1.Code) (x : ℕ) (m rho : List UInt64) :
    Carrier.okF (Fmt.M1.symF C x m rho) := by
  show (Fmt.M1.symF C x m rho).toNat < Fmt.Fld.two.p
  exact of_decide_eq_true (ok_hornerF _ _)

/-- The table names each place, holds words below the prime, and has 2^v words in a column. -/
theorem table_honestTab (S : Sz) (msg tl : ℕ → List UInt64) (x : S.Pos) :
    (honestTab S msg tl x).1 = x.val ∧ (∀ w ∈ (honestTab S msg tl x).2, Carrier.okF w) ∧
      (honestTab S msg tl x).2.length = 2 ^ S.P.v := by
  refine ⟨rfl, fun w hw => ?_, ?_⟩
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hw
    exact okF_symF _ _ _ _
  · show ((List.range (2 ^ S.P.v)).map _).length = _
    rw [List.length_map, List.length_range]

/-- **What the printer asks of a table and its leaves' salts.** -/
theorem tableOwes_honestTab (S : Sz) (msg tl : ℕ → List UInt64) (c : ByteArray)
    (s : ℕ → ByteArray) (hc : c.size = 32) (hs : ∀ j, j < 2 ^ S.P.T.a → (s j).size ≤ 64)
    (hv : 2 ^ S.P.v < 2 ^ 64) (P : S.Pos → Prop) :
    TableOwes c (honestTab S msg tl) (fun j => leafSalt c (s j)) P := by
  intro p _
  obtain ⟨h1, h2, h3⟩ := table_honestTab S msg tl p
  refine ⟨saltFrom_leafSalt c (s p.val) hc, ?_, h1, h2, by rw [h3]; exact hv⟩
  have := hs p.val p.isLt
  show (leafSalt c (s p.val)).length ≤ 256 + 8 * 64
  rw [OnBytes.Maker.length_leafSalt, hc]
  omega

/-- A coding whose encoder gives tables of the format's code words. -/
def HonestEnc {S : Sz} {Z : Cb.Ood.Sample Cb.Gl.E S.En} {cut : ℕ} {X : Type}
    {A : (S.toDecR Z cut).Claims X} (E : Coding A) : Prop :=
  ∀ m ρ, ∃ msg tl : ℕ → List UInt64, E.enc m ρ = honestTab S msg tl

theorem honestEnc_codingHonest (S : Sz) (Z : Cb.Ood.Sample Cb.Gl.E S.En) (cut : ℕ) {X : Type}
    (A : (S.toDecR Z cut).Claims X) (Pad : Type) [Fintype Pad] [Nonempty Pad]
    (holdW : A.Mat → Pad → ℕ → List UInt64) : HonestEnc (codingHonest S Z cut A Pad holdW) :=
  fun _ _ => ⟨_, _, rfl⟩

end Johnson.Prover.At

namespace VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open OnBytes.Prover (Draw DrawFit)
open OnBytes.Prover.Print (TableOwes ByteCoins coinsOf fit_coinsOf)
open Johnson.Prover.At (HonestEnc tableOwes_honestTab)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- **The object's own encoded index is a table as the printer asks**, if the coding's encoder gives
tables of the format's code words. -/
theorem tableOwes_fullD (hE : HonestEnc E) (i : (innerCompilerInputAtFullSize T).Index)
    (ρ : (innerCompilerInputAtFullSize T).protocol.EncodingRandomness) (c : ByteArray) (s : ℕ → ByteArray) (hc : c.size = 32)
    (hs : ∀ j, j < 2 ^ frS.P.T.a → (s j).size ≤ 64) (Q : Fin (2 ^ frS.P.T.a) → Prop) :
    TableOwes c ((innerCompilerInputAtFullSize T).protocol.encodeIndex i ρ) (fun j => leafSalt c (s j)) Q := by
  obtain ⟨msg, tl, e⟩ := hE (E.hold i ρ.1) ρ.2
  have e' : (innerCompilerInputAtFullSize T).protocol.encodeIndex i ρ = honestTab frS msg tl := e
  rw [e']
  exact tableOwes_honestTab frS msg tl c s hc hs (by rw [frS_v]; omega) Q

/-- **The lengths of what is drawn**, from coins of the bytes' form. sb: the bytes of a leaf's own
salt; sT, sL, sB: three binding shapes, whose depths are the three request depths. -/
theorem drawFit_fullD {Kap : Type}
    (d : Draw 256 (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).LeafBody (innerCompilerInputAtFullSize T).offlineRoundSplits
      (innerCompilerInputAtFullSize T).linkRoundSplits Kap)
    (sb : ℕ) (sT sL sB : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).LeafBody
      (innerCompilerInputAtFullSize T).offlineRoundSplits (innerCompilerInputAtFullSize T).linkRoundSplits))
    (aT bT aL bL aB bB : ℕ) (e1 : T.p.sMT = 256 + 8 * sb) (e2 : T.p.sFS = 256)
    (eT : T.depthReqT = sT.logLeaves) (eL : sL.logLeaves = 0) (eB : depthReq = sB.logLeaves)
    (hs : ∀ j, j < (innerCompilerInputAtFullSize T).protocol.wordLength → (d.s j).length = 256 + 8 * sb)
    (hT : d.coT = coinsOf aT bT sT.logLeaves bcT) (fT : bcT.Fit sb sT)
    (hL : d.coL = coinsOf aL bL sL.logLeaves bcL) (fL : bcL.Fit sb sL)
    (hB : d.coB = coinsOf aB bB sB.logLeaves bcB) (fB : bcB.Fit sb sB) :
    DrawFit (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).compilerParameters d where
  s := fun j hj => by
    show (d.s j).length = T.p.sMT
    rw [e1]
    exact hs j hj
  T := by
    show d.coT.Fit T.p.sMT T.p.sFS T.depthReqT
    rw [hT, e1, e2, eT]
    exact fit_coinsOf bcT aT bT sb sT fT
  Lk := by
    show d.coL.Fit T.p.sMT T.p.sFS 0
    rw [hL, e1, e2]
    have h := fit_coinsOf bcL aL bL sb sL fL
    rw [eL] at h ⊢
    exact h
  B := by
    show d.coB.Fit T.p.sMT T.p.sFS depthReq
    rw [hB, e1, e2]
    have h := fit_coinsOf bcB aB bB sb sB fB
    exact ⟨h.salt, h.leaf, lt_of_lt_of_eq h.slot (congrArg (fun n => 2 ^ n) eB.symm),
      h.path.trans eB.symm⟩

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open OnBytes.Prover (Draw DrawFit)
open OnBytes.Prover.Print (ByteCoins coinsOf)
open LPFD.Full (sBG sTG saltG)

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c : Digest) (m : List (_root_.Iop.Dig 256))

/-- **The lengths of what is drawn, at S**: the bytes of a leaf's own salt are the plan's; the key
file's and the proof file's shapes are the plan's; the entry file's is any shape of depth 0. -/
theorem drawFit_tOf {Kap : Type}
    (d : Draw 256 (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).protocol (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).LeafBody
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).offlineRoundSplits (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).linkRoundSplits Kap)
    (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).protocol
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).LeafBody (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).offlineRoundSplits
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).linkRoundSplits))
    (aT bT aL bL aB bB : ℕ) (eL : sL.logLeaves = 0)
    (hs : ∀ j, j < (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).protocol.wordLength → (d.s j).length = 256 + 8 * saltG S.G)
    (hT : d.coT = coinsOf aT bT (sTG S.G).logLeaves bcT) (fT : bcT.Fit (saltG S.G) (sTG S.G))
    (hL : d.coL = coinsOf aL bL sL.logLeaves bcL) (fL : bcL.Fit (saltG S.G) sL)
    (hB : d.coB = coinsOf aB bB (sBG S.G).logLeaves bcB) (fB : bcB.Fit (saltG S.G) (sBG S.G)) :
    DrawFit (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).queryLayout (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).compilerParameters d :=
  drawFit_fullD (S.inputFieldsAtReadings c m) d (saltG S.G) (sTG S.G) sL (sBG S.G) bcT bcL bcB aT bT aL bL aB bB
    (sMT_tOf S c m) (sFS_tOf S c m) (depthReqT_tOf S c m) eL rfl hs hT fT hL fL hB fB

end FlashProve

namespace Meaning
open VerifierAndGoals FlashProve FlashProve
open Johnson.Prover.At (HonestEnc honestEnc_codingHonest)

/-- **The goals' description's coding gives tables of the format's code words**, at all public
files. -/
theorem honestEnc_the (Z : PublicFiles) : HonestEnc (dataAtFiles flashProveData Z).E :=
  fun _ _ => ⟨_, _, rfl⟩

end Meaning
