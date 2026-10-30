-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/PrintRaw.lean: the printer of a whole request: a form out of what the typed runs
yield (`Raw`, Johnson/Prover/All/Defs.lean); and: where the runs yield a proof, the goals' verify
says yes to that form, under the premises of `printed_star` (Johnson/Prover/At/Printed.lean).

Main names.
  `printWith mk f₀ y` (namespace `OnBytes.Prover`)   for all objects: where the three runs returned
      strings: mk of the two roots, the two seeds and the three strings; else f₀
  `printWith_of_pack`   where `pack` yields a proof, that proof is laid of the three strings, and
      the printed value is mk of these
  `prf_inj`   a proof that is laid of three strings and a root in two ways: the same strings, the
      same root
  `printWith_allY`   what is printed of the typed runs' value (`allY`) under g: mk of the two kept
      trees' roots, the two seeds and the proof's three strings
  `printRaw S c₀ m₀ i r₁ d f₀ y` (namespace `Johnson.Prover.Print`)   the printer at the letters S:
      `formOf` (Johnson/Prover/Print/Form.lean) of: no further token · the first root · the honest
      OOD sample at the first seed · the draw's number · the key file's string · the second root ·
      the honest OOD sample of the copy at the second seed · the copy's file's string · the proof
      file's
  `printed_raw`   `printed_star` with the form `printRaw … y`, y the value of the typed runs
      (`allY`) under g, where `pack` of it yields the proof

Limits. As `printed_star`'s: each premise is asked, none is shown here. Where a run returned no
string the printer gives f₀, of which nothing is said. No probability. No goal is stated. Nothing on
soundness or completeness.

Local letters (notation of one section). 𝔗: the told record at Z, DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀ · ℜ: its
  ground input, R (S Z) c₀ m₀ · 𝔡: the public reading under the hash function, (cAt Z hash, sevenAt
  Z hash) · 𝔤: the typed oracle functions that are read off the hash function there.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.Printed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap F : Type}

/-- Where the three runs returned strings: mk of the two roots, the two seeds and the three strings;
else f₀. -/
def printWith
    (mk : Dig lam → L.OutOfDomainSeed → OneProtocolProof lam (batTC L aT) → Dig lam → L.OutOfDomainSeed → OneProtocolProof lam (batLC L aL) →
      OneProtocolProof lam L.onlineBatch → F) (f₀ : F) (y : Raw lam L aT aL) : F :=
  match y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2 with
  | .ok a, .ok b, .ok c => mk y.1.1 y.2.1 a.1 y.1.2 y.2.2.1 b.1 c.1
  | _, _, _ => f₀

/-- **Where `pack` yields a proof, it is laid of the three strings, and these are printed.** -/
theorem printWith_of_pack
    (mk : Dig lam → L.OutOfDomainSeed → OneProtocolProof lam (batTC L aT) → Dig lam → L.OutOfDomainSeed → OneProtocolProof lam (batLC L aL) →
      OneProtocolProof lam L.onlineBatch → F) (f₀ : F) (i : I) (d : Draw lam L Bd aT aL Kap) (y : Raw lam L aT aL)
    (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed) (τT : Tr L.offline.shape) (τL : Tr L.link.shape)
    (τB : Tr L.onlineBatch.loc.shape) (h : pack i d y = .ok (π, e₁, e₂, τT, τL, τB)) :
    ∃ πT πL πB, π = ⟨d.n, some πT, (y.1.2, L.recOf i d.r e₂, some πL), some πB⟩ ∧
      printWith mk f₀ y = mk y.1.1 e₁ πT y.1.2 e₂ πL πB := by
  obtain ⟨a, b, c, ha, hb, hc, hz⟩ := three_eq_ok (show three _ _ _ _ = Res.ok _ from h)
  obtain ⟨rfl, rfl, rfl, -, -, -⟩ : π = _ ∧ e₁ = _ ∧ e₂ = _ ∧ τT = _ ∧ τL = _ ∧ τB = _ := by
    simpa only [Prod.mk.injEq] using hz
  refine ⟨a.1, b.1, c.1, rfl, ?_⟩
  unfold printWith
  rw [ha, hb, hc]

/-- A proof that is laid of three strings and a root in two ways. -/
theorem prf_inj {n n' : ℕ} {a a' : OneProtocolProof lam (batTC L aT)} {c c' : Dig lam} {r r' : L.Rec}
    {b b' : OneProtocolProof lam (batLC L aL)} {e e' : OneProtocolProof lam L.onlineBatch}
    (h : (⟨n, some a, (c, r, some b), some e⟩ : OfflineLinkOnlineProof lam L aT aL) =
      ⟨n', some a', (c', r', some b'), some e'⟩) : a = a' ∧ b = b' ∧ e = e' ∧ c = c' := by
  injection h with _ e1 e2 e3
  injection e1 with e1
  injection e3 with e3
  injection e2 with e0 e2
  injection e2 with _ e2
  injection e2 with e2
  exact ⟨e1, e2, e3, e0⟩

/-- **What is printed of the typed runs' value**, where `pack` of it yields a proof that is laid of
three strings. -/
theorem printWith_allY (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (b₀ : Bd) (st : Strats L Kap)
    (capT capL capB : ℕ → ℕ) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (mk : Dig lam → L.OutOfDomainSeed → OneProtocolProof lam (batTC L aT) → Dig lam → L.OutOfDomainSeed → OneProtocolProof lam (batLC L aL) →
      OneProtocolProof lam L.onlineBatch → F) (f₀ : F) (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X)
    (d : Draw lam L Bd aT aL Kap) (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed)
    (τT : Tr L.offline.shape) (τL : Tr L.link.shape) (τB : Tr L.onlineBatch.loc.shape)
    (hp : pack i d ((allY W Sd cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g) =
      .ok (π, e₁, e₂, τT, τL, τB))
    (n : ℕ) (πT : OneProtocolProof lam (batTC L aT)) (c : Dig lam) (r : L.Rec) (πL : OneProtocolProof lam (batLC L aL))
    (πB : OneProtocolProof lam L.onlineBatch) (hπ : π = ⟨n, some πT, (c, r, some πL), some πB⟩) :
    printWith mk f₀ ((allY W Sd cA r₀ b₀ st capT capL capB (i, r₁, s₁) x d).det g) =
      mk ((committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g).root e₁ πT
        ((committerTreeKeptByProver W b₀ (L.encodeIndex i d.r) d.s).det g).root e₂ πL πB := by
  obtain ⟨πT', πL', πB', hπ', hw⟩ := printWith_of_pack mk f₀ i d _ π e₁ e₂ τT τL τB hp
  obtain ⟨rfl, rfl, rfl, -⟩ := prf_inj (hπ.symm.trans hπ')
  rw [hw, allY_roots W Sd cA r₀ b₀ st capT capL capB g (i, r₁, s₁) x d]

end OnBytes.Prover

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open LPFD.Full (XF sBG sTG KF)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover OnBytes.Prover.Print

/-- **The printer of a whole request, at the letters S.** -/
def printRaw {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256)) {Kap : Type}
    (i : (R S c₀ m₀).Index) (r₁ : (R S c₀ m₀).protocol.EncodingRandomness)
    (d : Draw 256 (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap) (f₀ : FormBytes)
    (y : Raw 256 (R S c₀ m₀).protocol (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits) : FormBytes :=
  printWith (fun c₁ e₁ πT c₂ e₂ πL πB =>
    formOf S ⟨[], c₁, (R S c₀ m₀).protocol.recOf i r₁ e₁, d.n, πT, c₂, (R S c₀ m₀).protocol.recOf i d.r e₂, πL,
      πB⟩) f₀ y

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)
  (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles) (hash : VerifiableInference.Hash)

/-- the told record at Z -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀
/-- its ground input -/
local notation "ℜ" => R (S Z) c₀ m₀
/-- the public reading under the hash function -/
local notation "𝔡" => (cAt Z hash, sevenAt Z hash)
/-- the typed oracle functions that are read off the hash function there -/
local notation "𝔤" =>
  readBlocks (LayoutsByPublicReading.m (DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀) (cAt Z hash, sevenAt Z hash)) (famOne hash)

set_option maxRecDepth 20000 in
/-- **Where the typed runs yield a proof, verify says yes to the printed form.** -/
theorem printed_raw {Kap : Type} (scope : VerifierAndGoals.InScope Z = true) (prompt output : List Token)
    (b₀ : (ℜ).LeafBody) (st : Strats (ℜ).protocol Kap) (capT capL capB : ℕ → ℕ)
    (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (x : XF)
    (d : Draw 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap) (π : OfflineLinkOnlineProof 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (e₁ e₂ : (ℜ).protocol.OutOfDomainSeed) (τT : Tr (QT (S Z)).loc.shape) (τL : Tr (QL (S Z)).loc.shape)
    (τB : Tr (QB (S Z)).loc.shape) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (LC (S Z) c₀ m₀)) (fb : FormBytes) (hS : PublicS (S Z))
    (hN : NumbersFit (KF (S Z).DK (S Z).DP) (S Z).DK dsF (S Z).DP)
    (hp : pack i d ((allY (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample b₀ st capT capL capB (i, r₁, s₁) x
      d).det 𝔤) = .ok (π, e₁, e₂, τT, τL, τB))
    (hE : Ends (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample b₀ st capT capL capB 𝔤 i r₁ s₁ x d π e₁ e₂ τT τL
      τB)
    (aT : (QT (S Z)).loc.accept ((ℜ).protocol.recOf i r₁ e₁) ((ℜ).protocol.encodeIndex i r₁) τT = true)
    (aB : (QB (S Z)).loc.accept (x, (ℜ).protocol.recOf i d.r e₂) ((ℜ).protocol.encodeIndex i d.r) τB = true)
    (hG : GoodOwes (S Z) c₀ m₀ (digToBytes (cAt Z hash)) salt sL bcT bcL bcB capT capL capB i r₁ s₁
      d)
    (hσ : ∀ (πT : OneProtocolProof 256 (QT (S Z))) (πL : OneProtocolProof 256 (QL (S Z))) (πB : OneProtocolProof 256 (QB (S Z))),
      π = ⟨d.n, some πT, (((committerTreeKeptByProver (ℜ).queryLayout b₀ ((ℜ).protocol.encodeIndex i d.r) d.s).det 𝔤).root,
          (ℜ).protocol.recOf i d.r e₂, some πL), some πB⟩ →
      StratOwes (ckP .two) ((S Z).DK.at frS.P.T.a) (front₀ (S Z).G.rec₀) (join₀ (S Z).G.rec₀)
          ByteArray.empty silK (S Z).runK bcT πT ∧
        StratOwes (ckP .two) ((S Z).DP.at frS.P.T.a) (front₀ (S Z).G.z₀.2) (join₀ (S Z).G.z₀.2)
          ByteArray.empty silP (S Z).runP bcB πB)
    (hn : ((𝔗).Sd 𝔡).num d.n τB.plains = true)
    (hb : (ℜ).buildInstance (prompt, output) [] = some x)
    (hv : (verifyAtKeyRoot (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample (ℜ).compilerParameters
      ((committerAtFixedCoins (ℜ).queryLayout ((𝔗).Sd 𝔡) b₀ i r₁ s₁).det 𝔤).1 x π).det 𝔤 = true) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z)
      (ZKCP.digestUnder hash (𝔗).encT
        ((𝔗).part 𝔡, ((committerAtFixedCoins (ℜ).queryLayout ((𝔗).Sd 𝔡) b₀ i r₁ s₁).det 𝔤).1))
      prompt output
      (printRaw (S Z) c₀ m₀ i r₁ d fb ((allY (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample b₀ st capT capL
        capB (i, r₁, s₁) x d).det 𝔤))).evaluate hash = true := by
  obtain ⟨πT, πL, πB, hπ, hy⟩ := printed_star S f₀ Hb c₀ m₀ Z hash scope prompt output b₀ st capT
    capL capB i r₁ s₁ x d π e₁ e₂ τT τL τB salt sL bcT bcL bcB hS hN hE aT aB hG hσ hn hb hv
  have hw := printWith_allY (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample b₀ st capT capL capB 𝔤
    (fun c₁ e₁ πT c₂ e₂ πL πB =>
      formOf (S Z) ⟨[], c₁, (ℜ).protocol.recOf i r₁ e₁, d.n, πT, c₂, (ℜ).protocol.recOf i d.r e₂, πL, πB⟩) fb i r₁
    s₁ x d π e₁ e₂ τT τL τB hp _ πT _ _ πL πB hπ
  exact (congrArg (fun F : FormBytes =>
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z)
      (ZKCP.digestUnder hash (𝔗).encT
        ((𝔗).part 𝔡, ((committerAtFixedCoins (ℜ).queryLayout ((𝔗).Sd 𝔡) b₀ i r₁ s₁).det 𝔤).1))
      prompt output F).evaluate hash) hw).trans hy

end Johnson.Prover.Print
