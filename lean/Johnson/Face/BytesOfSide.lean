-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Face/BytesOfSide.lean: at the letters S of one set of public files, from what the honest
side's letters owe at the bytes, to FitsAtCoins (Johnson/Face/UndoOfFits.lean) outside the coins at
which one of the six run values is 32 zero bytes.

Main names (namespace Johnson.Face).
  RunsOkT, RunsOkB, ZeroRun   a string's three run values pass the format's test; the whole key and
    the proof are excepted where one of the six fails it. The compiled verifier does not read this;
    the byte format refuses it.
  SideBytes   what the compiler's own honest settings owe at the bytes: the digest has 32 bytes; the
    tables' salts are leafSalt of the digest; the three kinds of run's coins, as they are handed on,
    are the coins of byte coins of the right lengths, and the two whole files' run values are those
    that the strategy's coins fix; caps and copies' numbers are below 2^64; the copy's file's
    binding tree has depth 0.
  StratsPrint   what the interactive prover owes: StratLaw of the two whole files' strategies at
    these run values, the key file's at the indices of ok, the proof file's at the instances of Tr.
    ok is wider than what Tr reaches, since the run values must be sent at every index in range
    (RunVals).
  fitsAtCoins_of_side   the end.
  not_zeroRun_of_coins   the exception read off the coins: where the verifier says yes and the six
    values that the coins fix pass the format's test, the key and the proof are not in it.
-/
import Johnson.Face.UndoOfFitsAt
import Johnson.Face.FitsOfGoodW
import Johnson.WholeKey.EndsOfYes
import Johnson.Prover.Print.FitsOfGood
import Johnson.Prover.Print.DrawAtS
import Johnson.Prover.At.StratsAt
import Johnson.Prover.At.NumBack
import Johnson.Prover.At.ToldAt
import Johnson.Prover.At.DrawHome

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Face

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)
open Johnson.Prover.At (HonestEnc)
open OnBytes.Prover OnBytes.Prover.Print OnBytes.WholeKey
open Johnson.Prover.Print
open OnBytes.K.Arm.Pub (D8)

/-- What the re-packed proof holds. -/
theorem lowPrf_parts {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (k : FullKey lam L aT aL) (p : RequestProof lam L) {n : ℕ}
    {a : Option (OneProtocolProof lam (batTC L aT))} {lk : Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))}
    {b : Option (OneProtocolProof lam L.onlineBatch)} (e : lowPrf k p = ⟨n, a, lk, b⟩) : k.piT = a ∧ p.piB = b :=
  ⟨congrArg OfflineLinkOnlineProof.piT e, congrArg OfflineLinkOnlineProof.piB e⟩

section Letters
variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- the ground input -/
local notation "ℜ" => R S c₀ m₀

/-- The key file's string: its three run values pass the format's test. -/
def RunsOkT (π : OneProtocolProof 256 (QT S)) : Prop :=
  Fmt.runOk (bitsToBytes π.salt) = true ∧
    Fmt.runOk (pls₂ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty silK S.runK) π).1.run = true ∧
    Fmt.runOk (pls₃ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty silK S.runK) π).1 = true

/-- The proof file's string: the same. -/
def RunsOkB (π : OneProtocolProof 256 (QB S)) : Prop :=
  Fmt.runOk (bitsToBytes π.salt) = true ∧
    Fmt.runOk (pls₂ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty silP S.runP) π).1.run = true ∧
    Fmt.runOk (pls₃ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty silP S.runP) π).1 = true

/-- **The exception**: one of the six run values of the key's string and the proof's string is 32
zero bytes. At these the byte format refuses what the compiled verifier accepts. -/
def ZeroRun (k : FullKey 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) (π : RequestProof 256 (ℜ).protocol) : Prop :=
  (∃ a : OneProtocolProof 256 (batTC (ℜ).protocol (ℜ).offlineRoundSplits), k.piT = some a ∧ ¬ RunsOkT S a) ∨
    ∃ b : OneProtocolProof 256 (ℜ).protocol.onlineBatch, π.piB = some b ∧ ¬ RunsOkB S b

/-- **What the compiler's honest settings owe at the bytes.** cB: the digest's bytes at this reading.
runsT, runsB: the run values that the strategies' coins fix. -/
structure SideBytes (H : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) (cB : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (runsT : H.KT → ByteArray × ByteArray)
    (runsB : H.KB → ByteArray × ByteArray) : Prop where
  c32 : cB.size = 32
  depthL : sL.logLeaves = 0
  tableSalts : ∀ b j, j < 2 ^ frS.P.T.a →
    ∃ o : ByteArray, o.size = saltG S.G ∧ H.sl.e b j = leafSalt cB o
  coinsT : ∀ a k, ∃ bc : ByteCoins (LC S c₀ m₀),
    H.dressT (H.rvT (H.kT.e k)) (H.coT.e a) = coinsOf (GT S).nJ (GT S).n3 (sTG S.G).logLeaves bc ∧
      bc.Fit (saltG S.G) (sTG S.G) ∧ bc.run2 = (runsT (H.kT.e k)).1 ∧
      bc.run3 = (runsT (H.kT.e k)).2
  coinsL : ∀ a k, ∃ bc : ByteCoins (LC S c₀ m₀),
    H.dressL (H.rvL (H.kL.e k)) (H.coL.e a) =
        coinsOf (dsF.length + 1) (dsF.length + 1) sL.logLeaves bc ∧
      bc.Fit (saltG S.G) sL
  coinsB : ∀ a k, ∃ bc : ByteCoins (LC S c₀ m₀),
    H.dressB (H.rvB (H.kB.e k)) (H.coB.e a) = coinsOf (GB S).nJ (GB S).n3 (sBG S.G).logLeaves bc ∧
      bc.Fit (saltG S.G) (sBG S.G) ∧ bc.run2 = (runsB (H.kB.e k)).1 ∧
      bc.run3 = (runsB (H.kB.e k)).2
  capT : ∀ j, H.capT j < 2 ^ 64
  capL : ∀ j, H.capL j < 2 ^ 64
  capB : ∀ j, H.capB j < 2 ^ 64
  number : ∀ j, j < H.M + 1 → H.nm j < 2 ^ 64

/-- **What the two whole files' strategies owe at the bytes**: the run values that their coins fix
are what they send, and their words and columns can be printed. -/
structure StratsPrint (H : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (runsT : H.KT → ByteArray × ByteArray) (runsB : H.KB → ByteArray × ByteArray)
    (ok : (ℜ).Index → Prop) (Tr : (ℜ).Index → (ℜ).Instance → Prop) : Prop where
  T : ∀ i r e κ, ok i → StratLaw (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
    ByteArray.empty (H.st.T i r e κ) (runsT κ).1 (runsT κ).2
  B : ∀ i r e x n κ, Tr i x → StratLaw (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀
    S.G.z₀.2)
    ByteArray.empty (H.st.B i r e x n κ) (runsB κ).1 (runsB κ).2

theorem tableOwes_congr {cfg : ByteArray} {n : ℕ} {y : Fin n → PQ.SgX} {sl sl' : ℕ → Bits}
    {P : Fin n → Prop} (h : ∀ p : Fin n, sl p.val = sl' p.val) (t : TableOwes cfg y sl P) :
    TableOwes cfg y sl' P := by
  intro p hp
  rw [← h p]
  exact t p hp

/-- A table's salts at the places of its leaves. -/
theorem side_salts (H : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) {cB : ByteArray}
    {sL : OnBytes.Params.LinBindingShape} {runsT : H.KT → ByteArray × ByteArray}
    {runsB : H.KB → ByteArray × ByteArray} (hB : SideBytes S c₀ m₀ H cB sL runsT runsB)
    (h64 : saltG S.G ≤ 64) (hE : HonestEnc S.E) (i : (ℜ).Index) (r : (ℜ).protocol.EncodingRandomness)
    (b : Fin (H.sl.n + 1)) :
    TableOwes (n := 2 ^ frS.P.T.a) cB ((ℜ).protocol.encodeIndex i r) (cutS (2 ^ (ℜ).queryLayout.depth) (H.sl.e b))
        (fun _ => True) ∧
      ∀ j, j < 2 ^ frS.P.T.a →
        (cutS (2 ^ (ℜ).queryLayout.depth) (H.sl.e b) j).length = 256 + 8 * saltG S.G := by
  have hex : ∀ j, ∃ o : ByteArray, j < 2 ^ frS.P.T.a →
      o.size = saltG S.G ∧ H.sl.e b j = leafSalt cB o := by
    intro j
    by_cases hj : j < 2 ^ frS.P.T.a
    · obtain ⟨o, h1, h2⟩ := hB.tableSalts b j hj
      exact ⟨o, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨ByteArray.empty, fun h => absurd h hj⟩
  choose o ho using hex
  have hcut : ∀ j, j < 2 ^ frS.P.T.a →
      cutS (2 ^ (ℜ).queryLayout.depth) (H.sl.e b) j = leafSalt cB (o j) := by
    intro j hj
    show (if j < 2 ^ (ℜ).queryLayout.depth then H.sl.e b j else []) = _
    rw [if_pos (show j < 2 ^ (ℜ).queryLayout.depth from hj)]
    exact (ho j hj).2
  refine ⟨tableOwes_congr (fun p => (hcut p.val p.isLt).symm)
    (tableOwes_fullD (S.inputFieldsAtReadings c₀ m₀) hE i r cB o hB.c32
      (fun j hj => by rw [(ho j hj).1]; exact h64) _), ?_⟩
  intro j hj
  have e := OnBytes.Maker.length_leafSalt cB (o j)
  rw [hB.c32, (ho j hj).1] at e
  rw [hcut j hj]
  omega

/-- the told record -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading S c₀ m₀

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

set_option maxRecDepth 20000 in
/-- **At one reading**: outside the exception, what the honest side returns and the verifier accepts
is a typed proof that Fits. -/
theorem fits_at_side (d : D8)
    (H : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (g : Fam (typedOracleFamily 256 (ℜ).queryLayout.K (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits))) (cB : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (runsT : H.KT → ByteArray × ByteArray)
    (runsB : H.KB → ByteArray × ByteArray) (hB : SideBytes S c₀ m₀ H cB sL runsT runsB)
    (ok : (ℜ).Index → Prop) (Tr : (ℜ).Index → (ℜ).Instance → Prop) (hok : ∀ i x, Tr i x → ok i)
    (hP : StratsPrint S c₀ m₀ H runsT runsB ok Tr)
    (hN : NumbersFit (KF S.DK S.DP) S.DK dsF S.DP) (h64 : saltG S.G ≤ 64) (hEnc : HonestEnc S.E)
    (wK : ∀ d ∈ S.DK.ds₁ ++ (S.DK.ds₂ ++ S.DK.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64)
    (wP : ∀ d ∈ S.DP.ds₁ ++ (S.DP.ds₂ ++ S.DP.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64)
    (i : (ℜ).Index) (x : XF) (hTr : Tr i x) (c : DrawC 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits H.KT H.KL) (hc :
                                                    DrawCOf H c)
    (dP : DrawP 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits H.KB) (hdP : DrawPOf H dP)
    (hy : (verifyW (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) (ℜ).fixedSample (ℜ).compilerParameters ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d)
                                          H i c).det g).1 x
      ((proveAt (ℜ).queryLayout ((𝔗).cA d) (ℜ).fixedSample H ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2 x
        dP).det g)).det g = true)
    (hBad : ¬ ZeroRun S c₀ m₀ ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).1
      ((proveAt (ℜ).queryLayout ((𝔗).cA d) (ℜ).fixedSample H ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2 x
        dP).det g)) :
    ∃ q : Johnson.Prover.Print.Typed S, q.aux = [] ∧
      lowKey ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).1 = ⟨q.cm, q.rcd⟩ ∧
      lowPrf ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).1 ((proveAt (ℜ).queryLayout ((𝔗).cA d)
                  (ℜ).fixedSample H ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2 x dP).det g) =
        ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩ ∧
      Fits S cB q := by
  obtain ⟨⟨b₁, hs₁⟩, ⟨a₁, k₁, hco₁, hk₁⟩, hlen, hcop⟩ := hc
  obtain ⟨hj, ⟨a₃, k₃, hco₃, hk₃⟩⟩ := hdP
  have hj' : dP.j < c.copies.length := by rw [hlen]; exact hj
  have he : c.copies[dP.j]? = some c.copies[dP.j] := List.getElem?_eq_getElem hj'
  obtain ⟨⟨b₂, hs₂⟩, ⟨a₂, k₂, hco₂, hk₂⟩⟩ := hcop _ (List.getElem_mem hj')
  generalize c.copies[dP.j] = e at he hs₂ hco₂ hk₂
  obtain ⟨bcT, eT, fT, r2T, r3T⟩ := hB.coinsT a₁ k₁
  obtain ⟨bcL, eL, fL⟩ := hB.coinsL a₂ k₂
  obtain ⟨bcB, eB, fB, r2B, r3B⟩ := hB.coinsB a₃ k₃
  have hcoT : (drawOf (ℜ).queryLayout H c e dP).coT =
      coinsOf (GT S).nJ (GT S).n3 (sTG S.G).logLeaves bcT := by
    show H.dressT (H.rvT c.κ) c.co = _
    rw [hco₁, hk₁]
    exact eT
  have hcoL : (drawOf (ℜ).queryLayout H c e dP).coL =
      coinsOf (dsF.length + 1) (dsF.length + 1) sL.logLeaves bcL := by
    show H.dressL (H.rvL e.κ) e.co = _
    rw [hco₂, hk₂]
    exact eL
  have hcoB : (drawOf (ℜ).queryLayout H c e dP).coB =
      coinsOf (GB S).nJ (GB S).n3 (sBG S.G).logLeaves bcB := by
    show H.dressB (H.rvB dP.κ) dP.co = _
    rw [hco₃, hk₃]
    exact eB
  obtain ⟨tK, lK⟩ := side_salts S c₀ m₀ H hB h64 hEnc i c.r b₁
  obtain ⟨tC, lC⟩ := side_salts S c₀ m₀ H hB h64 hEnc i e.r b₂
  rw [← hs₁] at tK lK
  rw [← hs₂] at tC lC
  have hd : DrawFit (ℜ).queryLayout (ℜ).compilerParameters (drawOf (ℜ).queryLayout H c e dP) :=
    drawFit_tOf S c₀ m₀ _ sL bcT bcL bcB _ _ _ _ _ _ hB.depthL (fun j hj => lC j hj) hcoT fT hcoL
      fL hcoB fB
  have l₁ : ∀ j, j < (ℜ).protocol.wordLength → (cutS (2 ^ (ℜ).queryLayout.depth) c.s j).length = (ℜ).compilerParameters.sMT :=
    fun j hj => (lK j hj).trans (sMT_tOf S c₀ m₀).symm
  obtain ⟨π, e₁, e₂, τT, τL, τB, hπ, hkey, hE, aT, aB, hn⟩ :=
    ends_of_yes (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) (ℜ).fixedSample (ℜ).compilerParameters H g (wiresFit_layoutsByPublicReading S c₀ m₀ d hN) i x c e dP
      he l₁ hd hy
  obtain ⟨πT, πL, πB, hπ₀, rT, -, rB, -, -, pB⟩ := hE.fields
  have lT : StratLaw (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty (H.st.joint.T i c.r e₁ (drawOf (ℜ).queryLayout H c e dP).κ) bcT.run2 bcT.run3 := by
    rw [r2T, r3T, ← hk₁]
    exact hP.T i c.r e₁ c.κ (hok i x hTr)
  have lB : StratLaw (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty (H.st.joint.B i e.r e₂ x (H.nm dP.j) (drawOf (ℜ).queryLayout H c e dP).κ) bcB.run2
      bcB.run3 := by
    rw [r2B, r3B, ← hk₃]
    exact hP.B i e.r e₂ x (H.nm dP.j) dP.κ hTr
  obtain ⟨sT, sB⟩ := stratsOwe_fullD (S.inputFieldsAtReadings c₀ m₀) ((𝔗).Sd d) ((𝔗).cA d) H.b₀ H.st.joint H.capT
    H.capL H.capB g i c.r _ x _ π e₁ e₂ τT τL τB bcT bcB hE lT lB _ _ _ πT πL πB hπ₀
  have ee := hπ.symm.trans hπ₀
  obtain ⟨kpi, ppi⟩ := lowPrf_parts _ _ ee
  have okT : RunsOkT S πT := by
    by_contra hb
    exact hBad (Or.inl ⟨πT, kpi, hb⟩)
  have okB : RunsOkB S πB := by
    by_contra hb
    exact hBad (Or.inr ⟨πB, ppi, hb⟩)
  have saltT : πT.salt = bytesToBits bcT.run1 := by
    have r := rT
    rw [hcoT, proveTA_fullD] at r
    obtain ⟨z, -, e₀, -⟩ := (proveX_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 r
    rw [e₀]
    rfl
  have saltB : πB.salt = bytesToBits bcB.run1 := by
    have r := rB
    rw [hcoB, proveBA_fullD] at r
    obtain ⟨z, -, e₀, -⟩ := (proveX_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 r
    rw [e₀]
    rfl
  have cT : CoinsPrint bcT (saltG S.G) (sTG S.G) :=
    ⟨fT, h64, by
      have h := okT.1
      rw [saltT, bitsToBytes_bytesToBits] at h
      exact h, by
      have h := okT.2.1
      rw [sT.run2] at h
      exact h, by
      have h := okT.2.2
      rw [sT.run3] at h
      exact h⟩
  have cB' : CoinsPrint bcB (saltG S.G) (sBG S.G) :=
    ⟨fB, h64, by
      have h := okB.1
      rw [saltB, bitsToBytes_bytesToBits] at h
      exact h, by
      have h := okB.2.1
      rw [sB.run2] at h
      exact h, by
      have h := okB.2.2
      rw [sB.run3] at h
      exact h⟩
  have hPO := publicOwes_of S H.capT H.capL H.capB hN wK wP hB.capT hB.capL hB.capB
  have hG : GoodOwes S c₀ m₀ cB (saltG S.G) sL bcT bcL bcB H.capT H.capL H.capB i c.r
      (cutS (2 ^ (ℜ).queryLayout.depth) c.s) (drawOf (ℜ).queryLayout H c e dP) :=
    { c32 := hB.c32
      formT := hcoT
      formL := hcoL
      formB := hcoB
      coT := cT
      coB := cB'
      coL := fL
      depthL := hB.depthL
      capT := hPO.capT
      capL := hPO.capL
      capB := hPO.capB
      depT := hPO.depT
      depB := hPO.depB
      depL := hPO.depL
      widT := hPO.widT
      widB := hPO.widB
      number := hB.number _ hj
      tableK := tK
      tableC := tC }
  obtain ⟨πT', πL', πB', hπ', hF⟩ := fits_of_good S c₀ m₀ ((𝔗).Sd d) ((𝔗).cA d) H.b₀ H.st.joint
    H.capT H.capL H.capB g i c.r (cutS (2 ^ (ℜ).queryLayout.depth) c.s) x (drawOf (ℜ).queryLayout H c e dP) π e₁ e₂ τT
    τL τB cB (saltG S.G) sL bcT bcL bcB hE (wiresFit_layoutsByPublicReading S c₀ m₀ d hN) aT aB hG
    fun a b c' ha => by
      obtain ⟨rfl, -, rfl, -⟩ := prf_inj (hπ₀.symm.trans ha)
      exact ⟨sT, sB, copy_of_num_layoutsByPublicReading S c₀ m₀ d (H.nm dP.j) πB (by rw [pB]; exact hn)⟩
  exact typed_of_parts S c₀ m₀ cB _ _ _ _ _ _ _ _ hF _ hkey _ (hπ.symm.trans hπ')

set_option maxRecDepth 20000 in
/-- **The exception, read off the coins.** Where the verifier says yes, and the six run values of the
coins that were drawn pass the format's test, the whole key and the proof are not excepted. -/
theorem not_zeroRun_of_coins (d : D8)
    (H : HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (g : Fam (typedOracleFamily 256 (ℜ).queryLayout.K (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits))) (cB : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (runsT : H.KT → ByteArray × ByteArray)
    (runsB : H.KB → ByteArray × ByteArray) (hB : SideBytes S c₀ m₀ H cB sL runsT runsB)
    (ok : (ℜ).Index → Prop) (Tr : (ℜ).Index → (ℜ).Instance → Prop) (hok : ∀ i x, Tr i x → ok i)
    (hP : StratsPrint S c₀ m₀ H runsT runsB ok Tr)
    (hN : NumbersFit (KF S.DK S.DP) S.DK dsF S.DP) (h64 : saltG S.G ≤ 64) (hEnc : HonestEnc S.E)
    (wK : ∀ d ∈ S.DK.ds₁ ++ (S.DK.ds₂ ++ S.DK.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64)
    (wP : ∀ d ∈ S.DP.ds₁ ++ (S.DP.ds₂ ++ S.DP.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64)
    (i : (ℜ).Index) (x : XF) (hTr : Tr i x) (c : DrawC 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits H.KT H.KL) (hc :
                                                    DrawCOf H c)
    (dP : DrawP 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits H.KB) (hdP : DrawPOf H dP)
    (hy : (verifyW (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) (ℜ).fixedSample (ℜ).compilerParameters ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d)
                                          H i c).det g).1 x
      ((proveAt (ℜ).queryLayout ((𝔗).cA d) (ℜ).fixedSample H ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2 x
        dP).det g)).det g = true)
    (okT1 : Fmt.runOk (bitsToBytes c.co.salt) = true) (okB1 : Fmt.runOk (bitsToBytes dP.co.salt) =
      true)
    (okT2 : Fmt.runOk (runsT c.κ).1 = true) (okT3 : Fmt.runOk (runsT c.κ).2 = true)
    (okB2 : Fmt.runOk (runsB dP.κ).1 = true) (okB3 : Fmt.runOk (runsB dP.κ).2 = true) :
    ¬ ZeroRun S c₀ m₀ ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).1
      ((proveAt (ℜ).queryLayout ((𝔗).cA d) (ℜ).fixedSample H ((commitAt (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) H i c).det g).2 x
        dP).det g) := by
  obtain ⟨⟨b₁, hs₁⟩, ⟨a₁, k₁, hco₁, hk₁⟩, hlen, hcop⟩ := hc
  obtain ⟨hj, ⟨a₃, k₃, hco₃, hk₃⟩⟩ := hdP
  have hj' : dP.j < c.copies.length := by rw [hlen]; exact hj
  have he : c.copies[dP.j]? = some c.copies[dP.j] := List.getElem?_eq_getElem hj'
  obtain ⟨⟨b₂, hs₂⟩, ⟨a₂, k₂, hco₂, hk₂⟩⟩ := hcop _ (List.getElem_mem hj')
  generalize c.copies[dP.j] = e at he hs₂ hco₂ hk₂
  obtain ⟨bcT, eT, fT, r2T, r3T⟩ := hB.coinsT a₁ k₁
  obtain ⟨bcL, eL, fL⟩ := hB.coinsL a₂ k₂
  obtain ⟨bcB, eB, fB, r2B, r3B⟩ := hB.coinsB a₃ k₃
  have hcoT : (drawOf (ℜ).queryLayout H c e dP).coT =
      coinsOf (GT S).nJ (GT S).n3 (sTG S.G).logLeaves bcT := by
    show H.dressT (H.rvT c.κ) c.co = _
    rw [hco₁, hk₁]
    exact eT
  have hcoL : (drawOf (ℜ).queryLayout H c e dP).coL =
      coinsOf (dsF.length + 1) (dsF.length + 1) sL.logLeaves bcL := by
    show H.dressL (H.rvL e.κ) e.co = _
    rw [hco₂, hk₂]
    exact eL
  have hcoB : (drawOf (ℜ).queryLayout H c e dP).coB =
      coinsOf (GB S).nJ (GB S).n3 (sBG S.G).logLeaves bcB := by
    show H.dressB (H.rvB dP.κ) dP.co = _
    rw [hco₃, hk₃]
    exact eB
  obtain ⟨tK, lK⟩ := side_salts S c₀ m₀ H hB h64 hEnc i c.r b₁
  obtain ⟨tC, lC⟩ := side_salts S c₀ m₀ H hB h64 hEnc i e.r b₂
  rw [← hs₁] at tK lK
  rw [← hs₂] at tC lC
  have hd : DrawFit (ℜ).queryLayout (ℜ).compilerParameters (drawOf (ℜ).queryLayout H c e dP) :=
    drawFit_tOf S c₀ m₀ _ sL bcT bcL bcB _ _ _ _ _ _ hB.depthL (fun j hj => lC j hj) hcoT fT hcoL
      fL hcoB fB
  have l₁ : ∀ j, j < (ℜ).protocol.wordLength → (cutS (2 ^ (ℜ).queryLayout.depth) c.s j).length = (ℜ).compilerParameters.sMT :=
    fun j hj => (lK j hj).trans (sMT_tOf S c₀ m₀).symm
  obtain ⟨π, e₁, e₂, τT, τL, τB, hπ, hkey, hE, aT, aB, hn⟩ :=
    ends_of_yes (ℜ).queryLayout ((𝔗).Sd d) ((𝔗).cA d) (ℜ).fixedSample (ℜ).compilerParameters H g (wiresFit_layoutsByPublicReading S c₀ m₀ d hN) i x c e dP
      he l₁ hd hy
  obtain ⟨πT, πL, πB, hπ₀, rT, -, rB, -, -, pB⟩ := hE.fields
  have lT : StratLaw (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty (H.st.joint.T i c.r e₁ (drawOf (ℜ).queryLayout H c e dP).κ) bcT.run2 bcT.run3 := by
    rw [r2T, r3T, ← hk₁]
    exact hP.T i c.r e₁ c.κ (hok i x hTr)
  have lB : StratLaw (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty (H.st.joint.B i e.r e₂ x (H.nm dP.j) (drawOf (ℜ).queryLayout H c e dP).κ) bcB.run2
      bcB.run3 := by
    rw [r2B, r3B, ← hk₃]
    exact hP.B i e.r e₂ x (H.nm dP.j) dP.κ hTr
  obtain ⟨sT, sB⟩ := stratsOwe_fullD (S.inputFieldsAtReadings c₀ m₀) ((𝔗).Sd d) ((𝔗).cA d) H.b₀ H.st.joint H.capT
    H.capL H.capB g i c.r _ x _ π e₁ e₂ τT τL τB bcT bcB hE lT lB _ _ _ πT πL πB hπ₀
  have ee := hπ.symm.trans hπ₀
  obtain ⟨kpi, ppi⟩ := lowPrf_parts _ _ ee
  have saltT : πT.salt = c.co.salt := by
    have r := rT
    rw [proveTA_fullD] at r
    obtain ⟨z, -, e₀, -⟩ := (proveX_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 r
    rw [e₀]
    rfl
  have saltB : πB.salt = dP.co.salt := by
    have r := rB
    rw [proveBA_fullD] at r
    obtain ⟨z, -, e₀, -⟩ := (proveX_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 r
    rw [e₀]
    rfl
  have hT : RunsOkT S πT := ⟨by rw [saltT]; exact okT1, by
    rw [sT.run2, r2T, ← hk₁]; exact okT2, by rw [sT.run3, r3T, ← hk₁]; exact okT3⟩
  have hB' : RunsOkB S πB := ⟨by rw [saltB]; exact okB1, by
    rw [sB.run2, r2B, ← hk₃]; exact okB2, by rw [sB.run3, r3B, ← hk₃]; exact okB3⟩
  rintro (⟨a, ha, hb⟩ | ⟨b, hb', hb⟩)
  · obtain rfl := Option.some.inj (ha.symm.trans kpi)
    exact hb hT
  · obtain rfl := Option.some.inj (hb'.symm.trans ppi)
    exact hb hB'

end Letters

section AtFiles

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles)

/-- the told record at Z -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀
/-- its ground input -/
local notation "ℜ" => R (S Z) c₀ m₀

/-- The value of the public reading under a hash function. -/
theorem readAt_told (f : ZKCP.Oracle 256) : readAt (𝔗) f = (cAt Z f, sevenAt Z f) :=
  pub_det_layoutsByPublicReading S Z c₀ m₀ f

set_option maxRecDepth 20000 in
/-- **FitsAtCoins, outside the exception.** -/
theorem fitsAtCoins_of_side
    (h : (𝔗).D → HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (sL : (𝔗).D → OnBytes.Params.LinBindingShape)
    (runsT : ∀ d, (h d).KT → ByteArray × ByteArray)
    (runsB : ∀ d, (h d).KB → ByteArray × ByteArray)
    (hB : ∀ d, SideBytes (S Z) c₀ m₀ (h d) (digToBytes d.1) (sL d) (runsT d) (runsB d))
    (ok : (ℜ).Index → Prop) (Tr : (ℜ).Index → (ℜ).Instance → Prop) (hok : ∀ i x, Tr i x → ok i)
    (hP : ∀ d, StratsPrint (S Z) c₀ m₀ (h d) (runsT d) (runsB d) ok Tr)
    (hN : NumbersFit (KF (S Z).DK (S Z).DP) (S Z).DK dsF (S Z).DP) (h64 : saltG (S Z).G ≤ 64)
    (hEnc : HonestEnc (S Z).E)
    (wK : ∀ d ∈ (S Z).DK.ds₁ ++ ((S Z).DK.ds₂ ++ (S Z).DK.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64)
    (wP : ∀ d ∈ (S Z).DP.ds₁ ++ ((S Z).DP.ds₂ ++ (S Z).DP.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64) :
    FitsAtCoins S c₀ m₀ Z h Tr (ZeroRun (S Z) c₀ m₀) := by
  intro f i x hTr c hc dP hdP hy hBad
  obtain ⟨q, a, b, e, hq⟩ := fits_at_side (S Z) c₀ m₀ (readAt (𝔗) f) (h (readAt (𝔗) f))
    (oraclesAt (𝔗) f (readAt (𝔗) f)) _ _ _ _ (hB _) ok Tr hok (hP _) hN h64 hEnc wK wP i x hTr c hc
      dP hdP hy
    hBad
  refine ⟨q, a, b, e, ?_⟩
  have hc₀ : (readAt (𝔗) f).1 = cAt Z f := congrArg Prod.fst (readAt_told S c₀ m₀ Z f)
  rw [← hc₀]
  exact hq

end AtFiles

end Johnson.Face

#print axioms Johnson.Face.side_salts
#print axioms Johnson.Face.fits_at_side
#print axioms Johnson.Face.not_zeroRun_of_coins
#print axioms Johnson.Face.fitsAtCoins_of_side
