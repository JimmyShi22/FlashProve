-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Face/UndoOfFits.lean: what the committer, the prover and the verifier of the scheme whose
letters are read off the hash function (readOne, Johnson/FrontRoad/Front.lean) can return under one
hash function; and from it: the parser undoes the writer on what the honest side makes (UndoOn,
Johnson/FrontRoad/Complete.lean), at the description of the byte format, wherever each accepted
typed proof that the honest side makes Fits (Johnson/Prover/Print/FormBack.lean).

Main names (namespace Johnson.Face).
  keys_of_support, prf_of_support, yes_of_support   what readOne's three parts can return, as the
    values of the programs behind their coins under the oracle functions read off the hash function.
  UndoOnBut   UndoOn outside a set of excepted keys and proofs.
  undoOnBut_of_coins   UndoOnBut from a statement at all coins that can be drawn.

Not shown here: that such a statement holds.
-/
import Johnson.FrontRoad.Complete
import Johnson.FrontRoad.Front
import Johnson.Prover.Print.FormBack
import Johnson.Prover.Print.FitsOfEnds
import Johnson.Goal.Tie.DescriptionOnBytes
import Johnson.WholeKey.Complete
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Face

open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt OnBytes.FrontRoad
open VerifiableInference VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## Runs under fixed oracle functions -/

section Run
variable {S : OSpec} {α β : Type}

theorem mem_runEager_bind {c : OComp S α} {k : α → OComp S β} {g : Fam S} {b : β}
    (h : b ∈ ((c.bind k).runEager g).support) :
    ∃ a, a ∈ (c.runEager g).support ∧ b ∈ ((k a).runEager g).support := by
  rw [OComp.runEager_bind] at h
  obtain ⟨a, ha, hb⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
  exact ⟨a, ha, hb⟩

theorem mem_runEager_pure {a b : α} {g : Fam S}
    (h : b ∈ ((OComp.pure a : OComp S α).runEager g).support) : b = a :=
  (PMF.mem_support_pure_iff _ _).1 h

theorem mem_runEager_noCoin {c : OComp S α} {g : Fam S} {a : α} (hc : c.NoCoin)
    (h : a ∈ (c.runEager g).support) : a = c.det g := by
  rw [hc.runEager g] at h
  exact (PMF.mem_support_pure_iff _ _).1 h

theorem mem_runEager_onlyCoins {P : α → Prop} {g : Fam S} :
    ∀ {c : OComp S α}, OnlyCoins P c → ∀ {a : α}, a ∈ (c.runEager g).support → P a
  | .pure a, hc, b, h => by
    obtain rfl := mem_runEager_pure h
    exact hc
  | .sample _ _, hc, _, h => by
    obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
    exact mem_runEager_onlyCoins (hc r) hr
  | .query _ _ _, hc, _, _ => hc.elim

theorem run_ofRom {lam : ℕ} (c : OComp (rom lam) α) (f : ZKCP.Oracle lam) :
    (ofRom c).run f = c.runEager (_root_.Run.famOne f) := by
  have e : _root_.Run.famOne f = famOf f := by
    funext o q
    cases o
    rfl
  rw [e, ← runEager_toRom, toRom_ofRom]

end Run

/-! ## What readOne's parts can return -/

section Read
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)

/-- The value of the public reading under the hash function. -/
def readAt (f : ZKCP.Oracle 256) : T.D := T.Pub.det (_root_.Run.famOne f)

/-- The typed oracle functions at d, read off the hash function. -/
def oraclesAt (f : ZKCP.Oracle 256) (d : T.D) :
    Fam (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) :=
  readBlocks (T.m d) (_root_.Run.famOne f)

/-- **The committer.** What it can return is the committer behind coins that can be drawn, at the
reading's value. -/
theorem keys_of_support (hp : T.Pub.NoCoin) (i : R.Index) (f : ZKCP.Oracle 256)
    (keys : KeyT R × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (hk : keys ∈ (((readOne T h).C i).run f).support) :
    ∃ c : DrawC 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits (h (readAt T f)).KT (h (readAt T f)).KL,
      DrawCOf (h (readAt T f)) c ∧
      keys = ((T.part (readAt T f),
          ((commitAt R.queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (h (readAt T f)) i c).det
            (oraclesAt T f (readAt T f))).1),
        (readAt T f,
          ((commitAt R.queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (h (readAt T f)) i c).det
            (oraclesAt T f (readAt T f))).2)) := by
  have h1 : keys ∈ ((T.Pub.bind fun d => ((toldAt T h d).C i).bind fun k =>
      .pure (k.1, (d, k.2))).runEager (_root_.Run.famOne f)).support := by
    have e := run_ofRom ((readTold T h).C i) f
    have e' : ((readOne T h).C i).run f = ((readTold T h).C i).runEager (_root_.Run.famOne f) := e
    rw [e'] at hk
    exact hk
  obtain ⟨d, hd, h2⟩ := mem_runEager_bind h1
  obtain rfl : d = readAt T f := mem_runEager_noCoin hp hd
  obtain ⟨k₁, hk₁, h3⟩ := mem_runEager_bind h2
  obtain rfl := mem_runEager_pure h3
  have h4 : k₁ ∈ ((((wholeAt T h (readAt T f)).C i).bind fun k =>
      .pure ((T.part (readAt T f), k.1), k.2)).runEager (_root_.Run.famOne f)).support := hk₁
  obtain ⟨k₂, hk₂, h5⟩ := mem_runEager_bind h4
  obtain rfl := mem_runEager_pure h5
  have h6 : k₂ ∈ ((((typedAt T h (readAt T f)).C i).overOne (T.m (readAt T f))).runEager
      (_root_.Run.famOne f)).support := hk₂
  rw [runEager_overOne] at h6
  have h7 : k₂ ∈ (((coinsC R.queryLayout (h (readAt T f))).bind fun c =>
      commitAt R.queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (h (readAt T f)) i c).runEager
        (oraclesAt T f (readAt T f))).support := h6
  obtain ⟨c, hc, h8⟩ := mem_runEager_bind h7
  obtain rfl := mem_runEager_noCoin (noCoin_commitAt R.queryLayout _ _ _ i c) h8
  exact ⟨c, mem_runEager_onlyCoins (onlyCoins_coinsC R.queryLayout _) hc, rfl⟩

/-- **The prover.** -/
theorem prf_of_support (d : T.D) (isk : Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (x : R.Instance)
    (f : ZKCP.Oracle 256) (π : RequestProof 256 R.protocol)
    (hπ : π ∈ (((readOne T h).P (d, isk) x ()).run f).support) :
    ∃ dP : DrawP 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits (h d).KB, DrawPOf (h d) dP ∧
      π = (proveAt R.queryLayout (T.cA d) R.fixedSample (h d) isk x dP).det (oraclesAt T f d) := by
  have h1 : π ∈ (((((typedAt T h d).P isk [(x, ())]).overOne (T.m d)).bind fun πs =>
      .pure (ZKCP.Special.head1 πs)).runEager (_root_.Run.famOne f)).support := by
    have e := run_ofRom (((readTold T h).P (d, isk) [(x, ())]).bind fun πs =>
      .pure (ZKCP.Special.head1 πs)) f
    have e' : ((readOne T h).P (d, isk) x ()).run f =
        (((readTold T h).P (d, isk) [(x, ())]).bind fun πs =>
          .pure (ZKCP.Special.head1 πs)).runEager (_root_.Run.famOne f) := e
    rw [e'] at hπ
    exact hπ
  obtain ⟨πs, hs, h2⟩ := mem_runEager_bind h1
  obtain rfl := mem_runEager_pure h2
  rw [runEager_overOne] at hs
  have h3 : πs ∈ (((coinsP R.queryLayout (h d)).bind fun dP =>
      (proveAt R.queryLayout (T.cA d) R.fixedSample (h d) isk x dP).bind fun π =>
        (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof 256 R.protocol) [(x, ())]))).runEager
      (oraclesAt T f d)).support := hs
  obtain ⟨dP, hdP, h4⟩ := mem_runEager_bind h3
  obtain ⟨π', hπ', h5⟩ := mem_runEager_bind h4
  obtain rfl := mem_runEager_pure h5
  obtain rfl := mem_runEager_noCoin (noCoin_proveAt R.queryLayout _ _ _ isk x dP) hπ'
  exact ⟨dP, mem_runEager_onlyCoins (onlyCoins_coinsP R.queryLayout _) hdP, rfl⟩

/-- **The verifier.** -/
theorem yes_of_support (hp : T.Pub.NoCoin) (k : KeyT R) (x : R.Instance) (π : RequestProof 256 R.protocol)
    (f : ZKCP.Oracle 256) (hV : true ∈ (((readOne T h).V k x π).run f).support) :
    (verifyW R.queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) R.fixedSample R.compilerParameters k.2 x π).det
      (oraclesAt T f (readAt T f)) = true := by
  have h1 : true ∈ ((T.Pub.bind fun d => (toldAt T h d).V k x π).runEager (_root_.Run.famOne
    f)).support := by
    have e := run_ofRom ((readTold T h).V k x π) f
    have e' : ((readOne T h).V k x π).run f = ((readTold T h).V k x π).runEager (_root_.Run.famOne
      f) := e
    rw [e'] at hV
    exact hV
  obtain ⟨d, hd, h2⟩ := mem_runEager_bind h1
  obtain rfl : d = readAt T f := mem_runEager_noCoin hp hd
  have h3 : true ∈ ((if k.1 = T.part (readAt T f) then (wholeAt T h (readAt T f)).V k.2 x π
      else .pure false).runEager (_root_.Run.famOne f)).support := h2
  split at h3
  · have h4 : true ∈ (((typedAt T h (readAt T f)).V k.2 x π).overOne
        (T.m (readAt T f)) |>.runEager (_root_.Run.famOne f)).support := h3
    rw [runEager_overOne] at h4
    exact (mem_runEager_noCoin (noCoin_VRA R.queryLayout _ _ R.fixedSample R.compilerParameters _ _ _) h4).symm
  · cases mem_runEager_pure h3

end Read

/-! ## The parser undoes the writer -/

open VerifierAndGoals FlashProve
open Johnson.Prover.Print
open _root_.Run (digToBytes)

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)
  (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles)

/-- the told record at Z -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀
/-- its ground input -/
local notation "ℜ" => R (S Z) c₀ m₀

/-- **UndoOn outside a set of excepted keys and proofs.** The words of UndoOn, with one more premise:
the whole key and the proof are not in Bad. -/
def UndoOnBut (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    {J : Type} (idx : J → (D.input Z c₀ m₀).Index)
    (Tr : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) {Form : Type}
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
    (Bad : FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits →
      RequestProof 256 (D.input Z c₀ m₀).protocol → Prop) : Prop :=
  ∀ (w : J) (f : ZKCP.Oracle 256), ∀ keys ∈ (((readOne T h).C (idx w)).run f).support,
    ∀ (x' : List Token × List Token) x, (D.input Z c₀ m₀).buildInstance x' [] = some x → Tr (idx w) x →
      ∀ π ∈ (((readOne T h).P keys.2 x ()).run f).support,
        true ∈ (((readOne T h).V keys.1 x π).run f).support → ¬ Bad keys.1.2 π →
          (parse x'.1 x'.2 (encF ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))).evaluate f =
            ([], (lowKey keys.1.2, lowPrf keys.1.2 π))

/-- **UndoOnBut from a statement at all coins**: what readOne's parts can return, at any description.
-/
theorem undoOnBut_of_coins (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀))
    (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)
    {J : Type} (idx : J → (D.input Z c₀ m₀).Index)
    (Tr : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) {Form : Type}
    (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
    (Bad : FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits →
      RequestProof 256 (D.input Z c₀ m₀).protocol → Prop) (hp : T.Pub.NoCoin)
    (hC : ∀ (f : ZKCP.Oracle 256) (i : (D.input Z c₀ m₀).Index) (x : (D.input Z c₀ m₀).Instance), Tr i x →
      ∀ (c : DrawC 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
        (D.input Z c₀ m₀).linkRoundSplits (h (readAt T f)).KT (h (readAt T f)).KL),
      DrawCOf (h (readAt T f)) c →
      ∀ dP : DrawP 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
        (D.input Z c₀ m₀).linkRoundSplits (h (readAt T f)).KB,
      DrawPOf (h (readAt T f)) dP →
      (verifyW (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (D.input Z c₀ m₀).fixedSample
        (D.input Z c₀ m₀).compilerParameters
        ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (h (readAt T f)) i
          c).det (oraclesAt T f (readAt T f))).1 x
        ((proveAt (D.input Z c₀ m₀).queryLayout (T.cA (readAt T f)) (D.input Z c₀ m₀).fixedSample (h (readAt T f))
          ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (h (readAt T f)) i
            c).det (oraclesAt T f (readAt T f))).2 x dP).det
          (oraclesAt T f (readAt T f)))).det (oraclesAt T f (readAt T f)) = true →
      ¬ Bad ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (h (readAt T f))
          i c).det (oraclesAt T f (readAt T f))).1
        ((proveAt (D.input Z c₀ m₀).queryLayout (T.cA (readAt T f)) (D.input Z c₀ m₀).fixedSample (h (readAt T f))
          ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f)) (h (readAt T f)) i
            c).det (oraclesAt T f (readAt T f))).2 x dP).det
          (oraclesAt T f (readAt T f))) →
      ∀ x' : List Token × List Token,
        (parse x'.1 x'.2 (encF ([], (lowKey ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f))
          (T.cA (readAt T f)) (h (readAt T f)) i c).det (oraclesAt T f (readAt T f))).1,
          lowPrf ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f))
            (h (readAt T f)) i c).det (oraclesAt T f (readAt T f))).1
            ((proveAt (D.input Z c₀ m₀).queryLayout (T.cA (readAt T f)) (D.input Z c₀ m₀).fixedSample (h (readAt T f))
              ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f))
                (h (readAt T f)) i c).det (oraclesAt T f (readAt T f))).2 x dP).det
              (oraclesAt T f (readAt T f))))))).evaluate f =
          ([], (lowKey ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f))
            (T.cA (readAt T f)) (h (readAt T f)) i c).det (oraclesAt T f (readAt T f))).1,
            lowPrf ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f))
              (h (readAt T f)) i c).det (oraclesAt T f (readAt T f))).1
              ((proveAt (D.input Z c₀ m₀).queryLayout (T.cA (readAt T f)) (D.input Z c₀ m₀).fixedSample
                (h (readAt T f))
                ((commitAt (D.input Z c₀ m₀).queryLayout (T.Sd (readAt T f)) (T.cA (readAt T f))
                  (h (readAt T f)) i c).det (oraclesAt T f (readAt T f))).2 x dP).det
                (oraclesAt T f (readAt T f)))))) :
    UndoOnBut D Z c₀ m₀ T h idx Tr parse encF Bad := by
  intro w f keys hk x' x _ hTr π hπ hV hBad
  obtain ⟨c, hc, rfl⟩ := keys_of_support T h hp (idx w) f keys hk
  obtain ⟨dP, hdP, rfl⟩ := prf_of_support T h _ _ x f π hπ
  have hy := yes_of_support T h hp _ x _ f hV
  exact hC f (idx w) x hTr c hc dP hdP hy hBad x'

end Johnson.Face

#print axioms Johnson.Face.keys_of_support
#print axioms Johnson.Face.prf_of_support
#print axioms Johnson.Face.yes_of_support
#print axioms Johnson.Face.undoOnBut_of_coins
