-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsLeftOf.lean: the record `ArmsLeft b` (Johnson/Top/FrontPaid.lean: the bounds on the
input r's checks of the key file and of the proof file, and that neither check tosses a coin), at
an input r and a b that meet the side hypotheses listed below, from bounds on the two typed checks
that ask for their public digests themselves, each at its own reading and its own coding. The two
bounds and the side hypotheses are hypotheses here.

What this file states. `keyArm_at`: `ArmBoundD b.rd (liftKC r) (KeyHoldsCD b) b.εK`. `proofArm_at`:
`ArmBoundD b.rd (liftPC r) (ProofHoldsCD b) b.εP`. `armsLeft_of_bounds`: `ArmsLeft b`, which is what
remains of `CoreArmsCD b` once `EntryPaid b` is taken out. At the inputs of
Johnson/Top/Pub/EntryFamC.lean [not in this library] b's reading (a computation that queries the
hash function) and b's word are the entry file's check's: two public digests, and the word through
that check's coding. The key file's and the proof file's checks read more public digests and have
codings of their own, and their bounds are stated at their own readings (`armBoundD_test`,
Johnson/Top/ArmsFoldTest.lean;
`armBoundD_sess`, Johnson/Top/ArmsFoldSess.lean). Here they are carried to b: to the wide key and to
r's own checks by Johnson/Top/ArmsFoldGuard.lean, and to b's reading and word by `ArmBoundD.reread`
(Johnson/Top/ArmsReread.lean).

Under which hypotheses. Required of each check, in addition to its bound (bK, bP) at an error that
is at most b's (the names are those of `armsLeft_of_bounds`; the lemmas on one check call them hV,
hPc, hn, hy, hw):
  * r's check tosses no coin, and says yes, at every function, only where "the check's own reading,
    then the typed check at its value through its own coding at that value" says yes (hyK, hyP);
  * the word: at every function and key, the word through the check's coding at its own reading's
    value is b's word at b's reading's value (wK, wP); the left side does not hang on the key, so
    this also requires that b's word at b's reading's value is one at all keys;
  * for the proof's check: its relation is b's (it is stated at `b.Rno`);
  * b's reading tosses no coin at any key (hb), and the check's own reading tosses none (hPK, hPP);
  * each member of the typed family is a check in the sense of the bound's own file (hVT, hVB), and
    both families are at one wiring W.
Two of the four fields, that neither of r's two checks tosses a coin, are premises handed through.

What it does not show. The two bounds are premises. Their own premises, the key file's and the proof
file's soundness round by round among them, are proved in none of the files named above: what
`ArmsLeft b` requires moves to them and is not proved. r, b, the typed checks, the codings and the
readings are parameters; hyK, hyP, wK, wP are shown of no concrete check or coding here, and wK, wP
can be false. The weight lies in the two bounds, not in the carrying. An r whose checks refuse
everything meets hyK and hyP, and the fields then hold vacuously: they claim nothing there. At a
`b.Rno` that some witness meets at every index and instance the promise of `proofArm` holds always:
what `b.Rno` says is pinned by the hypothesis on the meaning alone, which is not touched here. wK
and wP are equations of words under a root, and by its definition such a word hangs on a log's leaf
and node entries alone: that the checks' codings spell a record's seed's queries alike is neither
required nor shown, and where they spell them apart the checks can hardly say yes together.
Soundness alone. All that the heads of ArmsFoldGuard.lean, ArmsReread.lean and FrontPaid.lean do not
claim.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFoldGuard
import Johnson.Top.ArmsReread
import Johnson.Top.FrontPaid

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles

variable {r : InputArmsC} {Bd : Type} {W : QueryLayout 256 (typedOracleCarrier r.L Bd r.aT r.aL)}

/-- The key file's check's bound at b, from the typed key's check's bound at its own reading and its
own coding. -/
theorem keyArm_at (b : BesideArmsCD r) (hb : ∀ k, (b.rd k).NoCoin) {DK : Type}
    {S : DK → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL} {cA : DK → r.L.OutOfDomainAnswer → List (Dig 256)}
    {V : DK → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d))
    (m : DK → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) DK}
    (hPc : Pub.NoCoin) (hn : ∀ c cm rc p, (r.armK c cm rc p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm rc p, (r.armK c cm rc p).det f = true →
      (armKOf V m Pub cm rc p).det f = true)
    (hw : ∀ (f : Fam (rom 256)) k tr cm,
      wordL m (Pub.det f) tr cm = b.wordOf ((b.rd k).det f) tr cm)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (bK : ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := r.X) V m Pub)
      (holdsTestOf (W := W) m) ε) (hε : ∀ tC tP, ε tC tP ≤ b.εK tC tP) :
    ZKCP.Gen.ArmBoundD b.rd (liftKC r) (KeyHoldsCD b) b.εK := by
  have c1 : ∀ k x π, (liftKC r k x π).NoCoin := fun k x π => by
    unfold liftKC
    split
    · exact hn _ _ _ _
    · trivial
  refine ZKCP.Gen.ArmBoundD.reread (fun _ => hPc) hb c1 c1 (fun _ _ _ _ h => h)
    (fun f k x π _ trC trP hH => ?_)
    (keyArmC_of_test hV m hPc hn hy b.q₀ b.Wn b.Rno b.εK b.εE b.εP b.x₀ bK hε)
  unfold KeyHoldsCD at hH ⊢
  simp only [hw f k] at hH
  exact hH

/-- The proof file's check's bound at b, from the typed proof's check's bound at its own reading and
its own coding. -/
theorem proofArm_at (b : BesideArmsCD r) (hb : ∀ k, (b.rd k).NoCoin) {DP : Type}
    {S : DP → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL} {cA : DP → r.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : r.L.Rec}
    {V : DP → OutBA 256 r.L → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d))
    (m : DP → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) DP}
    (hPc : Pub.NoCoin) (hn : ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm x rc n p, (r.armP c cm x rc n p).det f = true →
      (Pub.bind fun d => (V d (cm, x, rc, p)).overOne (m d)).det f = true)
    (hw : ∀ (f : Fam (rom 256)) k tr cm,
      wordL m (Pub.det f) tr cm = b.wordOf ((b.rd k).det f) tr cm)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (bP : ZKCP.Gen.ArmBoundD (fun _ : r.C × KeyRoot 256 r.L => Pub)
      (armSessOf (aT := r.aT) (aL := r.aL) V m Pub) (holdsSessOf (W := W) b.Rno m) ε)
    (hε : ∀ tC tP, ε tC tP ≤ b.εP tC tP) :
    ZKCP.Gen.ArmBoundD b.rd (liftPC r) (ProofHoldsCD b) b.εP := by
  have c3 : ∀ k x π, (liftPC r k x π).NoCoin := fun k x π => by
    unfold liftPC
    split
    · exact hn _ _ _ _ _ _
    · trivial
  refine ZKCP.Gen.ArmBoundD.reread (fun _ => hPc) hb c3 c3 (fun _ _ _ _ h => h)
    (fun f k x π _ trC trP hH => ?_)
    (proofArmC_of_sess hV m hPc hn hy b.q₀ b.Wn b.Rno b.εK b.εE b.εP b.x₀ bP hε)
  unfold ProofHoldsCD at hH ⊢
  simp only [hw f k] at hH
  exact hH

/-- **What is left of `CoreArmsCD b` beside the entry file's check, from the two typed checks'
bounds, each at its own reading and coding.** -/
theorem armsLeft_of_bounds (b : BesideArmsCD r) (hb : ∀ k, (b.rd k).NoCoin) {DK DP : Type}
    {ST : DK → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL} {cT : DK → r.L.OutOfDomainAnswer → List (Dig 256)}
    {VT : DK → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hVT : ∀ d, IsArmT W (ST d) (cT d) (VT d))
    (mT : DK → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {PubK : OComp (rom 256) DK}
    (hPK : PubK.NoCoin) (hnK : ∀ c cm rc p, (r.armK c cm rc p).NoCoin)
    (hyK : ∀ (f : Fam (rom 256)) c cm rc p, (r.armK c cm rc p).det f = true →
      (armKOf VT mT PubK cm rc p).det f = true)
    (wK : ∀ (f : Fam (rom 256)) k tr cm,
      wordL mT (PubK.det f) tr cm = b.wordOf ((b.rd k).det f) tr cm)
    {εk : ℕ → ℕ → ℝ≥0∞}
    (bK : ZKCP.Gen.ArmBoundD (fun _ => PubK) (armTestOf (X' := r.X) VT mT PubK)
      (holdsTestOf (W := W) mT) εk) (hεK : ∀ tC tP, εk tC tP ≤ b.εK tC tP)
    {SB : DP → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL} {cB : DP → r.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : r.L.Rec}
    {VB : DP → OutBA 256 r.L → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hVB : ∀ d, IsArmB W (SB d) (cB d) r₀ (VB d))
    (mB : DP → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {PubP : OComp (rom 256) DP}
    (hPP : PubP.NoCoin) (hnP : ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin)
    (hyP : ∀ (f : Fam (rom 256)) c cm x rc n p, (r.armP c cm x rc n p).det f = true →
      (PubP.bind fun d => (VB d (cm, x, rc, p)).overOne (mB d)).det f = true)
    (wP : ∀ (f : Fam (rom 256)) k tr cm,
      wordL mB (PubP.det f) tr cm = b.wordOf ((b.rd k).det f) tr cm)
    {εp : ℕ → ℕ → ℝ≥0∞}
    (bP : ZKCP.Gen.ArmBoundD (fun _ : r.C × KeyRoot 256 r.L => PubP)
      (armSessOf (aT := r.aT) (aL := r.aL) VB mB PubP) (holdsSessOf (W := W) b.Rno mB) εp)
    (hεP : ∀ tC tP, εp tC tP ≤ b.εP tC tP) : ArmsLeft b where
  keyArm := keyArm_at b hb hVT mT hPK hnK hyK wK bK hεK
  proofArm := proofArm_at b hb hVB mB hPP hnP hyP wP bP hεP
  noCoinK := hnK
  noCoinP := hnP

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyArm_at
#print axioms TypedOracleCompiler.Compile.Batch.Cms.proofArm_at
#print axioms TypedOracleCompiler.Compile.Batch.Cms.armsLeft_of_bounds
