-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/PremisesAtWiring.lean: those premises of `OnBytes.WholeKey.PremW`
(Johnson/WholeKey/Premises.lean) that speak of the verifiers, the marks or the wires alone, at the
three files' protocols of the full size (`threeProtocolsAtFullSize`) and their wiring (`wireOfFullD`,
Johnson/Flat/Dec/WiresAtSizes.lean). No prover, no coin and no simulator is read.

What is shown, at ANY claims, rounds' data DK, DP, ds, openings xs, three decisions, provers P,
number K of blocks for a verifier message and depth of the key file's request tree.
  `free_fullD`: `ReadsFree`, three times: the positions that a verifier reads are the same at two
    transcripts that are alike but for nonces. From E2E/ReadsBlindAtWiring.lean.
  `fmt_fullD`: every round of the three protocols has a format (`RoundSplits.Fmt`).
  `coherent_fullD`, `local_fullD`: the marks fit together; the verifiers read at the declared
    positions alone. The library's theorems, in the form in which `PremW` asks them.
  `BackFree`, `noncesBack_of_free`, `backFree_app`, `back_Dn`, `backFree_wiresLo`,
    `backFree_wiresSh`, `backFree_wiresSL`, `backFree_wqWhole`, `backFree_wqW`; `back_fullD`:
    `NoncesBack`, three times, AT ALL CAPS: at these wires a nonce is its number, so every number is
    read back from the plain part into which it was written.
  `oka_fullD`: the wires' laws and the law of the answers' code (`OKA`), from the library's one test
    on numbers (`FrameFitFullD`, Johnson/Flat/Dec/FailsClosed.lean).
  `nonceOf_plainFirst`: the plain part `plainFirst` (OnBytes/TypedOracleCompiler/Run/SeedVals.lean) stands for the
    number 0 under a wire whose first round has no test for one request's component.

Limits.
  * Nothing here says that `PremW` holds of anything: its premises on provers, coins and simulators
    are not touched, and neither are its premises on reads, OOD seeds and budgets
    (E2E/PremisesAtFiles.lean).
  * The statements hold at every data: no public file, no scope and no gate occurs in them.
  * `back_fullD` is about natural numbers. In a file a nonce has eight bytes; nothing here bounds a
    cap.
  * Johnson/WholeKey/Premises.lean states no goal, and its own head says that it proves nothing.


-/
import Johnson.WholeKey.Premises
import E2E.ReadsBlindAtWiring
import OnBytes.Maker.WholeLaws
import Compile.Joined.Ann
import Johnson.EntryRec.AtMakerA
import Johnson.Flat.Dec.FailsClosed
import Johnson.Flat.ArmSibAt
import Johnson.RunOne.StrictLinkW

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Premises
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Reads
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS frZ)
open _root_.Run.PQ (CK View XO Dn)
open _root_.Run (ckP chalP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize wireOfFullD)
open TypedOracleCompiler.Compile.Batch.Cms (batTC batLC wTC wLC wBC OKA)

section
variable {lam K : ℕ}

/-! ## 1. Every number is read back -/

/-- In every round, whatever test data the wire holds read back every number from the plain part
into which it was written: no cap, no round number. -/
def BackFree : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) =>
      (∀ g, w.grJ = some g → ∀ k α, g.get (g.put k α) = k) ∧
        (∀ g, w.gr0 = some g → ∀ k α, g.get (g.put k α) = k) ∧ BackFree s A W

/-- So each number up to a cap is read back, whatever the cap and the round's number. -/
theorem noncesBack_of_free : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    BackFree s A W → ∀ (cap : ℕ → ℕ) (i : ℕ), NoncesBack s A W cap i
  | [], _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), h, cap, i => by
    refine ⟨?_, noncesBack_of_free s A W h.2.2 cap (i + 1)⟩
    cases a.kind with
    | lo => exact fun g hg k α _ => h.1 g hg k α
    | sh => exact fun g hg k α _ => h.2.1 g hg k α

/-- Two wires in a row. -/
theorem backFree_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B}, BackFree s A W → BackFree u B V →
      BackFree (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, hW.2.1, backFree_app hW.2.2 hV⟩

/-- The written test data read every number back: a nonce is its number. -/
theorem back_Dn {Cc P : Type} : ∀ (b : ℕ) (g : GrW (GChal b Cc) (GPlain ℕ b P)),
    (_root_.Iop.grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr = some g →
      ∀ k α, g.get (g.put k α) = k
  | 0, _, h => by cases h
  | b + 1, g, h => by
    obtain rfl : TypedOracleCompiler.Tagged.ofGr (_root_.Iop.GrW.ofBits Dn b Cc P) = g := Option.some.inj h
    intro k α
    rfl

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- A file's chain of local rounds. -/
theorem backFree_wiresLo : ∀ ds : List RDT, BackFree _ _ (wiresLo C K chal ds)
  | [] => trivial
  | _ :: ds => ⟨fun g hg => back_Dn _ g hg, (fun _ hg => by cases hg), backFree_wiresLo ds⟩

/-- A file's chain of shared rounds. -/
theorem backFree_wiresSh : ∀ ds : List RDT, BackFree _ _ (wiresSh C K chal ds)
  | [] => trivial
  | _ :: ds => ⟨(fun _ hg => by cases hg), fun g hg => back_Dn _ g hg, backFree_wiresSh ds⟩

/-- The rounds of the written link. -/
theorem backFree_wiresSL : ∀ ds : List TypedOracleCompiler.Run.PQ.RD,
    BackFree _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds)
  | [] => trivial
  | _ :: ds => ⟨fun g hg => back_Dn _ g hg, (fun _ hg => by cases hg), backFree_wiresSL ds⟩

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- The wire of a whole written file: the front round, the joining round and the seam have no
test. -/
theorem backFree_wqWhole : BackFree _ _ (wqWhole C K chal D tF tJ t3 silent run).sh :=
  ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg),
    backFree_app (backFree_wiresLo C K chal D.ds₁)
      ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg),
        backFree_app (backFree_wiresSh C K chal D.ds₂)
          ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg), backFree_wiresLo C K chal D.ds₃⟩⟩⟩

variable (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
  (dec : Y → View → Bool)

/-- The wire of the written link: the round in front has no test. -/
theorem backFree_wqW : BackFree _ _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh :=
  ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg), backFree_wiresSL C K chal ds⟩

end

/-! ## 2. An OOD seed's plain part -/

/-- `plainFirst` stands for the number 0 under a wire whose first round has no test for one
request's component. -/
theorem nonceOf_plainFirst (r : Round) (s : Shape) (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (h : w.grJ = none) :
    nonceOf (r :: s) (a, A) (w, W) (TypedOracleCompiler.Run.SeedVals.plainFirst r s a A) = 0 := by
  show (match w.grJ with
    | none => 0
    | some g => g.get (a.plain r.dPlain).2) = 0
  rw [h]

end

/-! ## 3. At the wiring of the full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → View → View → View → Bool) (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

/-- The three files' protocols. -/
local notation "Ff" => threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt

/-- The object. -/
local notation "Lo" => OnBytes.Flat.Files.withProvers Ff P

/-- The wiring. -/
local notation "Ww" =>
  wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

/- The statements name these letters through the notations alone. -/
include A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

/-- **The positions that the three verifiers read do not hang on nonces.** More holds: they hang on
no plain part at all, so the premise that two transcripts are alike but for nonces is not used. -/
theorem free_fullD :
    ReadsFree (batTC Lo (Ff).annT) (wTC Ww).sh ∧ ReadsFree (batLC Lo (Ff).annL) (wLC Ww).sh ∧
      ReadsFree (Lo).onlineBatch (wBC Ww).sh :=
  have h := blind_wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT
  ⟨fun x τ τ' _ => h.1.plains x τ.rho τ'.plains τ.plains,
    fun x τ τ' _ => h.2.1.plains x τ.rho τ'.plains τ.plains,
    fun x τ τ' _ => h.2.2.plains x τ.rho τ'.plains τ.plains⟩

omit K depthReqT in
/-- **Every round of the three protocols has a format.** -/
theorem fmt_fullD : (Ff).annT.Fmt ∧ (Ff).annL.Fmt ∧ (Lo).onlineBatch.ann.Fmt := by
  refine ⟨?_, ?_, ?_⟩
  · show (chainsOf (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
      ByteArray.empty).ann.Fmt
    exact Compile.Joined.Chains.ann_fmt _ (chainsOf_laws _ _ _ _ _)
  · show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) ds)).Fmt
    rw [_root_.Run.Twin.allLo_eq]
    exact RoundSplits.fmt_allLocal _
  · show (chainsOf (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP) (OnBytes.Flat.join₀ rP)
      ByteArray.empty).ann.Fmt
    exact Compile.Joined.Chains.ann_fmt _ (chainsOf_laws _ _ _ _ _)

omit K depthReqT in
/-- The marks fit together: the library's theorems. -/
theorem coherent_fullD : (Ff).annT.Coherent ∧ (Ff).annL.Coherent ∧ (Lo).onlineBatch.ann.Coherent :=
  ⟨(VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_coherent A R DK DP runK runP ds xs dec rK rP depthReq
      early salt).1,
    VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_entryCoherent A R DK DP runK runP ds xs dec rK rP
      depthReq early salt,
    (VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_coherent A R DK DP runK runP ds xs dec rK rP depthReq
      early salt).2⟩

omit K depthReqT in
/-- The verifiers read at the declared positions alone: the library's theorem. -/
theorem local_fullD : (Lo).offline.IsLocal ∧ (Lo).link.IsLocal ∧ (Lo).onlineBatch.loc.IsLocal :=
  VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_local A R DK DP runK runP ds xs dec rK rP depthReq early
    salt

/-- **Every number is read back, at all caps.** -/
theorem back_fullD (capT capL capB : ℕ → ℕ) :
    NoncesBack (Lo).offline.shape (Ff).annT (wTC Ww).sh capT 0 ∧
      NoncesBack (Lo).link.shape (Ff).annL (wLC Ww).sh capL 0 ∧
      NoncesBack (Lo).onlineBatch.loc.shape (Lo).onlineBatch.ann (wBC Ww).sh capB 0 :=
  ⟨noncesBack_of_free _ _ _
      (backFree_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
        (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK) capT 0,
    noncesBack_of_free _ _ _ (backFree_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec) capL 0,
    noncesBack_of_free _ _ _
      (backFree_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
        (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP) capB 0⟩

/-- **The wires' laws and the law of the answers' code**, from the library's one test on numbers. -/
theorem oka_fullD {v : ℕ}
    (f : VerifiableInference.OnPublicFiles.FrameFitFullD K v depthReq depthReqT DK DP ds xs) :
    OKA Ww (OnBytes.Flat.codeA (v := frS.P.v) (s := 1)) :=
  TypedOracleCompiler.Compile.Batch.Cms.oka_of_four
    (VerifiableInference.OnPublicFiles.wiresOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early
      salt P K depthReqT f.hk f.hE.bL f.hE.wLk f.hE.own f.hE.dL f.wK f.dK f.wP f.dP)
    ⟨OnBytes.Flat.codeA_inj,
      fun a a' => (OnBytes.Flat.codeA_length a).trans (OnBytes.Flat.codeA_length a').symm⟩

end

end AtPublicFiles.Premises

#print axioms AtPublicFiles.Premises.noncesBack_of_free
#print axioms AtPublicFiles.Premises.backFree_app
#print axioms AtPublicFiles.Premises.back_Dn
#print axioms AtPublicFiles.Premises.backFree_wiresLo
#print axioms AtPublicFiles.Premises.backFree_wiresSh
#print axioms AtPublicFiles.Premises.backFree_wiresSL
#print axioms AtPublicFiles.Premises.backFree_wqWhole
#print axioms AtPublicFiles.Premises.backFree_wqW
#print axioms AtPublicFiles.Premises.nonceOf_plainFirst
#print axioms AtPublicFiles.Premises.free_fullD
#print axioms AtPublicFiles.Premises.fmt_fullD
#print axioms AtPublicFiles.Premises.coherent_fullD
#print axioms AtPublicFiles.Premises.local_fullD
#print axioms AtPublicFiles.Premises.back_fullD
#print axioms AtPublicFiles.Premises.oka_fullD
