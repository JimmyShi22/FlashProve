-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15M.lean: THE JOINING: ROW 1.15 OF THE KEY FILE's TABLES FROM PARTS OF THE YES OF THE KEY FILE's PIECE, ONE TEST ON THE DATA, ONE TEST ON THE PLAN, AND THE TWO PREMISES THAT HOLD THE WEIGHT. Statements with proofs: calls alone. IT PAYS NO FIELD OF THE TABLES: Gives15 HOLDS ALL THE WEIGHT AND IS SHOWN OF NOTHING. (Where this and lean/THEOREM.md differ, the page holds.)
OBJECT. `LPFD.The21`'s field r1_15. USER. The21's filler; Johnson/RunOne/Law/K12Facts15S.lean.
LETTERS. The35.lean's; on: the promise; file, the radii stageRad, rd, and m: what the planner makes of the public files.

  Le15: the law's errors lie below the maker's rest's at the 15th piece, however the stretch is written. A condition on the frame's letter rest₁.
  Gives15: the field "gives" of Left15JG (Johnson/RunOne/Law/K12Left15JG.lean), to the letter, at nl := nlAt (rangesParams N) 0, however the stretch is written. The stretch fixes dB and dt, so nothing is lost against the field; whoever has it at all dB dt has it here.
  left15JG_ex: a member of Left15JG at any promise, from: hX hN hp data (parts of the yes of Key.keyDataAndDecisionAtFixedDigest) · q₁ hl · hno (no round's data in front bears the batching's name) · joh · Le15 · Gives15. Of the structure's eleven facts EIGHT ARE NO PREMISE ANY MORE: stretch, behind, plan, arm, written, batOne, labels, bat. "free" stands as hno; data and joh as they were.
  r1_15_of_facts: the field, from the same, with Gives15 at OnH (Johnson/RunOne/Law/K12Left15H.lean): so it may spend "the state in front was reached".
Limits. As empty as Gives15. A NON-DEGENERATE INSTANCE IS NOT SHOWN. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Left15H
import Johnson.RunOne.Law.K12Facts15B

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open OnBytes.Slice (Sg)
open H2K.Pin (NTuple)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁)
open LPFD

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)
    (on : ℕ → (Xi × FirstState) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)


/-- The law's errors lie below the maker's rest's at the 15th piece. -/
abbrev Le15 (stageRad : _root_.Fmt.M1.Stage → ℕ) : Prop :=
  ∀ dB dt, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 = dB :: dt →
    Err.le ((batV0 (rangesParams N) stageRad * (bsRound .two dB.entry dB.kind).w, errJ (rangesParams N) stageRad dt) : Err (uLT (ckP .two) (dB :: dt))) (rest₁ 15 (dB :: dt)).err

/-- ALL THE WEIGHT: the field "gives", however the stretch is written. -/
abbrev Gives15 (stageRad : _root_.Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ) : Prop :=
  ∀ dB dt, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 = dB :: dt →
    ∀ a τ b, on 15 a →
    (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) (dB :: dt) [] (rest₁ 15 (dB :: dt))).ior.red.out a τ = some b →
    (∃ t t', enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t ∧
      (leaveRanges a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) (nlAt (rangesParams N) 0) t) (fun s => stageRad s.st) rd) (t, a.2)) →
    on 16 b ∧ ((Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 16 b → (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15 a)

variable {X N P DK c₁ k₁ rest₁ B at_ R coll on}

/-- **A member of Left15JG.** -/
theorem left15JG_ex (file : String) (stageRad : _root_.Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ) (m : Johnson.G.OfPlan.Made)
    (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a))
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hno : ∀ d ∈ (DK.at frS.P.T.a).ds₁.take (((c₁ :: k₁).take 15).flatMap (·.rounds)).length, (d.entry.name == "BAT") = false)
    (joh : johOk (rangesParams N) stageRad = true)
    (le : Le15 X N P DK c₁ k₁ rest₁ stageRad)
    (gives : Gives15 X N P DK c₁ k₁ rest₁ B at_ R on stageRad rd) :
    Nonempty (Left15JG X N P DK c₁ k₁ rest₁ B at_ R on) := by
  have plan := K12Facts15.plan_of X N P hp
  obtain ⟨w0, l, hw⟩ := K12Facts15.written_of_plan plan
  obtain ⟨dB, dt, hcut⟩ := List.exists_cons_of_ne_nil (K12Facts15.stretch_ne X N P c₁ k₁ file _ data hp q₁ hl)
  have hbe := K12Facts15.behind_ne X N P c₁ k₁ hp q₁ hl
  have hbeh : ((c₁ :: k₁).drop 16).flatMap (·.rounds) =
      (((c₁ :: k₁).drop 16).flatMap (·.rounds)).dropLast ++ [(((c₁ :: k₁).drop 16).flatMap (·.rounds)).getLast hbe] := by
    first
      | exact (List.dropLast_concat_getLast hbe).symm
      | exact (List.dropLast_append_getLast hbe).symm
  have hfree := K12Facts15.free_of c₁ k₁ file _ hX hN hp data q₁ hl hno
  have hbase := K12Facts15.base_15 X N P c₁ k₁ file _ data hp q₁ hl
  exact ⟨{
    file := file, dB := dB, dt := dt
    post := (((c₁ :: k₁).drop 16).flatMap (·.rounds)).dropLast
    r₀ := (((c₁ :: k₁).drop 16).flatMap (·.rounds)).getLast hbe
    writtenHead := w0, writtenTail := l, stageRad := stageRad
    batErr := batV0 (rangesParams N) stageRad * (bsRound .two dB.entry dB.kind).w
    nl := nlAt (rangesParams N) 0, rd := rd
    data := data, stretch := hcut, behind := hbeh, plan := plan
    arm := K12Facts15.arm_of hN plan, written := hw, free := hfree, joh := joh
    batOne := K12Facts15.batOne_of_plan plan
    labels := K12Facts15.labels_of hN plan _ _ _ (by omega)
    bat := Nat.le_refl _, le := le dB dt hcut, gives := gives dB dt hcut }⟩

variable (X N P DK c₁ k₁ rest₁ B at_ R coll)

/-- **THE FIELD r1_15 OF The21 AT THE KEY FILE's OWN DESCRIPTION.** -/
theorem r1_15_of_facts (file : String) (stageRad : _root_.Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ) (m : Johnson.G.OfPlan.Made)
    (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a))
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hno : ∀ d ∈ (DK.at frS.P.T.a).ds₁.take (((c₁ :: k₁).take 15).flatMap (·.rounds)).length, (d.entry.name == "BAT") = false)
    (joh : johOk (rangesParams N) stageRad = true)
    (le : Le15 X N P DK c₁ k₁ rest₁ stageRad)
    (gives : Gives15 X N P DK c₁ k₁ rest₁ B at_ R (OnH X N P DK B at_ R coll) stageRad rd) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 := by
  obtain ⟨H⟩ := left15JG_ex file stageRad rd m hX hN hp data q₁ hl hno joh le gives
  exact r1_15_atH X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll q₁ hl H

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.left15JG_ex
#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_of_facts
