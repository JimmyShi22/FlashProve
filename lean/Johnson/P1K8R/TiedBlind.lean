-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/TiedBlind.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE KIND K8's SHARE OF THE
CHAIN OF PROMISES, WITH THREE OF THE SIX TIES PAID DOWN TO ONE STRUCTURE ON THE FILLING. JOININGS
over Johnson/P1K8R/Tied.lean (k08_tied · k08_kindTied) and Johnson/Desc/First/K8/TieRides.lean
(k08_seatLaws_blind).
WHAT IS SAID.
  k8StepB_full · k8_step_full     by Lean's kernel (decide +kernel): in the written list of places of the full size, at each number ixOf l, l ≤ 24: there is a place pK, of the kind K8, and a next place pN; the table's row at pK is quiet (it closes and opens no class of rows and no pin with a sample); pN lies in the same link; the chain is to stand at pN as at pK; no count of rows may wait at pK. THESE ARE THE SIX FACTS ON THE LIST OF PLACES THAT k08_t2 TAKES.
  k08_kindTied_blind              KindTied … K8 UNDER: scope · an opening's letters · OfDesc · the extractor lays nothing at the 25 numbers · AND AT EACH OF THE 25: the kind's law hG (GoodIn at four letters) · the ties t1, t3, t4 · DrawBlind (what the filling owes for the draw).
LIMITS. hG, t1, t3, t4 AND DrawBlind ARE PREMISES, SHOWN AT NO FILLING. Those of Tied.lean. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.Tied
import Johnson.Desc.First.K8.TieRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P1K8T

open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run.PQ (CK)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf rowOf quietRow standAt
  mayWait)
open VerifiableInference.Desc.First.K8 (DrawBlind whole approximateRangeProofDrawKind atS k08_seatLaws_blind)
open ProofFile (Cl)

/-- The test at one number. -/
def k8StepAt (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]?, ps[k + 1]? with
  | some pK, some pN =>
    pK.kind == KindName.K8 && quietRow (rowOf links pK) && decide (pN.link = pK.link) &&
      decide (standAt links pN = standAt links pK) && !mayWait links pK
  | _, _ => false

set_option maxRecDepth 1000000 in
theorem k8StepB_full :
    ((List.range 25).all fun l => k8StepAt linksFull (flatPlacesOf linksFull true) (ixOf l)) =
      true := by decide +kernel

/-- **The six facts on the list of places, at each of the 25 numbers.** -/
theorem k8_step_full {l : ℕ} (hl : l ≤ 24) :
    ∃ pK pN, (flatPlacesOf linksFull true)[ixOf l]? = some pK ∧
      (flatPlacesOf linksFull true)[ixOf l + 1]? = some pN ∧
      quietRow (rowOf linksFull pK) = true ∧ pN.link = pK.link ∧
      standAt linksFull pN = standAt linksFull pK ∧ mayWait linksFull pK = false := by
  have h := List.all_eq_true.1 k8StepB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold k8StepAt at h
  cases hK : (flatPlacesOf linksFull true)[ixOf l]? with
  | none => simp [hK] at h
  | some pK =>
    cases hN : (flatPlacesOf linksFull true)[ixOf l + 1]? with
    | none => simp [hK, hN] at h
    | some pN =>
      simp only [hK, hN, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
      exact ⟨pK, pN, rfl, rfl, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **THE KIND K8's SHARE OF THE CHAIN OF PROMISES, three ties paid down to the filling's debt.** -/
theorem k08_kindTied_blind {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ l, l ≤ 24 → ∀ a b w, E (ixOf l) a b w = w)
    (o oB : ℕ → S × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (R R' : ℕ → S × (frameAt D all D.key₁ T.ft₁).E.Str → W → Prop)
    (o' : ℕ → ProofFile.InstPub → S → Strs → Prop)
    (hoB : ∀ l z b, oB l b → o' l z b.1 (strsOf (frameAt D all D.key₁ T.ft₁) b.2))
    (H : ∀ l Xl q, l ≤ 24 → Bs.G₀.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      DrawBlind N Mg linksFull (flatPlacesOf linksFull true) (ixOf l) q.base (o' l) ∧
      (∀ B' : Block S Claim, B'.Narrows (whole (ProofFile.k8ParW Z Bs.G₀ Xl l)) →
        (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
          Piece C (frameAt D all D.key₁ T.ft₁) S Claim W).GoodIn (o l) (oB l) (R l) (R' l)) ∧
      (∀ (z : ProofFile.InstPub) a, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
        (ixOf l) a → ¬ a.1.failed ≠ none → o l a) ∧
      (∀ (z : ProofFile.InstPub) a b w, onQ N Mg linksFull (flatPlacesOf linksFull true)
          (fun s => (z, s)) (ixOf l) a → ¬ a.1.failed ≠ none →
        (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar).decide a.1 rs gs =
          .ok b.1) →
        (∃ τ : Iop.Tr (uLT C q.ds),
          b.2 = behind C (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
        oB l b → relAt (meansQ N Mg fun s => (z, s))
          (outsQ linksFull (flatPlacesOf linksFull true) (ixOf l)) b w → R' l b w) ∧
      (∀ (z : ProofFile.InstPub) a b w, onQ N Mg linksFull (flatPlacesOf linksFull true)
          (fun s => (z, s)) (ixOf l) a → ¬ a.1.failed ≠ none →
        (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar).decide a.1 rs gs =
          .ok b.1) →
        (∃ τ : Iop.Tr (uLT C q.ds),
          b.2 = behind C (frameAt D all D.key₁ T.ft₁) q.base q.ds a.2 τ) →
        oB l b → relAt (meansQ N Mg fun s => (z, s))
          (outsQ linksFull (flatPlacesOf linksFull true) (ixOf l)) b w → R l a w →
        relAt (meansQ N Mg fun s => (z, s))
          (insQ linksFull (flatPlacesOf linksFull true) (ixOf l)) a w)) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K8 := by
  refine k08_kindTied hS hR O hT N Mg E hE fun l Xl q hl hX hq => ?_
  obtain ⟨hD, hG, t1, t3, t4⟩ := H l Xl q hl hX hq
  obtain ⟨pK, pN, eK, eN, hqr, hlk, hst, hmw⟩ := k8_step_full hl
  exact k08_seatLaws_blind q (ProofFile.k8ParW Z Bs.G₀ Xl l) (o l) (R l) (R' l) (oB l) (hoB l) hD pK pN eK
    eN hqr hlk hst hmw hG t1 t3 t4

end P1K8T

#print axioms P1K8T.k8StepB_full
#print axioms P1K8T.k8_step_full
#print axioms P1K8T.k08_kindTied_blind
