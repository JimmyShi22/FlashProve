-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/TiedEach.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE KIND K8's SHARE OF THE
CHAIN OF PROMISES, THE LAW's FOUR LETTERS TAKEN OFF THE STATEMENT IN FRONT. A JOINING over
Johnson/P1K8R/TiedBlind.lean (k8_step_full), Johnson/P1K8R/Tied.lean (k08_kindTied) and
Johnson/Desc/First/K8/TieEach.lean (k08_seatLaws_each_blind).
WHAT IS SAID.
  K8Owes …          what is owed at one of the 25 places, as one structure: DrawBlind · «the kind's condition behind gives DrawBlind's» · the kind's law hG at every (z, a₀) · the ties t1, t3, t4 at a := a₀; THE FOURTH ENDS IN WHAT THE ROW CLOSES ALONE (constr m small · tie m): what it reads (pin m 0 · pin m 1) comes back from behind by DrawBlind's field reads, and «no mark» stands in front (k08_ins_of_closed).
  k08_kindTied_each KindTied … K8 UNDER: scope · an opening's letters · OfDesc · the extractor lays nothing at the 25 numbers · K8Owes at each of the 25.
LIMITS. K8Owes IS SHOWN AT NO FILLING. Those of Tied.lean. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.TiedBlind
import Johnson.Desc.First.K8.TieEach

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
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K8 (DrawBlind ParW whole approximateRangeProofDrawKind atS k08_seatLaws_each_blind
  k08_ins_of_closed)
open ProofFile (Cl)

/-- **What is owed at one place of the kind.** -/
structure K8Owes {Pp W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (k : ℕ) (q : Piece C Fr (Pp × S) Claim W) (p : ParW) :
    Prop where
  letters : ∃ (o o' : Pp → S × Fr.E.Str → S × Fr.E.Str → Prop)
      (R R' : Pp → S × Fr.E.Str → S × Fr.E.Str → W → Prop) (oS : Pp → S → Strs → Prop),
    (∀ z a b, o' z a b → oS z b.1 (strsOf Fr b.2)) ∧
    DrawBlind N Mg links ps k q.base oS ∧
    (∀ (z : Pp) (a₀ : S × Fr.E.Str), onQ N Mg links ps (fun s => (z, s)) k a₀ →
      ¬ a₀.1.failed ≠ none → ∀ B' : Block S Claim, B'.Narrows (whole p) →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W).GoodIn
        (o z a₀) (o' z a₀) (R z a₀) (R' z a₀)) ∧
    (∀ (z : Pp) (a : S × Fr.E.Str), onQ N Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → o z a a) ∧
    (∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R' z a b w) ∧
    (∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R z a a w →
      ∀ i ∈ (rowQ links ps k).ins, meansQ N Mg (fun s => (z, s)) i a w)

/-- **THE KIND K8's SHARE OF THE CHAIN OF PROMISES, the law's letters off the statement in front.** -/
theorem k08_kindTied_each {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
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
    (H : ∀ l Xl q, l ≤ 24 → Bs.G₀.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      K8Owes N Mg linksFull (flatPlacesOf linksFull true) (ixOf l) q (ProofFile.k8ParW Z Bs.G₀ Xl l)) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K8 := by
  refine k08_kindTied hS hR O hT N Mg E hE fun l Xl q hl hX hq => ?_
  obtain ⟨o, o', R, R', oS, hoS, hD, hG, t1, t3, t4⟩ := (H l Xl q hl hX hq).letters
  obtain ⟨pK, pN, eK, eN, hqr, hlk, hst, hmw⟩ := k8_step_full hl
  exact k08_seatLaws_each_blind q (ProofFile.k8ParW Z Bs.G₀ Xl l) o o' R R' oS hoS hD pK pN eK eN hqr hlk
    hst hmw hG t1 t3 fun z a b w ha hm hy hb ho hw hr =>
      k08_ins_of_closed hD (ProofFile.k8ParW Z Bs.G₀ Xl l) q.ds z a b w hm hy hb hw
        (t4 z a b w ha hm hy hb ho hw hr)

end P1K8T

#print axioms P1K8T.k08_kindTied_each
