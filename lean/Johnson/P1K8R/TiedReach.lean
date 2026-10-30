-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/TiedReach.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS, AT THE PROOF FILE's
DESCRIPTION, IN THE FORM WITH A CONDITION THAT EVERY ACCEPTING STEP HANDS ON (TiedAtR,
Johnson/Desc/Sound/ChainOfPromisesR.lean). JOININGS over TiedBlind.lean (k8_step_full),
Tied.lean (ixOf · built_at · k8_places_full) and Johnson/Desc/First/K8/TieReach.lean
(k08_seatR).
WHAT IS SAID.
  k08_seated       in scope, at an opening's letters, at each l ≤ 24: the piece at number ixOf l of the first row of pieces that hold the description's sub-protocols (OfDesc) holds, beneath the lift over the public part, the strict reading of a sub-protocol b that narrows K8.whole (k8ParW Z G₀ Xl l).
  K8OwesR          WHAT IS OWED AT ONE PLACE OF THE KIND, as one structure: K8Owes (TiedEach.lean) with ONE PREMISE MORE in the kind's law hG and in the ties t1, t3, t4: Rch k ((z, a.1), a.2), right behind the promise in front. DrawBlind is as it was. THE CLAUSE «the kind's condition behind gives oS» HAS THE PROMISE IN FRONT, Rch, «no mark» AND THE DRAW's OWN YES IN HAND: oS is what the draw must MAKE behind itself: the public test that the table ties to the run of forms «small», which the draw's row opens: no blindness.
  KindTiedR'       one kind's share of the chain of promises in the form with Rch: KindTied (Johnson/Desc/Sound/TiedPlaces.lean) with TiedAtR for TiedAt. A NAME OF THIS FILE's.
  k08_kindTiedR    KindTiedR' … K8 UNDER: scope · an opening's letters · OfDesc · the extractor lays nothing at the 25 numbers · K8OwesR at each of the 25.
LIMITS. Rch IS A LETTER: whoever calls the chain's rule owes Rch 0 at the start and the hand-on at every sub-protocol. K8OwesR IS SHOWN AT NO FILLING. Those of Tied.lean. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.TiedBlind
import Johnson.Desc.First.K8.TieReach

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
open VerifiableInference.Desc.First.K8 (DrawBlind ParW whole approximateRangeProofDrawKind atS k08_seatR)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ W : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ W}

/-- One place, general in the lot's sub-protocol. -/
theorem seated_at (hT : OfDesc _ T) {l i k : ℕ} {Lk : Link S Cl} {b B₀ : Block S Cl}
    {name : String} {a : Place} (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (ef : IM.flatIx c l i = k) (hla : IM.LaidAlone ProofFile.sameReply b B₀ name a)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) :
    ∃ b : Block S Cl, b.Narrows B₀ ∧ q.b = (below b).lift Prod.snd fun t s => (t.1, s) := by
  have h3 := IM.hear_at_flat e1 e2
  rw [ef] at h3
  exact ⟨b, IM.alone_underR hla, OfDesc.pieceAt hT hq h3⟩

/-- **What the piece at each of the 25 numbers holds.** -/
theorem k08_seated (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    {l : ℕ} (hl : l ≤ 24) {Xl : LinkH} (hX : Bs.G₀.built[l]? = some Xl)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[ixOf l]? = some q) :
    ∃ b : Block S Cl, b.Narrows (whole (ProofFile.k8ParW Z Bs.G₀ Xl l)) ∧
      q.b = (below b).lift Prod.snd fun t s => (t.1, s) := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, b, Xl', e1, e2, e3, hla, _⟩ := IM.k8_of_head hS hR O
    obtain rfl : Xl' = Xl := Option.some.inj (e3.symm.trans hX)
    exact seated_at hT e1 e2 (IM.flatIx_scope hS hR O (by decide) 5) hla hq
  · have ei : ixOf l = 14 * l + 4 + 2 := by
      unfold ixOf
      rw [if_neg h24]
    rw [ei] at hq
    by_cases he : l % 2 = 0
    · obtain ⟨Lk, b, Xl', _, e1, e2, e3, hla, _⟩ := IM.k8_of_layers hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) = l by omega] at e1 e3 hla
      obtain rfl : Xl' = Xl := Option.some.inj (e3.symm.trans hX)
      exact seated_at hT e1 e2 (IM.flatIx_scope hS hR O hl 4) hla hq
    · obtain ⟨Lk, b, Xl', _, e1, e2, e3, hla, _⟩ := IM.k8_of_attention hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) + 1 = l by omega] at e1 e3 hla
      obtain rfl : Xl' = Xl := Option.some.inj (e3.symm.trans hX)
      exact seated_at hT e1 e2 (IM.flatIx_scope hS hR O hl 4) hla hq

end

/-- **What is owed at one place of the kind, with Rch in hand.** -/
structure K8OwesR {Pp W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (k : ℕ)
    (q : Piece C Fr (Pp × S) Claim W) (p : ParW) : Prop where
  letters : ∃ (o o' : Pp → S × Fr.E.Str → S × Fr.E.Str → Prop)
      (R R' : Pp → S × Fr.E.Str → S × Fr.E.Str → W → Prop) (oS : Pp → S → Strs → Prop),
    (∀ (z : Pp) (a b : S × Fr.E.Str), onQ N Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      o' z a b → oS z b.1 (strsOf Fr b.2)) ∧
    DrawBlind N Mg links ps k q.base oS ∧
    (∀ (z : Pp) (a₀ : S × Fr.E.Str), onQ N Mg links ps (fun s => (z, s)) k a₀ →
      Rch k ((z, a₀.1), a₀.2) → ¬ a₀.1.failed ≠ none →
      ∀ B' : Block S Claim, B'.Narrows (whole p) →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W).GoodIn
        (o z a₀) (o' z a₀) (R z a₀) (R' z a₀)) ∧
    (∀ (z : Pp) (a : S × Fr.E.Str), onQ N Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → o z a a) ∧
    (∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R' z a b w) ∧
    (∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ N Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R z a a w →
      ∀ i ∈ (rowQ links ps k).ins, meansQ N Mg (fun s => (z, s)) i a w)

/-- One kind's share of the chain of promises, in the form with Rch. -/
def KindTiedR' {Pp Cl' W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (E : ℕ → (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W)
    (l : List (Piece C Fr (Pp × S) Cl' W)) (K : KindName) : Prop :=
  ∀ i q a, l[i]? = some q → ps[i]? = some a → a.kind = K →
    TiedAtR N Mg links ps (fun a => a) Rch i (q.withMap (E i))

/-- **THE KIND K8's SHARE OF THE CHAIN OF PROMISES, IN THE FORM WITH Rch.** -/
theorem k08_kindTiedR {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ l, l ≤ 24 → ∀ a b w, E (ixOf l) a b w = w)
    (H : ∀ l Xl q, l ≤ 24 → Bs.G₀.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      K8OwesR N Mg linksFull (flatPlacesOf linksFull true) Rch (ixOf l) q
        (ProofFile.k8ParW Z Bs.G₀ Xl l)) :
    KindTiedR' N Mg linksFull (flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁) KindName.K8 := by
  intro i q a hq ha hk
  obtain ⟨l, hl, rfl⟩ := k8_places_full i a ha hk
  obtain ⟨Xl, hX⟩ := built_at hS hR O hl
  obtain ⟨b, hb, hqb⟩ := k08_seated hS hR O hT hl hX hq
  obtain ⟨o, o', R, R', oS, hoS, hD, hG, t1, t3, t4⟩ := (H l Xl q hl hX hq).letters
  obtain ⟨pK, pN, eK, eN, hqr, hlk, hst, hmw⟩ := k8_step_full hl
  exact k08_seatR q (ProofFile.k8ParW Z Bs.G₀ Xl l) b hb hqb Rch (E _) (hE l hl) o o' R R' oS hoS hD pK pN
    eK eN hqr hlk hst hmw hG t1 t3 t4

end P1K8T

#print axioms P1K8T.k08_seated
#print axioms P1K8T.k08_kindTiedR
