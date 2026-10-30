-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/TieReach.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS, IN THE FORM WITH A
CONDITION THAT EVERY ACCEPTING STEP HANDS ON (`TiedAtR`, Johnson/Desc/Sound/ChainOfPromisesR.lean):
each tie has one premise more: Rch k at the statement in front. Rch is a letter: a family of
conditions, a border a member ("this state of the verifier is reached from the start" is the
instance that is meant).

  The two rules that are general in the kind, `goodInR_of_each` and `tiedAtR_of_seat`, stand in
  Johnson/Top/H0/TiedAtSeatR.lean.
  `k08_seatR`: **`TiedAtR` for the smallness test's piece**, at a sub-protocol that narrows
    `whole p`, from: the kind's law hG at every (z, a₀) with the promise, Rch and "no mark"; the
    ties t1, t3, t4 at a := a₀, each with Rch in hand, the fourth ending in what the row CLOSES;
    `DrawBlind` (Johnson/Desc/First/K8/TieRides.lean), which pays the promise behind, what rides,
    what the row reads, and "decodes"; and hoS: WHAT THE DRAW MUST MAKE BEHIND ITSELF (oS: the
    letter that `DrawBlind`'s fields on the public items take): from the kind's condition behind,
    with the promise in front, Rch, "no mark" and the draw's own yes in hand. IT IS NO BLINDNESS:
    the row opens the forms of the run "small", and the table ties a public test to an open run of
    forms, which is the opener's to make (`pubOfItems`, `tiedNew`, Johnson/Desc/First/Borders.lean).
Limits. A RULE OVER LETTERS: at Rch := never every tie is free and nothing is said: whoever calls
the chain's rule owes Rch 0 at the start and the hand-on at every sub-protocol: neither is shown
here. SHOWN AT NO FILLING. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.K8.TieEach
import Johnson.Top.H0.TiedAtSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.K8
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Place Claim Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start rowOf quietRow standAt
  mayWait)

section
variable {Pp W : Type} {C : CK} {Fr : Frame}

/-- **The smallness test's piece is tied in the form with Rch**, at a sub-protocol B that narrows
`whole p`. -/
theorem k08_seatR {links : List ModelPart} {ps : List Place} {k : ℕ} {Nn : Numbers} {Mg : Meaning Pp W}
    (q : Piece C Fr (Pp × S) Claim W) (p : ParW) (B : Block S Claim) (hB : B.Narrows (whole p))
    (hqb : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (E : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (o o' : Pp → S × Fr.E.Str → S × Fr.E.Str → Prop)
    (R R' : Pp → S × Fr.E.Str → S × Fr.E.Str → W → Prop) (oS : Pp → S → Strs → Prop)
    (hoS : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      o' z a b → oS z b.1 (strsOf Fr b.2))
    (D : DrawBlind Nn Mg links ps k q.base oS) (pK pN : Place)
    (hK : ps[k]? = some pK) (hN : ps[k + 1]? = some pN) (hq : quietRow (rowOf links pK) = true)
    (hl : pN.link = pK.link) (hs : standAt links pN = standAt links pK)
    (hw : mayWait links pK = false)
    (hG : ∀ (z : Pp) (a₀ : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a₀ →
      Rch k ((z, a₀.1), a₀.2) → ¬ a₀.1.failed ≠ none →
      ∀ B' : Block S Claim, B'.Narrows (whole p) →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W).GoodIn
        (o z a₀) (o' z a₀) (R z a₀) (R' z a₀))
    (t1 : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → o z a a)
    (t3 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R' z a b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R z a a w →
      ∀ i ∈ (rowQ links ps k).ins, meansQ Nn Mg (fun s => (z, s)) i a w) :
    TiedAtR Nn Mg links ps (fun a => a) Rch k (q.withMap E) := by
  have hy : ∀ (a b : S × Fr.E.Str) (τ : Iop.Tr (uLT C q.ds)),
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Claim W).ior.red.out a τ = some b →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) ∧
        (∃ τ' : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ') ∧
        b.1.failed = a.1.failed := by
    intro a b τ h
    exact ⟨whole_yes p (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Claim W) B hB rfl a b τ h,
      ⟨τ, out_behind (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Claim W) a b τ h⟩,
      whole_mark p (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Claim W) B hB rfl a b τ h⟩
  have hMark : ∀ a τ b,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Claim W).ior.red.out a τ = some b → a.1.failed ≠ none →
      b.1.failed ≠ none := by
    intro a τ b h hm
    rw [(hy a b τ h).2.2]
    exact hm
  have hDec : ∀ (z : Pp) a τ b,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Claim W).ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2) := fun z a τ b h hd =>
    k08_hD D p q.ds z a b (hy a b τ h).1 (hy a b τ h).2.1 hd
  refine tiedAtR_of_seat links ps k B q hqb Nn Mg Rch E hE (fun z => ?_) ?_ hMark hDec
  · refine goodInR_of_each Nn Mg links ps z k (fun a => Rch k ((z, a.1), a.2)) _
      (fun _ _ _ => rfl) ?_ hMark (hDec z)
    intro a₀ ha hr hm
    refine ⟨o z a₀, o' z a₀, R z a₀, R' z a₀, hG z a₀ ha hr hm B hB, t1 z a₀ ha hr hm, ?_⟩
    intro τ b h ho
    refine ⟨k08_t2 D p q.ds pK pN hK hN hq hl hs hw z a₀ b ha (hy a₀ b τ h).1 (hy a₀ b τ h).2.1
      (hoS z a₀ b ha hr hm (hy a₀ b τ h).1 ho), fun w hw' =>
        ⟨t3 z a₀ b w ha hr hm (hy a₀ b τ h).1 (hy a₀ b τ h).2.1 ho hw',
        fun hR => k08_ins_of_closed D p q.ds z a₀ b w hm (hy a₀ b τ h).1 (hy a₀ b τ h).2.1 hw'
          (t4 z a₀ b w ha hr hm (hy a₀ b τ h).1 (hy a₀ b τ h).2.1 ho hw' hR)⟩⟩
  · intro z a τ b w i ha _ hm h _ hr ho hi
    exact k08_t5 D p q.ds z a b w i ha hm (hy a b τ h).1 (hy a b τ h).2.1 hr ho hi

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k08_seatR
