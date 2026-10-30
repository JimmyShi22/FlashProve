-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/TieEach.lean: THE SMALLNESS TEST: `k08_seatLaws` (Johnson/Desc/First/K8/
TieLaws.lean) WITH THE LAW'S FOUR LETTERS TAKEN OFF THE STATEMENT IN FRONT.

Why. The kind's law is stated at fixed letters: one list of members, one table of cells. The table
of joints' sentences read these off the verifier's state. `Piece.GoodIn` is owed statement by
statement (the rule in general: `goodIn_of_each`, Johnson/Desc/First/K8/LawLocal.lean
[not in this library], not imported here): so the four letters may hang on the public part z and on
the statement a₀ in front.
  `own_of_each`: THE DOOR AT THE TABLE, STATEMENT BY STATEMENT (general in the kind): `Piece.Own` at
    the table's words from: for each unmarked a₀ inside the promise, four letters with `GoodIn` and
    the four ties AT a₀, the fourth under a yes from a₀ to b; a mark stays; "decodes" rides. At a
    marked a₀ nothing is asked: the promise behind holds by the mark and "decodes", and what the row
    opens holds of no witness.
  `k08_seatLaws_each`: **`SeatLaws links ps k q Nn Mg (whole p)`** from: hG at every (z, a₀); t1,
    t2, t3, t4 at a := a₀, each with what the wide door hands (t4: the statement behind, the
    kind's condition there and what the row opens there); t5; hD.
  `k08_seatLaws_each_blind`: the same with t2, t5 and hD paid by `DrawBlind`
    (Johnson/Desc/First/K8/TieRides.lean).
Limits. SHOWN AT NO FILLING. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.K8.TieRides

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
variable {Pp W Cl : Type} {C : CK} {Fr : Frame}

/-- **The door at the table, statement by statement.** -/
theorem own_of_each (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (z : Pp) (k : ℕ) (x : Piece C Fr S Cl W) (hx : ∀ a τ w, x.ext a τ w = w)
    (h : ∀ a₀, onQ Nn Mg links ps (fun s => (z, s)) k a₀ → ¬ a₀.1.failed ≠ none →
      ∃ (o o₁ : S × Fr.E.Str → Prop) (Q Q' : S × Fr.E.Str → W → Prop),
        x.GoodIn o o₁ Q Q' ∧ o a₀ ∧
        ∀ τ b, x.ior.red.out a₀ τ = some b → o₁ b →
          onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b ∧
          ∀ w, relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → Q' b w ∧
            (Q a₀ w → relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a₀ w))
    (hMark : ∀ a τ b, x.ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none)
    (hDec : ∀ a τ b, x.ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    x.Own (onQ Nn Mg links ps (fun s => (z, s)) k) (onQ Nn Mg links ps (fun s => (z, s)) (k + 1))
      (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k) := by
  intro a ha
  by_cases hm : a.1.failed ≠ none
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    refine ⟨⟨hDec a τ b hb ha.1, Or.inl (hMark a τ b hb hm)⟩, fun w hw => ?_⟩
    have hu : meansQ (Fr := Fr) Nn Mg (fun s => (z, s)) .unmarked b w :=
      hw .unmarked (List.mem_append_right _ (List.mem_singleton.2 rfl))
    exact absurd hu (hMark a τ b hb hm)
  · obtain ⟨o, o₁, Q, Q', hG, hoa, h1⟩ := h a ha hm
    refine Doomed.mono _ _ (fun τ hτ b hb => ?_) (hG a hoa)
    obtain ⟨u, v⟩ := hτ b hb
    refine ⟨(h1 τ b hb u).1, fun w hw => ?_⟩
    have hq := v w ((h1 τ b hb u).2 w hw).1
    rw [hx] at hq ⊢
    exact ((h1 τ b hb u).2 w hw).2 hq

end

section
variable {Pp W : Type} {C : CK} {Fr : Frame}

/-- **WHAT THE KIND'S AUTHORS OWE AT THE KIND'S PLACE, the law's letters off the statement in
front.** -/
theorem k08_seatLaws_each (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (Pp × S) Claim W) (Nn : Numbers) (Mg : Meaning Pp W) (p : ParW)
    (o o' : Pp → S × Fr.E.Str → S × Fr.E.Str → Prop)
    (R R' : Pp → S × Fr.E.Str → S × Fr.E.Str → W → Prop)
    (hG : ∀ (z : Pp) (a₀ : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a₀ →
      ¬ a₀.1.failed ≠ none → ∀ B' : Block S Claim, B'.Narrows (whole p) →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W).GoodIn
        (o z a₀) (o' z a₀) (R z a₀) (R' z a₀))
    (t1 : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → o z a a)
    (t2 : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b)
    (t3 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R' z a b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R z a a w →
      relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w)
    (t5 : ∀ (z : Pp) (a b : S × Fr.E.Str) w i, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    (hD : ∀ (z : Pp) (a b : S × Fr.E.Str),
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      Mg.decodes (z, a.1) (strsOf Fr a.2) → Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    SeatLaws links ps k q Nn Mg (whole p) := by
  obtain ⟨qb, qbase, qds, qback, qext, qerr⟩ := q
  have hy : ∀ B' : Block S Claim, SeatOf (whole p) B' → ∀ (a b : S × Fr.E.Str)
      (τ : Iop.Tr (uLT C qds)),
      (⟨below B', qbase, qds, qback, fun _ _ w => w, qerr⟩ :
        Piece C Fr S Claim W).ior.red.out a τ = some b →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) ∧
        (∃ τ' : Iop.Tr (uLT C qds), b.2 = behind C Fr qbase qds a.2 τ') ∧
        b.1.failed = a.1.failed := by
    intro B' hB a b τ h
    exact ⟨whole_yes p (⟨below B', qbase, qds, qback, fun _ _ w => w, qerr⟩ :
        Piece C Fr S Claim W) B' hB.1 rfl a b τ h,
      ⟨τ, out_behind (⟨below B', qbase, qds, qback, fun _ _ w => w, qerr⟩ :
        Piece C Fr S Claim W) a b τ h⟩,
      whole_mark p (⟨below B', qbase, qds, qback, fun _ _ w => w, qerr⟩ :
        Piece C Fr S Claim W) B' hB.1 rfl a b τ h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B' hB z
    refine own_of_each Nn Mg links ps z k _ (fun _ _ _ => rfl) ?_ ?_ ?_
    · intro a₀ ha hm
      refine ⟨o z a₀, o' z a₀, R z a₀, R' z a₀, hG z a₀ ha hm B' hB.1, t1 z a₀ ha hm, ?_⟩
      intro τ b h ho
      exact ⟨t2 z a₀ b ha hm (hy B' hB a₀ b τ h).1 (hy B' hB a₀ b τ h).2.1 ho,
        fun w hw => ⟨t3 z a₀ b w ha hm (hy B' hB a₀ b τ h).1 (hy B' hB a₀ b τ h).2.1 ho hw,
          t4 z a₀ b w ha hm (hy B' hB a₀ b τ h).1 (hy B' hB a₀ b τ h).2.1 ho hw⟩⟩
    · intro a τ b h hm
      rw [(hy B' hB a b τ h).2.2]
      exact hm
    · intro a τ b h hd
      exact hD z a b (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hd
  · intro B' hB z a τ b w i ha hm h hb hr ho hi
    exact t5 z a b w i ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hb hr ho hi
  · intro B' hB a τ b h hm
    rw [(hy B' hB a b τ h).2.2]
    exact hm
  · intro B' hB z a τ b h hd
    exact hD z a b (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hd

/-- **The same with the promise behind, what rides and "decodes" paid by what the filling owes for
the draw.** oS: the kind's own condition behind, as `DrawBlind` reads it. -/
theorem k08_seatLaws_each_blind {links : List ModelPart} {ps : List Place} {k : ℕ} {Nn : Numbers}
    {Mg : Meaning Pp W} (q : Piece C Fr (Pp × S) Claim W) (p : ParW)
    (o o' : Pp → S × Fr.E.Str → S × Fr.E.Str → Prop)
    (R R' : Pp → S × Fr.E.Str → S × Fr.E.Str → W → Prop) (oS : Pp → S → Strs → Prop)
    (hoS : ∀ z a b, o' z a b → oS z b.1 (strsOf Fr b.2))
    (D : DrawBlind Nn Mg links ps k q.base oS) (pK pN : Place)
    (hK : ps[k]? = some pK) (hN : ps[k + 1]? = some pN) (hq : quietRow (rowOf links pK) = true)
    (hl : pN.link = pK.link) (hs : standAt links pN = standAt links pK)
    (hw : mayWait links pK = false)
    (hG : ∀ (z : Pp) (a₀ : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a₀ →
      ¬ a₀.1.failed ≠ none → ∀ B' : Block S Claim, B'.Narrows (whole p) →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W).GoodIn
        (o z a₀) (o' z a₀) (R z a₀) (R' z a₀))
    (t1 : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → o z a a)
    (t3 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R' z a b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' z a b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R z a a w →
      relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w) :
    SeatLaws links ps k q Nn Mg (whole p) :=
  k08_seatLaws_each links ps k q Nn Mg p o o' R R' hG t1
    (fun z a b ha _ hy hb ho =>
      k08_t2 D p q.ds pK pN hK hN hq hl hs hw z a b ha hy hb (hoS z a b ho))
    t3 t4
    (fun z a b w i ha hm hy hb _ hr ho hi => k08_t5 D p q.ds z a b w i ha hm hy hb hr ho hi)
    (fun z a b hy hb hd => k08_hD D p q.ds z a b hy hb hd)

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.own_of_each
#print axioms VerifiableInference.Desc.First.K8.k08_seatLaws_each
#print axioms VerifiableInference.Desc.First.K8.k08_seatLaws_each_blind
