-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/TiedAtSeatR.lean: A SUB-PROTOCOL AT A PLACE OF A DESCRIPTION IS TIED AT THE TABLE
OF JOINTS IN THE FORM WITH A CONDITION THAT EVERY ACCEPTING STEP HANDS ON (`TiedAtR`,
Johnson/Desc/Sound/ChainOfPromisesR.lean), WHATEVER ITS KIND. Two theorems; rules over letters. A
file BESIDE the table of joints: it turns nothing of it. Rch is a letter: a family of conditions, a
border a member.

  `goodInR_of_each`: what a sub-protocol owes between "the promise and a condition Rz" in front and
    the promise behind, at the table's two relations, STATEMENT BY STATEMENT: for each unmarked a₀
    inside the promise and with Rz: four letters with `GoodIn` and four ties at a₀, the fourth under
    an accepting step from a₀ to b. At a marked a₀ nothing is asked: the promise behind holds by the
    mark and "decodes", and what the row opens holds of no witness.
  `tiedAtR_of_seat`: a description's piece that holds the strict reading of a sub-protocol B
    beneath the lift over the public part, with an extractor that lays nothing, is `TiedAtR`, at the
    letters "the promise and Rch" | the promise behind | what the row closes and reads | what it
    opens and reads: FROM the row's law between these; what rides, with Rch in hand; a mark stays;
    "decodes" rides: each at the piece over the verifier's state, for every public part z.
Limits. RULES OVER LETTERS: at Rch := never every tie is free and nothing is said: whoever calls the
chain's rule owes Rch 0 at the start and the hand-on at every sub-protocol. If the table's files
bring the like, this file gives way. Nothing on soundness.

-/
import Johnson.Desc.Sound.TiedLift
import Johnson.Desc.Sound.ChainOfPromisesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open Iop
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start)

section
variable {Pp W Cl : Type} {C : CK} {Fr : Frame}

/-- **The door at the table, statement by statement, with a condition beside the promise.** -/
theorem goodInR_of_each (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (z : Pp) (k : ℕ) (Rz : S × Fr.E.Str → Prop) (x : Piece C Fr S Cl W)
    (hx : ∀ a τ w, x.ext a τ w = w)
    (h : ∀ a₀, onQ Nn Mg links ps (fun s => (z, s)) k a₀ → Rz a₀ → ¬ a₀.1.failed ≠ none →
      ∃ (o o₁ : S × Fr.E.Str → Prop) (Q Q' : S × Fr.E.Str → W → Prop),
        x.GoodIn o o₁ Q Q' ∧ o a₀ ∧
        ∀ τ b, x.ior.red.out a₀ τ = some b → o₁ b →
          onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b ∧
          ∀ w, relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → Q' b w ∧
            (Q a₀ w → relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a₀ w))
    (hMark : ∀ a τ b, x.ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none)
    (hDec : ∀ a τ b, x.ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    x.GoodIn (fun a => onQ Nn Mg links ps (fun s => (z, s)) k a ∧ Rz a)
      (onQ Nn Mg links ps (fun s => (z, s)) (k + 1))
      (relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k))
      (relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k)) := by
  intro a ha
  by_cases hm : a.1.failed ≠ none
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    refine ⟨⟨hDec a τ b hb ha.1.1, Or.inl (hMark a τ b hb hm)⟩, fun w hw => ?_⟩
    have hu : meansQ (Fr := Fr) Nn Mg (fun s => (z, s)) .unmarked b w :=
      hw .unmarked (List.mem_append_right _ (List.mem_singleton.2 rfl))
    exact absurd hu (hMark a τ b hb hm)
  · obtain ⟨o, o₁, Q, Q', hG, hoa, h1⟩ := h a ha.1 ha.2 hm
    refine Doomed.mono _ _ (fun τ hτ b hb => ?_) (hG a hoa)
    obtain ⟨u, v⟩ := hτ b hb
    refine ⟨(h1 τ b hb u).1, fun w hw => ?_⟩
    have hq := v w ((h1 τ b hb u).2 w hw).1
    rw [hx] at hq ⊢
    exact ((h1 τ b hb u).2 w hw).2 hq

/-- **A sub-protocol at a place is tied in the form with Rch, whatever its kind.** -/
theorem tiedAtR_of_seat (links : List ModelPart) (ps : List Place) (k : ℕ) (B : Block S Cl)
    (q : Piece C Fr (Pp × S) Cl W) (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (Nn : Numbers) (Mg : Meaning Pp W) (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (E : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (row : ∀ z : Pp,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Cl W).GoodIn
        (fun a => onQ Nn Mg links ps (fun s => (z, s)) k a ∧ Rch k ((z, a.1), a.2))
        (onQ Nn Mg links ps (fun s => (z, s)) (k + 1))
        (relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k))
        (relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k)))
    (rides : ∀ (z : Pp) a τ b w i,
      onQ Nn Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Cl W).ior.red.out a τ = some b →
      onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    (hMark : ∀ a τ b,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Cl W).ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none)
    (hDec : ∀ (z : Pp) a τ b,
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr S Cl W).ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    TiedAtR Nn Mg links ps (fun a => a) Rch k (q.withMap E) := by
  rw [withMap_is_liftAt q (below B) hq E hE]
  refine ⟨fun a => onQ Nn Mg links ps (fun s => (a.1.1, s)) k (a.1.2, a.2) ∧
        Rch k ((a.1.1, a.1.2), a.2),
      fun a => onQ Nn Mg links ps (fun s => (a.1.1, s)) (k + 1) (a.1.2, a.2),
      fun a w => relAt (meansQ Nn Mg fun s => (a.1.1, s)) (insQ links ps k) (a.1.2, a.2) w,
      fun a w => relAt (meansQ Nn Mg fun s => (a.1.1, s)) (outsQ links ps k) (a.1.2, a.2) w,
      liftGoodInExt (Pp × S) S Pp Cl W C Fr Prod.snd (fun t s => (t.1, s)) Prod.fst
        (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Cl W)
        (fun _ => fun _ _ w => w)
        (fun z a => onQ Nn Mg links ps (fun s => (z, s)) k a ∧ Rch k ((z, a.1), a.2))
        (fun z => onQ Nn Mg links ps (fun s => (z, s)) (k + 1))
        (fun z => relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k))
        (fun z => relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k))
        (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) row,
      fun a ha hr _ => ⟨ha, hr⟩, fun _ _ _ _ _ _ _ hb => hb, fun _ _ _ _ _ _ _ _ _ hO => hO,
      fun _ _ _ _ _ _ _ _ _ _ hR => hR, ?_, ?_, ?_⟩
  · intro a τ b w i ha hr hm hb hon hall hi hin
    obtain ⟨y, hy, rfl⟩ := out_liftAt
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Cl W) a b τ hb
    exact rides a.1.1 (a.1.2, a.2) τ y w i ha hr hm hy hon hall hi hin
  · intro a τ b hb hm
    obtain ⟨y, hy, rfl⟩ := out_liftAt
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Cl W) a b τ hb
    exact hMark (a.1.2, a.2) τ y hy hm
  · intro a τ b hb hd
    obtain ⟨y, hy, rfl⟩ := out_liftAt
      (⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Cl W) a b τ hb
    exact hDec a.1.1 (a.1.2, a.2) τ y hy hd

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodInR_of_each
#print axioms VerifiableInference.Desc.Sound.tiedAtR_of_seat
