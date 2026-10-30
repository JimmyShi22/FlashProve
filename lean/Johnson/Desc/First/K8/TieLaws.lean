-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/TieLaws.lean: THE SMALLNESS TEST: what the kind's authors owe where a written
description lays the kind's block, in the words of the table of joints (`SeatLaws`,
Johnson/Desc/Sound/TiedSeat.lean). After the pattern of Johnson/Top/H0/MergeLaw/TieLaws.lean.

What is said.
  `whole_yes`: at a piece that holds the strict reading of a block that narrows `whole p`: where it
    puts out, the draw's own decision (`approximateRangeProofDrawKind atS p.toPar`) has said yes, from the verifier's state
    in front to the verifier's state behind.
  `whole_mark`: there the mark of failure is as it was.
  `k08_seatLaws`: **`SeatLaws links ps k q Nn Mg (whole p)`**: the row's own law at the table; what
    rides; a mark stays; "decodes" rides: each over every block B' that narrows the kind's block and
    whose yes bears no mark. FROM:
    (a) hG: THE KIND'S LAW AS `GoodIn`, AT FOUR LETTERS o o' R R' (a condition in front and one
      behind; a relation in front and one behind), at the piece that holds the strict reading of ANY
      block that narrows `whole p`, with q's own base, written rounds, rounds behind and errors;
    (b) FIVE TIES BETWEEN THESE FOUR LETTERS AND THE TABLE'S WORDS, each with the promise in front,
      "no mark", the draw's own decision's yes and "the strings behind are the library's `behind` of
      the strings in front, at the piece's own base and rounds, at some transcript" in hand: t1: the
      promise in front gives o; t2: o' gives the promise behind; t3: what the row opens gives R';
      t4: R gives what the row closes; t5: what rides;
    (c) hD: "decodes" rides past the draw's yes, with the same two facts in hand.
  `goodIn_whole`: (a) FROM THE LAW AT THE DRAW'S OWN BLOCK: `GoodIn` at a piece that holds the
    strict reading of `approximateRangeProofDrawKind atS p.toPar` gives it at every block that narrows `whole p`: a block
    that refuses more owes no more. `goodIn_whole_plain`: the same from the law at a piece that
    holds `approximateRangeProofDrawKind atS p.toPar` itself, as `piece atS p base e` (Johnson/Desc/First/K8/LawPiece.lean)
    does.
Paid here, no premises: a mark stays; that the piece's yes is the draw's own decision's yes; what
the strings behind are.
Limits. SHOWN AT NO FILLING: hG, t1 to t5 and hD are premises; whether one filling of the table
meets them all is not tried. THE BLOCK IS THE WHOLE KIND'S, but of `whole p` its rounds and its
decision alone are read here, which are the draw's: nothing is said of its three runs of claims.
Of `SeatOf` the first half alone is spent. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.First.K8.LawLeaves
import Johnson.Desc.Sound.TiedSeat
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.K8
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Place Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start)

/-- Narrowing passes the strict reading. -/
theorem below_mono8 {T Cl : Type} {b' b : Block T Cl} (h : b'.Narrows b) :
    (below b').Narrows (below b) := by
  refine ⟨h.1, fun s rs gs s' e => ?_⟩
  have e' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b'.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := e
  show (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s'
  split at e'
  · rename_i hv
    rw [if_pos hv]
    exact h.2 _ _ _ _ e'
  · cases e'

/-- The kind, whole, narrows the draw's own block: one list of rounds, one decision. -/
theorem whole_narrows (p : ParW) : (whole p).Narrows (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar) :=
  ⟨rfl, fun _ _ _ _ h => h⟩

section
variable {C : CK} {Fr : Frame} {W : Type}

/-- **Where such a piece puts out, the draw's own decision has said yes.** -/
theorem whole_yes (p : ParW) (x : Piece C Fr S Claim W) (B' : Block S Claim)
    (hB : B'.Narrows (whole p)) (hx : x.b = below B') (a b : S × Fr.E.Str)
    (τ : Iop.Tr (uLT C x.ds)) (h : x.ior.red.out a τ = some b) :
    ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1 := by
  obtain ⟨rs, gs, hd⟩ := out_yes x a b τ h
  rw [hx] at hd
  exact ⟨rs, gs, hB.2 _ _ _ _ ((below_narrows B').2 _ _ _ _ hd)⟩

/-- **The mark of failure is as it was.** -/
theorem whole_mark (p : ParW) (x : Piece C Fr S Claim W) (B' : Block S Claim)
    (hB : B'.Narrows (whole p)) (hx : x.b = below B') (a b : S × Fr.E.Str)
    (τ : Iop.Tr (uLT C x.ds)) (h : x.ior.red.out a τ = some b) : b.1.failed = a.1.failed := by
  obtain ⟨rs, gs, hd⟩ := whole_yes p x B' hB hx a b τ h
  exact hear_leaves_mark p.toPar a.1 rs gs b.1 hd

/-- **The law at the draw's own block gives it at every block that narrows the kind's.** -/
theorem goodIn_whole (p : ParW) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (err : Err (uLT C ds)) (o o' : S × Fr.E.Str → Prop) (R R' : S × Fr.E.Str → W → Prop)
    (g : (⟨below (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar), base, ds, back, fun _ _ w => w, err⟩ :
      Piece C Fr S Claim W).GoodIn o o' R R')
    (B' : Block S Claim) (hB : B'.Narrows (whole p)) :
    (⟨below B', base, ds, back, fun _ _ w => w, err⟩ : Piece C Fr S Claim W).GoodIn o o' R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (g a ha)
  intro τ hτ b hb
  exact hτ b (out_narrow (⟨below (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar), base, ds, back, fun _ _ w => w,
    err⟩ : Piece C Fr S Claim W) (below B')
    (below_mono8 ⟨hB.1, fun s rs gs s' e => hB.2 s rs gs s' e⟩) a b τ hb)

/-- The same from the law at the draw's own block as it is, without the strict reading. -/
theorem goodIn_whole_plain (p : ParW) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (err : Err (uLT C ds)) (o o' : S × Fr.E.Str → Prop) (R R' : S × Fr.E.Str → W → Prop)
    (g : (⟨approximateRangeProofDrawKind (Cl := Claim) atS p.toPar, base, ds, back, fun _ _ w => w, err⟩ :
      Piece C Fr S Claim W).GoodIn o o' R R')
    (B' : Block S Claim) (hB : B'.Narrows (whole p)) :
    (⟨below B', base, ds, back, fun _ _ w => w, err⟩ : Piece C Fr S Claim W).GoodIn o o' R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (g a ha)
  intro τ hτ b hb
  exact hτ b (out_narrow (⟨approximateRangeProofDrawKind (Cl := Claim) atS p.toPar, base, ds, back, fun _ _ w => w, err⟩ :
    Piece C Fr S Claim W) (below B')
    ⟨hB.1, fun s rs gs s' e => hB.2 s rs gs s' ((below_narrows B').2 s rs gs s' e)⟩ a b τ hb)

/-- **WHAT THE KIND'S AUTHORS OWE AT THE KIND'S PLACE** (`SeatLaws`), at the kind's own block. -/
theorem k08_seatLaws {Pp : Type} (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (Pp × S) Claim W) (Nn : Numbers) (Mg : Meaning Pp W) (p : ParW)
    (o o' : S × Fr.E.Str → Prop) (R R' : S × Fr.E.Str → W → Prop)
    -- the kind's law
    (hG : ∀ B' : Block S Claim, B'.Narrows (whole p) →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr S Claim W).GoodIn
        o o' R R')
    -- four ties between the law's four letters and the table's words; the fifth, what rides
    (t1 : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → o a)
    (t2 : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' b → onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b)
    (t3 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R' b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      o' b → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w → R a w →
      relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w)
    (t5 : ∀ (z : Pp) (a b : S × Fr.E.Str) w i, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT C q.ds), b.2 = behind C Fr q.base q.ds a.2 τ) →
      onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    -- "decodes" rides past the draw's yes
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
    refine ownAtTableWide _ _ _ _ _ _ Nn Mg links ps (fun s => (z, s)) k _ o o' R R'
      (hG B' hB.1) (t1 z) ?_ ?_ ?_ ?_ ?_
    · intro a τ b ha hm h ho
      exact t2 z a b ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho
    · intro a τ b w ha hm h ho hw
      exact t3 z a b w ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho hw
    · intro a τ b w ha hm h ho hw hr
      exact t4 z a b w ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho hw hr
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

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.whole_yes
#print axioms VerifiableInference.Desc.First.K8.whole_mark
#print axioms VerifiableInference.Desc.First.K8.goodIn_whole
#print axioms VerifiableInference.Desc.First.K8.goodIn_whole_plain
#print axioms VerifiableInference.Desc.First.K8.k08_seatLaws
