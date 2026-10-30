-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeatLawsOfTied.lean: FROM THE TIE AT A KIND's OWN BLOCK TO WHAT IS OWED AT A SEAT, WHATEVER THE KIND. Another
file's rule for a seat (tiedBy_of_seat and the proposition SeatLaws, Johnson/Desc/Sound/TiedSeat.lean) asks four things of a kind's files at the piece that
holds `below B'`, B' ANY block that narrows the kind's own block Bst, for every value z of the public part: the row's own law at
the table · what rides, fenced · a mark stays · "decodes" rides. THEY FOLLOW FROM `TiedAt` (Johnson/Desc/Sound/ChainOfPromises.lean)
AT THE PIECE THAT HOLDS Bst ITSELF, for every z.

Why. A yes of a piece whose block narrows another's is a yes of the other's piece, with the same statement behind
(out_narrow, Johnson/Desc/Sound/MergeNarrow.lean); and a law passes to a narrowing (goodIn_narrow, the same file). So a kind's files prove its tie ONCE, at its own block.

Main names:
  `narrows_trans` · `own_of_tied`: a tie gives the row's own law at the table (by ownAtTableWide,
    Johnson/Desc/Sound/BordersQ.lean).
  `SeatLawsN links ps k base ds back err N Mg Bst`: the four, IN TiedSeat.lean's OWN WORDS (its SeatLaws, sign for sign) but
    for two things: the piece's four fields are letters here (there: q.base, q.ds, q.back, q.err) · B' is asked to narrow Bst
    and no more (there: SeatOf Bst B': that, and that its yes bears no mark): SO THIS IS THE STRONGER PROPOSITION.
  `seatLaws_of_tied`: **TiedAt at ⟨Bst, base, ds, back, the identity, err⟩ for every z gives SeatLawsN.**
Over Johnson/Desc/Sound/MergeNarrow.lean, which has out_narrow by name.
narrows_trans HAS A KIN UNDER ANOTHER NAME: Block.Narrows.trans
(Johnson/Desc/Sound/MergeNarrowMakers.lean).
Limits. A RULE OVER LETTERS. ONE THING MORE IS ASKED THAN THE PROPOSITION SeatLaws NAMES: [Nonempty P]: its third clause ("a
mark stays") names no z, and the tie is had at a z: so the public part's type must have a member. The extractor is the identity on the witness: so not for a row that lays. It says nothing on the
facts on the description's own piece q (its back, ds, err, base).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.Sound.ChainOfPromises
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

theorem narrows_trans {S Cl : Type} {a b c : Block S Cl} (h : a.Narrows b) (h' : b.Narrows c) : a.Narrows c :=
  ⟨h.1.trans h'.1, fun s rs gs s' e => h'.2 s rs gs s' (h.2 s rs gs s' e)⟩

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place)

/-- A tie gives the row's own law at the table. -/
theorem own_of_tied (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl W) (h : TiedAt N Mg links ps get k q) :
    q.Own (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get) (insQ links ps k)
      (outsQ links ps k) := by
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, _, hMark, hDec⟩ := h
  exact ownAtTableWide A Cl P W C Fr N Mg links ps get k q o o' R R' hl t1 t2 t3 t4 hMark hDec

/-- **What a kind's files owe at a seat**, at every block that narrows its own. -/
def SeatLawsN (k : ℕ) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (err : Err (uLT C ds))
    (Bst : Block First.S Cl) : Prop :=
  (∀ B', Block.Narrows B' Bst → ∀ z : P,
      (⟨below B', base, ds, back, fun _ _ w => w, err⟩ : Piece C Fr First.S Cl W).Own
        (onQ N Mg links ps (fun s => (z, s)) k) (onQ N Mg links ps (fun s => (z, s)) (k + 1))
        (meansQ N Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k)) ∧
  (∀ B', Block.Narrows B' Bst → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', base, ds, back, fun _ _ w => w, err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) ∧
  (∀ B', Block.Narrows B' Bst → ∀ a τ b,
      (⟨below B', base, ds, back, fun _ _ w => w, err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none) ∧
  ∀ B', Block.Narrows B' Bst → ∀ (z : P) a τ b,
      (⟨below B', base, ds, back, fun _ _ w => w, err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)

/-- **THE TIE AT THE KIND's OWN BLOCK GIVES WHAT IS OWED AT A SEAT.** [P]: the third of the four names no z: so one value of
the public part is asked to be there. -/
theorem seatLaws_of_tied [Nonempty P] (k : ℕ) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) (err : Err (uLT C ds))
    (Bst : Block First.S Cl)
    (H : ∀ z : P, TiedAt N Mg links ps (fun s => (z, s)) k
      (⟨Bst, base, ds, back, fun _ _ w => w, err⟩ : Piece C Fr First.S Cl W)) :
    SeatLawsN (Fr := Fr) (W := W) N Mg links ps k base ds back err Bst := by
  have out : ∀ B', Block.Narrows B' Bst → ∀ a τ b,
      (⟨below B', base, ds, back, fun _ _ w => w, err⟩ : Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      (⟨Bst, base, ds, back, fun _ _ w => w, err⟩ : Piece C Fr First.S Cl W).ior.red.out a τ = some b :=
    fun B' hN a τ b e =>
      out_narrow ⟨Bst, base, ds, back, fun _ _ w => w, err⟩ (below B')
        (narrows_trans (below_narrows B') hN) a b τ e
  refine ⟨fun B' hN z => ?_, fun B' hN z a τ b w i ha hm e hb hall ho hn => ?_, fun B' hN a τ b e hm => ?_,
    fun B' hN z a τ b e hd => ?_⟩
  · have h := goodIn_narrow ⟨Bst, base, ds, back, fun _ _ w => w, err⟩ (below B')
      (narrows_trans (below_narrows B') hN) (fun _ => True) (fun _ _ _ _ _ => trivial) _ _ _ _
      (own_of_tied N Mg links ps _ k _ (H z))
    exact fun a ha => Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1.1, (hτ b hb).2⟩) (h a ha)
  · obtain ⟨_, _, _, _, _, _, _, _, _, t5, _, _⟩ := H z
    exact t5 a τ b w i ha hm (out B' hN a τ b e) hb hall ho hn
  · obtain ⟨z⟩ := (inferInstance : Nonempty P)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hMark, _⟩ := H z
    exact hMark a τ b (out B' hN a τ b e) hm
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hDec⟩ := H z
    exact hDec a τ b (out B' hN a τ b e) hd

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.own_of_tied
#print axioms VerifiableInference.Desc.Sound.seatLaws_of_tied
