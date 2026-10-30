-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/OfMeans.lean: THE LINE same OF `K4Riders` (K4RidesFenced.lean) AS A THEOREM,
OUT OF THE STRUCTURE OF EQUATIONS `K4Means` (K4Means.lean): every item but the lookup's own claims
that rides at K4's row goes back from behind an accept to in front, at its owner's own sentence. One
statement with its proof: the sorts (`riderSort`), then a call a sort (Riders/Proofs.lean).

  `lay_in`: inside the fence (`SameIn`) the verifier's state in front stands in a feed-forward
    segment.
  **`same_of_means`**: UNDER `K4Means Mg D`, hsort (what rides has `riderSort`: `riders_are` |
    `riders_full` pay it) AND FOUR LINES ON THE OWNERS' LETTERS, each asked inside the fence: hrw
    (the pile's reader of the witness reads one thing at the two states) · hdecT (so does the
    committed table's decoder) · hReq (and the relation's reader of the request) · hHead (the head's
    part goes back): the line same.

Limits. The four lines are premises: they say that a LETTER which may read the verifier's state
reads of it what K4's accept leaves: their owners' to pay, or ours once the letters are terms. The
fourth sort, formsT m 2 "objects" (the line objects), is not here. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Riders.Proofs
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.K4PromiseFront
import Johnson.Road.K4.SameReadSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open Iop OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Strs)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Meaning start)
open VerifiableInference.Desc.K13.Law (RowsTrue)
open VerifiableInference.Desc.Sound (Frame Piece strsOf insQ outsQ openAfter meansQ onQ MsgT)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- Inside the fence the verifier's state in front stands in a feed-forward segment. -/
theorem lay_in (H : AtK4 links ps k m pl) {base : ℕ} {x y : S × Fr.E.Str}
    (h : SameIn D.N Mg Z links ps k base x y) : ∃ a : LayOwn, x.1.here = .lay a := by
  obtain ⟨b1, _, _⟩ := bools_of_onQ D.N Mg Z h.1 h.2.1
  rw [H.here] at b1
  exact lay_of_shape H b1

/-- **The line same of `K4Riders`, out of the structure of equations.** -/
theorem same_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) (base : ℕ)
    (hsort : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → riderSort m i = true)
    (hrw : ∀ x y : S × Fr.E.Str, SameIn D.N Mg Z links ps k base x y →
      D.rw13 (Z, y.1) = D.rw13 (Z, x.1))
    (hdecT : ∀ x y : S × Fr.E.Str, SameIn D.N Mg Z links ps k base x y →
      ∀ c, D.decT c (Z, y.1) = D.decT c (Z, x.1))
    (hReq : ∀ x y : S × Fr.E.Str, SameIn D.N Mg Z links ps k base x y →
      D.H.req (Z, x.1) = D.H.req (Z, y.1))
    (hHead : ∀ x y : S × Fr.E.Str, SameIn D.N Mg Z links ps k base x y → ∀ p i w,
      D.headPart p i (Z, y.1) (strsOf Fr y.2) w → D.headPart p i (Z, x.1) (strsOf Fr x.2) w) :
    ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i ≠ .formsT m 2 "objects" →
      ∀ (x y : S × Fr.E.Str) (w : Wit (CellsK rows cols) Tok MsgT),
      SameIn D.N Mg Z links ps k base x y → meansQ D.N Mg (fun s => (Z, s)) i y w →
      meansQ D.N Mg (fun s => (Z, s)) i x w := by
  intro i ho hi hne x y w hS hy
  have hs := hsort i ho hi
  have hR := hS.2.2.rest
  cases i with
  | pile =>
    obtain ⟨a, ha⟩ := lay_in H hS
    have hy' : Mg.pile (Z, y.1) (strsOf Fr y.2) w := hy
    show Mg.pile (Z, x.1) (strsOf Fr x.2) w
    rw [E.pile] at hy' ⊢
    have hy2 : RowsTrue (D.rw13 (Z, y.1)) y.1 w := hy'
    show RowsTrue (D.rw13 (Z, x.1)) x.1 w
    unfold RowsTrue at hy2 ⊢
    rw [hrw x y hS, rides_pile x.1 y.1 a hR ha] at hy2
    exact hy2
  | row j c =>
    have hy' : Mg.row j c (Z, y.1) (strsOf Fr y.2) w := hy
    show Mg.row j c (Z, x.1) (strsOf Fr x.2) w
    rw [E.row] at hy' ⊢
    exact (rides_row P (CellsK rows cols) Tok D.N D.arr j c Z x.1 y.1 (strsOf Fr x.2)
      (strsOf Fr y.2) w hR).1 hy'
  | constr j p =>
    have hy' : Mg.constr j p (Z, y.1) (strsOf Fr y.2) w := hy
    show Mg.constr j p (Z, x.1) (strsOf Fr x.2) w
    rw [E.constr] at hy' ⊢
    refine rides_constr X P _ rows cols D.hd D.put D.H D.headPart D.digitsPart j p (Z, x.1) (Z, y.1)
      (strsOf Fr x.2) (strsOf Fr y.2) w ?_ (hReq x y hS) (fun _ i' => hHead x y hS p i' w) ?_ hy'
    · rw [E.decIs]
      show D.decT (strsOf Fr x.2).cell (Z, x.1) = D.decT (strsOf Fr y.2).cell (Z, y.1)
      rw [cell_same hS.2.2, hdecT x y hS]
    · intro hp
      exfalso
      simp [riderSort, hp] at hs
  | formsT j k' r =>
    exfalso
    simp only [riderSort, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
    exact hne rfl
  | _ => simp [riderSort] at hs

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.same_of_means
