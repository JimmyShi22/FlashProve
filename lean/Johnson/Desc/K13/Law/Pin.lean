-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Pin.lean: which pins are carried back over a piece; and the silly text at the
release's own reading. Statements with their proofs.
Main names:
  `colAt`: the column at (a tree's number, a leaf) in the oracles at a border.
  `table_kept`, `old_kept`: a piece leaves the stored table, and the trees that were sent in front
    of its stretch, as they are. General in the piece.
  `back_of_reads`: a pin that reads these alone is carried back over the piece.
  `gl_section`, `gl_three`, `not_sound_yes_gl`: the release's reading has a section, its field more
    than 2 elements: so the text that always answers fails the law's form there, without a premise.
Used of `verify-on-bytes`: `E.ofTriple`.

What is not claimed. That a pin of the protocol reads these alone.

-/
import Johnson.Desc.K13.Law.Good
import Johnson.Desc.K13.Law.Silly
import OnBytes.Maker.RowWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type}

/-- The column at (the tree with the number j, leaf x) in the oracles at a border. -/
def colAt (F : Frame) (y : F.E.Str) (j x : ℕ) : Option (List UInt64) := (posL F.all j x).map y.2

/-- A piece leaves the stored table as it is. -/
theorem table_kept {T : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W) (y : F.E.Str)
    (τ : Tr (uLT C p.ds)) : (p.ior.imp y τ).1 = y.1 := rfl

/-- A piece leaves the columns of the trees that were sent in front of its stretch as they are. -/
theorem old_kept {T : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W) (y : F.E.Str)
    (τ : Tr (uLT C p.ds)) (j x : ℕ) (hj : j < p.base) :
    colAt F (p.ior.imp y τ) j x = colAt F y j x := by
  unfold colAt
  cases hp : posL F.all j x with
  | none => rfl
  | some q =>
    obtain ⟨h1, h2⟩ := posL_spec F.all j x q hp
    show some ((sCol C p.stage y τ (.tree (F.all.get q.1).no q.2.val)).getD []) = some (y.2 q)
    rw [h1, h2]
    show some ((if j < p.base then (posL F.all j x).map y.2
      else colAtST C p.ds τ (j - p.base) x).getD []) = _
    rw [if_pos hj, hp]
    rfl

/-- **A pin that reads the stored table and the trees sent in front of the stretch alone is carried
back over the piece.** -/
theorem back_of_reads {T : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W)
    (Pin : F.E.Str → W → Prop)
    (hPin : ∀ y y' w, y.1 = y'.1 → (∀ j x, j < p.base → colAt F y j x = colAt F y' j x) →
      Pin y w → Pin y' w) :
    ∀ a τ b w, p.ior.red.out a τ = some b → Pin b.2 w → Pin a.2 w := by
  intro a τ b w hb hw
  have hb' : (p.ior.out a.1 a.2 τ).map (fun xo => (xo, p.ior.imp a.2 τ)) = some b := hb
  cases ho : p.ior.out a.1 a.2 τ with
  | none =>
    rw [ho] at hb'
    cases hb'
  | some s' =>
    rw [ho] at hb'
    obtain rfl := Option.some.inj hb'
    exact hPin _ _ w (table_kept p a.2 τ) (fun j x hj => old_kept p a.2 τ j x hj) hw

/-! ## The silly text at the release's own reading -/

/-- The release's reading has a section. -/
theorem gl_section (a : GE) : ρg.val (E.ofTriple (ofE a)) = a := toE_ofE a

/-- The field has more than 2 elements. -/
theorem gl_three : 2 < Fintype.card GE := by
  rw [Cb.Gl.gl_card.2.1]
  exact lt_trans (by norm_num) Cb.Gl.gl_card.2.2.1

/-- **The text that always answers with a row that is true of everything does not meet the form of
the law** at the release's own reading. -/
theorem not_sound_yes_gl (nR k : ℕ) : ¬ SoundAt ρg nR k sillyYes :=
  not_sound_yes ρg (fun a => E.ofTriple (ofE a)) gl_section nR k gl_three
    { st := default, book := default, roots := 0, opened := [], loc := () } extNone
    ()

end VerifiableInference.Desc.K13.Law
