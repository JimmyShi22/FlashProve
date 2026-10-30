-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/PieceFits.lean: what a piece's yes says BESIDE its block's decision: the two
tests that `Block.step` asks in front of `decide`, at the same named rounds and columns.

Why. `piece_decides_at` (Johnson/Desc/Plain/PieceYes.lean) names the rounds and the groups that a
block's decision was shown, and drops the two tests in front of it. A block that lays what a round
DREW into its record (a point; a row for each drawn position) tests no count of what was drawn: the
counts are `roundsFit`'s. So "the block's decision went on to b" does not give "the record behind
holds as many as the plan declares": the law of such a block needs `roundsFit` at the same rounds.

  `need_ok`: a test under a name that went on said yes.
  `step_fits`: of `Block.step`: `roundsFit` at the rounds, and the view's next columns are, in key,
    position and width, those that are read.
  `piece_fits_at`: of a piece's reduction, at the transcript's own rounds and the stage's own opened
    columns: the very ones of `piece_decides_at`.
  `roundsFit_length`: so the rounds are as many as the block declares.
No protocol in it. Nothing on soundness.
-/
import Johnson.Desc.Plain.PieceYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Sound

variable {S Cl W : Type} {C : CK} {F : Frame}

theorem need_ok {name : String} {t : Bool} {u : Unit} (h : need name t = .ok u) : t = true := by
  unfold need at h
  cases t with
  | true => rfl
  | false => exact nomatch h

/-- The columns that `Block.step` wants of the view: key, position and width. -/
def wantAt (ft : ℕ) (b : Block S Cl) (rs : List Fmt.RoundView) : List (ℕ × ℕ × ℕ) :=
  (groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id

theorem step_fits {ft : ℕ} {b : Block S Cl} {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {s' : S} {k : ℕ} (H : b.step ft s rs cols = .ok (s', k)) :
    roundsFit b.rounds rs = true ∧
      ((cols.take (wantAt ft b rs).length).map (fun c => (c.1, c.2.1, c.2.2.length)) ==
        wantAt ft b rs) = true := by
  unfold Block.step at H
  obtain ⟨_, h1, H⟩ := bindOk H
  obtain ⟨_, h2, _⟩ := bindOk H
  exact ⟨need_ok h1, need_ok h2⟩

/-- **Where a piece's reduction puts out b: the two tests in front of its block's decision said yes,
on the transcript's own rounds and the stage's own opened columns.** -/
theorem piece_fits_at (p : Piece C F S Cl W) (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (b : S × F.E.Str) (hb : p.ior.red.out a τ = some b) :
    roundsFit p.b.rounds (rvT C p.ds τ ++ p.back) = true ∧
      (((sView C p.stage a.2 τ).opened.take
          (wantAt F.ft p.b (rvT C p.ds τ ++ p.back)).length).map
        (fun c => (c.1, c.2.1, c.2.2.length)) ==
          wantAt F.ft p.b (rvT C p.ds τ ++ p.back)) = true := by
  obtain ⟨s', k, hst, H'⟩ := foldConsOk (chainAtOk (pieceOk p a τ b hb))
  have e : (s', (rvT C p.ds τ ++ p.back).drop p.b.rounds.length, _) =
      (b.1, ([] : List Fmt.RoundView), ([] : List OpenedColumn)) := Except.ok.inj H'
  have e₂ : (rvT C p.ds τ ++ p.back).drop p.b.rounds.length = [] :=
    congrArg (fun x => x.2.1) e
  have e₃ : (rvT C p.ds τ ++ p.back).take p.b.rounds.length = rvT C p.ds τ ++ p.back :=
    List.take_of_length_le (List.drop_eq_nil_iff.1 e₂)
  rw [e₃] at hst
  exact step_fits hst

/-- `roundsFit` says that the two lists are of one length. -/
theorem roundsFit_length : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true → rs.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | d :: ds, r :: rs, h => by
    unfold roundsFit at h
    simp only [Bool.and_eq_true] at h
    simp only [List.length_cons, roundsFit_length ds rs h.2]

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.step_fits
#print axioms VerifiableInference.Desc.Plain.piece_fits_at
#print axioms VerifiableInference.Desc.Plain.roundsFit_length
