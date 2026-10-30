-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow24Depth.lean: ROW 2.4 OF THE KEY FILE's TABLE OF JOINTS
AT THE SEAT (Johnson/RunOne/KeyRowsBackAtSeat.lean: loc_back₂_seat): ITS TWO PREMISES ON THE FRAME
AND THE WRITTEN ROUND, hA (logN ≤ the frame's depth of the stored table) AND
ho (the round opens no tree), PAID OUT OF THE TILING's OWN SENTENCE: Matches Fr₂.a dep b4.rounds [d]
(Johnson/Desc/Sound/Tiles.lean): K14's fourth block declares ONE round, which reads the stored table
at the index's own tree (readsAtLoc: its depth IS code.logN, by IndexShape.tree's text) and opens no
tree; RoundMatch says that every stored part is read at the frame's depth, and ties the opened trees
one to one.
OBJECT: b4.rounds, blocks Q = some [b1, …, b8] · USER: loc_back₂_seat · LETTERS: Q; a dep d.
  loc_match            Matches a dep b4.rounds [d] gives logN = a and d.opens = []
  loc_back₂_seat_m     row 2.4 at the seat with hA | ho replaced by the tiling's sentence
What is not claimed. That the maker's stretch at piece number 4 is [d] and matches (the frame's
tiling). NO MEMBER OF on₂ … 4 IS SHOWN BY ANYBODY. Nothing on soundness.

-/
import Johnson.RunOne.KeyRowsBackAtSeat
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.K14 (P14 blocks)
open _root_.Desc.K14.Law (atW posAt)
open scoped ENNReal

/-- **What the tiling says at K14's fourth block.** -/
theorem loc_match (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some [b1,
    b2, b3, b4, b5, b6, b7, b8])
    (a : Nat) (dep : Nat → Option Nat) (d : RDT) (hm : Matches a dep b4.rounds [d]) :
    Q.S.fold.index.code.logN = a ∧ d.opens = [] := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  have hm' : Matches a dep ((((_root_.Desc.K14.entries Q).drop 1).take 1).map fun e =>
      ({ entry := e, stored := [_root_.Desc.K14.readsAtLoc Q.S.fold Q.item] } : Fmt.DeclaredRound)) [d]
          := hm
  rcases hl : ((_root_.Desc.K14.entries Q).drop 1).take 1 with _ | ⟨e, t⟩
  · rw [hl] at hm'
    exact hm'.elim
  · rw [hl] at hm'
    obtain ⟨⟨_, h2, h3⟩, _⟩ := hm'
    exact ⟨h2 _ (List.mem_singleton.2 rfl), List.forall₂_nil_left_iff.1 h3⟩

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame) (T : BaseSt Cells M Smp
           Rec) (at_ : Where)
  (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some [b1, b2, b3, b4, b5,
      b6, b7, b8]) (b : Block St₂ Cl)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
include hbl

/-- **ROW 2.4 AT THE SEAT, hA | ho out of the tiling's sentence.** -/
theorem loc_back₂_seat_m {K : Type} [Field K] (ρ : Model.Reading K) (hd4 : b.decide = b4.decide) (hS
    : Q.par.S = Lk6.AtPlan.keyFull.once.shape)
    (d : RDT) (hW : atW Johnson.G.dryKeyFull.2.1 3 = some (d.entry, d.kind))
    (dep : Nat → Option Nat) (hm : Matches Fr₂.a dep b4.rounds [d]) (base : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (henc : EncIs ρ Q.par.S.fold enc) :
    (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d Q.par.S.fold.index.code.logN
        Q.par.S.fold.columns ((2 ^ Q.par.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1) ^
        Q.par.S.fold.columns) ext).ior.red.Leads
        (on₂ F Fr₂ T.h₂ at_ Q.par.S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ 4)
        (fun x x' => L₂ F Fr₂ T.h₂ at_ Q.par.S K₁ R enc OnBytes.Params.recordRadius 5 x' → L₂ F Fr₂
            T.h₂ at_ Q.par.S K₁ R enc OnBytes.Params.recordRadius 4 x)
        (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d Q.par.S.fold.index.code.logN
            Q.par.S.fold.columns ((2 ^ Q.par.S.fold.index.code.logN - OnBytes.Params.recordRadius -
            1) ^ Q.par.S.fold.columns) ext).err ∧
      Err.Below (posAt (F := Fr₂) (held b : Block (P₂ × St₂) Cl) base d Q.par.S.fold.index.code.logN
          Q.par.S.fold.columns ((2 ^ Q.par.S.fold.index.code.logN - OnBytes.Params.recordRadius - 1)
          ^ Q.par.S.fold.columns) ext).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  loc_back₂_seat F Fr₂ T at_ Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b K₁ R enc a coll last₁ off₂ ρ hd4 hS d
      hW
    (loc_match Q b1 b2 b3 b4 b5 b6 b7 b8 hbl Fr₂.a dep d hm).2 base ext hbase hsame henc
    (Nat.le_of_eq (loc_match Q b1 b2 b3 b4 b5 b6 b7 b8 hbl Fr₂.a dep d hm).1)

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.loc_match
#print axioms Johnson.RunOne.KeyRows23.loc_back₂_seat_m
