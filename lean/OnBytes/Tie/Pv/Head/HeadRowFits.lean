-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Head/HeadRowFits.lean: the rounds of the row of the output head's own rounds fit the
entries that the planner adds for them.

OnBytes/Tie/Pv/Head/HeadList.lean has the list ownShape of rounds, for any parameters of the four
sumchecks behind the head's lookup, and shows that it fits, one by one and in order, the entries
headOwnList w x of the plan (own_fits). Here the parameters are those of the blocks of the row of
Cb/Pv/Head/HeadRow.lean.

rowRounds s lkW rows: the record of the head's numbers: s.lt, s.lPd; nine sums, seven products, four
row values; lkW and rows are not read by these rounds.
row_shape: the row's rounds are ownShape at that record and at the four blocks' parameters.
row_fits: they fit the entries headOwnList w (rowRounds s lkW rows), for every work w.

What is not claimed. What Fits does not read (an entry's name, work, rows, logN). That the record is
that of a configuration: Cb/Pv/Head/TestNormSizes.lean and
Cb/Pv/Head/TestToks.lean compare the sizes with written lists.


-/
import OnBytes.Tie.Pv.Head.HeadList
import Cb.Pv.Head.HeadRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Head
open Iop Prob Cb Johnson.L5.Layers Cb.Pv.Head Cb.Pv.Head.Bat Cb.Pv.Head.Tok Inst.Model

/-- The head's numbers, from the sizes of the row. -/
def rowRounds (s : SqSize) (lkW rows : ℕ) : OnBytes.Params.HeadRounds :=
  ⟨s.lt, s.lPd, lkW, 9, 7, 4, rows⟩

section
variable {E : Type} [Field E] [Fintype E] {J P M Wp Kc : Type} [Fintype J] [DecidableEq J]
variable (np : NormPar) (limb : (J → E) → ℕ → ℕ → E) (dig : (J → E) → ℕ → ℕ → E)
variable (msk : ℕ → J) (sW : ℕ) (Ex : ExtSpec) (msg : M → J → E)
variable (Q0 : IOR.Rels Kc P Ex (M × Wp)) (s : SqSize)
variable (ztN ztH : P → Fin s.lt → E) (tabN tabH : P → (J → E) → Fin 2 → ℕ → E)
variable (join : P → E → E → (J → E) → Prop)

/-- The row's rounds are the list ownShape. -/
theorem row_shape (lkW rows : ℕ) :
    (rowR np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).shape =
      ownShape (rowRounds s lkW rows) (sqKind (P := P) limb (sqSlot msk sW) s).par
        (tokT (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind).par
        (tokT (kN s.lt (sPvOf sW s))
          (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatN.world).par
        (tokT (kH s.lt s.lPd (sPvOf sW s))
          (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatH.world).par := by
  show (([IOR.drawRound (Fin s.lt → E)] ++ ([batRound E 9] ++ (shapeS _ ++ [IOR.drawRound E]))) ++
      ([batRound E 7] ++ shapeR _)) ++ shapeR _ ++ shapeR _ =
    [IOR.drawRound (Fin s.lt → E)] ++ [batRound E 9] ++ (shapeS _ ++ [IOR.drawRound E]) ++
      [batRound E 7] ++ shapeR _ ++ shapeR _ ++ shapeR _
  simp only [List.append_assoc]

/-- **The row's rounds fit the plan's entries**, one by one and in order. -/
theorem row_fits (w lkW rows : ℕ) :
    List.Forall₂ (Fits E) (rowR np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).shape
      (headOwnList w (rowRounds s lkW rows)) := by
  rw [row_shape np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join lkW rows]
  exact own_fits w (rowRounds s lkW rows) _ _ _ _ rfl Fintype.card_bool rfl (Fintype.card_fin 4)
    rfl (Fintype.card_fin 2) rfl (Fintype.card_fin 2)

end

end OnBytes.Tie.Pv.Head

#print axioms OnBytes.Tie.Pv.Head.row_shape
#print axioms OnBytes.Tie.Pv.Head.row_fits
