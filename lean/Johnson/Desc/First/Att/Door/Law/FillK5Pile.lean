-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/FillK5Pile.lean: KIND K5: K5FillRel.pile (Johnson/Desc/First/Att/K05Riders.lean: "the pile's rows are true" rides BACK over the kind's lay) AT THE LAYER fillK13's OWN TERM (Johnson/Desc/K13/Law/FillK13.lean: pile := fun x _ w => RowsTrue (D.rw x) x.2 w; mgAll pays "Mg1.pile = (fillK13 (d13 𝔇) Mg).pile" by rfl). The rows on the table (S.rows) are what goes out's pending rows wherever an attention segment is open: the lay leaves them. UNDER ONE FACT ON THAT LAYER's LETTER rw: it answers alike at the verifier's state in front of and behind the kind's lay: PAID BY WHOEVER FILLS rw. Mathlib beneath.
import Johnson.Desc.First.Att.Door.Law.LayKeeps
import Johnson.Desc.K13.Law.FillK13

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (behind hear Heard)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13 RowsTrue)

theorem rows_behind {s : S} {a : AttOwn} (h : Heard) (G : Fork) (e : s.here = .att a) : (behind s a h G).rows = s.rows := by
  show (behind s a h G).out.pending = s.rows
  unfold S.rows
  rw [e]
  rfl

theorem at_pile {Pp W : Type} {nR : Nat} (d : K5Data) (Mg1 Mg0 : Meaning Pp W) (π : Pp) (D13 : DataK13 Pp W nR)
    (hpile : Mg1.pile = (fillK13 D13 Mg0).pile)
    (hrw : ∀ s a h G, s.here = .att a → D13.rw (π, behind s a h G) = D13.rw (π, s))
    (s : S) (a : AttOwn) (h : Heard) (G : Fork) (y y' : Strs) (w : W) (e : s.here = .att a) :
    (fillK5 d Mg1).pile (π, behind s a h G) y' w → (fillK5 d Mg1).pile (π, s) y w := by
  show Mg1.pile _ _ w → Mg1.pile _ _ w
  rw [hpile]
  show RowsTrue (D13.rw (π, behind s a h G)) (behind s a h G) w → RowsTrue (D13.rw (π, s)) s w
  rw [hrw s a h G e]
  unfold RowsTrue
  rw [rows_behind h G e]
  exact fun x => x

#print axioms rows_behind
#print axioms at_pile

end H2K5.Door
