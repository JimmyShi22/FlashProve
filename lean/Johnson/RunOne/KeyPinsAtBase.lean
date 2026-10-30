-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyPinsAtBase.lean: The key file, the shared chain: THE ONE PREMISE ON THE READING THAT THE THREE ROWS WITHOUT A DRAW (2.3 · 2.6 · 2.8) TAKE FROM OTHER FILES, PinsStay (Johnson/Desc/Key/KeyLetters.lean), IS MET AT THE TABLES' FILES' OWN READING BaseSt.h₂ (Johnson/RunOne/KeyOneReading.lean): at 2.3 | 2.6 under SmGroups (Johnson/RunOne/KeyLettersAt.lean), at 2.8 under SmReads (KeyOneReading.lean). Three theorems; no definition.
NOT HERE, SO THAT NO TWIN GROWS: the like for the three rows that draw (2.1 · 2.4 · 2.7): other files have it (samePins_h₂, Johnson/RunOne/KeyReadsH2.lean | pinsStay_h₂_zeta, Johnson/RunOne/KeyRow27Pins.lean: called at the premise hP of KeyForward.lean's halves in the whole rows at the seat, Johnson/RunOne/KeyRowsWholeAtSeat.lean).

OBJECT. PinsStay T.h₂ at_ l (z, d) (z, d') at two records tied by RecLaid | Joined | SplitLaid (Johnson/Desc/Key/Laid/).
USER. r2_3_seat | r2_6_seat | r2_8_seat (Johnson/RunOne/KeyRowsAtSeat.lean), at G₂ := T.h₂: they
call pins_rec | pins_joined | pins_split, and hand on the condition on sm as a premise of their own
(hg : T.SmGroups at 2.3 and 2.6, hr : T.SmReads at 2.8).
LETTERS. T : BaseSt …, at_, l, z: free. No tie of T.arr to at_ is asked: pinsStay_h₂ (Johnson/RunOne/KeyLettersAt.lean) needs none.

THE CAUTION. These laws speak of the reading's SAMPLES and of the stored table's RECORD alone: one value in front and behind. THAT A BaseSt IS THE LIBRARY's (code · radius · sample · decoding) IS SHOWN NOWHERE: all its fields are letters.
IS IT EMPTY HERE? Two premises each. (1) The plain facts: by a walk of this project (in a file that is not in this library: evaluated at two stored key files, made-up weights) the three blocks say yes there, and their yes gives the plain facts (Johnson/RunOne/KeyBridges23.lean): met there. (2) A condition on the letter sm: that it reads neither a message's list «groups» (SmGroups) nor its ledger (SmReads). An sm that gives every message the same sample meets both, so the conditions can be met; WHETHER THE SAMPLE THAT THE LIBRARY WANTS MEETS THEM IS FOR WHOEVER FILLS sm: NOT SHOWN.

WHY IT HOLDS. T.h₂ reads the table's messages 0 · 1 · 2 in what was handed (z: the same on both sides) and 3 · 4 · 5 in the chain's own statement, by number, at the statement's codes. (rec_gamma) and the joinings leave the codes and turn, in a message's record, its list «groups» alone; SPLIT o_sp's ledger alone.

Limits. NOT FOR ROW 3.0: at the last chain's reading T.h₃ Omega's seat is read in the border's copy in front and in the own statement behind, under another number: there the reading must do something: not typed here. Nothing on chance. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.RunOne.KeyLettersAt
import Johnson.RunOne.KeyRow23
import Johnson.RunOne.KeyRow28

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState)
open Desc.Plain (Par)

section
variable {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec) (at_ : Where) (l : List Nat) (z : P₂) (d d' : St₂)

/-- **2.3**, where sm does not read a message's list of groups. -/
theorem pins_rec (hg : T.SmGroups) {p : Par} {GU : OnBytes.Group} {rows : List OnBytes.Row} (P : RecLaid p d d' GU rows) : PinsStay T.h₂ at_ l (z, d) (z, d') :=
  pinsStay_h₂ T at_ l z d d' fun o => smAt_congr T d.st d'.st o P.codes (by
    cases hx : d.st.oracles[o]? with
    | none => rw [rec_none P o hx]
    | some x0 =>
      obtain ⟨gs, e⟩ := rec_msg P o x0 hx
      rw [e]
      exact hg _ o x0 gs)

/-- **2.6**, where sm does not read a message's list of groups. -/
theorem pins_joined (hg : T.SmGroups) {GU GO : OnBytes.Group} (J : Joined d d' GU GO) : PinsStay T.h₂ at_ l (z, d) (z, d') :=
  pinsStay_h₂ T at_ l z d d' fun o => smAt_congr T d.st d'.st o J.codes (by
    cases hx : d.st.oracles[o]? with
    | none => rw [joined_none J o hx]
    | some x0 =>
      obtain ⟨gs, e⟩ := J.msgs o x0 hx
      rw [e]
      exact hg _ o x0 gs)

/-- **2.8**, where sm does not read a message's ledger. -/
theorem pins_split (hr : T.SmReads) {S : LinShape} {GU GO : OnBytes.Group} {x : OnBytes.Oracle} {lg : OnBytes.Ledger} {n : Nat} {row : OnBytes.Row} {mu : E}
    (P : SplitLaid S d d' GU GO x lg n row mu) : PinsStay T.h₂ at_ l (z, d) (z, d') :=
  pinsStay_h₂ T at_ l z d d' fun o => smAt_congr T d.st d'.st o P.codes (by
    cases hx : d.st.oracles[o]? with
    | none => rw [split_none P o hx]
    | some x0 =>
      obtain ⟨L, e⟩ := split_msg P o x0 hx
      rw [e]
      exact hr _ o x0 L)

end

end Johnson.RunOne.KeyRows23
