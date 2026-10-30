-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerAtSeam.lean: WHAT THE FILLING OF RECORD GIVES INSIDE THE PROMISE AT A
BORDER, BY NAME, FOR WHOEVER TYPES THE LAST CALL AT THE SEAM OF THE TWO PROXIMITY TESTS. Each is a
projection of beside_of_on (Johnson/Desc/K14/Law/LedgerNineTen.lean) through EK_iff and the tests'
own iffs: no new content.

  codes_of_on     the record's codes are the plan's.
  tidy_of_on      the statement is tidy (so in order, its kinds open).
  shared_of_on    sharedX (book · seats · members · sizes).
  msgU_of_on, msgO_of_on, msgS_of_on   behind border 2 | 5 | 5: the record's message number 0 | nO |
                  nO + 1 is there, with the plan's whole shape, the mark, and as many sample rows as
                  the shape has answers.
What is not claimed. No soundness; no level. NO MEMBER IS SHOWN.

-/
import Johnson.Desc.K14.Law.LedgerNineTen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Cb Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence

variable {Cells : Type} (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (Pm₁ : PromMeaning St) (Q : P14) (n nU nO : ℕ)
  (sO : OracleShape × OracleShape × OracleShape × (ℕ → St → Bool))
  (cs : Codes) {Xi P₁ Cl Tok : Type} (G : FileDescription Xi) (ms : List Mem) (N : NumbersS)
  (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ) (sentU : Array OracleNotice)
  (layU layO : TreeLay) (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece
      (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))) (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
  (ha : onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc true f l k a)

include ha

theorem shared_of_on : sharedX Q sentU layU layO k a.1.2 = true :=
  (beside_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a ha).1

theorem ek_of_on : EK Q sO nO k a.1.2 = true :=
  (beside_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a ha).2.2.1

theorem codes_of_on : a.1.2.st.codes = Q.codes :=
  (codX_iff Q k _).1 ((EK_iff Q sO nO k _).1
    (ek_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a ha)).1

theorem tidy_of_on : OnBytes.Means.Tidy a.1.2.st :=
  (tidY_iff k _).1 ((EK_iff Q sO nO k _).1
    (ek_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a ha)).2.2.1

theorem msgU_of_on (hk : 2 < k) : ∃ x, a.1.2.st.oracles[0]? = some x ∧ x.shape = sO.1 ∧
    x.sampled = true ∧ x.sampleRows.size = sO.1.answers :=
  ((msgY_iff _ _ _ k _).1 ((EK_iff Q sO nO k _).1
    (ek_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a
        ha)).2.2.2.1).resolve_left
    (by omega)

theorem msgO_of_on (hk : 5 < k) : ∃ x, a.1.2.st.oracles[nO]? = some x ∧ x.shape = sO.2.1 ∧
    x.sampled = true ∧ x.sampleRows.size = sO.2.1.answers :=
  ((omY_iff _ _ k _).1 ((EK_iff Q sO nO k _).1
    (ek_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a ha)).2.1).resolve_left
    (by omega)

theorem msgS_of_on (hk : 5 < k) : ∃ x, a.1.2.st.oracles[nO + 1]? = some x ∧ x.shape = sO.2.2.1 ∧
    x.sampled = true ∧ x.sampleRows.size = sO.2.2.1.answers :=
  ((msgY_iff _ _ _ k _).1 ((EK_iff Q sO nO k _).1
    (ek_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a
        ha)).2.2.2.2.1).resolve_left
    (by omega)

/-- The letter that is laid beside. -/
theorem letter_of_on : sO.2.2.2 k a.1.2 = true :=
  ((EK_iff Q sO nO k _).1
    (ek_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l k a ha)).2.2.2.2.2

end Desc.K14.Law

#print axioms Desc.K14.Law.shared_of_on
#print axioms Desc.K14.Law.codes_of_on
#print axioms Desc.K14.Law.tidy_of_on
#print axioms Desc.K14.Law.msgU_of_on
#print axioms Desc.K14.Law.msgO_of_on
#print axioms Desc.K14.Law.msgS_of_on
#print axioms Desc.K14.Law.letter_of_on
