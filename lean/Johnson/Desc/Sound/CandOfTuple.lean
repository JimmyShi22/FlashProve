-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/CandOfTuple.lean: FOR THE PROXIMITY TEST's ONE TUPLE OF CANDIDATES, AT THE
MEMBERS OF THE RULE OF COMPOSITION: ITS PREMISE (s1) ALONE. Two theorems, proved; none is on the
tuple.
  `rowAtW_eq` (proved, by unfolding): the row's symbol out of a tenant's words at a leaf, as
    Johnson/Desc/K12/Law/StrRows.lean copied it (`rowAtW`), IS `rowAt` (MsgSig.lean).
  `wordsOf_eq_strOf` (proved): (s1): A MEMBER's WORD OFF THE PLAIN STRINGS (`wordsOf`) IS "THE WORD
    AS SENT" OFF A WRITTEN ORACLE (`strOf`, Johnson/Desc/K12/Law/StrOf.lean), where the tenant's
    main and mask words at each leaf are the stretches of the written oracle's column from the
    tenant's first words on (hM, hZ): a call of `strOf_rowAt`.
  This file holds no theorem on the tuple itself. That what the first arm of `tuple_words_or_few`
    (Johnson/Desc/K12/Law/TupleWords.lean) says of its tuple c', member by member, gives one tuple c
    over `Mem` with `CandAt` at every member of `mine` is not proved here. `tuple_of_port`
    (Johnson/Desc/Sound/CandMove.lean) makes such a tuple from a family of candidates.
Limits. PREMISES, AT EACH MEMBER j OF THE GROUP: mem j's entry is the member's shape with the radius
e0s j (s3); hM, hZ, the main degree (s1); the record holds the member's one sample row as
`Send.form`'s row at a seed with the answer as its target, and the reading smp of the record gives a
sample with that answer at a seed that the library's sample map reads as it reads that seed (s2).
mem is one to one and `mine` are its values. Nothing says that the row's ins hold of the witness
that c lays (`AllSay` at `wordsT D c'` is not carried here). NO GAME. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.CandMove
import Johnson.Desc.K12.Law.TupleWords
import Johnson.Desc.K12.Law.StrRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run

theorem rowAtW_eq : @H2K.Pin.rowAtW = @rowAt := by
  funext b ws k
  cases b <;> rfl

/-- **(s1): a member's word off the plain strings is the word as sent off a written oracle.** -/
theorem wordsOf_eq_strOf (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (y : Strs)
    (i : Fin l.length) (L : OnBytes.Slice.Lay) (d : PQ.RD) (o : (wRound d).Orc)
    (hdeg : (l.get i).1.mainDeg = 1 ∨ (l.get i).1.mainDeg = 3)
    (hM : ∀ x k, k < (l.get i).1.mainRows * (l.get i).1.mainDeg →
      (((wordOf G y (seat i).1 (seat i).2 x).map (·.main)).getD []).getD k 0 =
        OnBytes.Slice.wordAt d o x (L.oM + k))
    (hZ : ∀ x k, k < (l.get i).1.maskRows * 3 →
      (((wordOf G y (seat i).1 (seat i).2 x).map (·.mask)).getD []).getD k 0 =
        OnBytes.Slice.wordAt d o x (L.oZ + k)) :
    wordsOf G cs l seat y i = H2K.Pin.strOf cs (l.get i).1 (l.get i).2 L d o := by
  rw [H2K.Pin.strOf_rowAt cs (l.get i).1 (l.get i).2 L d o
    (fun x => ((wordOf G y (seat i).1 (seat i).2 x).map (·.main)).getD [])
    (fun x => ((wordOf G y (seat i).1 (seat i).2 x).map (·.mask)).getD []) hdeg hM hZ, rowAtW_eq]
  funext p
  cases p <;> rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rowAtW_eq
#print axioms VerifiableInference.Desc.Sound.wordsOf_eq_strOf
