-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/WordsCongr.lean: a lemma for kind K1's law: words_congr.
THE STATEMENT: a member i of a sending's list l with l.get i = (s, e) and seat i = (j, t): the member's word in the reading of the whole list IS its word in the reading of the one-member list [(s, e)] at the seat (j, t): HEq, since the two words' types are `((sigOf cs ·).om ·).Str` at different lists.
WHY IT HOLDS: `sigOf cs l`'s member i is `portOmZ cs (l.get i).1 (l.get i).2` (Johnson/Pack/PortF.lean), and `wordAt` (Johnson/Desc/Sound/MsgSig.lean) reads l through that type alone and seat through `seat i` alone. `wordAtOne` says so by a definition: the word as a function of the member's own pair and seat.
IT IMPORTS Johnson.Desc.Sound.MsgSig ALONE. No axiom beyond Lean's three is meant; `#print axioms` at the foot.
-/
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)

/-- One member's word, off plain strings, AS A FUNCTION OF THE MEMBER's OWN SHAPE, RADIUS AND SEAT ALONE. -/
def wordAtOne (p : OnBytes.OracleShape × ℕ) (jt : ℕ × ℕ) (y : Strs) : (portOmZ cs p.1 p.2).Str
  | .inl x => fun r =>
      rowAt _ (((wordOf G y jt.1 jt.2 x.val).map (·.main)).getD []) r.1.val
  | .inr x => fun r =>
      rowAt _ (((wordOf G y jt.1 jt.2 x.val).map (·.mask)).getD []) r.1.val

/-- `wordAt` is `wordAtOne` at the member's pair and seat. -/
theorem wordAt_eq_one (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (y : Strs)
    (i : Fin l.length) : wordAt G cs l seat y i = wordAtOne G cs (l.get i) (seat i) y := by
  funext z
  cases z <;> rfl

/-- Equal pairs and seats give the same word, across the types. -/
theorem wordAtOne_heq (p q : OnBytes.OracleShape × ℕ) (a b : ℕ × ℕ) (y : Strs) (hp : p = q)
    (ha : a = b) : HEq (wordAtOne G cs p a y) (wordAtOne G cs q b y) := by
  subst hp
  subst ha
  exact HEq.rfl

/-- **words_congr**, general in the two lists: two members with one pair and one seat have one word. -/
theorem words_congr' (l l' : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (seat' : Fin l'.length → ℕ × ℕ) (y : Strs) (i : Fin l.length) (k : Fin l'.length)
    (hl : l'.get k = l.get i) (hs : seat' k = seat i) :
    HEq (wordsOf G cs l' seat' y k) (wordsOf G cs l seat y i) :=
  (heq_of_eq (wordAt_eq_one G cs l' seat' y k)).trans
    ((wordAtOne_heq G cs _ _ _ _ y hl hs).trans (heq_of_eq (wordAt_eq_one G cs l seat y i)).symm)

/-- **words_congr** (K01_law J2c): a member i with `l.get i = (s, e)` and `seat i = (j, t)`: its word is the word of the one-member list `[(s, e)]` at the seat `(j, t)`; at EVERY index k of that list (there is one), so that it fits however the caller writes its 0. -/
theorem words_congr (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (y : Strs)
    (i : Fin l.length) (s : OnBytes.OracleShape) (e j t : ℕ) (hl : l.get i = (s, e))
    (hs : seat i = (j, t)) (k : Fin [(s, e)].length) :
    HEq (wordsOf G cs [(s, e)] (fun _ => (j, t)) y k) (wordsOf G cs l seat y i) := by
  refine words_congr' G cs l [(s, e)] seat (fun _ => (j, t)) y i k ?_ hs.symm
  have hk : k = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (Nat.lt_one_iff.mp k.isLt)
  subst hk
  exact hl.symm

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.words_congr
#print axioms VerifiableInference.Desc.Sound.words_congr'
