-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/FillK5.lean: KIND K5's LAYER OF THE FILLING OF THE TABLE OF JOINTS' MEANING: fillK5 : K5Data → Meaning P W → Meaning P W := pub is the layer's half with code (Johnson/Desc/First/Att/Door/PubK5.lean) over what was there; more is what was there merged with K5's door's rows (Johnson/Desc/First/Att/Door/Door.lean); every other field as it was. No Mathlib.
THE THREE SORTS OF LEMMA: (i) fillK5_pub: by the make · (ii) fillK5_callerIn | _look | _readsThere | _okAt | _liveReq | _plain: what it lays at an attention link, AT EVERY Meaning · (iii) fillK5_else: every other item is handed on. fillK5_more.
K5's FILES FILL NO LETTER OF THE RELATION AND NO pubP: K5's six items say nothing but their Bools.
-/
import Johnson.Desc.First.Att.Door.PubK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First

/-- **Kind K5's layer.** -/
def fillK5 {P W : Type} (d : K5Data) (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubK5 d Mg.pub, more := Mg.more.merge more }

section
variable {P W : Type} (d : K5Data) (Mg : Meaning P W)

theorem fillK5_pub : (fillK5 d Mg).pub = pubK5 d Mg.pub := rfl

theorem fillK5_more : (fillK5 d Mg).more = Mg.more.merge more := rfl

theorem fillK5_callerIn {m : Nat} (h : d.isAtt m = true) (a : P × S) :
    (fillK5 d Mg).pub (.callerIn m) a = (d.first? m).any fun n => callerIn3B n a.2 := by
  show (if d.isAtt m then _ else _) = _
  rw [if_pos h]

theorem fillK5_look {m : Nat} (h : d.isAtt m = true) (a : P × S) :
    (fillK5 d Mg).pub (.look m) a = lookAttB a.2 := by
  show (if d.isAtt m then _ else _) = _
  rw [if_pos h]

theorem fillK5_readsThere {m : Nat} (h : d.isAtt m = true) (a : P × S) :
    (fillK5 d Mg).pub (.more (some m) "K5.readsThere") a = readsThereB d.W (d.ownOf m) a.2 := by
  show (if (d.isAtt m && "K5.readsThere" == "K5.readsThere") = true then _ else _) = _
  rw [h]
  rfl

theorem fillK5_okAt {m : Nat} (h : d.isAtt m = true) (a : P × S) :
    (fillK5 d Mg).pub (.more (some m) "K5.okAt") a =
      (d.W.A[m / 2]?).any fun p => okThereB (Att.P.geoOf p.S) a.2 := by
  show (if (d.isAtt m && "K5.okAt" == "K5.readsThere") = true then _
    else if (d.isAtt m && "K5.okAt" == "K5.okAt") = true then _ else _) = _
  rw [h]
  rfl

theorem fillK5_liveReq {m : Nat} (h : d.isAtt m = true) (a : P × S) :
    (fillK5 d Mg).pub (.more (some m) "K5.liveReq") a = Att.P.liveReqB (bornOf d.shape m) a.2 := by
  show (if (d.isAtt m && "K5.liveReq" == "K5.readsThere") = true then _
    else if (d.isAtt m && "K5.liveReq" == "K5.okAt") = true then _
    else if (d.isAtt m && "K5.liveReq" == "K5.liveReq") = true then _ else _) = _
  rw [h]
  rfl

theorem fillK5_plain {m : Nat} (h : d.isAtt m = true) (a : P × S) :
    (fillK5 d Mg).pub (.more (some m) "K5.plain") a = (d.W.A[m / 2]?).any fun p => plainThereB p.iU3 p.nW a.2 := by
  show (if (d.isAtt m && "K5.plain" == "K5.readsThere") = true then _
    else if (d.isAtt m && "K5.plain" == "K5.okAt") = true then _
    else if (d.isAtt m && "K5.plain" == "K5.liveReq") = true then _
    else if (d.isAtt m && "K5.plain" == "K5.plain") = true then _ else _) = _
  rw [h]
  rfl

/-- Every other item is handed on. -/
theorem fillK5_else (q : Pub) (h : k5Item d q = false) (a : P × S) : (fillK5 d Mg).pub q a = Mg.pub q a := by
  cases q with
  | callerIn m =>
    show (if d.isAtt m then _ else _) = _
    rw [if_neg (by simpa [k5Item] using h)]
  | look m =>
    show (if d.isAtt m then _ else _) = _
    rw [if_neg (by simpa [k5Item] using h)]
  | more sg n =>
    cases sg with
    | none => rfl
    | some m =>
      have h' : (d.isAtt m && n == "K5.readsThere") = false ∧ (d.isAtt m && n == "K5.okAt") = false ∧
          (d.isAtt m && n == "K5.liveReq") = false ∧ (d.isAtt m && n == "K5.plain") = false := by
        simp only [k5Item, Bool.and_eq_false_iff, Bool.or_eq_false_iff] at h
        rcases h with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        · simp [h]
        · simp [h1, h2, h3, h4]
      show (if (d.isAtt m && n == "K5.readsThere") = true then _
        else if (d.isAtt m && n == "K5.okAt") = true then _
        else if (d.isAtt m && n == "K5.liveReq") = true then _
        else if (d.isAtt m && n == "K5.plain") = true then _ else _) = _
      rw [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2]
      rfl
  | _ => rfl

end

#print axioms fillK5_pub
#print axioms fillK5_more
#print axioms fillK5_callerIn
#print axioms fillK5_look
#print axioms fillK5_readsThere
#print axioms fillK5_okAt
#print axioms fillK5_liveReq
#print axioms fillK5_plain
#print axioms fillK5_else

end H2K5.Door
