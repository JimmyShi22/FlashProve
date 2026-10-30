-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngHolds.lean: IN FRONT OF A PROXIMITY TEST: THE RELATION AND THE CONDITION, IN THE WORDS OF THE KIND K12's OWN FILES. They stand here free of the frame of the table of joints; Johnson/RunOne/Law/RngRows.lean lays them into rows of that frame's type.
OBJECT. The statement and the group in front of a proximity test, and the word under test: the relation `Holds` and the condition `Cond`, in the words of the kind's law.
USER. Johnson/RunOne/Law/RngCond.lean (Cond), RngSeam.lean and the rows of the table of joints (Holds).
LETTERS. The stage, the radius, the statement, the group's number, the word and the witness are free.
  `Holds s e St g y w`: THE RELATION IN FRONT: the group g of the statement St is there with its layout; the witness w's encoding is within e positions of the group's word y; and ALL THE ROWS THAT THE BATCHING WILL TAKE (the claims that lie open on the group, then the members' sample rows: `runRows`) say their claims of
    the words that w's own tables hold.
  `noneNear_iff`: that it has no witness is `NoneNear` (Johnson/Desc/K12/Law/BatJoint.lean), to the letter: the premise of the batching's converse.
  `Cond s e St g y`: THE CONDITION IN FRONT: the stage's sizes are in order; the radius is below the distance; the test combineAt says yes at the statement with the test begun; the layout's four numbers are the stage's; the word has rows of zeros wherever no member has a real row (`RowsBlank`).
  `cond_of_asks`: where the seat's asking (asksOnRecord) has returned, the condition's public clauses hold: what is left of `Cond` is the stage's sizes, the radius, and `RowsBlank`.
Limits. Nothing says that `Cond` and `Holds` are met anywhere. Nothing on soundness.

-/
import Johnson.Desc.K12.Law.BatJoint
import Johnson.Desc.K12.Law.FirstOkLaw
import Johnson.RunOne.Law.RngAsked

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngHolds
open Iop Cb OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open H2K.ClaimSays (NoneNear RowsBlank wordsOf tabOf)
open VerifiableInference.Desc.Key (asksOnRecord)
open VerifiableInference.Desc.K12 (T12 P12)

/-! ## 1 The relation and the condition in front -/

/-- **The relation in front.** -/
def Holds (s : Sg) (e : ℕ) (St : Statement) (g : Nat) (y : s.cIn.Word) (w : s.cIn.N.Wit) : Prop :=
  ∃ G L, St.groups[g]? = some G ∧ St.layout g = some L ∧
    offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e ∧
    AllSay rdE (begun St g G) (runRows St G).toList (wordsOf (begun St g G) L (tabOf s w.1))

/-- That it has no witness is the premise of the batching's converse, to the letter. -/
theorem noneNear_iff (s : Sg) (e : ℕ) {St : Statement} {g : Nat} {G : Group} {L : GroupLayout}
    (hG : St.groups[g]? = some G) (hL : St.layout g = some L) (y : s.cIn.Word) :
    (∀ w, ¬ Holds s e St g y w) ↔ NoneNear s e (begun St g G) L (runRows St G) y := by
  constructor
  · intro h w hw ha
    exact h w ⟨G, L, hG, hL, hw, ha⟩
  · rintro h w ⟨G', L', hG', hL', hw, ha⟩
    obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
    obtain rfl : L' = L := Option.some.inj (hL'.symm.trans hL)
    exact h w hw ha

/-- **The condition in front.** -/
def Cond (s : Sg) (e : ℕ) (St : Statement) (g : Nat) (y : s.cIn.Word) : Prop :=
  s.Sized ∧ e < s.d ∧ ∃ G L, St.groups[g]? = some G ∧ St.layout g = some L ∧
    combineAt (begun St g G) g ⟨L, runRows St G⟩ = true ∧
    L.k = s.h + s.g ∧ L.h = s.h ∧ 2 ^ L.logEll = s.C.l ∧ 2 ^ L.logEllZk = s.Z.l ∧
    RowsBlank s (begun St g G) L y

/-! ## 2 What the seat's asking gives of the condition -/

/-- Where the asking has returned, the condition's public clauses hold. -/
theorem cond_of_asks {p : P12} {t : T12} (ha : asksOnRecord p t = .ok ()) {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} (hs : p.nums.stages = a :: rest) (e : ℕ)
    (hz : (H2K.First.sg a).Sized) (he : e < (H2K.First.sg a).d) (y : (H2K.First.sg a).cIn.Word)
    (hy : ∀ G L, t.st.groups[t.g]? = some G → t.st.layout t.g = some L →
      RowsBlank (H2K.First.sg a) (begun t.st t.g G) L y) :
    Cond (H2K.First.sg a) e t.st t.g y := by
  obtain ⟨G, L, a', rest', hG, hL, hs', _, a2, a3, _, _⟩ := RngAsked.asksRecord_ok ha
  obtain ⟨rfl, _⟩ := List.cons.inj (hs'.symm.trans hs)
  obtain ⟨f1, f2, f3, f4⟩ := RngAsked.four_of_ok a3
  exact ⟨hz, he, G, L, hG, hL, a2, f1, f2, f3, f4, hy G L hG hL⟩

end Johnson.RunOne.Law.RngHolds

#print axioms Johnson.RunOne.Law.RngHolds.noneNear_iff
#print axioms Johnson.RunOne.Law.RngHolds.cond_of_asks
