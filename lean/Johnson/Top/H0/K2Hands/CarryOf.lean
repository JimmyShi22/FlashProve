-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/CarryOf.lean: the code switch: WHAT STANDS IN FRONT OF A SWITCH, AS
ONE SENTENCE ON A RECORD, ITS ORACLES AND A WITNESS, WITH THE OPEN WORD's CODE WORD UNDER A «THERE
IS»: the carried claim holds of a message whose encoding is near the open word.

The stage in front of the typed code switch (Johnson/Top/H/SwitchSel.lean's switchSel) is the
target stage of the fold in front of it, with the claim stated by its vector (stage_is, by rfl). In
the library's stage the open word's (message, randomness) is a COMPONENT OF THE WITNESS. Whoever
wants the sentence of a witness that does not hold that pair takes it under a «there is».
  carryOf      the sentence, general in the fold's data D and in two readings, which are LETTERS:
               fa (the typed statement AND the typed strings, off a record and the oracles
               TOGETHER: the open word is the fold of the committed words by elements that stand in
               the record: StrMade.lean) · rest (the witness's open messages' part and its carried
               part):
               there is a pair c = (message, randomness) such that the stage's relaxed relation
               holds at fa a y of ((rest a y w).1, (c, (rest a y w).2))
  carryOf_iff  THE SENTENCE WRITTEN OUT, by unfolding alone: there is c such that: each open message
               decodes, with its sample, to the witness's; the open word differs from the encoding
               of c in at most e positions; THE CLAIM HOLDS OF c's MESSAGE; each held member's slot
               of the open word decodes, with its held sample, to its part of c's message; the
               carried joint A₀ holds
  carryOf_of   FROM THE LIBRARY's RELATION: the relation at fa a y of a typed witness u whose two
               outer parts are rest's gives the sentence: c is u's pair
  holds_vec    at the vector's data the claim is: the sum of vector * message is the target
  carryOf_claim  so, where fa reads the claim as (τ, v): there is c, near the open word, with
               the sum of v * (c's message) = τ
  stage_is     the stage in front of switchSel is that stage
fa IS ONE READING, off record and oracles together, for the typed statement and the typed strings;
rest is one reading for the witness's two parts, and may read record and oracles as well.
LIMITS. A DEFINITION AND ITS UNFOLDING: NO LAW. fa and rest are letters: nothing here reads a
record, an oracle or a witness; that fa's claim is the record's carried rows' is TiePaid.lean's
FrontAt (target, vector), a premise there; that fa's open word is what the text hears is its strIs,
a theorem at StrMade.lean's strOpen. Whether the sentence can be met is not shown. No soundness is
claimed.
-/
import Johnson.Top.H.SwitchSel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

section
variable {Kc : Type} (D : LdFoldD GE Kc) {A Y W : Type} (fa : A → Y → D.tgt.X × D.tgt.Ex.Str)
  (rest : A → Y → W → D.S₂.Wit × D.Wp)

/-- **What stands in front of a switch**, the open word's code word under a «there is». -/
def carryOf : A → Y → W → Prop := fun a y w =>
  ∃ c : D.Cf.N.Wit, (D.tgt.S.over D.tgt.A).relR (fa a y) ((rest a y w).1, (c, (rest a y w).2))

/-- **The sentence written out.** -/
theorem carryOf_iff (a : A) (y : Y) (w : W) :
    carryOf D fa rest a y w ↔ ∃ c : D.Cf.N.Wit,
      (∀ i, D.S₂.decs (fa a y).1.2 (fa a y).2.2 i = some ((rest a y w).1 i).1) ∧
      offCnt (fa a y).2.1.1 (D.Cf.N.enc c.1 c.2) ≤ D.e ∧
      D.slf.Holds (fa a y).1.1.1.1 c.1 ∧
      (∀ k, (D.held.o k).decW (D.held.sW k (fa a y).2.1.1) ((fa a y).1.1.1.2 k) =
        some (D.held.msg c.1 k)) ∧
      D.A₀.relR ((fa a y).1.1.2, (fa a y).2.1.2)
        (D.rd (D.S₂.msgs (rest a y w).1) (D.held.msg c.1), (rest a y w).2) :=
  ⟨fun ⟨c, h1, ⟨h2, h3⟩, h4, h5⟩ => ⟨c, h1, h2, h3, h4, h5⟩,
    fun ⟨c, h1, h2, h3, h4, h5⟩ => ⟨c, h1, ⟨h2, h3⟩, h4, h5⟩⟩

/-- **From the library's relation.** -/
theorem carryOf_of {a : A} {y : Y} {w : W} {u : D.tgt.W}
    (h : (D.tgt.S.over D.tgt.A).relR (fa a y) u) (h1 : u.1 = (rest a y w).1)
    (h2 : u.2.2 = (rest a y w).2) : carryOf D fa rest a y w := by
  obtain ⟨u1, c, u2⟩ := u
  obtain rfl : u1 = (rest a y w).1 := h1
  obtain rfl : u2 = (rest a y w).2 := h2
  exact ⟨c, h⟩

end

section
variable {Kc : Type} (D : LdFoldD GE Kc)

/-- At the vector's data the claim is a sum. -/
theorem holds_vec (x : GE × (D.Cf.J → GE)) (m : D.Cf.J → GE) :
    (vecD D).slf.Holds x m ↔ ∑ j, x.2 j * m j = x.1 := Iff.rfl

variable {A Y W : Type} (fa : A → Y → (vecD D).tgt.X × (vecD D).tgt.Ex.Str)
  (rest : A → Y → W → (vecD D).S₂.Wit × (vecD D).Wp)

/-- Where fa reads the claim as (τ, v). -/
theorem carryOf_claim {a : A} {y : Y} {w : W} {τ : GE} {v : D.Cf.J → GE}
    (hx : (fa a y).1.1.1.1 = (τ, v)) (h : carryOf (vecD D) fa rest a y w) :
    ∃ c : D.Cf.N.Wit, offCnt (fa a y).2.1.1 (D.Cf.N.enc c.1 c.2) ≤ D.e ∧
      ∑ j, v j * c.1 j = τ := by
  obtain ⟨c, -, h2, h3, -, -⟩ := (carryOf_iff (vecD D) fa rest a y w).1 h
  rw [hx] at h3
  exact ⟨c, h2, h3⟩

end

section
variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : Sh.Cf.J → (sigOf cs l).Ent) (iQ : Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

/-- The stage in front of the typed code switch. -/
theorem stage_is :
    Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw =
      (vecD (Hd.foldD Sb sl Z A₀)).tgt := rfl

end

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.carryOf_iff
#print axioms VerifiableInference.Desc.First.K2Hands.carryOf_of
#print axioms VerifiableInference.Desc.First.K2Hands.carryOf_claim
#print axioms VerifiableInference.Desc.First.K2Hands.stage_is
