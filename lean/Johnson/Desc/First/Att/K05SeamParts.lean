-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeamParts.lean: THE KIND's OWN TEXT AND THE TEXT THAT SAYS YES TO ALL ARE
PARTED AT THE LAW's OWN ERRORS: at bearErr (written p) _ (… .ch.eps Ex), the errors of
K05_keepsW_piece (Att/K05KeepsPiece.lean), the yes-text (k5Yes, Att/K05SeamSilly.lean) has not the
law's form.

Main names:
  `entries_work`, `entriesOf_work`, `written_work`: a written round of the kind bears no work or the
    policy's p.work.
  `law_ltPass`: kap = 4; the plan's record is recOf P rows; k5Held k (zOf p.own) on the kind's
  ROUNDS
    with the format's kinds says yes; p.work < k: then each of the law's errors is below its round's
    number of verifier's messages that pass the work (LtPass).
  `K05_yes_fails`: so KeepsW on on' R R' fails of the yes-text at these errors, wherever there are a
    statement a with "on" and a world w such that what stands in front fails at (a, w) and what
    stands behind holds at w at the record as it came, whatever the oracles.

Limits. The Boolean k5Held is evaluated in no file of this tree. That there are such a and w at the
law's own letters is a premise: no member is shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Kinds
import Johnson.Desc.First.Att.K05SeamSilly

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb OnBytes OnBytes.Model Cb.Pv.Att Inst.Model OnBytes.Maker
open OnBytes.Tie.Pv.Att (recOf)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run (ckP)
open scoped ENNReal

theorem entries_work (k : MaskedSum.Call) : ∀ e ∈ MaskedSum.entries k, e.work = 0 := by
  intro e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain rfl := List.mem_singleton.1 he
      rfl
    · obtain ⟨v, _, rfl⟩ := List.mem_map.1 he
      rfl
  · cases hk : k.ends with
    | none => rw [hk] at he; cases he
    | some x =>
      rw [hk] at he
      rcases List.mem_cons.1 he with rfl | he
      · rfl
      · obtain rfl := List.mem_singleton.1 he
        rfl

theorem entriesOf_work : ∀ (l : List Stage) (lead : ℕ), ∀ e ∈ entriesOf lead l, e.work = 0
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, e, h => entriesOf_work l (lead + n) e h
  | .sum vs x :: l, lead, e, h => by
    rcases List.mem_append.1
      (show e ∈ MaskedSum.entries ⟨lead, vs, some x⟩ ++ entriesOf 0 l from h) with h | h
    · exact entries_work _ e h
    · exact entriesOf_work l 0 e h
  | .batch rows :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rfl
    · exact entriesOf_work l 0 e h
  | .point n :: l, lead, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · rfl
    · exact entriesOf_work l 0 e h

/-- A written round of the kind bears no work, or the policy's. -/
theorem written_work (p : Par) : ∀ d ∈ written p, d.entry.work = 0 ∨ d.entry.work = p.work := by
  intro d hd
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
  unfold rounds at hr
  obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 hr
  show (if e0.drawE == 0 then e0 else { e0 with work := p.work }).work = 0 ∨
    (if e0.drawE == 0 then e0 else { e0 with work := p.work }).work = p.work
  split
  · exact Or.inl (entriesOf_work _ _ e0 h0)
  · exact Or.inr rfl

/-- **The law's own errors are each below the number of messages that pass the work.** -/
theorem law_ltPass {M X : Type} (P : OwnPar Cb.Gl.E M X) (hk4 : P.kap = 4) (rows : ℕ) (p : Par)
    (hrec : p.own = recOf P rows) (Ex : ExtSpec) (k : ℕ)
    (hc : k5Held k (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true)
    (hw : p.work < k) :
    LtPass (ckP .two) (written p)
      (bearErr (written p) _ ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.eps Ex)) :=
  ltPass_of_below (ckP .two) k (written p) _
    (K05_below_fmt P hk4 rows p hrec Ex k (written p) (seam_entries p) (seam_kinds p) hc)
    fun d hd => by
      rcases written_work p d hd with h | h <;> rw [h]
      · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hw
      · exact hw

/-- **At the law's own errors the yes-text has not the law's form.** -/
theorem K05_yes_fails {M X S Cl W : Type} {F : Frame} (P : OwnPar Cb.Gl.E M X) (hk4 : P.kap = 4)
    (rows : ℕ) (p : Par) (hrec : p.own = recOf P rows) (Ex : ExtSpec) (k : ℕ)
    (hc : k5Held k (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true)
    (hw : p.work < k) (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (base : ℕ)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (a : S × F.E.Str) (w : W)
    (ha : on a) (hR : ¬ R a w) (hR' : ∀ y', R' (a.1, y') w) :
    ¬ (pieceAt (W := W) (F := F) (k5Yes seat claims p) p base
        (bearErr (written p) _ ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.eps Ex))).ior.red.KeepsW
      on on' R R' (bearErr (written p) _ ((P.own (theMeans Cb.Gl.E P.D P.C P.kap)).ch.eps Ex)) :=
  yes_not_keeps seat claims p base _ (law_ltPass P hk4 rows p hrec Ex k hc hw) on on' R R' a w ha hR
    hR'

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.law_ltPass
#print axioms VerifiableInference.Desc.First.Att.P.K05_yes_fails
