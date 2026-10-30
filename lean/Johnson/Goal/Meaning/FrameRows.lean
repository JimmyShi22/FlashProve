-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/FrameRows.lean: what the frame of a code switch reads of the carried rows; and
the shapes at the head of the list of a switch's new messages.

switchFrame S old T g anew (OnBytes/Iop/Cs.lean:412) is handed the single rows "old" that the last
closing returned. These hold challenges, forms and a target, which a prover and the drawn elements
have made. Of them the frame reads five public things alone.
  SameRows old old': the same code, maskCode, masks, keptRows, and the same kept members
    (switchKept).
  parts_rows, frame_rows: at two such rows switchParts and switchFrame have one value, at all other
    arguments.
  heads_of: a list l of pairs whose first components begin with T.shape and the shapes of T.kept has
    T.shape at 0 and T.kept[i].shape at 1 + i.
Not claimed: that a record's carried rows have a plan's five things.
-/
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes

/-- The five things that the frame reads of the carried rows. -/
structure SameRows (old old' : SingleRows) : Prop where
  code : old'.code = old.code
  maskCode : old'.maskCode = old.maskCode
  masks : old'.masks = old.masks
  keptRows : old'.keptRows = old.keptRows
  kept : switchKept old' = switchKept old

theorem parts_rows {old old' : SingleRows} (h : SameRows old old') (S : Statement) :
    switchParts S old' = switchParts S old := by
  unfold switchParts
  rw [h.code, h.maskCode, h.masks, h.keptRows, h.kept]

/-- **The frame reads five things of the carried rows.** -/
theorem frame_rows {old old' : SingleRows} (h : SameRows old old') (S : Statement)
    (T : SwitchTarget) (g : Nat) (anew : Array Nat) :
    switchFrame S old' T g anew = switchFrame S old T g anew := by
  unfold switchFrame
  rw [parts_rows h, h.code, h.maskCode, h.masks, h.kept]

/-- The shapes at the head of the list of the new messages. -/
theorem heads_of {α : Type} {T : SwitchTarget} {l : List (OracleShape × α)}
    {rest : List OracleShape}
    (h : l.map (·.1) = T.shape :: (T.kept.toList.map (·.shape) ++ rest)) :
    (∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = T.shape) ∧
      ∀ i (hi : i < T.kept.size), ∃ h' : 1 + i < l.length,
        (l.get ⟨1 + i, h'⟩).1 = T.kept[i].shape := by
  have hlen : l.length = 1 + (T.kept.size + rest.length) := by
    have e := congrArg List.length h
    simp only [List.length_map, List.length_cons, List.length_append, Array.length_toList] at e
    omega
  have at_ : ∀ j (hj : j < l.length), (l.get ⟨j, hj⟩).1 =
      (T.shape :: (T.kept.toList.map (·.shape) ++ rest))[j]'(by rw [← h]; simpa using hj) := by
    intro j hj
    have e : (l.map (·.1))[j]'(by simpa using hj) = (l.get ⟨j, hj⟩).1 := by simp
    rw [← e]
    congr 1
  refine ⟨⟨by omega, ?_⟩, fun i hi => ⟨by omega, ?_⟩⟩
  · rw [at_]
    rfl
  · rw [at_]
    have e : 1 + i = i + 1 := Nat.add_comm 1 i
    simp only [e, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simpa using hi)]
    simp

#print axioms frame_rows
#print axioms heads_of

end Meaning.K2
