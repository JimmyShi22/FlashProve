-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Alike.lean: TWO STATEMENTS WITH THE SAME CODES AND THE SAME CORE OF
EACH ORACLE MESSAGE (shape, sampled, stored sample rows, pad: `core`, Returns/Joins.lean) ARE ALIKE
TO THOSE PREMISES OF THE LAW ON THE STEP BEHIND THE SENDING THAT READ NO GROUP: so what of these
holds in front of the joins holds behind them. (The tables' sizes and the forms: `TablesFit.make`,
Returns/BehindAt.lean. The group's own fields do turn: Returns/Joins.lean says how.) Statements and
proofs.

  `Alike`           the relation
  `Alike.at`, `.shapeD`, `.rowsD`, `.shape?`, `.pad?`, `.lt`, `.bits`
                    what it gives of a message; of the tables' index bits
  `Alike.parts`, `.sizes`   `switchParts` and `sizesAt` are one
  `Alike.target`, `.check`, `.old`, `.seated`, `.stored`, `.reads`   the program's test on the
                    target · `OldFits` · `SeatedAt` · `PadsStored` · «the stored rows read the main
                    table alone»

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.Joins
import Johnson.Desc.K2.Honest.Returns.Can
import Johnson.Desc.K2.Honest.Inner.PadsWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open _root_.Tw.K2 (TargetFits readsMainOf)

/-- The same codes, and the same core of each oracle message. -/
structure Alike (S S' : Statement) : Prop where
  codes : S'.codes = S.codes
  cores : ∀ o : Nat, (S'.oracles[o]?).map core = (S.oracles[o]?).map core

variable {S S' : Statement}

/-- A message on both sides: none, or two with one core. -/
theorem Alike.at (h : Alike S S') (o : Nat) :
    (S'.oracles[o]? = none ∧ S.oracles[o]? = none) ∨
      ∃ x x', S.oracles[o]? = some x ∧ S'.oracles[o]? = some x' ∧ core x' = core x := by
  have e := h.cores o
  cases hx : S.oracles[o]? with
  | none =>
    rw [hx] at e
    left
    exact ⟨by simpa using e, rfl⟩
  | some x =>
    rw [hx] at e
    obtain ⟨x', hx', ec⟩ := Option.map_eq_some_iff.1 e
    exact Or.inr ⟨x, x', rfl, hx', ec⟩

theorem Alike.shapeD (h : Alike S S') (o : Nat) :
    (S'.oracles.getD o default).shape = (S.oracles.getD o default).shape := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  rcases h.at o with ⟨a, b⟩ | ⟨x, x', a, b, c⟩
  · rw [a, b]
  · rw [a, b]
    exact congrArg (·.1) c

theorem Alike.rowsD (h : Alike S S') (o : Nat) :
    (S'.oracles.getD o default).sampleRows = (S.oracles.getD o default).sampleRows := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  rcases h.at o with ⟨a, b⟩ | ⟨x, x', a, b, c⟩
  · rw [a, b]
  · rw [a, b]
    exact congrArg (·.2.2.1) c

theorem Alike.shape? (h : Alike S S') (o : Nat) :
    (S'.oracles[o]?).map (fun x : OnBytes.Oracle => x.shape) =
      (S.oracles[o]?).map fun x : OnBytes.Oracle => x.shape := by
  rcases h.at o with ⟨a, b⟩ | ⟨x, x', a, b, c⟩
  · rw [a, b]
  · rw [a, b]
    exact congrArg (fun t : Core => some t.1) c

theorem Alike.pad? (h : Alike S S') (o : Nat) :
    (S'.oracles[o]?).map (·.pad) = (S.oracles[o]?).map (·.pad) := by
  rcases h.at o with ⟨a, b⟩ | ⟨x, x', a, b, c⟩
  · rw [a, b]
  · rw [a, b]
    exact congrArg (fun t : Core => some t.2.2.2) c

theorem Alike.lt (h : Alike S S') (o : Nat) (ho : o < S.oracles.size) : o < S'.oracles.size := by
  rcases h.at o with ⟨_, b⟩ | ⟨_, _, _, b, _⟩
  · rw [Array.getElem?_eq_getElem ho] at b
    cases b
  · exact (Array.getElem?_eq_some_iff.1 b).1

theorem Alike.bits (h : Alike S S') (o : Nat) (part : Part) :
    S'.tableBits o part = S.tableBits o part := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rcases h.at o with ⟨a, b⟩ | ⟨x, x', a, b, c⟩
  · rw [a, b]
  · have es : x'.shape = x.shape := congrArg (·.1) c
    rw [a, b, h.codes]
    simp only [es]

theorem Alike.parts (h : Alike S S') (old : SingleRows) :
    switchParts S' old = switchParts S old := by
  unfold switchParts padOf
  simp only [h.codes, h.shapeD]

theorem Alike.sizes (h : Alike S S') (old : SingleRows) (T : SwitchTarget) :
    sizesAt S' old T = sizesAt S old T := by
  unfold sizesAt
  simp only [h.codes, h.shapeD]

/-- The program's test on the target. -/
theorem Alike.target (h : Alike S S') {old : SingleRows} {T : SwitchTarget}
    (F : TargetFits S old T) : TargetFits S' old T := by
  have hc := h.codes
  exact ⟨F.masks, by rw [hc]; exact F.oldCode, by rw [hc]; exact F.oldMaskCode,
    by rw [hc]; exact F.code, F.rows, F.degree, F.sampled, by rw [hc]; exact F.pad, F.mainPart,
    by rw [hc]; exact F.power, F.mainAligned, F.restAligned, by rw [hc]; exact F.fill,
    by rw [hc]; exact F.mainSmall, by rw [hc]; exact F.mainRoom,
    by rw [hc, h.parts]; exact F.restRoom, F.keptCount,
    fun p hp => by rw [hc, h.shapeD]; exact F.keptShapes p hp⟩

theorem Alike.check (h : Alike S S') {old : SingleRows} {T : SwitchTarget}
    (c : switchTargetCheck S old T = true) : switchTargetCheck S' old T = true :=
  (_root_.Tw.K2.targetOk_eq S' old T).symm.trans ((_root_.Tw.K2.targetOk_means S' old T).2
    (h.target ((_root_.Tw.K2.targetOk_means S old T).1
      ((_root_.Tw.K2.targetOk_eq S old T).trans c))))

theorem Alike.old (h : Alike S S') {old : SingleRows} (F : OldFits S old) : OldFits S' old := by
  have hc := h.codes
  exact ⟨by rw [hc]; exact F.mainVars, by rw [hc]; exact F.d0, by rw [hc]; exact F.d1,
    by simp only [h.shapeD]; exact F.rows, F.named, F.once,
    fun o ho => by rw [h.shapeD]; exact F.keptCode o ho,
    fun o ho => by rw [h.rowsD]; exact F.stored o ho⟩

theorem Alike.seated (h : Alike S S') {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} (F : SeatedAt S old T g anew) : SeatedAt S' old T g anew :=
  ⟨by rw [h.shape?]; exact F.carrying, fun a k hk => by simp only [h.shape?]; exact F.copies a k hk,
    fun o ho => h.lt o (F.olds o ho), F.apart⟩

theorem Alike.stored (h : Alike S S') {T : SwitchTarget} {g : Nat} {anew : Array Nat}
    (F : PadsStored S T g anew) : PadsStored S' T g anew :=
  ⟨by rw [h.pad?, h.codes]; exact F.carrying,
    fun a k hk => by rw [h.pad?, h.codes]; exact F.copies a k hk⟩

theorem Alike.reads (h : Alike S S') {old : SingleRows}
    (F : ∀ o ∈ (switchKept old).toList,
      ∀ r ∈ (S.oracles.getD o default).sampleRows.toList, readsMainOf o r = true) :
    ∀ o ∈ (switchKept old).toList,
      ∀ r ∈ (S'.oracles.getD o default).sampleRows.toList, readsMainOf o r = true :=
  fun o ho => by rw [h.rowsD]; exact F o ho

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.Alike.check
#print axioms VerifiableInference.Desc.K2.Honest.Returns.Alike.old
#print axioms VerifiableInference.Desc.K2.Honest.Returns.Alike.seated
