-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Key/KeyHom.lean: the two lemmas a function on the key's road over m:
climb, readPlace; readTail, readKey (do-notation inside Reading m); Key.check.
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Key.File
import OnBytes.ChecksWithHashAsArgument.M.Proof.ReadingHom

set_option autoImplicit false

namespace OnBytes.TwoPort.M.KeyHom

open OnBytes.Proof hiding climb readPlace Reading need Reading.fromStart readerName
    readNamed readTail
open OnBytes.TwoPort.M.Proof
open OnBytes.Params

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Run.Hom m n) (h : HashM m)

theorem app_climb (cfg b : ByteArray) :
    ∀ (levels : Nat) (x : ByteArray) (p i : Nat),
      φ.app (climb h cfg b levels x p i) = climb (φ.on h) cfg b levels x p i
  | 0, _, _, _ => φ.app_pure _
  | levels + 1, x, p, i => by
    unfold climb
    split
    · exact φ.app_pure _
    · dsimp only
      split <;> (simp only [φ.app_bind, app_climb cfg b levels]; rfl)

theorem app_readPlace (s : LinBindingShape) (cfg closing b : ByteArray) (i : Nat) :
    φ.app (readPlace h s cfg closing b i) = readPlace (φ.on h) s cfg closing b i := by
  unfold readPlace
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · split
        · exact φ.app_pure _
        · simp only [φ.app_bind, φ.app_pure, app_climb]
          rfl

theorem rel_readTail (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray) :
    Rel φ (readTail h p dry first b) (readTail (φ.on h) p dry first b) := by
  unfold readTail
  dsimp only
  refine rel_bind φ (rel_need φ _ _) fun seal1 => ?_
  refine rel_bind φ (rel_needM φ _ (app_readPlace φ h _ _ _ _ _)) fun place => ?_
  refine rel_bind φ (rel_needM φ _ (RoadHom.app_tableKey φ h _ _ _ _ _)) fun key => ?_
  refine rel_bind φ (rel_need φ _ _) fun x => ?_
  obtain ⟨rounds2, end2⟩ := x
  refine rel_bind φ (rel_need φ _ _) fun spec2 => ?_
  refine rel_bind φ (rel_readNamed φ h _ _ _ _) fun shared => ?_
  refine rel_bind φ (rel_need φ _ _) fun seal2 => ?_
  refine rel_bind φ (rel_need φ _ _) fun rounds3 => ?_
  refine rel_bind φ (rel_need φ _ _) fun spec3 => ?_
  refine rel_bind φ (rel_readNamed φ h _ _ _ _) fun second => ?_
  exact rel_pure φ _

theorem rel_readKey (k : KeyChains) (table : TableName) (file : ByteArray) (j : Nat) :
    Rel φ (Key.readKey h k table file j) (Key.readKey (φ.on h) k table file j) := by
  unfold Key.readKey
  dsimp only
  refine rel_bind φ (rel_need φ _ _) fun x => ?_
  obtain ⟨rounds, dry⟩ := x
  refine rel_bind φ (rel_need φ _ _) fun spec => ?_
  refine rel_bind φ (rel_readNamed φ h _ _ _ _) fun first => ?_
  refine rel_bind φ (rel_readTail φ h _ _ _ _) fun r => ?_
  dsimp only
  split
  · exact rel_bind φ (rel_throw φ _) fun _ => rel_pure φ _
  · exact rel_bind φ (rel_pure φ _) fun _ => rel_pure φ _

theorem app_check (k : KeyChains) (file : ByteArray) :
    φ.app (Key.check h k file) = Key.check (φ.on h) k file := by
  unfold Key.check
  dsimp only
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · simp only [φ.app_bind]
        rw [RoadHom.app_fromStart φ _ _ (rel_readKey φ h _ _ _ _)]
        refine congrArg _ (funext fun r => ?_)
        cases r with
        | error why => exact φ.app_pure _
        | ok r =>
          simp only []
          split <;> exact φ.app_pure _

/-! ## The second lemma -/

variable (q : Keeps m) (hh : ∀ n t i s b, q.ok (h n t i s b))
include hh

theorem ok_climb (cfg b : ByteArray) :
    ∀ (levels : Nat) (x : ByteArray) (p i : Nat), q.ok (climb h cfg b levels x p i)
  | 0, _, _, _ => q.ok_pure _
  | levels + 1, x, p, i => by
    unfold climb
    split
    · exact q.ok_pure _
    · dsimp only
      split <;> exact q.ok_bind _ _ (hh _ _ _ _ _) fun _ => ok_climb cfg b levels _ _ _

theorem ok_readPlace (s : LinBindingShape) (cfg closing b : ByteArray) (i : Nat) :
    q.ok (readPlace h s cfg closing b i) := by
  unfold readPlace
  split
  · exact q.ok_pure _
  · split
    · exact q.ok_pure _
    · split
      · exact q.ok_pure _
      · split
        · exact q.ok_pure _
        · refine q.ok_bind _ _ (hh _ _ _ _ _) fun leaf => ?_
          exact q.ok_bind _ _ (ok_climb h q hh _ _ _ _ _ _) fun _ => q.ok_pure _

theorem okR_readTail (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray) :
    OkR q (readTail h p dry first b) := by
  unfold readTail
  dsimp only
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun seal1 => ?_
  refine okR_bind q (RoadKeeps.ok_needM q _ _ (ok_readPlace h q hh _ _ _ _ _)) fun place => ?_
  refine okR_bind q (RoadKeeps.ok_needM q _ _ (RoadKeeps.ok_tableKey q h hh _ _ _ _ _)) fun key =>
      ?_
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun x => ?_
  obtain ⟨rounds2, end2⟩ := x
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun spec2 => ?_
  refine okR_bind q (RoadKeeps.ok_readNamed q h hh _ _ _ _) fun shared => ?_
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun seal2 => ?_
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun rounds3 => ?_
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun spec3 => ?_
  refine okR_bind q (RoadKeeps.ok_readNamed q h hh _ _ _ _) fun second => ?_
  exact okR_pure q _

theorem okR_readKey (k : KeyChains) (table : TableName) (file : ByteArray) (j : Nat) :
    OkR q (Key.readKey h k table file j) := by
  unfold Key.readKey
  dsimp only
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun x => ?_
  obtain ⟨rounds, dry⟩ := x
  refine okR_bind q (RoadKeeps.ok_need q _ _) fun spec => ?_
  refine okR_bind q (RoadKeeps.ok_readNamed q h hh _ _ _ _) fun first => ?_
  refine okR_bind q (okR_readTail h q hh _ _ _ _) fun r => ?_
  dsimp only
  split
  · exact okR_bind q (okR_throw q _) fun _ => okR_pure q _
  · exact okR_bind q (okR_pure q _) fun _ => okR_pure q _

theorem ok_check (k : KeyChains) (file : ByteArray) : q.ok (Key.check h k file) := by
  unfold Key.check
  dsimp only
  split
  · exact q.ok_pure _
  · split
    · exact q.ok_pure _
    · split
      · exact q.ok_pure _
      · refine q.ok_bind _ _ (RoadKeeps.ok_fromStart q _ (okR_readKey h q hh _ _ _ _)) fun r => ?_
        cases r with
        | error why => exact q.ok_pure _
        | ok r =>
          simp only []
          split <;> exact q.ok_pure _

end OnBytes.TwoPort.M.KeyHom
