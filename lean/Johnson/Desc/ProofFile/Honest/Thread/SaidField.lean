-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/SaidField.lean: A LETTER THAT SAYS WHICH COLUMNS THE FIELD
`opened` HOLDS, AND ITS CARRYING OVER A SUB-PROTOCOL. `SaidOk` (Honest/Thread/SaidOk.lean) reads the
rounds seen alone. A part that reads the columns handed to it needs to know that the field holds the
columns of the sub-protocols in front. `SaidField` is `SaidOk` with one clause more: there is a
`base` of which `B` holds, and at every set of tables at which `Thread.Hand` holds, `Thread.Field`
holds at that `base`. It has no tables in its type, as a letter of `Said`'s type has none.

  `SaidField`, `BaseNil`   the letter; the base of a chain with nothing in front
  `opened_of_saidField`   at `Thr`'s own tables the field holds `base`, then the columns of
    `Thread.colsTo`, which `Thread.Made` binds
  `BaseKept`, `baseNil_kept`   `B` is carried over a sub-protocol's rounds
  `TreesNext`, `treesNext_of_playsS`, `treesNext_of_fresh_nil`   the new trees at the play of
    `Thread.Moved`
  `saidNext_field`, `saidNext_field_all`, `saidNext_field_of_owes`   the letter's `SaidNext`
  `saidField_start`   the letter at a start that has seen nothing, with the field at `some []`

What these are. Definitions and conditional lemmas on our own definitions. None is one of the
library's goals.

Limits.
  * Which `B` a chain takes is not said here. `BaseNil` serves a chain that is started at `[]`. At
    the last chain `B` has to say which columns the two earlier chains read: that is a letter here.
  * `SaidNext` at this letter rests on `PlaysS` at the same number at members with new trees. There
    is no circle in the statements: `PlaysS` at b reads the letter at b alone. That a proof of
    `PlaysS` at b does not call `SaidNext` at b has to be seen of each proof.
  * `hst` of `saidNext_field_of_owes`, `ho` and `hdp` are premises, and they are shown here of no
    thread.
  * The clause is true and empty at a state where no `E` has `Thread.Hand`.
  * `opened_of_saidField` says what the field holds at `Thr`'s own tables. It does not say that any
    state of a run meets `Thr`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FieldAllNext
import Johnson.Desc.ProofFile.Honest.Thread.ThrFieldStart
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 1 The letter -/

/-- **Every word seen is below the prime, and the field holds `base` and the columns in front**, at
every set of tables at which `Thread.Hand` holds, for some `base` of which `B` holds. A definition:
a filling of the letter `Said`. -/
def SaidField (B : Coins Bk → Mid W X → List OpenedColumn → Prop) (b : Nat) (k : Coins Bk)
    (m : Mid W X) : Prop :=
  SaidOk b k m ∧ ∃ base, B k m base ∧ ∀ E, T.Hand b k m E → T.Field base b m E

/-- The base of a chain with nothing in front. -/
def BaseNil (_ : Coins Bk) (_ : Mid W X) (base : List OpenedColumn) : Prop := base = []

/-- **What the field holds, at `Thr`'s own tables.** -/
theorem opened_of_saidField {B : Coins Bk → Mid W X → List OpenedColumn → Prop} {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid W X} {E : Env} (hA : Thr T b k s m E) (hS : SaidField T B b k m) :
    ∃ base cols, B k m base ∧ T.colsTo b m E = .ok cols ∧ m.opened = some (base ++ cols) := by
  obtain ⟨-, base, hB, hL⟩ := hS
  obtain ⟨cols, hc, ho⟩ := (field_iff T base b m E).1 (hL E hA.1)
  exact ⟨base, cols, hB, hc, ho⟩

/-! ## 2 What the carrying asks -/

/-- `B` holds behind a sub-protocol's rounds at the `base` at which it held in front. A definition,
meant as a hypothesis. -/
def BaseKept (B : Coins Bk → Mid W X → List OpenedColumn → Prop) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k m E ds y cols base, T.Moved blk k m E ds y cols →
    B k m base → B k (y.2.took cols) base

theorem baseNil_kept (b : Nat) : BaseKept T (BaseNil (Bk := Bk) (W := W) (X := X)) b :=
  fun _ _ _ _ _ _ _ _ _ _ h => h

/-- The sub-protocol's new trees, at the play that `Thread.Moved` names. A definition, meant as a
hypothesis. -/
def TreesNext (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E → Said b k m →
    drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
    T.Trees (T.fresh b) k y.2 (E.add y.1)

theorem treesNext_of_playsS {Said : Nat → Coins Bk → Mid W X → Prop} {b : Nat}
    (hP : PlaysS T Said b)
    (hst : ∀ blk, T.bs[b]? = some blk → ∀ (m : Mid W X) (ds : List Fmt.Drawn),
      chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none) : TreesNext T Said b :=
  fun blk hblk k s m E ds y cols hA hS hd hM =>
    trees_at_y T Said hblk hP hA hS hd (hst blk hblk m ds) hM

theorem treesNext_of_fresh_nil {Said : Nat → Coins Bk → Mid W X → Prop} {b : Nat}
    (h : T.fresh b = []) : TreesNext T Said b :=
  fun _ _ k _ _ E _ y _ _ _ _ _ => T.trees_of_fresh_nil h k y.2 (E.add y.1)

/-! ## 3 The letter is carried -/

/-- **`SaidNext` at the letter, at one number.** -/
theorem saidNext_field {n b : Nat} {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    (hfit : T.fits n = true) (hb : b ≤ n) (hT : TreesNext T (SaidField T B) b)
    (hK : BaseKept T B b) (ho : T.opensAvailable (b + 1) = true)
    (hdp : ∀ (k : Coins Bk) (m : Mid W X), DepthsAt T (b + 1) k m) :
    SaidNext T (SaidField T B) b := by
  intro blk hblk k s m E ds y cols hA hS hd hM
  have hS' := hS
  obtain ⟨hOk, base, hB, hL⟩ := hS'
  exact ⟨saidNext_ok T b blk hblk k s m E ds y cols hA hOk hd hM, base,
    hK blk hblk k m E ds y cols base hM hB,
    field_all_next T hfit hb hblk hA hM (hT blk hblk k s m E ds y cols hA hS hd hM) hL ho
      (hdp k _)⟩

/-- **`SaidNext` at the letter, at every number.** -/
theorem saidNext_field_all {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    (hfit : T.fits T.bs.length = true)
    (hT : ∀ b, b < T.bs.length → TreesNext T (SaidField T B) b)
    (hK : ∀ b, b < T.bs.length → BaseKept T B b)
    (ho : ∀ b, b < T.bs.length → T.opensAvailable (b + 1) = true)
    (hdp : ∀ b, b < T.bs.length → ∀ (k : Coins Bk) (m : Mid W X), DepthsAt T (b + 1) k m) :
    ∀ b, SaidNext T (SaidField T B) b := by
  intro b blk hblk
  have hj := lt_of_member T hblk
  exact saidNext_field T hfit (Nat.le_of_lt hj) (hT b hj) (hK b hj) (ho b hj) (hdp b hj) blk hblk

/-- **The same from `OwesS` at the letter**, with no stop at the members that have new trees. -/
theorem saidNext_field_of_owes {B : Coins Bk → Mid W X → List OpenedColumn → Prop}
    (hfit : T.fits T.bs.length = true) (o : OwesS T (SaidField T B))
    (hst : ∀ b, b < T.bs.length → T.fresh b ≠ [] → ∀ blk, T.bs[b]? = some blk →
      ∀ (m : Mid W X) (ds : List Fmt.Drawn),
        chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (hK : ∀ b, b < T.bs.length → BaseKept T B b)
    (ho : ∀ b, b < T.bs.length → T.opensAvailable (b + 1) = true)
    (hdp : ∀ b, b < T.bs.length → ∀ (k : Coins Bk) (m : Mid W X), DepthsAt T (b + 1) k m) :
    ∀ b, SaidNext T (SaidField T B) b :=
  saidNext_field_all T hfit
    (fun b hb => by
      by_cases h : T.fresh b = []
      · exact treesNext_of_fresh_nil T h
      · exact treesNext_of_playsS T (o b hb).1 (hst b hb h))
    hK ho hdp

/-! ## 4 At a start -/

/-- **The letter at a start that has seen nothing, with the field laid at `some []`.** -/
theorem saidField_start {k : Coins Bk} {m : Mid W X} (h : m.seen = []) :
    SaidField T BaseNil 0 k { m with opened := some [] } :=
  ⟨saidOk_nil h, [], rfl, fun E _ => T.field_start [] m E⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.SaidField
#print axioms ProofFile.Honest.BaseNil
#print axioms ProofFile.Honest.opened_of_saidField
#print axioms ProofFile.Honest.BaseKept
#print axioms ProofFile.Honest.baseNil_kept
#print axioms ProofFile.Honest.TreesNext
#print axioms ProofFile.Honest.treesNext_of_playsS
#print axioms ProofFile.Honest.treesNext_of_fresh_nil
#print axioms ProofFile.Honest.saidNext_field
#print axioms ProofFile.Honest.saidNext_field_all
#print axioms ProofFile.Honest.saidNext_field_of_owes
#print axioms ProofFile.Honest.saidField_start
