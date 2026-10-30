-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyRows1At.lean: THE KEY FILE's FIRST CHAIN: THE PROMISE on AND THE CLAIM L AT EACH OF ITS TWENTY BOUNDARIES, AS FUNCTIONS OF THE STATEMENT THAT THE RULES' PIECES CARRY: (the instance, the first chain's state), with the oracles: beside
Johnson/RunOne/KeyRows23At.lean (the shared and the last chain), in its form, for the adaptor (Johnson/Top/Fire/Code/KeyOfRows.lean: RowsOwed). Definitions, and three small theorems (off₁_on · off₁_L · on₁_two): NO BLOCK's LAW.
free₁ HOLDS THE FENCE ON THE ROWS' CONTENT (a promise that COUNTS rows fences no made-up row): every sample row of a message that is pinned at border k lies on that message's own tables (SampleIn, Johnson/RunOne/KeyHanded.lean: Means.RowIn); from border 18 every open row of the last group lies on
its members' tables (OpenIn). TO BE EARNED (no law is typed; the blocks' texts inside d not walked here): SampleIn by the message's sending; OpenIn by w.1.send (by reading, the call that adds an open row tests just this). THE PROMISE HOLDS THE TIES THAT HAVE BEEN FOUND SO FAR (the rule: what a block's decide reads against what the claim in front reads): the Bool ones in shape₁ (Johnson/Desc/Key/KeyShape.lean; KeyReaders1.ties₁); those that are no Bool in the promise's last letter: free₁ k:
no collision at the stored table's record's seed (as before) · ArrOk: what PIN j pins is the witness's message j (j = 0, 1, 2) · Placed: the state's book places every message that is pinned at border k where at_ says · from border 18 on: EvalIs (KeyHanded.lean): the own group's first open row IS the claim's (Eval).
AT WHICH STATE: the key file's description descriptionFromSource (Johnson/Desc/Key/Desc.lean; written over another working state of these files): its first chain's state FirstState. THE READERS ARE A FILLING OF THEIR OWN (Johnson/RunOne/KeyReaders.lean), called in Johnson/RunOne/KeyReaders1.lean, a file with
code that an honest run evaluates. The table (KeyBorders), the words (KeyWords), the meaning over readers (KeyMeaning · KeyK3Items) and the book-keeping over readers (KeyShape) did not turn with the state.
  plan₁ one · readers₁ one · book₁ one · k3At₁    Johnson/RunOne/KeyReaders1.lean
  meaning₁At                              the table's letter KMeaning at this chain: nine items by KeyMeaning.meaning₁; forms | worth by KeyK3Items; near and every later chain's claim: False (open at no border here)
  open₁ n k                               the open sets, computed from the rows
  on₁ | R₁ | L₁                           on k := the table's onAt at shape₁ and the open pins · R k x w := every open item holds at w · L k := THERE IS A WITNESS AT WHICH EVERY OPEN ITEM HOLDS
LETTERS LEFT: the description F (for what its blocks tell of a tree) · the frame Fr (the oracles' type) · the reading G (code, radius, samples, the stored table's decoding) · where message k lies · how a witness is read (R) · coll (the stored table has a collision at the
record's seed: the configuration's).
AT AN INSTANCE THAT IS NO RECORD's KEY: THE RECORD IS READ THROUGH G.recOf : … → Option Rec, NEVER THROUGH A DEFAULT: where it gives nothing on₁ k IS FALSE AT ALL TWENTY BOUNDARIES (off₁_on) AND L₁ k IS FALSE
AT ALL TWENTY (off₁_L: pinT is open at each): every law at these boundaries is idle there.
Limits. An honest run shows no witness: L has been evaluated nowhere. Machine elements: the words' test rides with every law. Nothing on soundness.
-/
import Johnson.RunOne.KeyReaders1
import Johnson.Desc.Means.Order
import Johnson.Desc.Key.KeyOff
import Johnson.Desc.Key.KeyTies
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)

section
variable {Cells M : Type} (one : OneTime) (R : KRead Cells M)

/-- **The table's meaning at the first chain.** -/
def meaning₁At : KMeaning Xi FirstState (Wit Cells Unit M) :=
  meaningK (plan₁ one) R (readers₁ one) k3At₁ one.ranges one.codes (fun _ _ _ => False) (fun _ _ _ _ _ => False)

end

/-- What is open at boundary k of the first chain of a key file with n lookups. -/
def open₁ (n k : Nat) : List KItem := ((openSets (rows₁ n) (start₁ n))[k]?).getD []

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- **The promise's last letter at boundary k**: no collision at the stored table · the ties that are no Bool. (At two lookups: shape₁'s ties ask that number.) -/
def free₁ (k : Nat) (a : Xi × FirstState) (y : Strs) : Prop :=
  FreeAt G coll a y ∧ (ArrOk G at_ [0, 1, 2] ∧ ReadsPinned G at_ R [0, 1, 2]) ∧ Placed (plan₁ one).orc (fun o => a.2.d.book.place[o]?) id at_ (pinned (open₁ 2 k)) ∧ (18 ≤ k → KeyRows23.EvalIs one.lin a.2) ∧
    (∀ j ∈ pinned (open₁ 2 k), ∀ o, (plan₁ one).orc j = some o → KeyRows23.SampleIn a.2.d.st o) ∧ (18 ≤ k → KeyRows23.OpenIn a.2.d.st (a.2.d.st.groups.size - 1)) ∧ Means.InOrder a.2.d.st ∧
    (∀ j ∈ pinned (open₁ 2 k), ShownAt F at_ j y) ∧ a.1.key.fits one.lin.fold.index = true ∧ (2 ≤ k ∧ k ≤ 15 → MaskWith (fun o => a.2.d.book.place[o]?) 1 2) ∧
    (18 ≤ k → ∀ o, (plan₁ one).orc 2 = some o → MaskWith (fun o => a.2.d.book.place[o]?) o (o + 1))

/-- **The promise at boundary k of the first chain.** -/
def on₁ (k : Nat) (x : (Xi × FirstState) × Fr.E.Str) : Prop :=
  onAt F G at_ (meaning₁At one R) (shape₁ (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) k) (free₁ F G at_ one R coll k) (open₁ (n₁ one) k) x.1 (strsOf Fr x.2)

/-- **The relation there, with its witness**: every open item holds. In the shape that JointRow.ofBorder takes (Johnson/Desc/Sound/KeyRowsOfBorders.lean): JointRow.ofBorder (on₁ … k) (R₁ … k). -/
def R₁ (k : Nat) (x : (Xi × FirstState) × Fr.E.Str) (w : Wit Cells Unit M) : Prop :=
  relAt F G at_ (meaning₁At one R) (open₁ (n₁ one) k) x.1 (strsOf Fr x.2) w

/-- **The claim there**: there is a witness at which every open item holds. -/
def L₁ (k : Nat) (x : (Xi × FirstState) × Fr.E.Str) : Prop := ∃ w, R₁ F Fr G at_ one R k x w

end

/-! ## Off the image -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- At an instance that is no record's key the promise is false at every boundary. -/
theorem off₁_on (k : Nat) (x : (Xi × FirstState) × Fr.E.Str) (h : G.recOf x.1 = none) : ¬ on₁ F Fr G at_ one R coll k x := fun ho =>
  ho.elim (fun hn => hn rfl) fun hr => not_free_off G coll x.1 _ h hr.2.2.1.1

/-- **The promise holds the number of lookups.** -/
theorem on₁_two (k : Nat) (x : (Xi × FirstState) × Fr.E.Str) (h : on₁ F Fr G at_ one R coll k x) : n₁ one = 2 := by
  have hs : shape₁ (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) k x.1.2 = true := h.elim (fun hn => absurd rfl hn) (·.1)
  have ht : ties₁ one k x.1.2 = true := ((shape₁_iff _ _ _ _ _ _ _).1 hs).1
  unfold ties₁ tiesA at ht
  simp only [Bool.and_eq_true] at ht
  exact beq_iff_eq.1 ht.1.1.1.1.1.1

/-- And the claim is false wherever pinT is open. -/
theorem off₁_L (k : Nat) (x : (Xi × FirstState) × Fr.E.Str) (hO : KItem.pinT ∈ open₁ (n₁ one) k) (h : G.recOf x.1 = none) : ¬ L₁ F Fr G at_ one R k x :=
  fun ⟨w, hw⟩ => not_rel_off F G at_ (meaning₁At one R) _ x.1 _ w hO h hw

end

/-! ## Tests, by evaluation -/

#eval (List.range 20).map fun k => (open₁ 2 k).length
#eval decide (open₁ 2 0 = start₁ 2) && decide (open₁ 2 19 = end₁)
-- no item whose meaning is «False» here (near; a later chain's claim) is open at any of the twenty boundaries: due «true»
#eval ((List.range 20).flatMap (open₁ 2)).all fun i => match i with
  | .near _ | .claim _ _ => false
  | _ => true
-- the goal's two halves: pinT is open at all twenty; inRange l just up to K3's block of lookup l: due «true»
#eval (List.range 20).all (fun k => (open₁ 2 k).contains .pinT) && ((List.range 20).filter fun k => (open₁ 2 k).contains (.inRange 0)) == List.range 5 && ((List.range 20).filter fun k => (open₁ 2 k).contains (.inRange 1)) == List.range 11

end Johnson.RunOne.KeyRows1
