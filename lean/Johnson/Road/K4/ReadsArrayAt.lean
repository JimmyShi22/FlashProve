-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ReadsArrayAt.lean: THE ARRAY OF READS AT A STATE IN A LAYERS' LINK: ONE PUBLIC TEST
WITH CODE, and what it gives where K4's hearing has returned. A definition, a structure, statements
and proofs.

Why. The tie formsT_of_item (Johnson/Road/K4/FormsOfItem.lean), the sentence FormsInTOwn
(Johnson/Road/K4/InT/Statement.lean) and what stands under them ask of the array of reads things
that read public shape alone and that nobody pays: that it has a name in the link's list (hc); that
the array of that name is of the open segment's second sending (h2: `second`,
Johnson/Desc/Sound/FormsT.lean); that the plan's length of the reads is at most the number of the
array's columns (hK); InTAsks' fields reads and oneRow; that the reader takes each entry
(`K9.ownRow`, Johnson/Desc/First/Batch/ReaderOf.lean); and the entries' half of K04Plain's thereAt:
`Fork.hasEnt` (OnBytes/Model/Hide.lean) at every entry (the reads' array, virtual row 0, an index
below the plan's length of the reads).

  `readsArrayB hp s`: the test. hp: the sub-proof's plan. s: the verifier's state. It says: the plan
    numbers an array of reads (hp.tl.ix.U's third place); s stands in a layers' link; `readsThereB`
    and `oneRowB` (InT/Statement.lean) at that number, the plan's length of the reads (hp.nU's third
    place) and the state's own part and ledger; that length is at most the columns K of the array
    in the plan's ledger hp.Fp; and in the state's own ledger the array has a virtual row 0 that
    begins at column 0 and holds at least so many weights.
  THE ARRAY IS READ AT THREE PLACES, ON PURPOSE: the layout's entry for it (sizeI, sizeC: what
    entInT asks: Johnson/Desc/First/Batch/FormsIn.lean); the plan's ledger hp.Fp (K: of which
    o.v.K3 is made, by `hear_public`); the state's live ledger (R, row 0: what hasEnt and ownRow
    read). No clause says that the three agree.
  `ReadsArrayIs hp s b o`: what is concluded, a field a user.
  `readsArray_gives`: where `hear` has returned o over the plain engine at the plan hp, and the test
    says yes at a state s in the layers' link b: ReadsArrayIs.
  `ReadsArrayIs.ents_same`: the field ents at a ledger with the very trees of b's (the two runs of
    claims turn no tree).
That in a layers' link the part which K9.segAt? gives has the link's context: `segAt_lay`
(Johnson/Road/K4/InT/ReaderAtK4.lean), called.

Limits. THAT THE TEST SAYS YES ANYWHERE IS NOT SAID: no law makes it, AND NO ITEM OF THE TABLE OF
JOINTS HOLDS IT. WHO WOULD MAKE IT: its clauses on the link's list, the layout and the frame's shape
read b.L, which K4's decision leaves as it finds it (Rest.here,
Johnson/Desc/First/K4/ReadsAtS.lean); that they are the plan's inside a link is said by no item that
I know (the three equations of First/FillStart.lean speak of S.check, not of the link's live
copy b.L.check; of b.L.arrayOf nobody speaks); the clause on hp alone is a fact on the plan (no law;
at two stored plans the two numbers are equal, by a run); the clauses on the state's ledger want
that the link's entry lays the plan's trees and that the two hearings in front keep the SHAPE of the
trees (adding a claim turns a row's weights, not their number): no law says either. The state s and
the hearing's return are tied by nothing here, and need not be: of o the conclusions read the
array's number and its columns alone, both the plan's. One direction. Nothing on soundness or on
hiding.


-/
import OnBytes.Desc.First.K4.HearPublic
import Johnson.Desc.Sound.FormsT
import Johnson.Road.K4.InT.Statement
import Johnson.Road.K4.InT.ReaderAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Desc.First.K4 (hear engFl hear_public)
open OnBytes.Road.K4.InT (readsThereB oneRowB)
open OnBytes.Desc.First.K4.InT (segAt_lay)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.Sound (second)
open VerifiableInference.Desc (K9.Part K9.segAt? K9.atMoment1 K9.ownRow)

/-- **The test.** -/
def readsArrayB (hp : HPlan2) (s : S) : Bool :=
  match hp.tl.ix.U.getD 2 none, s.here, K9.segAt? s with
  | some iU3, .lay b, some a =>
    readsThereB a iU3 (hp.nU.getD 2 0) && (oneRowB b.F iU3 &&
      (decide (hp.nU.getD 2 0 ≤ ((hp.Fp.trees[iU3]?).map (·.K)).getD 0) &&
        (match (b.F.trees[iU3]?).bind (·.rows[0]?) with
          | some r => r.L0 == 0 && decide (hp.nU.getD 2 0 ≤ r.L.size)
          | none => false)))
  | _, _, _ => false

/-- **What is concluded.** -/
structure ReadsArrayIs (hp : HPlan2) (s : S) (b : LayOwn) (o : Own) : Prop where
  /-- hc and h2 -/
  name : ∃ c, b.L.arrayOf[o.v.iU3]? = some c ∧ second s c = true
  /-- hK -/
  cols : hp.nU.getD 2 0 ≤ o.v.K3
  /-- InTAsks' field reads -/
  there : ∀ a, K9.segAt? s = some a → readsThereB a o.v.iU3 (hp.nU.getD 2 0) = true
  /-- InTAsks' field oneRow -/
  oneRow : oneRowB b.F o.v.iU3 = true
  /-- the reader `K9.ownRow` takes each entry at virtual row 0 -/
  ownRow : ∀ (i : ℕ) (k : E),
    K9.ownRow b.F { tree := o.v.iU3, row := 0, idx := i, coef := k } = true
  /-- the entries' half of thereAt, at every ledger whose arrays have the same entries -/
  ents : ∀ F' : Fork, (∀ x, Fork.hasEnt F'.trees x = Fork.hasEnt b.F.trees x) →
    ∀ (i : ℕ) (k : E), i < hp.nU.getD 2 0 →
      Fork.hasEnt F'.trees { tree := o.v.iU3, row := 0, idx := i, coef := k } = true

/-- At a ledger with the very trees. -/
theorem ReadsArrayIs.ents_same {hp : HPlan2} {s : S} {b : LayOwn} {o : Own}
    (R : ReadsArrayIs hp s b o) {F' : Fork} (hF : F'.trees = b.F.trees) (i : ℕ) (k : E)
    (hi : i < hp.nU.getD 2 0) :
    Fork.hasEnt F'.trees { tree := o.v.iU3, row := 0, idx := i, coef := k } = true :=
  R.ents F' (fun x => by rw [hF]) i k hi

/-- **What the test gives where the hearing has returned.** -/
theorem readsArray_gives {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) {s : S} {b : LayOwn}
    (hs : s.here = .lay b) (hB : readsArrayB hp s = true) : ReadsArrayIs hp s b o := by
  obtain ⟨-, -, iU3, tab, laid, nU3, TS, cP, pts, hd2, e3, -, -, -, ev, -⟩ := hear_public h
  have i3 : o.v.iU3 = iU3 := by rw [ev]
  have k3 : o.v.K3 = ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 := by rw [ev]
  unfold readsArrayB at hB
  rw [e3, hs] at hB
  cases ha : K9.segAt? s with
  | none => simp [ha] at hB
  | some a =>
    rw [ha] at hB
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨h1, h2, hK, h3⟩ := hB
    obtain ⟨a₀, ha₀, -, eL⟩ := segAt_lay hs
    obtain rfl : a = a₀ := Option.some.inj (ha.symm.trans ha₀)
    refine ⟨?_, by rw [k3]; exact hK, ?_, by rw [i3]; exact h2, ?_, ?_⟩
    · rw [i3, ← eL]
      unfold readsThereB at h1
      cases hc : a.L.arrayOf[iU3]? with
      | none => simp [hc] at h1
      | some c =>
        refine ⟨c, rfl, ?_⟩
        unfold second
        rw [ha]
        cases hA : reqArray a.L.check.rows.layout c.1 c.2 with
        | none => simp [hc, hA] at h1
        | some A =>
          simp only [hc, hA, Bool.and_eq_true] at h1
          simpa [hA] using h1.1
    · intro a' ha'
      obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
      rw [i3]
      exact h1
    · intro i k
      rw [i3]
      unfold oneRowB at h2
      unfold K9.ownRow
      cases hX : b.F.trees[iU3]? with
      | none => simp [hX] at h2
      | some X => simpa [hX] using h2
    · intro F' hF i k hi
      rw [hF, i3]
      unfold Fork.hasEnt
      cases hX : b.F.trees[iU3]? with
      | none => simp [hX] at h3
      | some X =>
        cases hr : X.rows[0]? with
        | none => simp [hX, hr] at h3
        | some r =>
          simp only [hX, hr, Option.bind_some, Bool.and_eq_true, beq_iff_eq,
            decide_eq_true_eq] at h3
          obtain ⟨l0, ls⟩ := h3
          simp only [hr, Bool.and_eq_true, decide_eq_true_eq]
          omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ReadsArrayIs.ents_same
#print axioms OnBytes.Road.K4.readsArray_gives
