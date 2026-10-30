-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/BookFence.lean: the honest side of the kind "lookup" (K3): the
two tests on the book, `bookFits` (Honest/K3/Law/RowLends.lean) and `startsFit`
(Honest/K3/Law/MasksBook.lean), hold every slot of a lookup inside its owner's count of coins: so a
reading "the owner's coin number base.e + j, or the default" never takes the default at
j < first + slots. Theorems alone. On public data, but for three theorems: `coinsE_length` and the
last one speak of the length of a list of coins, and `senderLays_mono` bears a letter for a reading
of coins.

Why. Several statements of this folder read a coin by `getD … zeroE`: `MasksFromBook`
(Honest/K3/Law/MasksBook.lean), `MasksWorldBook` (Honest/K3/Law/MasksWorld.lean) and, under
Honest/K3/Law/Thread/, `DictAt`, `DigitsRunAll` and the hypotheses of theorems over them. Each bears
the two tests beside the reading. That the tests keep the index below the list's length no theorem
said. The proof of `masksFromBook` calls of `bookFits` its third clause alone (the entries' names
and counts): its equation holds without the fourth (each entry lies inside its owner's coins). The
fourth clause is spent in Honest/K3/Law/RowLends.lean for another end: that the book lends the row
its coins (`lend_ok`). `tests_fence` spends it for the bound on the index.

What is shown.
  `sum_cut`: a number below a list's sum lies in the stretch of one member. On lists alone.
  `senderLays_mono`: `SenderLays` (Honest/K3/Law/MasksWorld.lean) is monotone in its number of
    entries.
  `coinsE_length`: `coinsE c` has as many elements as the count has coins of the extension field.
  `slots_pos`: a face with at least two planes has a slot.
  `tests_fence`: under the two tests, at every due, at every j below the face's slots:
    base.e + (first + j) is below the owner's count.
  `named_reads`: so, in the first chain, at the book's own numbers: at every j below first + slots
    the index base.e + j is below the length of the owner's list of coins.

Hypotheses that remain. `h2`: the face has at least two planes: public; at a site's face the planes
are 32 (so spent in Honest/K3/Law/Thread/ExchangeDict.lean). `hb`, `hs`: the two tests: hypotheses
on a book that other files make; no theorem of this file shows them.

How the proof of `tests_fence` goes. The face's slots are the sum of the stages' (`slots_stages`,
Honest/K3/RowLaw.lean): `sum_cut` finds the stage x in whose stretch j lies; its first slot is the
sum in front (`firstSlot_getElem`, Honest/K3/RowAt.lean). A stage without a call has no slot. At a
stage with a call the part states one stretch of `ownRun` coins and, where the call has end values,
a second of as many as these: `bookFits`' third clause gives the entries these counts, `startsFit`
their owner and starts, `bookFits`' fourth clause start + count ≤ the owner's count.

Imported. Honest/K3/Law/MasksWorld.lean, and what stands beneath it.

Users. Honest/K3/Law/BookFenceSite.lean; Honest/K3/Law/BookFenceToy.lean [not in this library] (a
test).

Limits. Nothing shows that a book passes the two tests. Nothing on what a coin is, on who lays it or
on what is sent. Below first the bound holds because it holds at the lookup's last slot: the tests
read no entry of those slots.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MasksWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open OnBytes.Slice (GE)

/-- A number below a list's sum lies in the stretch of one member. -/
theorem sum_cut : ∀ (l : List Nat) (j : Nat), j < l.sum →
    ∃ i, ∃ h : i < l.length, (l.take i).sum ≤ j ∧ j < (l.take i).sum + l[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, j, h => by
    by_cases hj : j < a
    · exact ⟨0, by simp, by simp, by simpa using hj⟩
    · have h' : j - a < l.sum := by
        rw [List.sum_cons] at h
        omega
      obtain ⟨i, hi, h1, h3⟩ := sum_cut l (j - a) h'
      refine ⟨i + 1, Nat.succ_lt_succ hi, ?_, ?_⟩
      · rw [List.take_succ_cons, List.sum_cons]
        omega
      · rw [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
        omega

/-- `SenderLays` is monotone in the number of entries. -/
theorem senderLays_mono {tab : Nat → OnBytes.Part → Nat → GE} {o m n n' start : Nat}
    {coin : Nat → GE} (h : n ≤ n') (hS : SenderLays tab o m n' start coin) :
    SenderLays tab o m n start coin :=
  fun j hj => hS j (Nat.lt_of_lt_of_le hj h)

/-- As many elements as the count's coins of the extension field. -/
theorem coinsE_length {d : Due} (c : Cs d) : (coinsE c).length = d.e := by
  unfold coinsE
  exact List.length_ofFn

/-- A face with at least two planes has a slot. -/
theorem slots_pos (f : LFace) (h2 : 2 ≤ f.planes) : 0 < f.slots := by
  have hm : Stage.leaves ∈ stages f := by
    unfold stages
    simp
  have h := stage_room f h2 .leaves hm
  have e : Stage.own f .leaves + Stage.tail f .leaves = 1 + f.mu + 2 * f.d := slots_leaves f
  omega

/-- **The two tests on the book hold every slot of the lookup inside the owner's count.** It spends
`bookFits`' fourth clause. Conditional on h2 and the two tests. -/
theorem tests_fence (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : At)
    (first : Nat) (o : Addr) (base : Due) (h2 : 2 ≤ a.face.planes)
    (hb : bookFits B rows due a = true) (hs : startsFit B a first o base = true) :
    ∀ j, j < a.face.slots → base.e + (first + j) < (due o).e := by
  intro j hj
  rw [← slots_stages a.face h2] at hj
  obtain ⟨i, hi, h1, h3⟩ := sum_cut _ j hj
  have hi' : i < (stages a.face).length := by simpa using hi
  rw [← List.map_take, ← firstSlot_getElem a.face i hi'] at h1 h3
  rw [List.getElem_map] at h3
  have hz : i < ((stages a.face).zipIdx).length := by simpa using hi'
  have hmem : ((stages a.face)[i], i) ∈ (stages a.face).zipIdx := by
    have e : ((stages a.face).zipIdx)[i]'hz = ((stages a.face)[i], i) := by
      simp [List.getElem_zipIdx]
    rw [← e]
    exact List.getElem_mem hz
  generalize (stages a.face)[i] = x at h1 h3 hmem
  have h3' : j < firstSlot a.face x + (x.own a.face + x.tail a.face) := h3
  cases hk : x.call a.face with
  | none =>
    have e1 : x.own a.face = 0 := by simp [Stage.own, hk]
    have e2 : x.tail a.face = 0 := by simp [Stage.tail, hk]
    omega
  | some k =>
    have g1 := List.all_eq_true.1 hb _ hmem
    have g2 := List.all_eq_true.1 hs _ hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at g1 g2
    have hnamed := g1.1.2
    have hin := g1.2
    simp only [runsAt, hk] at hnamed g2
    have hown : x.own a.face = ownRun k := by simp [Stage.own, hk]
    have htail : x.tail a.face = ((k.ends).map (·.n)).getD 0 := by simp [Stage.tail, hk]
    obtain ⟨lead, vs, ends⟩ := k
    cases ends with
    | none =>
      have ht : x.tail a.face = 0 := by rw [htail]; rfl
      have q0 : ((entriesAt B a.place i).map Ahead.named)[0]? =
          some (sumName a.place i, ⟨0, ownRun ⟨lead, vs, none⟩⟩) := by
        rw [hnamed]
        rfl
      have r0 : ((entriesAt B a.place i).map fun e => (e.owner, e.start))[0]? =
          some (o, base.plus ⟨0, first + firstSlot a.face x + 0⟩) := by
        rw [g2]
        rfl
      rw [List.getElem?_map] at q0 r0
      obtain ⟨e0, he0, hn0⟩ := Option.map_eq_some_iff.1 q0
      rw [he0] at r0
      have r0' : (e0.owner, e0.start) = (o, base.plus ⟨0, first + firstSlot a.face x + 0⟩) :=
        Option.some.inj r0
      have hin0 := List.all_eq_true.1 hin e0 (List.mem_of_getElem? he0)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin0
      have c0 : e0.count = ⟨0, ownRun ⟨lead, vs, none⟩⟩ := congrArg Prod.snd hn0
      have o0 : e0.owner = o := congrArg Prod.fst r0'
      have s0 : e0.start = base.plus ⟨0, first + firstSlot a.face x + 0⟩ := congrArg Prod.snd r0'
      have b0 := hin0.2
      rw [c0, o0, s0] at b0
      have b0' : base.e + (first + firstSlot a.face x + 0) + ownRun ⟨lead, vs, none⟩ ≤ (due o).e :=
        b0
      omega
    | some en =>
      have ht : x.tail a.face = en.n := by rw [htail]; rfl
      have q1 : ((entriesAt B a.place i).map Ahead.named)[1]? =
          some (endName a.place i, ⟨0, en.n⟩) := by
        rw [hnamed]
        rfl
      have r1 : ((entriesAt B a.place i).map fun e => (e.owner, e.start))[1]? =
          some (o, base.plus ⟨0, first + firstSlot a.face x + x.own a.face⟩) := by
        rw [g2]
        rfl
      rw [List.getElem?_map] at q1 r1
      obtain ⟨e1, he1, hn1⟩ := Option.map_eq_some_iff.1 q1
      rw [he1] at r1
      have r1' : (e1.owner, e1.start) =
          (o, base.plus ⟨0, first + firstSlot a.face x + x.own a.face⟩) := Option.some.inj r1
      have hin1 := List.all_eq_true.1 hin e1 (List.mem_of_getElem? he1)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin1
      have c1 : e1.count = ⟨0, en.n⟩ := congrArg Prod.snd hn1
      have o1 : e1.owner = o := congrArg Prod.fst r1'
      have s1 : e1.start = base.plus ⟨0, first + firstSlot a.face x + x.own a.face⟩ :=
        congrArg Prod.snd r1'
      have b1 := hin1.2
      rw [c1, o1, s1] at b1
      have b1' : base.e + (first + firstSlot a.face x + x.own a.face) + en.n ≤ (due o).e := b1
      omega

/-- **So at first + slots entries `SenderLays`' reading never meets the default**, in the first
chain, at the book's own numbers. Conditional on h2 and the two tests. -/
theorem named_reads (Bk : ProverCoinCounts) (k : Coins Bk) (a : At) (first : Nat) (ow : Addr) (base : Due)
    (h2 : 2 ≤ a.face.planes)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) a = true)
    (hs : startsFit Bk a first ow base = true) :
    ∀ j, j < first + a.face.slots → base.e + j < (coinsE (k.look 0 ow).2).length := by
  intro j hj
  have h0 := slots_pos a.face h2
  have h := tests_fence Bk (Bk.rowsOf 0) (dueAt Bk.first) a first ow base h2 hb hs
    (a.face.slots - 1) (by omega)
  rw [coinsE_length, look_due_first]
  omega

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.sum_cut
#print axioms ProofFile.Honest.K3.Law.senderLays_mono
#print axioms ProofFile.Honest.K3.Law.coinsE_length
#print axioms ProofFile.Honest.K3.Law.slots_pos
#print axioms ProofFile.Honest.K3.Law.tests_fence
#print axioms ProofFile.Honest.K3.Law.named_reads
