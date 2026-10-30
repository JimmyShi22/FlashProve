-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/MemsAtPlan.lean: the field mems of PlanAt (MemsAt cs ms P rad nT:
Johnson/Desc/K1/Law/MemsAt.lean: "the list of members and the place fit"), RESTATED OVER THE PLAN's
SEATS, at the members by the make (msOf (P5T.memberListsR n radM ps); P5T.msAtR Z radM).
A law file; no running text imports it. What a member is there. Its shape and its seat are a plan's
seat's own; its radius is radM k i: k the sending's number, i the seat's number among that sending's
seats with an OOD sample. So MemsAt falls into: the code tables are one; A TEST ON THE PLAN's SEATS
ALONE (memsPairsB: at the seat of every message of the place that has an OOD sample a plan's seat
stands, and every plan's seat there has the message's shape); and ONE NAMED EQUATION ON THE RADII
(RadAt).
  tripleOf, triplesPlan, triples_of_sending, triples_membersR: the members' (shape, radius, seat),
      in order, are the plan's seats' own
  memsPairsB Y P nT: the test, on the pairs (shape, seat)
  RadAt n radM ps P rad nT: at each plan's seat that stands at the seat of a message j of the place
      with an OOD sample: radM k i = rad j
  memsAt_byMake, memsAt_atR: MemsAt from the three
  pairsFull: the pairs at the written seats
  placeL l d, baseL3 l d: the fifty later places at the placeholder qFull, and the number of trees
      in front of each: 3 * l + moment + 1
  mems_first, mems_fifty, mems_w: the test's accepts at the written seats (psFull;
      82 sendings) at all 52 places of the kind K1: Lean's kernel
  mems_base_rejects, mems_shape_rejects: the negative tests: one tree further no plan's seat stands;
      with one main row more in every plan's seat's shape the shapes part

What is not claimed. RadAt at any place: NO PAYER: the radii P5T.radOf are read off the rows
of the sendings at the three public files (0 where the rows have none), K1's files' off the written
list: that the two are one number is said by nothing here. That the number of trees in front of a
place is baseL3. That planSeats Z Z.D.1 = psFull at a seat. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.TestsOAtPlan
import Johnson.Desc.K1.Law.MemsAt
import Johnson.Desc.K1.Law.QFull
import Johnson.IMR.K1Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.Sound (Mem SitsAt seatOf msOf sendsOf membersOf Sending)
open _root_.Desc.K14.Law (pairsPlan)
open IM (k1Ix)

/-- A member's shape with its radius, and its seat. -/
def tripleOf (x : Mem) : (OracleShape × ℕ) × (ℕ × ℕ) := (x.1.l.get x.2, seatOf x)

/-- The like off the plan's seats. -/
def triplesPlan (n : ℕ) (radM : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) :
    List ((OracleShape × ℕ) × (ℕ × ℕ)) :=
  (List.range n).flatMap fun k =>
    (P5T.mineAt ps k).zipIdx.map fun y => ((y.1.shape, radM k y.2), y.1.seat)

theorem triples_of_sending (mine : List P5T.PSeat) (r : ℕ → ℕ) :
    (List.finRange (mine.zipIdx.map fun x => (x.1.shape, r x.2)).length).map
        (fun i => ((mine.zipIdx.map fun x => (x.1.shape, r x.2)).get i,
          (mine.map (·.seat)).getD i.val (0, 0))) =
      mine.zipIdx.map fun y => ((y.1.shape, r y.2), y.1.seat) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < mine.length := by simpa using h2
    simp [hi]

theorem triples_membersR (n : ℕ) (radM : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) :
    (msOf (P5T.memberListsR n radM ps)).map tripleOf = triplesPlan n radM ps := by
  unfold msOf sendsOf P5T.memberListsR triplesPlan
  rw [List.map_map]
  generalize List.range n = T
  induction T with
  | nil => rfl
  | cons k T ih =>
    simp only [membersOf, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih, List.map_map]
    congr 1
    exact triples_of_sending (P5T.mineAt ps k) (radM k)

/-- **The test on the plan's seats.** -/
def memsPairsB (Y : List (OracleShape × (ℕ × ℕ))) (P : Par) (nT : ℕ) : Bool :=
  (List.finRange (shapesOf P).length).all fun j =>
    !decide (sampledAt P j) ||
      ((Y.any fun y => y.2 == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) &&
        Y.all fun y =>
          !(y.2 == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) ||
            y.1 == shapeAt P j)

/-- **The one equation on the radii.** -/
def RadAt (n : ℕ) (radM : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) (P : Par) (rad : ℕ → ℕ) (nT : ℕ) :
    Prop :=
  ∀ j : Fin (shapesOf P).length, sampledAt P j → ∀ k, k < n → ∀ (i : ℕ) (p : P5T.PSeat),
    (P5T.mineAt ps k)[i]? = some p →
    p.seat = (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0) →
    radM k i = rad j.val

theorem pairs_of_triples (n : ℕ) (radM : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) {k i : ℕ}
    {q : P5T.PSeat} (hk : k < n) (hq : (P5T.mineAt ps k)[i]? = some q) :
    (q.shape, q.seat) ∈ pairsPlan n ps := by
  unfold pairsPlan
  exact List.mem_flatMap.2 ⟨k, List.mem_range.2 hk,
    List.mem_map.2 ⟨q, List.mem_of_getElem? hq, rfl⟩⟩

/-- **MemsAt at the members by the make**, from the code tables, the test on the plan's seats and
the equation on the radii. -/
theorem memsAt_byMake {cs : Codes} {n : ℕ} {radM : ℕ → ℕ → ℕ} {ps : List P5T.PSeat} {P : Par}
    {rad : ℕ → ℕ} {nT : ℕ} (hc : cs = P.codes) (hY : memsPairsB (pairsPlan n ps) P nT = true)
    (hr : RadAt n radM ps P rad nT) : MemsAt cs (msOf (P5T.memberListsR n radM ps)) P rad nT := by
  have key : ∀ j : Fin (shapesOf P).length, sampledAt P j →
      ((pairsPlan n ps).any fun y =>
        y.2 == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) = true ∧
      ((pairsPlan n ps).all fun y =>
        !(y.2 == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) ||
          y.1 == shapeAt P j) = true := by
    intro j hj
    have h1 := List.all_eq_true.1 hY j (List.mem_finRange j)
    rw [decide_eq_true hj, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
    exact h1
  refine ⟨hc, fun j hj => ?_, fun j hj x hx hs => ?_⟩
  · obtain ⟨y, hy, e⟩ := List.any_eq_true.1 (key j hj).1
    have hy' : y ∈ (msOf (P5T.memberListsR n radM ps)).map
        (fun x => ((x.1.l.get x.2).1, seatOf x)) := by
      rw [P5T.plain_membersR]
      exact hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    exact ⟨x, hx, eq_of_beq e⟩
  · have ht : tripleOf x ∈ triplesPlan n radM ps := by
      rw [← triples_membersR]
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    unfold triplesPlan at ht
    obtain ⟨k, hk, hm⟩ := List.mem_flatMap.1 ht
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
    have hq : (P5T.mineAt ps k)[y.2]? = some y.1 := by
      have := List.mem_zipIdx_iff_getElem?.1 (show (y.1, y.2) ∈ (P5T.mineAt ps k).zipIdx from hy)
      simpa using this
    have e1 : (y.1.shape, radM k y.2) = x.1.l.get x.2 := congrArg Prod.fst e
    have e2 : y.1.seat = x.1.seat x.2 := congrArg Prod.snd e
    have hs' : x.1.seat x.2 =
        (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0) := hs
    have hseat := e2.trans hs'
    have h2 := List.all_eq_true.1 (key j hj).2 _
      (pairs_of_triples n radM ps (List.mem_range.1 hk) hq)
    have h3 : (!(y.1.seat == (nT + (layOf P).tree.getD j.val 0, (layOf P).part.getD j.val 0)) ||
        y.1.shape == shapeAt P j) = true := h2
    rw [hseat, beq_self_eq_true, Bool.not_true, Bool.false_or] at h3
    rw [← e1, eq_of_beq h3, hr j hj k (List.mem_range.1 hk) y.2 y.1 hq hseat]

theorem memsAt_atR {cs : Codes} (Z : ProofFile.Pub) {radM : ℕ → ℕ → ℕ} {P : Par} {rad : ℕ → ℕ} {nT : ℕ}
    (hc : cs = P.codes)
    (hY : memsPairsB (pairsPlan Z.made.proof.1.sends.length (P5T.planSeats Z Z.D.1)) P nT = true)
    (hr : RadAt Z.made.proof.1.sends.length radM (P5T.planSeats Z Z.D.1) P rad nT) :
    MemsAt cs (P5T.msAtR Z radM) P rad nT := memsAt_byMake hc hY hr

/-! ## At the written seats -/

/-- The pairs at the written seats. -/
def pairsFull : List (OracleShape × (ℕ × ℕ)) :=
  pairsPlan Johnson.G.proofSendsFull.1.sends.length P5T.psFull

/-- The fifty later places at the placeholder, and the trees in front of each. -/
def placeL (l : ℕ) (d : Bool) : Par :=
  parLater qFull (⟨1, 0⟩ : _root_.Desc.Plain.GPar) l (k1Ix l d + 1) (cond d 2 1)

def baseL3 (l : ℕ) (d : Bool) : ℕ := 3 * l + cond d 2 1 + 1

set_option maxRecDepth 1000000 in
theorem mems_first : memsPairsB pairsFull (firstPar qFull ⟨1, 0⟩) 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem mems_fifty : ((List.range 25).all fun l =>
    memsPairsB pairsFull (placeL l false) (baseL3 l false) &&
      memsPairsB pairsFull (placeL l true) (baseL3 l true)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem mems_w : ((linMessageW qFull.lin).any fun msg =>
    memsPairsB pairsFull (parW qFull ⟨1, 0⟩ 4 msg) 82) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one tree further. -/
theorem mems_base_rejects : (memsPairsB pairsFull (firstPar qFull ⟨1, 0⟩) 1 ||
    memsPairsB pairsFull (placeL 7 true) (baseL3 7 true + 1) ||
    (linMessageW qFull.lin).any fun msg =>
      memsPairsB pairsFull (parW qFull ⟨1, 0⟩ 4 msg) 81) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the seats' shapes turned by one main row. -/
theorem mems_shape_rejects :
    memsPairsB (pairsFull.map fun y => ({ y.1 with mainRows := y.1.mainRows + 1 }, y.2))
      (placeL 7 true) (baseL3 7 true) = false := by decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.triples_membersR
#print axioms VerifiableInference.Desc.K1.memsAt_byMake
#print axioms VerifiableInference.Desc.K1.memsAt_atR
#print axioms VerifiableInference.Desc.K1.mems_first
#print axioms VerifiableInference.Desc.K1.mems_fifty
#print axioms VerifiableInference.Desc.K1.mems_w
#print axioms VerifiableInference.Desc.K1.mems_base_rejects
#print axioms VerifiableInference.Desc.K1.mems_shape_rejects
