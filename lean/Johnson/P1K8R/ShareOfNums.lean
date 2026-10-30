-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ShareOfNums.lean: THE SMALLNESS TEST: THE STATE'S SHARE OF THE FIRST HALF OF "alike",
AT ONE STATE: each place of the state's list (lA, sA: Johnson/P1K8R/OwesAt.lean) has a seat of the
plan with a sample, of its shape and at its seat: the premise A of alike_of_rows
(Johnson/P1K8R/AlikeOfRows.lean), to the letter: from two tests with code at the state, "the numbers
of the state's list are among os", and ONE TEST WITH CODE THAT READS NO STATE.

  k8NumsB ps Ld M os   the test that reads no state: at every number o of the list os the laid list
                    has a seat jt, M has a shape sh, and some seat q of ps has a sample, the shape
                    sh and the seat jt
  k8Nums_at         what its yes gives at one number
  place_at          what "the seats are carried" gives at one number
  share_nums        the share at Named.listOf | Named.seatFn
  share_of_nums     THE SHARE, at lA | sA

THE ROAD. A member of the state's list is a number o with the shape of the statement's message o and
the book's place of o. Under atFirstShapes M the shape is M's at o; under atFirstSeats Ld the place
is Ld's at o.
A FIRST FORM ASKED A SEAT WITH A SAMPLE FOR EVERY TENANT OF THE TREES THAT THE SUB-PROTOCOL NAMES.
IT WAS EVALUATED AT THE FULL SIZE'S PUBLIC FILES AND SAID NO AT ALL 25 LINKS: each link's named
trees house one message without a sample. So this form asks the members' numbers alone.

Limits. The four premises are premises; none is shown here. No soundness statement.

-/
import Johnson.P1K8R.OwesAt
import Johnson.Desc.First.K8.LawNamed
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.P5T.NumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes seatsCarriedB msgShape_at)

/-- **The test that reads no state.** -/
def k8NumsB (ps : List P5T.PSeat) (Ld : Laid) (M : List OracleShape) (os : List ℕ) : Bool :=
  os.all fun o =>
    match Ld.places[o]?, M[o]? with
    | some jt, some sh =>
      ps.any fun q => q.smpd && decide (q.shape = sh) && decide (q.seat = jt)
    | _, _ => false

/-- What its yes gives at one number. -/
theorem k8Nums_at {ps : List P5T.PSeat} {Ld : Laid} {M : List OracleShape} {os : List ℕ}
    (h : k8NumsB ps Ld M os = true) {o : ℕ} (ho : o ∈ os) {jt : ℕ × ℕ} {sh : OracleShape}
    (h1 : Ld.places[o]? = some jt) (h2 : M[o]? = some sh) :
    ∃ q ∈ ps, q.smpd = true ∧ q.shape = sh ∧ q.seat = jt := by
  have hx := List.all_eq_true.1 h o ho
  simp only [h1, h2] at hx
  obtain ⟨q, hq, hb⟩ := List.any_eq_true.1 hx
  rw [Bool.and_eq_true, Bool.and_eq_true] at hb
  exact ⟨q, hq, hb.1.1, of_decide_eq_true hb.1.2, of_decide_eq_true hb.2⟩

/-- What "the seats are carried" gives at one number. -/
theorem place_at {Ld : Laid} {B : TreeBook} (h : seatsCarriedB Ld B = true) {o : ℕ} {jt : ℕ × ℕ}
    (ho : B.place[o]? = some jt) : Ld.places[o]? = some jt := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.place.toList = Ld.places.take B.place.size := eq_of_beq h.1.1.1
  have hlt : o < B.place.size := (Array.getElem?_eq_some_iff.1 ho).1
  have e1 : B.place.toList[o]? = some jt := by rw [Array.getElem?_toList]; exact ho
  rw [e, List.getElem?_take_of_lt hlt] at e1
  exact e1

/-- The share, at the functions that read the statement of oracles and the book. -/
theorem share_nums {ps : List P5T.PSeat} {Ld : Laid} {M : List OracleShape} {os : List ℕ}
    (rad : OracleShape → ℕ) (s : S) (tl : HTailF2) (L : LinkCtx)
    (hMs : ∀ o ∈ Named.msgs tl L, o ∈ os) (hSh : atFirstShapes M s = true)
    (hSe : atFirstSeats Ld s = true) (hT : k8NumsB ps Ld M os = true)
    (i : Fin (Named.listOf rad s.st s.book tl L).length) :
    ∃ q ∈ ps, q.smpd = true ∧ q.shape = ((Named.listOf rad s.st s.book tl L).get i).1 ∧
      q.seat = Named.seatFn rad s.st s.book tl L i := by
  have hlen : (Named.listOf rad s.st s.book tl L).length =
      (Named.members s.st s.book tl L).length := by
    unfold Named.listOf
    exact List.length_map _
  have hi : i.1 < (Named.members s.st s.book tl L).length := hlen ▸ i.isLt
  have hm : (Named.members s.st s.book tl L)[i.1] ∈ Named.members s.st s.book tl L :=
    List.getElem_mem hi
  have eL : ((Named.listOf rad s.st s.book tl L).get i).1 =
      (Named.members s.st s.book tl L)[i.1].2.1 := by
    unfold Named.listOf
    simp [List.get_eq_getElem]
  have eS : Named.seatFn rad s.st s.book tl L i = (Named.members s.st s.book tl L)[i.1].2.2 := by
    unfold Named.seatFn Named.seatsOf
    simp [List.get_eq_getElem]
  rw [eL, eS]
  generalize (Named.members s.st s.book tl L)[i.1] = m at hm
  unfold Named.members at hm
  obtain ⟨o, ho, hom⟩ := List.mem_filterMap.1 hm
  obtain ⟨y, h1, rfl⟩ := Option.map_eq_some_iff.1 hom
  unfold Named.memberAt at h1
  cases hx : s.st.oracles[o]? with
  | none => simp [hx] at h1
  | some x =>
    cases hj : s.book.place[o]? with
    | none => simp [hx, hj] at h1
    | some jt =>
      simp only [hx, hj] at h1
      obtain rfl : (x.shape, jt) = y := Option.some.inj h1
      have hlt : o < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
      have e2 : M[o]? = some x.shape := by
        rw [← msgShape_at hSh o hlt, hx]
        rfl
      exact k8Nums_at hT (hMs o ho) (place_at hSe hj) e2

/-- **THE STATE'S SHARE OF THE FIRST HALF OF "alike", AT ONE STATE.** -/
theorem share_of_nums {ps : List P5T.PSeat} {Ld : Laid} {M : List OracleShape} {os : List ℕ}
    (rad : OracleShape → ℕ) (s : S) (tl : HTailF2) (L : LinkCtx)
    (hMs : ∀ o ∈ Named.msgs tl L, o ∈ os) (hSh : atFirstShapes M s = true)
    (hSe : atFirstSeats Ld s = true) (hT : k8NumsB ps Ld M os = true) :
    ∀ i : Fin (lA rad s tl L).length, ∃ q ∈ ps, q.smpd = true ∧
      q.shape = ((lA rad s tl L).get i).1 ∧ q.seat = sA rad s tl L i := by
  unfold lA sA
  exact share_nums rad s tl L hMs hSh hSe hT

end P1K8T

#print axioms P1K8T.k8Nums_at
#print axioms P1K8T.place_at
#print axioms P1K8T.share_nums
#print axioms P1K8T.share_of_nums
