-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SeatFitsB.lean: the code switch: `SeatFits G cs l seat`
(Johnson/Desc/Sound/MsgSig.lean: "the seats fit": a test on the plan alone) FROM A TEST WITH CODE,
at a typed list l and a function seat on its places.
KeptSeatOf.lean's `SeatFitAt` asks the seven clauses at ONE member:
that is `SeatFitOne` here. A law file; no running text imports it.

THE TEST AND ITS LAW AT ONE MEMBER ARE THE LIBRARY's: `seatFaultAt` (Johnson/Desc/SeatAt.lean),
`seatsFitB` (Johnson/Desc/PlanMem.lean), `seat_of_noFault` (Johnson/Desc/Sound/PlanMemProofs.lean).
They are called here. `SeatFits` is memberwise: of member i it reads the shape (l.get i).1 and the
seat alone: not the radius, not the order.

  `seatFits_of_noFault`   no member has a fault: the seats fit.
  `SeatFitOne`, `seatFits_iff`, `seatFitOne_of_noFault`   the seven clauses at ONE member:
                     `SeatFits`' own body; for a caller that spends them at some members alone.
  `noFault_of_B`    what a yes of `seatsFitB` says of member k of an entry.
  `seatFits_of_list`   a yes at the one entry (l, seats), where seats holds seat's values by
                     place.
  `seatFits_of_cover`  a yes at any lists L, where each member's shape and seat stand together at
                     some place of some entry of L.
  `seatFits_of_stretch`   so where l and seat are a stretch of one entry, by place, from a on.
  `coverB L l seats`, `cover_of_B`, `seatFits_of_coverB`   that premise as a test with code.
  Behind the theorems: two positive and six negative tests, five of them at the library's toy
  description (Johnson/Desc/BlockToy.lean: `FO`), by evaluation (#guard).
Limits. THE YES ITSELF IS A PREMISE: at a real plan it is known by an evaluation. That the lists are
the plan's is said by nothing here. NO VALUE AT ANY REAL PLAN IS SHOWN. Nothing on soundness or on
hiding.

-/
import Johnson.Desc.Sound.PlanMemProofs
import Johnson.Desc.BlockToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (FileDescription MemberLists seatsFitB seatFaultAt)
open VerifiableInference.Desc.Sound (SeatFits seat_of_noFault)

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)

/-- No member has a fault: the seats fit. -/
theorem seatFits_of_noFault (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (h : ∀ i : Fin l.length, seatFaultAt G cs "" (l.get i).1 (seat i).1 (seat i).2 = none) :
    SeatFits G cs l seat := fun i => seat_of_noFault G cs "" _ _ _ (h i)

/-- **The seven clauses at one member**: `SeatFits`' own body, to the letter.
K2Caller/KeptSeatOf.lean has the same body under the name `SeatFitAt`; that file
is not imported here: the two meet by unfolding
(a term of the one is a term of the other). -/
def SeatFitOne (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (i : Fin l.length) : Prop :=
  ∃ o n, G.oracleAt (seat i).1 = some o ∧ o.tenants[(seat i).2]? = some n ∧
    o.logLength = Johnson.Pack.aOf cs (l.get i).1 ∧
    n.main = (l.get i).1.mainRows * (l.get i).1.mainDeg ∧
    n.mask = (l.get i).1.maskRows * 3 ∧
    ((l.get i).1.mainRows = 0 ∨
      (Johnson.Pack.cMain cs (l.get i).1).a = Johnson.Pack.aOf cs (l.get i).1) ∧
    (o.tenants.map fun t => t.main + t.mask).sum = o.words ∧
    ((l.get i).1.mainDeg = 1 ∨ (l.get i).1.mainDeg = 3)

/-- `SeatFits` is that, at every member: by unfolding. -/
theorem seatFits_iff (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) :
    SeatFits G cs l seat ↔ ∀ i, SeatFitOne G cs l seat i := Iff.rfl

/-- One member without a fault. -/
theorem seatFitOne_of_noFault (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (i : Fin l.length)
    (h : seatFaultAt G cs "" (l.get i).1 (seat i).1 (seat i).2 = none) :
    SeatFitOne G cs l seat i := seat_of_noFault G cs "" _ _ _ h

/-- What a yes of the library's test says of member k of an entry. -/
theorem noFault_of_B {L : MemberLists} (h : seatsFitB G cs L = true)
    {e : List (OnBytes.OracleShape × ℕ) × List (ℕ × ℕ)} (he : e ∈ L) {k : ℕ}
    (hk : k < e.1.length) :
    seatFaultAt G cs "" (e.1.getD k default).1 (e.2.getD k (0, 0)).1 (e.2.getD k (0, 0)).2 =
      none := by
  have h1 := List.all_eq_true.1 h e he
  rw [Bool.and_eq_true] at h1
  exact Option.isNone_iff_eq_none.1 (List.all_eq_true.1 h1.2 k (List.mem_range.2 hk))

/-- **A yes at any lists, where each member's shape and seat stand together at some place.** -/
theorem seatFits_of_cover {L : MemberLists} (h : seatsFitB G cs L = true)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (hc : ∀ i : Fin l.length, ∃ e ∈ L, ∃ k, k < e.1.length ∧
      (e.1.getD k default).1 = (l.get i).1 ∧ e.2.getD k (0, 0) = seat i) :
    SeatFits G cs l seat :=
  seatFits_of_noFault G cs l seat fun i => by
    obtain ⟨e, he, k, hk, e1, e2⟩ := hc i
    have := noFault_of_B G cs h he hk
    rw [e1, e2] at this
    exact this

/-- **A yes at the one entry (l, seats).** -/
theorem seatFits_of_list (l : List (OnBytes.OracleShape × ℕ)) (seats : List (ℕ × ℕ))
    (h : seatsFitB G cs [(l, seats)] = true) (seat : Fin l.length → ℕ × ℕ)
    (hs : ∀ i : Fin l.length, seats[i.val]? = some (seat i)) : SeatFits G cs l seat :=
  seatFits_of_cover G cs h l seat fun i =>
    ⟨(l, seats), List.mem_singleton.2 rfl, i.val, i.isLt,
      congrArg Prod.fst (List.getD_eq_getElem _ _ i.isLt), by
        show seats.getD i.val (0, 0) = seat i
        rw [List.getD_eq_getElem?_getD, hs i]
        rfl⟩

/-- **A stretch of one entry, by place, from a on.** -/
theorem seatFits_of_stretch {L : MemberLists} (h : seatsFitB G cs L = true)
    {e : List (OnBytes.OracleShape × ℕ) × List (ℕ × ℕ)} (he : e ∈ L) (a : ℕ)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (hl : ∀ i : Fin l.length, ∃ x, e.1[a + i.val]? = some x ∧ x.1 = (l.get i).1)
    (hs : ∀ i : Fin l.length, e.2[a + i.val]? = some (seat i)) : SeatFits G cs l seat :=
  seatFits_of_cover G cs h l seat fun i => by
    obtain ⟨x, hx, e1⟩ := hl i
    refine ⟨e, he, a + i.val, (List.getElem?_eq_some_iff.1 hx).1, ?_, ?_⟩
    · rw [List.getD_eq_getElem?_getD, hx]
      exact e1
    · rw [List.getD_eq_getElem?_getD, hs i]
      rfl

/-- Each member's shape and seat stand together at some place of some entry: with code. -/
def coverB (L : MemberLists) (l : List (OnBytes.OracleShape × ℕ)) (seats : List (ℕ × ℕ)) : Bool :=
  l.length == seats.length && (List.range l.length).all fun i =>
    L.any fun e => (List.range e.1.length).any fun k =>
      decide ((e.1.getD k default).1 = (l.getD i default).1) &&
        e.2.getD k (0, 0) == seats.getD i (0, 0)

theorem cover_of_B {L : MemberLists} {l : List (OnBytes.OracleShape × ℕ)} {seats : List (ℕ × ℕ)}
    (h : coverB L l seats = true) (seat : Fin l.length → ℕ × ℕ)
    (hs : ∀ i : Fin l.length, seats[i.val]? = some (seat i)) :
    ∀ i : Fin l.length, ∃ e ∈ L, ∃ k, k < e.1.length ∧
      (e.1.getD k default).1 = (l.get i).1 ∧ e.2.getD k (0, 0) = seat i := by
  intro i
  unfold coverB at h
  rw [Bool.and_eq_true] at h
  have h1 := List.all_eq_true.1 h.2 i.val (List.mem_range.2 i.isLt)
  obtain ⟨e, he, h2⟩ := List.any_eq_true.1 h1
  obtain ⟨k, hk, h3⟩ := List.any_eq_true.1 h2
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h3
  refine ⟨e, he, k, List.mem_range.1 hk, ?_, ?_⟩
  · rw [h3.1]
    exact congrArg Prod.fst (List.getD_eq_getElem _ _ i.isLt)
  · rw [h3.2, List.getD_eq_getElem?_getD, hs i]
    rfl

/-- **Two yeses with code give that the seats fit.** -/
theorem seatFits_of_coverB {L : MemberLists} (h : seatsFitB G cs L = true)
    {l : List (OnBytes.OracleShape × ℕ)} {seats : List (ℕ × ℕ)} (hc : coverB L l seats = true)
    (seat : Fin l.length → ℕ × ℕ) (hs : ∀ i : Fin l.length, seats[i.val]? = some (seat i)) :
    SeatFits G cs l seat := seatFits_of_cover G cs h l seat (cover_of_B hc seat hs)

end

/-! ## Tests at the library's toy description, by evaluation -/

namespace Toy
open VerifiableInference.Desc VerifiableInference.Desc.BlockToy

/-- One code of 2^3 positions for main rows and one for mask rows. -/
def csT : OnBytes.Codes := { base := #[⟨3, 4, 1⟩], mask := #[⟨3, 4, 1⟩] }

/-- One main row over the base field, no mask row. -/
def sh : OnBytes.OracleShape :=
  { code := 0, mainRows := 1, mainDeg := 1, maskRows := 0, maskCode := 0 }

/-- The toy file, its shared chain's tree told as: 2^3 leaves, one word, one tenant of one main
word. -/
def FT : FileDescription Nat := FO ⟨3, 1, [⟨1, 0, 1, true, []⟩]⟩

/-- Does the member of the shape s fit at tenant t of some tree below 8? -/
def fitsSomewhere (F : FileDescription Nat) (s : OnBytes.OracleShape) (t : Nat) : Bool :=
  (List.range 8).any fun j => seatsFitB F csT [([(s, 0)], [(j, t)])]

-- the positive test: the told tree takes the member
#guard fitsSomewhere FT sh 0
-- a tenant that is not told
#guard !fitsSomewhere FT sh 1
-- two main rows against one told word
#guard !fitsSomewhere FT { sh with mainRows := 2 } 0
-- a tree that no sub-protocol tells
#guard !seatsFitB FT csT [([(sh, 0)], [(99, 0)])]
-- fewer seats than shapes
#guard !seatsFitB FT csT [([(sh, 0)], [])]
-- the cover: the pair stands in the lists; another seat does not
#guard coverB [([(sh, 7)], [(2, 0)])] [(sh, 0)] [(2, 0)]
#guard !coverB [([(sh, 7)], [(2, 0)])] [(sh, 0)] [(3, 0)]
#guard !coverB [([(sh, 7)], [(2, 0)])] [({ sh with mainRows := 2 }, 0)] [(2, 0)]

end Toy

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seatFits_of_list
#print axioms VerifiableInference.Desc.First.K2Caller.seatFits_of_cover
#print axioms VerifiableInference.Desc.First.K2Caller.seatFits_of_stretch
#print axioms VerifiableInference.Desc.First.K2Caller.seatFits_of_coverB
