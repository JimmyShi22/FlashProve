-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerAttReads.lean: THE GUARDS OF THE CALLER's READING AGAINST A SILENT 0
(AttReadsOK, K3CallerAtt.lean) FROM TESTS THAT A PROGRAM CAN RUN IN A MOMENT: no walk over the
symbols. Definitions with code, statements and proofs. NO SOUNDNESS IS CLAIMED.

Why. The closed callers of the lookups on a link's calls read a symbol or a mask entry that has no
seat as 0. AttReadsOK shuts that; three of its four fields speak of the seats alone and are the same
at all three sorts of link (the layers' and the head's callers read by the same symAt | seatCalls).
«seated» speaks of every symbol of every matrix of the sub-proof's list: millions.
K3CallerLaid.lean has the road: an array is laid in a few dozen blocks; if the blocks lie
inside the array, no two share an element and their sizes add up, every element has a place.

Main names:
  `symArrB D l i t R K`: the test on array number t of link i's list, of R rows and K columns:
    arrayOf names it; the layout has it under the link that sent it; its message stands in the
    signature's list l: behind the kept ones if it is the link's own, else as the kept message that
    took its rows; blocksB at R, K and that message's main rows and their length.
  `sym_seated`: under it every element (r, c), r < R, c < K, has a seat that fits.
  `maskCallsB`, `mask_seated`: the like for the mask entries below a bound.
  `seatsB`: symArrB at every matrix of the list (its symbols' rows; its columns) and maskCallsB up
    to the lookup's last mask entry. `seated_of`: its yes gives AttReadsOK's field seated.
  `sampledB`, `keptSameB` with `sampled_of`, `keptSame_of`.
  `readsB`: the three together. `attReadsOK_of`: with the fourth field as a premise: AttReadsOK.
Limits. THE FOURTH FIELD, cellsIn («every valid name of a cell has a cell of the list's matrices»),
IS NOT HAD HERE: it is arithmetic on the library's rule of addresses, at attention alone. blocksB is
a test written here after the programs' own; no theorem says that a yes of the programs' reqLayoutOk
gives it. Nothing is evaluated in this file.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Desc.First.Look.K3CallerLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)

/-- In which message of the signature's list the array's message stands. bn: (the link that sent the
array, its name). msg: the array's message's number among that link's. -/
def msgIn (D : Sent) (i b msg : Nat) : Option Nat :=
  if b == i then some ((keptAt D i).length + msg) else (bornAt D i).idxOf? (b, msg)

/-- **The test on array number t of link i's list**, of R rows and K columns. -/
def symArrB (D : Sent) (l : List (OracleShape × Nat)) (i t R K : Nat) : Bool :=
  match (D.arrayOf.getD i #[])[t]? with
  | some bn =>
    match OnBytes.reqArray D.layout bn.1 bn.2 with
    | some a =>
      match msgIn D i bn.1 a.message with
      | some k =>
        match l[k]? with
        | some o => blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D.codes o.1).ell
        | none => false
      | none => false
    | none => false
  | none => false

/-- **Under the test every element of the array has a seat, and the seat fits.** -/
theorem sym_seated {D : Sent} {l : List (OracleShape × Nat)} {i t R K : ℕ}
    (h : symArrB D l i t R K = true) {r c : ℕ} (hr : r < R) (hc : c < K) :
    ∃ s, seatCalls D i (.cell t r c) = some s ∧ s.Fits D.codes l := by
  unfold symArrB at h
  split at h
  · rename_i bn hbn
    split at h
    · rename_i a ha
      split at h
      · rename_i k hk
        split at h
        · rename_i o ho
          obtain ⟨hkl, eo⟩ := List.getElem?_eq_some_iff.1 ho
          obtain ⟨rp, e1, e2, e3⟩ := laidPlace_some h hr hc
          refine ⟨⟨k, false, rp.1, rp.2⟩, ?_, hkl, ?_⟩
          · unfold msgIn at hk
            by_cases hb : (bn.1 == i) = true
            · rw [if_pos hb] at hk
              simp only [seatCalls, hbn, Option.bind_some, ha, e1, hb, if_true]
              rw [Option.some.inj hk]
            · rw [if_neg hb] at hk
              simp only [seatCalls, hbn, Option.bind_some, ha, e1, hb, hk, Option.map_some]
              rfl
          · rw [if_neg (by simp)]
            show rp.1 < (l.get ⟨k, hkl⟩).1.mainRows ∧ _
            rw [List.get_eq_getElem, eo]
            exact ⟨e2, e3⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- **The test on the mask row**, behind the kept messages. -/
def maskCallsB (D : Sent) (l : List (OracleShape × Nat)) (i upTo : Nat) : Bool :=
  match (messagesAt D i).findIdx? fun x => x.shape.maskRows != 0 with
  | some m =>
    match l[(keptAt D i).length + m]? with
    | some o => decide (0 < o.1.maskRows) && decide (upTo ≤ (Johnson.Pack.pMask D.codes o.1).ell)
    | none => false
  | none => false

theorem mask_seated {D : Sent} {l : List (OracleShape × Nat)} {i upTo : ℕ}
    (h : maskCallsB D l i upTo = true) {j : ℕ} (hj : j < upTo) :
    ∃ s, seatCalls D i (.mask j) = some s ∧ s.Fits D.codes l := by
  unfold maskCallsB at h
  split at h
  · rename_i m hm
    split at h
    · rename_i o ho
      obtain ⟨hk, eo⟩ := List.getElem?_eq_some_iff.1 ho
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨⟨(keptAt D i).length + m, true, 0, j⟩, ?_, hk, ?_⟩
      · simp only [seatCalls, hm, Option.map_some]
      · rw [if_pos rfl]
        show 0 < (l.get ⟨(keptAt D i).length + m, hk⟩).1.maskRows ∧ _
        rw [List.get_eq_getElem, eo]
        exact ⟨h.1, Nat.lt_of_lt_of_le hj h.2⟩
    · cases h
  · cases h

/-- **Every symbol of every matrix of the list, and every mask entry of the lookup, has a seat.** -/
def seatsB (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) : Bool :=
  ((List.range (szOf tl).NM).all fun μ =>
    symArrB D (sigListCalls D rad x.link) x.link (tl.gtTree.getD μ 0)
      (Alg.symRows ((szOf tl).m μ)) ((szOf tl).k μ)) &&
    maskCallsB D (sigListCalls D rad x.link) x.link (x.F.next + FoNums.nMasks x.fs)

theorem seated_of {x : Place} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat}
    (e : seatsB x tl D rad = true) :
    Seated D.codes (sigListCalls D rad x.link) (seatCalls D x.link)
      (ReadsAtt tl x.fs x.F.next) := by
  unfold seatsB at e
  rw [Bool.and_eq_true] at e
  intro a ha
  cases ha with
  | sym μ i' c =>
    exact sym_seated (List.all_eq_true.1 e.1 μ.val (List.mem_range.2 μ.isLt)) i'.isLt c.isLt
  | mask s hs => exact mask_seated e.2 (Nat.add_lt_add_left hs _)

def sampledB (x : Place) (D : Sent) (rad : OracleShape → Nat) : Bool :=
  (sigListCalls D rad x.link).all fun o => o.1.answers == 1

theorem sampled_of {x : Place} {D : Sent} {rad : OracleShape → Nat}
    (e : sampledB x D rad = true) : ∀ o ∈ sigListCalls D rad x.link, o.1.answers = 1 :=
  fun o ho => beq_iff_eq.1 (List.all_eq_true.1 e o ho)

def keptSameB (x : Place) (D : Sent) : Bool :=
  (List.range (keptAt D x.link).length).all fun k =>
    decide ((((messagesAt D ((bornAt D x.link).getD k (0, 0)).1)[((bornAt D x.link).getD k
      (0, 0)).2]?).map (·.shape)) = ((keptAt D x.link)[k]?).map (·.shape))

theorem keptSame_of {x : Place} {D : Sent} (e : keptSameB x D = true) :
    ∀ k (hk : k < (keptAt D x.link).length),
      (((messagesAt D ((bornAt D x.link).getD k (0, 0)).1)[((bornAt D x.link).getD k
        (0, 0)).2]?).map (·.shape)) = some ((keptAt D x.link).get ⟨k, hk⟩).shape := by
  intro k hk
  have h := of_decide_eq_true (List.all_eq_true.1 e k (List.mem_range.2 hk))
  rw [h, List.getElem?_eq_getElem hk]
  rfl

/-- **The three guards that speak of the seats, as one Bool.** -/
def readsB (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) : Bool :=
  sampledB x D rad && keptSameB x D && seatsB x tl D rad

/-- **A yes, with the fourth field, gives AttReadsOK.** -/
theorem attReadsOK_of {x : Place} {S : Attention.Shape} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} (e : readsB x tl D rad = true)
    (hc : ∀ r : Inst.Model.AttSeg.Raw, r.Valid (Road.L5.dimOf S) →
      (cellJ (szOf tl) (Road.L5.addrA S r).1 (Road.L5.addrA S r).2.1
        (Road.L5.addrA S r).2.2).isSome = true) : AttReadsOK x S tl D rad := by
  unfold readsB at e
  rw [Bool.and_eq_true, Bool.and_eq_true] at e
  exact ⟨sampled_of e.1.1, keptSame_of e.1.2, seated_of e.2, hc⟩

#print axioms sym_seated
#print axioms mask_seated
#print axioms seated_of
#print axioms attReadsOK_of

end VerifiableInference.Desc.First.Look
