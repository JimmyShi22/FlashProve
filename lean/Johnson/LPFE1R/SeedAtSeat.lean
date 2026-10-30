-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/SeedAtSeat.lean: e₁'s SHEET, ROW 130, THE LAST JOIN: THE SENDINGS' INVARIANT
`K1.SeedIs` AT EVERY MEMBER OF A WRITTEN LIST, AT THE NUMBER BY WHICH THE READER OF SAMPLES READS
                    THE MEMBER (`numAt`, Johnson/Desc/Sound/SmpNamed.lean: the place of its seat in
                    the plan's list of seats), AT A REACHED STATE UNDER THE PROMISE: the form in
                    which the clause "tied" of the closing kind K10 asks it. A join. Theorems. A law
                    file; no running text imports it.
  `place_back`       where the fold's fact "seatsCarried" holds: what the book lays at a number, the
                    plan's list of places has there.
  `seedIs_at_seat`   one message: SeedAtRch.lean's seedIs_of_held, its four premises on the state
                    paid by: the promise's bookAt · the fold's facts seatsCarried (atFirstSeats Ld)
                    and msgShapes (atFirstShapes M) · public: o lies below the plan's number of
                    messages sent; the plan's lists have the seat q and the shape sh at o; no place
                    stands twice in the plan's list.
  `held_of_onTR`     the table's own condition gives the composed meaning's "held" at every tenant
                    whose pin is open at the border.
  `seed_field`       at every member i of a list lo with seats seat: ∃ ρ y, K1.SeedIs cs (lo.get
i).1 s.st (numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y. CALLED: book_place · bookAt_sizes
(Johnson/Desc/First/Look/K3MaskOkTools.lean) · the door's msgShape_at
(Johnson/Desc/K12/Door/MsgShapes.lean).

Limits. At OnBytes.secondHashFunction. ON THE STATE, PREMISES: reached under the test on the words · bookAt ·
atFirstSeats · atFirstShapes · the codes · smpHeld at each member's seat. ON PUBLIC DATA, PREMISES,
evaluated at no plan here: hB (three clauses a member) · no place twice · K1.Tie. No member. Nothing
on soundness or on hiding.
-/
import Johnson.LPFE1R.SeedAtRch
import Johnson.Desc.First.Link.Law.LinkTiedR
import Johnson.Desc.First.Look.K3MaskOkTools
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes Johnson.Pack
open VerifiableInference.OnPublicFiles (book_place bookAt_sizes)
open VerifiableInference.Desc (Block Chain FileDescription Place smpHeld)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning bookAt sampledIn samplesHeld openSets
  start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes msgShape_at)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2 (frontOf)
open ProofFile (Cl)

/-- What the book lays at a number, the plan's list of places has there. -/
theorem place_back {s : S} {Ld : Laid} (hseats : atFirstSeats Ld s = true) {o : ℕ} {q : ℕ × ℕ}
    (h : s.book.place[o]? = some q) : Ld.places[o]? = some q := by
  have ho : o < s.book.place.size := (Array.getElem?_eq_some_iff.1 h).1
  unfold atFirstSeats Desc.K12.Door.seatsCarriedB at hseats
  simp only [Bool.and_eq_true] at hseats
  have e : s.book.place.toList = Ld.places.take s.book.place.size := eq_of_beq hseats.1.1.1
  rw [← Array.getElem?_toList, e, List.getElem?_take_of_lt ho] at h
  exact h

section
variable {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- One message, at its number in the plan's lists. -/
theorem seedIs_at_seat (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true) {k : ℕ}
    (hk : k ≤ (frontOf c).length) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) {cs : Codes} {N : Numbers}
    {p : Option Place} {Ld : Laid} {M : List OracleShape} (hc : s.st.codes = cs)
    (hbook : bookAt N p s = true) (hseats : atFirstSeats Ld s = true)
    (hshapes : atFirstShapes M s = true) (hnd : Ld.places.Nodup) {o : ℕ} {q : ℕ × ℕ}
    {sh : OracleShape} (hlt : o < N.msgsAt p) (hq : Ld.places[o]? = some q)
    (hM : M[o]? = some sh) (hh : smpHeld s.st s.book q.1 q.2 = true) (hT : K1.Tie cs sh) :
    ∃ ρ y, K1.SeedIs cs sh s.st o ρ y := by
  refine seedIs_of_held O hF hpl hk hr hc (j := q.1) (t := q.2) (book_place hbook hseats hlt hq)
    (fun o' h' => ?_) hh (fun x hx => ?_) hT
  · have h1 := place_back hseats h'
    have hl : o' < Ld.places.length := (List.getElem?_eq_some_iff.1 h1).1
    exact (List.getElem?_inj hl hnd (h1.trans hq.symm))
  · have hoS : o < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
    have hsh := msgShape_at hshapes o hoS
    rw [hx, hM] at hsh
    exact Option.some.inj hsh

/-- **At every member of a written list, at the reader of samples' own number.** -/
theorem seed_field (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true) {k : ℕ}
    (hk : k ≤ (frontOf c).length) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) {cs : Codes} {N : Numbers}
    {p : Option Place} {Ld : Laid} {M : List OracleShape} (hc : s.st.codes = cs)
    (hbook : bookAt N p s = true) (hseats : atFirstSeats Ld s = true)
    (hshapes : atFirstShapes M s = true) (hnd : Ld.places.Nodup) (seats : List (ℕ × ℕ))
    (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)
    (hB : ∀ i : Fin lo.length, seats.idxOf (seat i) < N.msgsAt p ∧
      Ld.places[seats.idxOf (seat i)]? = some (seat i) ∧
      M[seats.idxOf (seat i)]? = some (lo.get i).1)
    (hh : ∀ i : Fin lo.length, smpHeld s.st s.book (seat i).1 (seat i).2 = true)
    (hT : ∀ i : Fin lo.length, K1.Tie cs (lo.get i).1) (i : Fin lo.length) :
    ∃ ρ y, K1.SeedIs cs (lo.get i).1 s.st
      (VerifiableInference.Desc.Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y :=
  seedIs_at_seat O hF hpl hk hr hc hbook hseats hshapes hnd (hB i).1 (hB i).2.1 (hB i).2.2 (hh i)
    (hT i)

end

section
variable {A P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
  {ps : List Place} {get : A → P × S} {Rch : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {a : A × Fr.E.Str}

/-- The promise's "held", out of the table's own condition. -/
theorem held_of_onTR (h : onTR N Mg links ps get Rch k a) {x : ℕ × ℕ}
    (hx : x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])) :
    Mg.held x.1 x.2 (get a.1) = true := by
  obtain ⟨⟨hq, hm⟩, _⟩ := h
  rcases hq.2 with hf | ⟨_, hs, _⟩
  · exact absurd hf hm
  · unfold samplesHeld at hs
    exact List.all_eq_true.1 hs x hx

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.place_back
#print axioms VerifiableInference.Desc.LinkJoin.seedIs_at_seat
#print axioms VerifiableInference.Desc.LinkJoin.seed_field
#print axioms VerifiableInference.Desc.LinkJoin.held_of_onTR
