-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/LotPlaces.lean: the closing of a segment (K10): where the halves stand that the lot
lays for the kind: no two at one place, and none at a place that the description's first chain lacks. Lemmas; no
definition.

  `open_first`     the first chain of the description that `IM.Open` opens is c, as a heterogeneous equation
  `filterMap_key`, `par_link`, `filter_le_one`   three small ones
  `places_once`, `halves_once`   under `IM.Open` (Johnson/IMR/SeatOpen.lean): no two of the kind's places that the lot
                   (`seatLotT`, Honest/K10/SeatLotT.lean; `seatLotC`) reads are one place; so of the halves. At every
                   older hash; no premise on scope
  `pars_tied`      in scope each of the kind's numbers that the lot reads is the Q of `Tied` (Honest/K10/SimLot.lean) at
                   a link l < 25
  **`no_twice`**, **`no_strays`**   the frame's two tests on halves (`twice`, `strays`, Honest/Frame.lean) find nothing
                   among the kind's halves; `strays` at the description's own list `F.first.blocksInOrder`, in scope
  **`seatLotC_once`**, **`seatLotC_no_twice`**, **`seatLotC_no_strays`**   the same of the halves of `seatLotC`
                   (Honest/K10/SeatLotC.lean), which are these

Limits. readers, rows and stAt are letters: nothing of them is read. `pars_tied`, `no_strays` and `seatLotC_no_strays`:
at `OnBytes.secondHashFunction` alone, in the goals' scope: for the two on `strays` that hash and the scope are not needed:
`seatLotC_clean` (Honest/K10/LotAll.lean) has, under `IM.Open` alone, `seatLotC_no_strays`' conclusion to the sign, and
`no_strays`' once `seatLotC`'s halves are written out (`lot_no_strays` there has it of the wider list, with K9's own
halves); the two are left as they were. `places_once`, `halves_once`, `no_twice` and the two at `seatLotC` hold also
where `closePars Z` is empty: there for nothing. Whether `IM.Open` can be had is no theorem. F is a description at
`ProofFile.Inst`, the halves stand at a letter Xi: the frame's calls want the same one for both. Of another lot's halves
nothing is said. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SeatLotC
import Johnson.Desc.ProofFile.Honest.K10.SimLot
import Johnson.Desc.K10.Honest.LinksOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (segmentsOf)

variable {W₀ Rc Xi Tr V W X : Type}

/-! ## The description's own first chain -/

/-- **The first chain of the description that `IM.Open` opens is c**, as a heterogeneous equation: F is the maker's term
(the field `desc`), and that term's first chain is c by reduction. -/
theorem open_first {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) : HEq F.first c := by
  obtain rfl := O.desc
  exact HEq.rfl

/-! ## No stray, none twice -/

theorem filterMap_key {α : Type} (f : Nat → Option α) (key : α → Nat)
    (hk : ∀ l a, f l = some a → key a = l) : ∀ L : List Nat, ((L.filterMap f).map key).Sublist L
  | [] => List.Sublist.slnil
  | l :: L => by
    cases h : f l with
    | none =>
      rw [List.filterMap_cons_none h]
      exact (filterMap_key f key hk L).cons _
    | some a =>
      rw [List.filterMap_cons_some h, List.map_cons, hk l a h]
      exact (filterMap_key f key hk L).cons₂ _

/-- The numbers that the lot reads at a link bear that link's number. -/
theorem par_link {Z : ProofFile.Pub} {l : Nat} {Q : Par}
    (h : ((ProofFile.k9Where (ProofFile.k9Stretches Z) l).bind fun p => ProofFile.k10Par Z (ProofFile.k9Stretches Z) p) =
      some Q) : Q.link = l := by
  obtain ⟨p, hp, hQ⟩ := Option.bind_eq_some_iff.1 h
  rw [(IM.k10Par_fields hQ).1, (IM.k9Where_fields hp).2.1]

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **None twice**: no two of the kind's places that the lot reads are one place. At every older hash; no premise on
scope. -/
theorem places_once (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ((closePars Z).map closePlace).Nodup := by
  have h1 : ((closePars Z).map (·.link)).Nodup :=
    (filterMap_key _ (·.link) (fun _ _ h => par_link h) _).nodup (YesFree.links_once O).1
  refine List.Nodup.of_map (fun a : Place => a.link.getD 0) ?_
  rw [List.map_map]
  exact h1

/-- So of the halves that the lot lays for the kind. -/
theorem halves_once (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : Ground)
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ((seatClosings (X := X) (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G).map
      (·.place)).Nodup := by
  rw [closingsT_are, List.map_map]
  exact places_once O

end

/-- **No stray**, in scope: each of the kind's numbers that the lot reads is the Q of `Tied` at a link l < 25. -/
theorem pars_tied {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Q : Par}
    (hQ : Q ∈ closePars Z) :
    ∃ (l : Nat) (p : VerifiableInference.Desc.K9.Where) (b : Block S ProofFile.Cl),
      l < 25 ∧ Tied c Z l p Q b := by
  obtain ⟨l, hl, hf⟩ := List.mem_filterMap.1 hQ
  have hl25 := ((YesFree.links_scope hS hR O).2 l).1 hl
  obtain ⟨p, Q', b, hT⟩ := tied_at_scope hS hR O l hl25
  obtain ⟨p', hp', hQ'⟩ := Option.bind_eq_some_iff.1 hf
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hT.1)
  obtain rfl : Q = Q' := Option.some.inj (hQ'.symm.trans hT.2.1)
  exact ⟨l, p', b, hl25, hT⟩

/-! ## The frame's own two tests on halves, at the kind's halves -/

theorem filter_le_one.{u} {α : Type u} (f : α → Place) : ∀ hs : List α, (hs.map f).Nodup →
    ∀ a, (hs.filter fun h => f h == a).length ≤ 1
  | [], _, _ => Nat.zero_le _
  | h :: hs, hn, a => by
    rw [List.map_cons, List.nodup_cons] at hn
    have ih := filter_le_one f hs hn.2 a
    by_cases e : f h = a
    · subst e
      have h0 : (hs.filter fun x => f x == f h) = [] := by
        refine List.filter_eq_nil_iff.2 fun x hx hb => hn.1 ?_
        rw [← eq_of_beq hb]
        exact List.mem_map.2 ⟨x, hx, rfl⟩
      rw [List.filter_cons_of_pos (by exact beq_self_eq_true _), h0]
      exact Nat.le_refl _
    · rw [List.filter_cons_of_neg (by simpa using e)]
      exact ih

/-- **`twice` (Honest/Frame.lean) finds nothing among the kind's halves.** At every older hash; no premise on scope. -/
theorem no_twice (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : Ground)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) :
    twice (seatClosings (X := X) (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G) = [] := by
  have hn := halves_once (X := X) readers rows stAt G O
  unfold twice
  rw [List.filter_eq_nil_iff.2 fun a _ hb => ?_]
  · rfl
  · have h1 := filter_le_one
      (fun h : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X => h.place) _ hn a
    have h2 : 1 < ((seatClosings (X := X) (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G).filter
        fun h => h.place == a).length := by simpa using hb
    omega

/-- **`strays` (Honest/Frame.lean) finds nothing among the kind's halves, at the description's own list
`F.first.blocksInOrder`**, in scope. -/
theorem no_strays (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : Ground)
    {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    strays F.first.blocksInOrder
      (seatClosings (X := X) (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G) = [] := by
  have key : ∀ h ∈ seatClosings (X := X) (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G,
      ∃ b ∈ c.blocksInOrder, b.place = h.place := by
    intro h hh
    rw [closingsT_are] at hh
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hh
    obtain ⟨l, p, b, _, hT⟩ := pars_tied hS hR O hQ
    exact ⟨b, List.mem_of_getElem? hT.2.2.1, hT.2.2.2.2.2.1⟩
  obtain rfl := O.desc
  unfold strays
  rw [List.filter_eq_nil_iff.2 fun h hh hb => ?_]
  · rfl
  · obtain ⟨b, hb1, hb2⟩ := key h hh
    have h1 : (c.blocksInOrder.any fun b => b.place == h.place) = true :=
      List.any_eq_true.2 ⟨b, hb1, by rw [hb2]; exact beq_self_eq_true _⟩
    have h2 : (!(c.blocksInOrder.any fun b => b.place == h.place)) = true := hb
    rw [h1] at h2
    cases h2

/-! ## The same of the lot with the closings alone -/

/-- No two halves of `seatLotC` stand at one place. -/
theorem seatLotC_once (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : Ground)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    (((seatLotC (X := X) readers rows stAt).halves Z G).map (·.place)).Nodup :=
  halves_once readers rows stAt G O

/-- `twice` finds nothing among the halves of `seatLotC`. -/
theorem seatLotC_no_twice (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : Ground)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) :
    twice ((seatLotC (X := X) readers rows stAt).halves Z G) = [] :=
  no_twice readers rows stAt G O

/-- **`strays` finds nothing among the halves of `seatLotC`, at the description's own list**, in scope. -/
theorem seatLotC_no_strays (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : Ground)
    {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    strays F.first.blocksInOrder ((seatLotC (X := X) readers rows stAt).halves Z G) = [] :=
  no_strays readers rows stAt G hS hR O

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.open_first
#print axioms ProofFile.Honest.K10.filterMap_key
#print axioms ProofFile.Honest.K10.par_link
#print axioms ProofFile.Honest.K10.places_once
#print axioms ProofFile.Honest.K10.halves_once
#print axioms ProofFile.Honest.K10.pars_tied
#print axioms ProofFile.Honest.K10.filter_le_one
#print axioms ProofFile.Honest.K10.no_twice
#print axioms ProofFile.Honest.K10.no_strays
#print axioms ProofFile.Honest.K10.seatLotC_once
#print axioms ProofFile.Honest.K10.seatLotC_no_twice
#print axioms ProofFile.Honest.K10.seatLotC_no_strays
