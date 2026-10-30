-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SidePaysThrough.lean: what a side pays (`SidePays`,
Honest/Law/ReadyOfSides.lean) survives reading the side through two maps, and how a kind's payment
crosses `OnlineProverParts.through` (Honest/ThruK13.lean). Kind-free: no kind, lot or value of a filling is
named. No definition.

  `chainSteps_one_found`          at one member, `chainSteps` reads of the list of sides only what
                                  a search at the member's place finds
  `sidePays_thru`                 a side read through pays where the side pays
  `sidePays_of_thru`              the converse
  `atPure_base_of_through`        where the maker returns at a filling read through it returns at
                                  the filling, with the same public part, ground, description and
                                  book: the maker makes these four before it looks at the filling
  `side_of_through`               a side of the return's first chain is a base side read through
  `kindPays_of_base_sides`        **the general form**: every side of kind κ of the base filling pays
                                  at the return's book, so the kind pays at the return; with its
                                  twins `kindPays_shared_of_base_sides`, `kindPays_second_of_base_sides`
  `kindPays_of_through_sides`     the same with the payment at the side read through; and its twins
  `lot_holds_kind`                where the other lots lay no side of kind κ, every side of that kind
                                  in the return's first chain is a side of the one lot read through
  `kindPays_through`              the form for one lot, paid at its sides read through
  `kindPays_through_of_base`      the form for one lot, paid by a law at the base filling's return

Which form a kind calls. A lot that is general in the types of its input gets its payment at the
return itself, by its own law at any filling, and calls `kindPays_through` with the equation that
its lot read through is the lot at the new types. A lot that stands at the base filling's types calls
`kindPays_through_of_base`. A kind with several lots, or with sides in the other two chains, calls
`kindPays_of_base_sides` or its twins: no equation is asked there. The forms in `LotPays` are in
K5/Law/LotPaysThrough.lean. This file imports K5/Law/ReturnsOf.lean for `parts_of_atPure`,
`atPure_of_parts` and `strays_firstOf_iff`, which are general in the filling; with it come
K5/Law/LotClean.lean and some 180 files that the other imports do not bring.

Kin. `atPure_book_same` (Honest/AtPureBook.lean) compares two returns that exist;
`atPure_base_of_through` makes the second. `makerAsks_through` (Honest/ThruMade.lean) goes from the
filling to the filling read through; this file goes back.

Limits.
  * What is paid is that `chainSteps` returns at the members. Nothing here says that a part plays, or
    that a verifier accepts.
  * `atPure_base_of_through` asks that the base filling's named member is in range.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.ThruRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block KindName)

/-! ## 1 One side, one lot -/

section
variable {S Cl V V' W W' X : Type}

/-- **At one member, `chainSteps` reads of the list of sides only what a search at its place finds.**
-/
theorem chainSteps_one_found (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (v : Option V) (b : Block S Cl) {hs hs' : List (Placed V W X)}
    (e : (hs.find? fun q => q.place == b.place) = hs'.find? fun q => q.place == b.place) :
    chainSteps B rows look v [b] hs = chainSteps B rows look v [b] hs' := by
  simp only [chainSteps, e]

/-- A search at a side's own place in the list of that side finds it. -/
theorem find_own_place {b : Block S Cl} {g : Placed V W X} (h : b.place = g.place) :
    ([g].find? fun q => q.place == b.place) = some g := by
  simp [h]

/-- Where `chainSteps` returns at a member with the side alone, it returns with the side read
through first at that place. -/
theorem steps_of_thru (see : V' → V) (wit : W' → W) {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {v' : Option V'} (hv : v'.map see = v)
    {b : Block S Cl} {g : Placed V W X} (hbg : b.place = g.place)
    (hone : ∃ l, chainSteps B rows look v [b] [g] = .ok l) {hs : List (Placed V' W' X)}
    (hf : (hs.find? fun q => q.place == b.place) = some (g.thru see wit)) :
    ∃ l, chainSteps B rows look v' [b] hs = .ok l := by
  obtain ⟨l, hl⟩ := hone
  have e := chainSteps_thru see wit B rows look v v' hv [b] [g]
  rw [hl] at e
  have hm : (([g].map (Placed.thru see wit)).find? fun q => q.place == b.place) =
      some (g.thru see wit) := find_own_place (g := g.thru see wit) hbg
  exact ⟨l.map (Step.thru wit), (chainSteps_one_found B rows look v' b (hf.trans hm.symm)).trans e⟩

/-- **A side read through pays where the side pays.** `see`, `wit`: any. -/
theorem sidePays_thru (see : V' → V) (wit : W' → W) {B : ProverCoinCounts} {ch : Nat} {bs : List (Block S Cl)}
    {g : Placed V W X} (hp : SidePays B ch bs g) : SidePays B ch bs (g.thru see wit) := by
  intro b hb hbp hs hf v' k
  exact steps_of_thru see wit rfl hbp (hp b hb hbp [g] (find_own_place hbp) (v'.map see) k) hf

/-- **A side pays where the side read through pays.** `see`, `wit`: any. -/
theorem sidePays_of_thru (see : V' → V) (wit : W' → W) {B : ProverCoinCounts} {ch : Nat}
    {bs : List (Block S Cl)} {g : Placed V W X} (hp : SidePays B ch bs (g.thru see wit)) :
    SidePays B ch bs g := by
  intro b hb hbp hs hf v k
  have hbp' : b.place = (g.thru see wit).place := hbp
  have hm : (([g].map (Placed.thru see wit)).find? fun q => q.place == b.place) =
      some (g.thru see wit) := find_own_place hbp'
  obtain ⟨l, hl⟩ := hp b hb hbp' ([g].map (Placed.thru see wit)) hm none k
  have e := chainSteps_thru see wit B (B.rowsOf ch) (k.look ch) (none : Option V)
    (none : Option V') rfl [b] [g]
  rw [hl] at e
  cases hc : chainSteps B (B.rowsOf ch) (k.look ch) (none : Option V) [b] [g] with
  | error x =>
    rw [hc] at e
    cases e
  | ok l₀ =>
    obtain ⟨l', h'⟩ := chainSteps_any (fun _ => rfl) B (B.rowsOf ch) (none : Option V) v [g] [b]
      l₀ hc
    exact ⟨l', (chainSteps_one_found B _ _ v b (hf.trans (find_own_place hbp).symm)).trans h'⟩

end

/-! ## 2 The maker at a filling read through -/

section
variable {W₀ W₀' Rc Rc' Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  {P : OnlineProverParts W₀ Rc Tr X₀ X}

/-- **Where the maker returns at a filling read through, it returns at the filling, with the same
public part, ground, description and book.** Conditional: hA; hd: the base filling's named member is
in range. -/
theorem atPure_base_of_through (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (hd : P.inRange P.dummy = true) :
    ∃ A₀ : OnlineProverWithDescription W₀ Rc Tr X₀ X, onlineProverFromPublicFiles o pol lay KL P = .ok A₀ ∧ A₀.Z = A.Z ∧ A₀.G = A.G ∧
      A₀.F = A.F ∧ A₀.B = A.B := by
  obtain ⟨m, a⟩ := K5.parts_of_atPure hA
  refine K5.atPure_of_parts m ⟨?_, ?_, ?_, hd⟩
  · refine (K5.strays_firstOf_iff _ _ _ _).2 fun L hL => ?_
    have h := (K5.strays_firstOf_iff _ _ _ _).1 a.first
      (L.thru (Local.thru g rd) (Local.thru g rd)) (List.mem_map_of_mem hL)
    exact (strays_keep_places (Placed.thru (Local.thru g rd) (Local.thru g rd)) (fun _ => rfl) _
      _).symm.trans h
  · exact (strays_keep_places (Placed.thru id (Common.thru g rd)) (fun _ => rfl) _ _).symm.trans
      a.shared
  · exact (strays_keep_places (Placed.thru (Local.thru g rd) (Local.thru g rd)) (fun _ => rfl) _
      _).symm.trans a.second

/-- **A side of the return's first chain is a side of a lot of the base filling, read through.** -/
theorem side_of_through (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀') {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A) :
    ∀ q ∈ A.H.first, ∃ L ∈ P.lots, ∃ x ∈ L.halves A.Z A.G,
      q = x.thru (Local.thru g rd) (Local.thru g rd) := by
  obtain ⟨-, -, -, -, -, -, -, eH1, -⟩ := atPure_ok hA
  intro q hq
  rw [eH1] at hq
  obtain ⟨M', hM', hqM⟩ := List.mem_flatMap.1
    (hq : q ∈ (OnlineProverParts.through g rd d' P).lots.flatMap fun L => L.halves A.Z A.G)
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1
    (hM' : M' ∈ P.lots.map (HLot.thru (Local.thru g rd) (Local.thru g rd)))
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1
    (hqM : q ∈ (M.halves A.Z A.G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)))
  exact ⟨M, hM, x, hx, rfl⟩

/-- **A side of a lot of the base filling, read through, stands in the return's first chain.** -/
theorem through_side_mem (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀') {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A) {L : HLot (Local W₀ Rc Inst Tr)
                                        (Local W₀ Rc Inst Tr) X} (hL : L ∈ P.lots) {x : Placed (Local W₀ Rc Inst Tr)
                                        (Local W₀ Rc Inst Tr) X} (hx : x ∈ L.halves A.Z A.G) :
    x.thru (Local.thru g rd) (Local.thru g rd) ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, eH1, -⟩ := atPure_ok hA
  rw [eH1]
  exact List.mem_flatMap.2 ⟨L.thru (Local.thru g rd) (Local.thru g rd), List.mem_map_of_mem hL,
    List.mem_map_of_mem hx⟩

/-! ## 3 A kind's payment -/

variable {S Cl : Type} {bs : List (Block S Cl)} {κ : KindName}

/-- **The general form: where every base side of kind κ pays when read through, the kind pays at
the return's first chain.** -/
theorem kindPays_of_through_sides (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (H : ∀ L ∈ P.lots, ∀ x ∈ L.halves A.Z A.G, x.place.kind = κ →
      SidePays A.B 0 bs (x.thru (Local.thru g rd) (Local.thru g rd))) :
    KindPays A.B 0 bs A.H.first κ := by
  intro q hq hk
  obtain ⟨L, hL, x, hx, rfl⟩ := side_of_through g rd d' hA q hq
  exact H L hL x hx hk

/-- The same at the shared chain. -/
theorem kindPays_shared_of_through_sides (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (H : ∀ x ∈ P.shared A.Z A.G, x.place.kind = κ →
      SidePays A.B 1 bs (x.thru id (Common.thru g rd))) :
    KindPays A.B 1 bs A.H.shared κ := by
  obtain ⟨-, -, -, -, -, -, -, -, eS, -⟩ := atPure_ok hA
  intro q hq hk
  rw [eS] at hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1
    (hq : q ∈ (P.shared A.Z A.G).map (Placed.thru id (Common.thru g rd)))
  exact H x hx hk

/-- The same at the second chain. -/
theorem kindPays_second_of_through_sides (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (H : ∀ x ∈ P.second A.Z A.G, x.place.kind = κ →
      SidePays A.B 2 bs (x.thru (Local.thru g rd) (Local.thru g rd))) :
    KindPays A.B 2 bs A.H.second κ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, eS, -⟩ := atPure_ok hA
  intro q hq hk
  rw [eS] at hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1
    (hq : q ∈ (P.second A.Z A.G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)))
  exact H x hx hk

/-- **The crossing: where every side of kind κ of the base filling pays at the return's book, the kind
pays at the return's first chain.** The sides are the base filling's own, not read through. -/
theorem kindPays_of_base_sides (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (H : ∀ L ∈ P.lots, ∀ x ∈ L.halves A.Z A.G, x.place.kind = κ → SidePays A.B 0 bs x) :
    KindPays A.B 0 bs A.H.first κ :=
  kindPays_of_through_sides g rd d' hA fun L hL x hx hk => sidePays_thru _ _ (H L hL x hx hk)

/-- The same at the shared chain. -/
theorem kindPays_shared_of_base_sides (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (H : ∀ x ∈ P.shared A.Z A.G, x.place.kind = κ → SidePays A.B 1 bs x) :
    KindPays A.B 1 bs A.H.shared κ :=
  kindPays_shared_of_through_sides g rd d' hA fun x hx hk => sidePays_thru _ _ (H x hx hk)

/-- The same at the second chain. -/
theorem kindPays_second_of_base_sides (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (H : ∀ x ∈ P.second A.Z A.G, x.place.kind = κ → SidePays A.B 2 bs x) :
    KindPays A.B 2 bs A.H.second κ :=
  kindPays_second_of_through_sides g rd d' hA fun x hx hk => sidePays_thru _ _ (H x hx hk)

variable {L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X}

/-- **Where the other lots lay no side of kind κ, every side of that kind in the return's first
chain is a side of the one lot, read through.** -/
theorem lot_holds_kind (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀') {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (hother : ∀ M ∈ P.lots, M = L ∨ ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ κ) :
    ∀ q ∈ A.H.first, q.place.kind = κ →
      q ∈ (L.thru (Local.thru g rd) (Local.thru g rd)).halves A.Z A.G := by
  intro q hq hk
  obtain ⟨M, hM, x, hx, rfl⟩ := side_of_through g rd d' hA q hq
  rcases hother M hM with rfl | h
  · exact List.mem_map_of_mem hx
  · exact absurd hk (h x hx)

/-- **The form for one lot, paid at its sides read through.** hpay: each side of the lot read through
pays at the return. hother: no other lot lays a side of kind κ. -/
theorem kindPays_through (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀') {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (hpay : ∀ q ∈ (L.thru (Local.thru g rd) (Local.thru g rd)).halves A.Z A.G,
      SidePays A.B 0 bs q)
    (hother : ∀ M ∈ P.lots, M = L ∨ ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ κ) :
    KindPays A.B 0 bs A.H.first κ :=
  fun q hq hk => hpay q (lot_holds_kind g rd d' hA hother q hq hk)

/-- **The form for one lot, paid by a law at the base filling's return.** hd: the base filling's
named member is in range. hlaw: at every return of the maker at the base filling, each side of the
lot pays. hother: no other lot lays a side of kind κ. -/
theorem kindPays_through_of_base (g : W₀' → W₀) (rd : Rc' → Rc) (d' : W₀')
    {A : OnlineProverWithDescription W₀' Rc' Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' P) = .ok A)
    (hd : P.inRange P.dummy = true)
    (hlaw : ∀ A₀ : OnlineProverWithDescription W₀ Rc Tr X₀ X, onlineProverFromPublicFiles o pol lay KL P = .ok A₀ →
      ∀ q ∈ L.halves A₀.Z A₀.G, SidePays A₀.B 0 A₀.F.first.blocksInOrder q)
    (hother : ∀ M ∈ P.lots, M = L ∨ ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ κ) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first κ := by
  obtain ⟨A₀, h₀, eZ, eG, eF, eB⟩ := atPure_base_of_through g rd d' hA hd
  refine kindPays_through g rd d' hA (fun q hq => ?_) hother
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1
    (hq : q ∈ (L.halves A.Z A.G).map (Placed.thru (Local.thru g rd) (Local.thru g rd)))
  have hp := hlaw A₀ h₀ x (by rw [eZ, eG]; exact hx)
  rw [eB, eF] at hp
  exact sidePays_thru _ _ hp

end

end ProofFile.Honest

#print axioms ProofFile.Honest.chainSteps_one_found
#print axioms ProofFile.Honest.find_own_place
#print axioms ProofFile.Honest.steps_of_thru
#print axioms ProofFile.Honest.sidePays_thru
#print axioms ProofFile.Honest.sidePays_of_thru
#print axioms ProofFile.Honest.atPure_base_of_through
#print axioms ProofFile.Honest.side_of_through
#print axioms ProofFile.Honest.through_side_mem
#print axioms ProofFile.Honest.kindPays_of_through_sides
#print axioms ProofFile.Honest.kindPays_shared_of_through_sides
#print axioms ProofFile.Honest.kindPays_second_of_through_sides
#print axioms ProofFile.Honest.kindPays_of_base_sides
#print axioms ProofFile.Honest.kindPays_shared_of_base_sides
#print axioms ProofFile.Honest.kindPays_second_of_base_sides
#print axioms ProofFile.Honest.lot_holds_kind
#print axioms ProofFile.Honest.kindPays_through
#print axioms ProofFile.Honest.kindPays_through_of_base
