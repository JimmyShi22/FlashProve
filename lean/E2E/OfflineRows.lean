-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/OfflineRows.lean: rows of the frame for the honest side (`Sides`, Honest/Rule.lean) made of a
prover's own halves, each part with a simulator beside it. Definitions, and equations by unfolding.

  `partsBeside`      each part with the simulator at its number; `noSim` where the list is short
  `RowConditions`    the four letters of a row, beside its parts
  `rowOf`, `rowsAt`  a half as a row; a list of halves as rows, each by its own place
  `SimulatorsByChain`, `ConditionsByChain`   what is laid at each place of each chain
  `offlineSides`     the three lists, for a prover
  `offlineSides_prover`   the prover of these rows is that prover, at every value of the letters
  `RowsCovered`, `row_zip`  where every list of simulators is as long as its half, the row is the zip
  `owns_of`, `seated_of`    what `Sides.owns` and `Sides.seated` come to

Limits. Nothing here says that a simulator simulates anything: `Sim` asks nothing of its term, and
`Good.exact` is not stated here. A list of simulators that is too short leaves `noSim`, whose address
is at no place, so `Side.fits` says false there. The letters of `RowConditions` are free. Nothing on
any property.
-/
import E2E.KeyLaid
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open AtPublicFiles.KeyLink (noSim)

section Rows
variable {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type}

/-- **Each part with the simulator at its number.** Where the list of simulators is short the rest
stand beside `noSim`. -/
def partsBeside : List (Part V W Y) → List (Sim Pb) → List (Part V W Y × Sim Pb)
  | [], _ => []
  | p :: ps, [] => (p, noSim) :: partsBeside ps []
  | p :: ps, s :: sims => (p, s) :: partsBeside ps sims

/-- The parts of the list are the parts, whatever the simulators. -/
theorem partsBeside_parts (ps : List (Part V W Y)) :
    ∀ sims : List (Sim Pb), (partsBeside ps sims).map (·.1) = ps := by
  induction ps with
  | nil => intro sims; rfl
  | cons p ps ih =>
    intro sims
    cases sims with
    | nil => exact congrArg (p :: ·) (ih [])
    | cons s sims => exact congrArg (p :: ·) (ih sims)

/-- As many as the parts. -/
theorem partsBeside_length (ps : List (Part V W Y)) (sims : List (Sim Pb)) :
    (partsBeside ps sims).length = ps.length := by
  have e := congrArg List.length (partsBeside_parts ps sims)
  rwa [List.length_map] at e

/-- Where the two lists are equally long it is their zip. -/
theorem partsBeside_eq_zip (ps : List (Part V W Y)) :
    ∀ sims : List (Sim Pb), sims.length = ps.length → partsBeside ps sims = ps.zip sims := by
  induction ps with
  | nil => intro sims _; rfl
  | cons p ps ih =>
    intro sims h
    cases sims with
    | nil => exact absurd h (by simp)
    | cons s sims =>
      have h' : sims.length = ps.length := by simpa using h
      show (p, s) :: partsBeside ps sims = (p, s) :: ps.zip sims
      rw [ih sims h']

/-- **The four letters of a row**, as `Lettered` has them: a condition before the place and one
after it, and for each part a condition at its start and which positions may be read. -/
structure RowConditions (Bk : ProverCoinCounts) (S V W Y Pb : Type) where
  before : Coins Bk → S → Mid W Y → Env → Prop
  after : Coins Bk → S → Mid W Y → Env → Prop
  atPart : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop
  positions : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop

/-- Letters that say nothing, as `bareRow`'s. -/
def RowConditions.bare : RowConditions Bk S V W Y Pb :=
  ⟨fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- **A half as a row.** -/
def rowOf (h : Placed V W Y) (sims : List (Sim Pb)) (c : RowConditions Bk S V W Y Pb) :
    Lettered Bk S Cl V W Y Pb :=
  ⟨h.place, partsBeside h.parts sims, c.before, c.after, c.atPart, c.positions⟩

/-- The row's half is the half. -/
theorem rowOf_half (h : Placed V W Y) (sims : List (Sim Pb))
    (c : RowConditions Bk S V W Y Pb) :
    (⟨(rowOf (Cl := Cl) h sims c).place, (rowOf (Cl := Cl) h sims c).row.map (·.1)⟩ :
      Placed V W Y) = h := by
  cases h with
  | mk a ps =>
    show (⟨a, (partsBeside ps sims).map (·.1)⟩ : Placed V W Y) = ⟨a, ps⟩
    rw [partsBeside_parts]

/-- **A list of halves as rows**: each with what is laid at its own place. -/
def rowsAt (sims : Place → List (Sim Pb)) (c : Place → RowConditions Bk S V W Y Pb)
    (hs : List (Placed V W Y)) : List (Lettered Bk S Cl V W Y Pb) :=
  hs.map fun h => rowOf h (sims h.place) (c h.place)

/-- The rows' halves are the halves. -/
theorem rowsAt_back (sims : Place → List (Sim Pb)) (c : Place → RowConditions Bk S V W Y Pb)
    (hs : List (Placed V W Y)) :
    (rowsAt (Cl := Cl) sims c hs).map
      (fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) = hs := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
    exact congrArg₂ List.cons (rowOf_half (Cl := Cl) h (sims h.place) (c h.place)) ih

/-- The rows stand at the halves' places, in order. -/
theorem rowsAt_places (sims : Place → List (Sim Pb)) (c : Place → RowConditions Bk S V W Y Pb)
    (hs : List (Placed V W Y)) :
    (rowsAt (Cl := Cl) sims c hs).map (·.place) = hs.map (·.place) := by
  unfold rowsAt
  rw [List.map_map]
  rfl

/-- **Every list of simulators is as long as its half.** -/
def RowsCovered (sims : Place → List (Sim Pb)) (hs : List (Placed V W Y)) : Prop :=
  ∀ h ∈ hs, (sims h.place).length = h.parts.length

/-- Then a row is its half's parts zipped with its simulators. -/
theorem row_zip {sims : Place → List (Sim Pb)} {hs : List (Placed V W Y)}
    (hc : RowsCovered sims hs) {h : Placed V W Y} (hh : h ∈ hs)
    (c : RowConditions Bk S V W Y Pb) :
    (rowOf (Cl := Cl) h (sims h.place) c).row = h.parts.zip (sims h.place) :=
  partsBeside_eq_zip _ _ (hc h hh)

/-- A half's row has a side wherever a sub-protocol of the list is at its place. -/
theorem side_isSome (L : Lettered Bk S Cl V W Y Pb) (bs : List (Block S Cl))
    (fs : List (Fall S)) (h : L.place ∈ bs.map (·.place)) : (L.side bs fs).isSome = true := by
  obtain ⟨b, hb, e⟩ := List.mem_map.1 h
  have hf : (bs.find? fun b => b.place == L.place).isSome = true :=
    List.find?_isSome.2 ⟨b, hb, beq_iff_eq.2 e⟩
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hf
  unfold Lettered.side Side.seated
  rw [hb']
  rfl

end Rows

section Sides
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **What simulators are laid at each place of each chain.** -/
structure SimulatorsByChain (Xi Ky : Type) where
  first : Place → List (Sim Xi)
  shared : Place → List (Sim Ky)
  second : Place → List (Sim Xi)

/-- **What letters are laid at each place of each chain.** -/
structure ConditionsByChain (F : FileDescription Xi) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type) where
  first : Place → RowConditions Bk F.S₁ (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi
  shared : Place → RowConditions Bk F.S₂ Empty (Common W₀ Rc Ky) X₀ Ky
  second : Place → RowConditions Bk F.S₃ (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi

/-- Letters that say nothing, at every place. -/
def ConditionsByChain.bare (F : FileDescription Xi) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type) :
    ConditionsByChain F Bk W₀ Rc Ky Tr X₀ X :=
  ⟨fun _ => RowConditions.bare, fun _ => RowConditions.bare, fun _ => RowConditions.bare⟩

/-- **The rows of a prover's own halves**, with three lists of falls. -/
def offlineSides (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (sims : SimulatorsByChain Xi Ky) (c : ConditionsByChain F Bk W₀ Rc Ky Tr X₀ X)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃)) :
    Sides F Bk W₀ Rc Ky Tr X₀ X :=
  ⟨rowsAt sims.first c.first H.first, rowsAt sims.shared c.shared H.shared,
    rowsAt sims.second c.second H.second, f₁, f₂, f₃⟩

variable (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (sims : SimulatorsByChain Xi Ky) (c : ConditionsByChain F Bk W₀ Rc Ky Tr X₀ X)
  (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))

/-- **Their prover is the prover**, at every value of the letters. -/
theorem offlineSides_prover : (offlineSides F Bk H sims c f₁ f₂ f₃).prover H = H := by
  unfold Sides.prover offlineSides
  simp only [rowsAt_back]

/-- The first chain's sides of the prover are the lists'. -/
theorem offlineSides_first :
    H.first = (offlineSides F Bk H sims c f₁ f₂ f₃).first.map
      fun L => ⟨L.place, L.row.map (·.1)⟩ :=
  (rowsAt_back sims.first c.first H.first).symm

/-- The shared chain's. -/
theorem offlineSides_shared :
    H.shared = (offlineSides F Bk H sims c f₁ f₂ f₃).shared.map
      fun L => ⟨L.place, L.row.map (·.1)⟩ :=
  (rowsAt_back sims.shared c.shared H.shared).symm

/-- The second chain's. -/
theorem offlineSides_second :
    H.second = (offlineSides F Bk H sims c f₁ f₂ f₃).second.map
      fun L => ⟨L.place, L.row.map (·.1)⟩ :=
  (rowsAt_back sims.second c.second H.second).symm

/-- **Every list is at a place of its chain**, where every half is. -/
theorem seated_of (h₁ : ∀ g ∈ H.first, g.place ∈ F.first.blocksInOrder.map (·.place))
    (h₂ : ∀ g ∈ H.shared, g.place ∈ F.shared.blocksInOrder.map (·.place))
    (h₃ : ∀ g ∈ H.second, g.place ∈ F.second.blocksInOrder.map (·.place)) :
    (offlineSides F Bk H sims c f₁ f₂ f₃).seated = true := by
  unfold Sides.seated
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro L hL
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
    exact side_isSome _ _ _ (h₁ g hg)
  · intro L hL
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
    exact side_isSome _ _ _ (h₂ g hg)
  · intro L hL
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
    exact side_isSome _ _ _ (h₃ g hg)

end Sides

section Owners
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type}

/-- A row's part numbers stand among the addresses of its list. -/
theorem addr_mem {l : List (Lettered Bk S Cl V W Y Pb)} {L : Lettered Bk S Cl V W Y Pb}
    (hL : L ∈ l) {j : Nat} (hj : j < L.row.length) : (⟨L.place, j⟩ : Addr) ∈ addrsOf l := by
  unfold addrsOf
  exact List.mem_flatMap.2 ⟨L, hL, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩

/-- **Every entry's owner is a part of some side**, where the owners all stand in a list of addresses
and each of these is a part of some side. -/
theorem owns_of {F : FileDescription Xi} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (owners : List Addr)
    (hb : Bk.ahead.all (fun e => owners.contains e.owner) = true)
    (ho : ∀ a ∈ owners, a ∈ addrsOf G.first ++ addrsOf G.shared ++ addrsOf G.second) :
    G.owns = true := by
  unfold Sides.owns
  rw [List.all_eq_true] at hb ⊢
  intro e he
  have h1 : e.owner ∈ owners := List.contains_iff_mem.1 (hb e he)
  exact List.contains_iff_mem.2 (ho _ h1)

end Owners

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.partsBeside_parts
#print axioms AtPublicFiles.OfflineRows.partsBeside_eq_zip
#print axioms AtPublicFiles.OfflineRows.rowsAt_back
#print axioms AtPublicFiles.OfflineRows.offlineSides_prover
#print axioms AtPublicFiles.OfflineRows.seated_of
#print axioms AtPublicFiles.OfflineRows.owns_of
