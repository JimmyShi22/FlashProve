-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsOf.lean: WHEN THE MAKER OF THE ONE HONEST PROVER
(`onlineProverFromPublicFiles`, Honest/AtPure.lean) RETURNS: just where eight named parts hold: four things that it makes
of the public files, four that it asks of the filling. General in the filling. Two definitions, both
premises' forms; eleven theorems, which hold by unfolding the maker's text and by Law/LotClean.lean.
IT JOINS: of the four things made it shows none at any files. No property is claimed.

Why. "The maker returns" is a premise of statements at the prover that it makes. Here it is laid
open in its parts, so that whoever carries that premise can carry the list in its stead, and strike
a line when the line is shown.

Main names:
  `MakerHas` a premise's form: what the maker makes before it looks at the filling: the public part,
    the ground, the description, and the book of the last three chains of the list of sendings. The
    filling is not among its letters
  `MakerAsks` a premise's form: what the maker asks of the filling: in none of the three chains a
    half at a place where no sub-protocol stands; the named member of the range is in range
  `atPure_of_parts`   **where the eight hold the maker returns**, and what it returns has these four
  `parts_of_atPure` where it returns the eight hold. `atPure_ok` and `atPure_tests`
    (Honest/AtPureLaw.lean) have most of it in another form; new here: that the list of sendings has
    seven chains and that the book's maker has returned this book
  `atPure_returns_iff`   **the maker returns just where the eight hold**: none forgotten, none added
  `MakerHas.unique` the four are functions of the three files and of the function that stands for
    the earlier hash
  `no_return_of_ask` where the four are made and the filling fails an ask the maker does not return:
    the asks bite
  `idle_asks`, `idle_returns_iff` the filling without a half (`OnlineProverParts.idle`) meets the four asks at
    all letters; there the maker returns just where the four are made: so whether `MakerHas` holds
    at three files can be learnt by running the maker at that filling
  `strays_firstOf_iff` `strays` finds nothing in the lots' whole list just where it finds nothing in
    any lot's own: so each kind has one line to show
  `first_but_k5` CONDITIONAL: **the line of the kind K5 struck, at every filling whose list of lots
    holds `k5LotK`**: the first of the four asks follows from the other lots' lines (by
    `k5LotK_no_strays_desc`, Law/LotClean.lean)
  `open_strays`, `open_merges` CONDITIONAL on `IM.Open` (Johnson/IMR/SeatOpen.lean): the
    description's first chain is the chain of its opening, as `strays` and as the book's maker read
    it. The types of a description's states and claims hang on the description, so that "F.first =
    c" is not typed at a letter F

CALLED: `bind_ok`, `due?_ok` (Honest/AtPureLaw.lean); `strays_append`, `strays_firstOf`,
`k5LotK_no_strays_desc` (Law/LotClean.lean).
KIN, NOT IMPORTED. `atPure_returns_of_places` (Honest/K13/AtNowReturn.lean) goes from a return at
one filling to a return at another with the same places; its proof walks the maker's text in the
order in which `atPure_of_parts` does here.

Limits. OF THE FOUR THINGS MADE NONE IS SHOWN AT ANY FILES HERE (Law/ReturnsHead.lean has three of
them under the hypothesis on the public input, and of the book that the list of sendings has seven
chains where the verifier's test on the public files accepts; that the book's maker returns is shown
by no theorem that was found). Where the maker has been run and has returned, all eight hold there
by `parts_of_atPure`, on the word of that run of compiled code: an evaluation, no theorem. The four
asks are shown at the filling without a half alone; at a filling that lays `k5LotK`, the line of the
kind K5 inside the first ask. A RETURN OF THE MAKER IS NO WHOLE HONEST PROVER: the maker tests that
no half is astray, not that no half lacks (`OnlineProverWithDescription.stillIdle` lists the sub-protocols that send and
have no half, and rejects nothing). Of what is returned `atPure_of_parts` names four fields;
`atPure_ok` has most of the others. The statements say "= []"; the maker's text and `atPure_tests`
say "the list is empty" (`isEmpty`). It stands over the maker's text as it is: a test more in that
text breaks the proofs here, aloud.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K5.Law.LotClean

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)

variable {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  {P : OnlineProverParts W₀ Rc Tr X₀ X}

/-- **What the maker makes before it looks at the filling**: the public part, the ground, the
description, the book. A definition: a premise's form. The filling is not among its letters. -/
structure MakerHas (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : Pub) (G : Ground)
    (F : FileDescription Inst) (B : ProverCoinCounts) : Prop where
  pub : pubPlain o pol lay KL = .ok Z
  ground : blankBy pureRoad.links Z = some G
  desc : onlineDescription o pol lay KL = .ok F
  book : ∃ c0 c1 c2 c3 p0 p1 p2,
    Johnson.G.sendsOf pol lay KL = .ok [c0, c1, c2, c3, p0, p1, p2] ∧
      bookWhole F p0 p1 p2 (mergesByName F.first.blocksInOrder) = .ok B

/-- **What the maker asks of the filling.** A definition: a premise's form. -/
structure MakerAsks (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : Pub) (G : Ground) (F : FileDescription Inst) : Prop where
  first : strays F.first.blocksInOrder (firstOf Z G P.lots) = []
  shared : strays F.shared.blocksInOrder (P.shared Z G) = []
  second : strays F.second.blocksInOrder (P.second Z G) = []
  range : P.inRange P.dummy = true

/-- **WHERE THE EIGHT PARTS HOLD THE MAKER RETURNS**, and what it returns has these four. -/
theorem atPure_of_parts {Z : Pub} {G : Ground} {F : FileDescription Inst} {B : ProverCoinCounts}
    (m : MakerHas o pol lay KL Z G F B) (f : MakerAsks P Z G F) :
    ∃ A, onlineProverFromPublicFiles o pol lay KL P = .ok A ∧ A.Z = Z ∧ A.G = G ∧ A.F = F ∧ A.B = B := by
  obtain ⟨c0, c1, c2, c3, p0, p1, p2, hS, hB⟩ := m.book
  have hG : due? "the blank ground" (blankBy pureRoad.links Z) = .ok G := by
    rw [m.ground]
    rfl
  unfold onlineProverFromPublicFiles
  rw [m.pub]
  simp only [Except.bind]
  rw [hG]
  dsimp only
  rw [m.desc]
  dsimp only
  rw [hS]
  dsimp only
  rw [hB]
  dsimp only
  rw [f.first, f.shared, f.second, f.range]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- **WHERE THE MAKER RETURNS THE EIGHT PARTS HOLD**, at what it returns. -/
theorem parts_of_atPure {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    MakerHas o pol lay KL A.Z A.G A.F A.B ∧ MakerAsks P A.Z A.G A.F := by
  unfold onlineProverFromPublicFiles at h
  obtain ⟨Z, hZ, h⟩ := bind_ok h
  obtain ⟨G, hG, h⟩ := bind_ok h
  obtain ⟨F, hF, h⟩ := bind_ok h
  obtain ⟨cs, hS, h⟩ := bind_ok h
  split at h
  · obtain ⟨B, hB, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · rename_i hs
      split at h
      · cases h
      · rename_i hd
        cases h
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hs hd
        exact ⟨⟨hZ, due?_ok hG, hF, _, _, _, _, _, _, _, hS, hB⟩,
          ⟨List.isEmpty_iff.1 hs.1.1, List.isEmpty_iff.1 hs.1.2, List.isEmpty_iff.1 hs.2, hd⟩⟩
  · cases h

/-- **THE MAKER RETURNS JUST WHERE THE EIGHT PARTS HOLD.** -/
theorem atPure_returns_iff :
    (∃ A, onlineProverFromPublicFiles o pol lay KL P = .ok A) ↔
      ∃ Z G F B, MakerHas o pol lay KL Z G F B ∧ MakerAsks P Z G F :=
  ⟨fun ⟨A, h⟩ => ⟨A.Z, A.G, A.F, A.B, parts_of_atPure h⟩,
    fun ⟨_, _, _, _, m, f⟩ => (atPure_of_parts m f).imp fun _ h => h.1⟩

/-- **The four are functions of the three files** and of the function that stands for the earlier
hash. -/
theorem MakerHas.unique {Z Z' : Pub} {G G' : Ground} {F F' : FileDescription Inst} {B B' : ProverCoinCounts}
    (m : MakerHas o pol lay KL Z G F B) (m' : MakerHas o pol lay KL Z' G' F' B') :
    Z = Z' ∧ G = G' ∧ F = F' ∧ B = B' := by
  obtain rfl : Z = Z' := Except.ok.inj (m.pub.symm.trans m'.pub)
  obtain rfl : G = G' := Option.some.inj (m.ground.symm.trans m'.ground)
  obtain rfl : F = F' := Except.ok.inj (m.desc.symm.trans m'.desc)
  obtain ⟨c0, c1, c2, c3, p0, p1, p2, hS, hB⟩ := m.book
  obtain ⟨d0, d1, d2, d3, q0, q1, q2, hS', hB'⟩ := m'.book
  have e := Except.ok.inj (hS.symm.trans hS')
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := e
  exact ⟨rfl, rfl, rfl, Except.ok.inj (hB.symm.trans hB')⟩

/-- **WHERE THE FOUR ARE MADE AND THE FILLING FAILS AN ASK THE MAKER DOES NOT RETURN**: the asks
bite. -/
theorem no_return_of_ask {Z : Pub} {G : Ground} {F : FileDescription Inst} {B : ProverCoinCounts}
    (m : MakerHas o pol lay KL Z G F B) (h : ¬ MakerAsks P Z G F) :
    ¬ ∃ A, onlineProverFromPublicFiles o pol lay KL P = .ok A := by
  rintro ⟨A, hA⟩
  obtain ⟨m', f⟩ := parts_of_atPure hA
  obtain ⟨e1, e2, e3, -⟩ := m.unique m'
  rw [e1, e2, e3] at h
  exact h f

/-- The filling without a half meets the four asks, at all letters. -/
theorem idle_asks (Z : Pub) (G : Ground) (F : FileDescription Inst) : MakerAsks OnlineProverParts.idle Z G F :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **At the filling without a half the maker returns just where the four are made**: so whether
`MakerHas` holds at three files can be learnt by running the maker there at that filling. -/
theorem idle_returns_iff :
    (∃ A, onlineProverFromPublicFiles o pol lay KL OnlineProverParts.idle = .ok A) ↔ ∃ Z G F B, MakerHas o pol lay KL Z G F B :=
  ⟨fun h => by
      obtain ⟨Z, G, F, B, m, -⟩ := atPure_returns_iff.1 h
      exact ⟨Z, G, F, B, m⟩,
    fun ⟨Z, G, F, _, m⟩ => atPure_returns_iff.2 ⟨Z, G, F, _, m, idle_asks Z G F⟩⟩

/-- `strays` finds nothing in the lots' whole list just where it finds nothing in any lot's own. -/
theorem strays_firstOf_iff {σ C V W Y : Type} (bs : List (Block σ C)) (Z : Pub) (G : Ground) :
    ∀ ls : List (HLot V W Y), strays bs (firstOf Z G ls) = [] ↔
      ∀ L ∈ ls, strays bs (L.halves Z G) = []
  | [] => ⟨fun _ _ h => absurd h (by simp), fun _ => rfl⟩
  | L :: ls => by
    have e : strays bs (firstOf Z G (L :: ls)) =
        strays bs (L.halves Z G) ++ strays bs (firstOf Z G ls) := by
      show strays bs ((L :: ls).flatMap fun L => L.halves Z G) = _
      rw [List.flatMap_cons, strays_append]
      rfl
    rw [e, List.append_eq_nil_iff, strays_firstOf_iff bs Z G ls, List.forall_mem_cons]

/-- **K5's LINE STRUCK, AT EVERY FILLING THAT LAYS K5's LOT**: no half of the whole list strays
where none of the other lots' strays. -/
theorem first_but_k5 {Z : Pub} {G : Ground} {F : FileDescription Inst} {B : ProverCoinCounts}
    (m : MakerHas o pol lay KL Z G F B) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {l₁ l₂ : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)}
    (hl : P.lots = l₁ ++ k5LotK cells keyOf :: l₂)
    (h : ∀ L ∈ l₁ ++ l₂, strays F.first.blocksInOrder (L.halves Z G) = []) :
    strays F.first.blocksInOrder (firstOf Z G P.lots) = [] := by
  rw [hl]
  refine strays_firstOf _ Z G _ fun L hL => ?_
  rcases List.mem_append.1 hL with h1 | h1
  · exact h L (List.mem_append_left _ h1)
  · rcases List.mem_cons.1 h1 with rfl | h2
    · exact k5LotK_no_strays_desc cells keyOf m.pub m.ground m.desc
    · exact h L (List.mem_append_right _ h2)

section
variable {F : FileDescription Inst} {Z : Pub} {Bs : PureBase} {base : List (Block S Cl)}
  {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- **The description's first chain is the opening's, as `strays` reads it.** The types of the
description's states and claims hang on the description, so that "F.first = c" is not typed at a
letter F; what is read off the chain is. -/
theorem open_strays {V W Y : Type} (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hs : List (Placed V W Y)) : strays F.first.blocksInOrder hs = strays c.blocksInOrder hs := by
  obtain rfl := O.desc
  rfl

/-- The same as the book's maker reads it. -/
theorem open_merges (O : IM.Open o pol lay KL F Z Bs base c A B) :
    mergesByName F.first.blocksInOrder = mergesByName c.blocksInOrder := by
  obtain rfl := O.desc
  rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_of_parts
#print axioms ProofFile.Honest.K5.parts_of_atPure
#print axioms ProofFile.Honest.K5.atPure_returns_iff
#print axioms ProofFile.Honest.K5.MakerHas.unique
#print axioms ProofFile.Honest.K5.no_return_of_ask
#print axioms ProofFile.Honest.K5.idle_asks
#print axioms ProofFile.Honest.K5.idle_returns_iff
#print axioms ProofFile.Honest.K5.strays_firstOf_iff
#print axioms ProofFile.Honest.K5.first_but_k5
#print axioms ProofFile.Honest.K5.open_strays
#print axioms ProofFile.Honest.K5.open_merges
