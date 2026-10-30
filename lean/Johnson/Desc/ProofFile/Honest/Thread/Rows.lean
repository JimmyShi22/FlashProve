-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Rows.lean: the lists of parts of a description's three chains,
with their parameters A and B set from the `Thread`s. The rule for `Owed` at a file from what a
kind's author supplies (`file_owed_hands`, Honest/Thread/Hands.lean) speaks of lists G : `Sides`
whose parameters A and B are `ThrS` (the invariant together with `Said`), and of the prover whose
sides are these lists. Here such a G is built: from lists without A and B, which hold what an author
supplies (place, parts with simulators, On, bud), and from the three families of `Thread`s.
Definitions (data, and two functions that build) and lemmas. General in the description, the book,
the prover, the families and the lists: no kind is named.

  1  `Unlettered`, `Unlettered.half`, `Unlettered.of`, `Lettered.bare`   a list without A and B; its
     prover's side; from an author's side; from a list with A and B, by forgetting them
  2  `SLot`, `SLot.toHLot`, `rowsOfLots`   a lot of such lists: `HLot` (Honest/Frame.lean) with
     simulators
  3  `Unlettered.lay`, `laySides`   A, B := `ThrS` before and after the sub-protocol at the list's
     place, by its number in the chain's flat list (`borderNo`, Honest/Thread/Thr.lean)
  4  `borderNo_at`, `find_at`   where no two sub-protocols are at one place: the number and the
     look-up
  5  `lay_laidAt`   `Lettered.LaidAt` holds of every list so built
  6  `lay_side_at`, `Good.refall`, `seated_refall`, `hand_of_good`   such a list's side; `Good`
     carries over to another fall; an author's `Good` at its own side is what is asked
  7  `halves_lay`, `prover_lay`, `halves_of_lots`, `prover_lay_self`   the prover's sides are the
     lists' own; lot by lot they are `firstOf` (Honest/Frame.lean); at a prover that has these sides
     already the prover of the built lists is that prover
  8  `side_isSome_of_any`, `any_of_strays`, `seated_lay`   every list is at a place of its chain
  9  `forall_lay`, `forall_rowsOfLots`, `onFromS_bare`   list by list; lot by lot
  10  `file_owed_rows`   the rule, with the three hypotheses on A and B proved

The order of building. `Sits` (Honest/Thread/File.lean) asks that a `Thread`'s parameter hs be the
prover's sides; the lists' parameters A, B hold the `Thread`s. So the sides cannot be read from G.
The lists without A and B come first; a `Thread`'s hs is set from their sides (`Unlettered.half`, or
`firstOf` at `SLot.toHLot`); then G is built from both. `prover_lay` and `halves_of_lots` say what
the sides of G.prover H are. The circle is closed by `prover_lay_self` alone: the rule asks `Sits`,
the starts and `ready` at G.prover H; a lemma that has one prover, in a `Thread`'s parameters and in
these hypotheses, can be applied there because, at an H whose three lists of sides are the lists'
own, G.prover H = H.

What an author still adds, beside `Good` at its own side σ (at any A and B; `Good`'s parameter `pre`
is free in `Good.refall` and `hand_of_good`, and `file_owed_rows` asks it at the list's place:
`preOf`, Honest/Rule.lean), to have `hand_of_good`: one equation: (hb) σ.block is the description's
sub-protocol at some number b of the chain's flat list. Nothing on the fall: `Good.refall`: of an
author's `Good` the rule reads `fits`, `exact` and `fresh` (`good_at_pair`,
Honest/Thread/Hands.lean), and these read no fall.

A lot that cannot be run. If a simulator or a list of a lot is noncomputable, so is `SLot.toHLot` of
that lot: then no compiled program can run a prover whose lots are ls.map SLot.toHLot.

Limits.
  * Nothing is built at a description of the protocol here.
  * `file_owed_rows` is `file_owed_hands` at a G built by `laySides` (`hG`), with three hypotheses
    proved (those on A and B) and `seats` asked list by list (`seat₁` to `seat₃`: every list's place
    is a sub-protocol's): a conditional lemma on this folder's own definitions, whose conclusion is
    a structure of hypotheses (`good` with the field beside A and B, `owed` at the walk's own state:
    the heads of Honest/Owed.lean and Honest/Thread/FileOwed.lean): no property, and none of the
    library's goals.
  * Among the hypotheses that the prose above does not name: `sealPlain` (the first chain's last
    declared round declares no item except roots, and no root): `file_owed_rows`;
    `ProverCoinCounts.word … = none` (every test on the book passes): `file_owed_rows`. `Rel` is a variable: the
    inputs at which `input`, `hst`, `a₁` to `a₃` and `e₁` to `e₃` are asked. `e₁` to `e₃` are asked
    at the states as `ChainProgress.start` lays them (the head of Honest/Thread/FileOwed.lean).
  * `OwesS`, `YesS` and `OnFromS` are asked at every value of the state's field `opened` that `Said`
    allows (`Thr` does not read it): unless `Said` shuts them out, at `none` and at lists of columns
    that no run opens. At a prover with a part that reads the columns and errs at `none` (its duty:
    Honest/Frame.lean, `Seen.opened`), `PlaysS` at a `Said` that lets `none` through before that
    part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits). Of the field
    `OnFromS` has in hand only what `Said` says of it at the border before the sub-protocol.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Hands
import Johnson.Desc.ProofFile.Honest.ProverSelf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

section
variable {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 A list without A and B -/

/-- **A list of parts without A and B**: `Lettered` (Honest/Rule.lean) less A and B: what an author
supplies. -/
structure Unlettered (V W Y Pb : Type) where
  place : Place
  /-- each part with its simulator -/
  row : List (Part V W Y × Sim Pb)
  On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop
  bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop

/-- Its prover's side: the parts, at the place: as `Sides.prover` builds it. -/
def Unlettered.half (r : Unlettered V W Y Pb) : Placed V W Y := ⟨r.place, r.row.map (·.1)⟩

/-- From an author's side, with its On and bud. -/
def Unlettered.of (σ : Side S Cl V W Y Pb)
    (On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Unlettered V W Y Pb :=
  ⟨σ.block.place, σ.row, On, bud⟩

/-- From a list with A and B, by forgetting them. -/
def Lettered.bare (M : Lettered Bk S Cl V W Y Pb) : Unlettered V W Y Pb :=
  ⟨M.place, M.row, M.On, M.bud⟩

/-! ## 2 A lot of such lists -/

/-- **A lot's lists**: `HLot` (Honest/Frame.lean) with simulators, On and bud. -/
structure SLot (V W Y Pb : Type) where
  /-- the lot's name -/
  name : String
  rows : Pub → Ground → List (Unlettered V W Y Pb)

/-- The `HLot`, by forgetting. -/
def SLot.toHLot (l : SLot V W Y Pb) : HLot V W Y :=
  ⟨l.name, fun Z Gr => (l.rows Z Gr).map (·.half)⟩

/-- The lots' lists, lot by lot: as `firstOf` builds the prover's sides. -/
def rowsOfLots (Z : Pub) (Gr : Ground) (ls : List (SLot V W Y Pb)) :
    List (Unlettered V W Y Pb) := ls.flatMap fun l => l.rows Z Gr

/-! ## 3 Setting A and B -/

/-- **The list, with its parameters A and B set to `ThrS` at the input that the prover's state
holds**, before the sub-protocol at the list's place and after it. `bs`: the chain's flat list. -/
def Unlettered.lay (r : Unlettered V W Y Pb) (T : W → Thread Bk S Cl V W Y Pb)
    (Sd : W → Nat → Coins Bk → Mid W Y → Prop) (bs : List (Block S Cl)) :
    Lettered Bk S Cl V W Y Pb :=
  { place := r.place
    row := r.row
    A := fun k s m E => ThrS (T m.st.input) (Sd m.st.input) (borderNo bs r.place) k s m E
    B := fun k s m E => ThrS (T m.st.input) (Sd m.st.input) (borderNo bs r.place + 1) k s m E
    On := r.On
    bud := r.bud }

/-! ## 4 Where no two sub-protocols are at one place -/

/-- The number of the border before the sub-protocol at a sub-protocol's place is that
sub-protocol's number. -/
theorem borderNo_at : ∀ (bs : List (Block S Cl)) (b : Nat) (blk : Block S Cl),
    (bs.map (·.place)).Nodup → bs[b]? = some blk → borderNo bs blk.place = b
  | [], _, _, _, h => by cases h
  | x :: l, 0, blk, _, h => by
    obtain rfl : x = blk := Option.some.inj h
    simp [borderNo, List.findIdx_cons]
  | x :: l, b + 1, blk, hn, h => by
    have h' : l[b]? = some blk := by
      rw [List.getElem?_cons_succ] at h
      exact h
    have hn' : (x.place :: l.map (·.place)).Nodup := hn
    obtain ⟨n1, n2⟩ := List.nodup_cons.1 hn'
    have hp : ¬ (x.place == blk.place) = true := fun e =>
      n1 (by
        rw [beq_iff_eq.1 e]
        exact List.mem_map.2 ⟨blk, List.mem_of_getElem? h', rfl⟩)
    have e : borderNo (x :: l) blk.place = borderNo l blk.place + 1 := by
      simp [borderNo, List.findIdx_cons, hp]
    rw [e, borderNo_at l b blk n2 h']

/-- The first sub-protocol at a sub-protocol's place is that sub-protocol. -/
theorem find_at : ∀ (bs : List (Block S Cl)) (b : Nat) (blk : Block S Cl),
    (bs.map (·.place)).Nodup → bs[b]? = some blk →
    (bs.find? fun x => x.place == blk.place) = some blk
  | [], _, _, _, h => by cases h
  | x :: l, 0, blk, _, h => by
    obtain rfl : x = blk := Option.some.inj h
    rw [List.find?_cons_of_pos (by exact beq_self_eq_true _)]
  | x :: l, b + 1, blk, hn, h => by
    have h' : l[b]? = some blk := by
      rw [List.getElem?_cons_succ] at h
      exact h
    have hn' : (x.place :: l.map (·.place)).Nodup := hn
    obtain ⟨n1, n2⟩ := List.nodup_cons.1 hn'
    have hp : ¬ (x.place == blk.place) = true := fun e =>
      n1 (by
        rw [beq_iff_eq.1 e]
        exact List.mem_map.2 ⟨blk, List.mem_of_getElem? h', rfl⟩)
    rw [List.find?_cons_of_neg (by
      show ¬ ((x.place == blk.place) = true)
      exact hp)]
    exact find_at l b blk n2 h'

/-! ## 5 A and B are set so -/

/-- **`Lettered.LaidAt` holds of every list so built**, where no two sub-protocols are at one place.
-/
theorem lay_laidAt (r : Unlettered V W Y Pb) (T : W → Thread Bk S Cl V W Y Pb)
    (Sd : W → Nat → Coins Bk → Mid W Y → Prop) {bs : List (Block S Cl)}
    (hn : (bs.map (·.place)).Nodup) : (r.lay T Sd bs).LaidAt T Sd bs := by
  intro b blk hb hp
  have hp' : blk.place = r.place := hp
  have e : borderNo bs r.place = b := by
    rw [← hp']
    exact borderNo_at bs b blk hn hb
  subst e
  exact ⟨rfl, rfl⟩

/-! ## 6 Such a list's side; what an author supplies of `Good` -/

/-- Such a list's side: the sub-protocol at its place, its parts, the chain's falls at its place. -/
theorem lay_side_at (r : Unlettered V W Y Pb) (T : W → Thread Bk S Cl V W Y Pb)
    (Sd : W → Nat → Coins Bk → Mid W Y → Prop) {bs : List (Block S Cl)}
    (hn : (bs.map (·.place)).Nodup) {b : Nat} {blk : Block S Cl} (hb : bs[b]? = some blk)
    (hp : blk.place = r.place) (fs : List (Fall S)) :
    (r.lay T Sd bs).side bs fs = some ⟨blk, r.row, fallOf fs r.place⟩ := by
  have e := find_at bs b blk hn hb
  rw [hp] at e
  exact congrArg (Option.map fun x =>
    ({ block := x, row := r.row, fall := fallOf fs r.place } : Side S Cl V W Y Pb)) e

/-- **`Good` carries over to another fall**, at A, B that never hold. `plays` and `acc` hold
vacuously there. Nothing that the rule reads is lost by that: of the term that an author supplies
`good_at_pair` (Honest/Thread/Hands.lean) takes `fits`, `exact` and `fresh`, which read no fall and
neither A nor B; `plays` and `acc` at `ThrS` it has from the conditions on the sub-protocols
(`OwesS`, `YesS`). -/
theorem Good.refall {φ : Face V W Pb} {σ : Side S Cl V W Y Pb} {ord : List Place}
    {chain ft : Nat} {A B : Coins Bk → S → Mid W Y → Env → Prop}
    {On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (g : Good pre φ σ Bk ord chain ft A B On bud) (f : S → List Fmt.Drawn → Option String) :
    Good pre φ { σ with fall := f } Bk ord chain ft (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      On bud :=
  { fits := g.fits
    plays := fun _ _ _ _ _ h => h.elim
    acc := fun _ _ _ _ _ h => h.elim
    exact := g.exact
    fresh := g.fresh }

/-- Where `Side.seated` returns a side at some falls it returns one at any others: the same, with
their fall at the place. -/
theorem seated_refall {bs : List (Block S Cl)} {a : Place} {row : List (Part V W Y × Sim Pb)}
    {fs₀ : List (Fall S)} {σ₀ : Side S Cl V W Y Pb} (h : Side.seated bs a row fs₀ = some σ₀)
    (fs : List (Fall S)) : Side.seated bs a row fs = some { σ₀ with fall := fallOf fs a } := by
  unfold Side.seated at h ⊢
  cases hf : bs.find? fun b => b.place == a with
  | none =>
    rw [hf] at h
    cases h
  | some b =>
    rw [hf] at h
    obtain rfl := Option.some.inj h
    rfl

/-- **An author's `Good` at its own side is what the rule asks at the list built from that side**,
under the equation hb of this file's head; whatever falls the chain has. -/
theorem hand_of_good {φ : Face V W Pb} {ord : List Place} {chain ft : Nat} {fs : List (Fall S)}
    {σ : Side S Cl V W Y Pb} {A' B' : Coins Bk → S → Mid W Y → Env → Prop}
    {On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (g : Good pre φ σ Bk ord chain ft A' B' On bud) (T : W → Thread Bk S Cl V W Y Pb)
    (Sd : W → Nat → Coins Bk → Mid W Y → Prop) {bs : List (Block S Cl)}
    (hn : (bs.map (·.place)).Nodup) {b : Nat} (hb : bs[b]? = some σ.block) :
    ∀ τ, ((Unlettered.of σ On bud).lay T Sd bs).side bs fs = some τ →
      ∃ A₁ B₁, Good pre φ τ Bk ord chain ft A₁ B₁ ((Unlettered.of σ On bud).lay T Sd bs).On
        ((Unlettered.of σ On bud).lay T Sd bs).bud := by
  intro τ hτ
  rw [lay_side_at (Unlettered.of σ On bud) T Sd hn hb rfl fs] at hτ
  obtain rfl := Option.some.inj hτ
  exact ⟨_, _, g.refall (fallOf fs σ.block.place)⟩

/-! ## 7 The prover's sides -/

/-- The sides that `Sides.prover` builds from such lists are the lists' own. -/
theorem halves_lay (T : W → Thread Bk S Cl V W Y Pb) (Sd : W → Nat → Coins Bk → Mid W Y → Prop)
    (bs : List (Block S Cl)) : ∀ rs : List (Unlettered V W Y Pb),
    ((rs.map fun r => r.lay T Sd bs).map fun M =>
      (⟨M.place, M.row.map (·.1)⟩ : Placed V W Y)) = rs.map (·.half)
  | [] => rfl
  | r :: rs => congrArg (List.cons r.half) (halves_lay T Sd bs rs)

/-- **Lot by lot they are `firstOf` (Honest/Frame.lean).** -/
theorem halves_of_lots (Z : Pub) (Gr : Ground) : ∀ ls : List (SLot V W Y Pb),
    (rowsOfLots Z Gr ls).map (·.half) = firstOf Z Gr (ls.map SLot.toHLot)
  | [] => rfl
  | l :: ls => by
    have ih := halves_of_lots Z Gr ls
    unfold rowsOfLots firstOf at ih ⊢
    rw [List.flatMap_cons, List.map_append, List.map_cons, List.flatMap_cons]
    exact congrArg ((l.rows Z Gr).map (·.half) ++ ·) ih

/-! ## 8 Every list is at a place of its chain -/

theorem side_isSome_of_any {M : Lettered Bk S Cl V W Y Pb} {bs : List (Block S Cl)}
    (h : bs.any (fun b => b.place == M.place) = true) : (M.side bs).isSome = true := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.1 h
  unfold Lettered.side Side.seated
  cases hf : bs.find? fun b => b.place == M.place with
  | some b => rfl
  | none => exact absurd hp (List.find?_eq_none.1 hf x hx)

/-- What the test of Honest/Frame.lean on stray prover's sides says, side by side. -/
theorem any_of_strays {bs : List (Block S Cl)} {hs : List (Placed V W Y)}
    (h : strays bs hs = []) : ∀ g ∈ hs, bs.any (fun b => b.place == g.place) = true := by
  intro g hg
  unfold strays at h
  have h1 := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 h) g hg
  cases hb : bs.any fun b => b.place == g.place with
  | true => rfl
  | false => exact absurd (by simp [hb]) h1

/-! ## 9 List by list; lot by lot -/

/-- What holds of every list as built holds of every member of the list of built lists. -/
theorem forall_lay {T : W → Thread Bk S Cl V W Y Pb} {Sd : W → Nat → Coins Bk → Mid W Y → Prop}
    {bs : List (Block S Cl)} {Q : Lettered Bk S Cl V W Y Pb → Prop}
    {rs : List (Unlettered V W Y Pb)} (h : ∀ r ∈ rs, Q (r.lay T Sd bs)) :
    ∀ M ∈ rs.map (fun r => r.lay T Sd bs), Q M := by
  intro M hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  exact h r hr

/-- What holds of every list of every lot holds of every one of the lots' lists. -/
theorem forall_rowsOfLots {Z : Pub} {Gr : Ground} {ls : List (SLot V W Y Pb)}
    {Q : Unlettered V W Y Pb → Prop} (h : ∀ l ∈ ls, ∀ r ∈ l.rows Z Gr, Q r) :
    ∀ r ∈ rowsOfLots Z Gr ls, Q r := by
  intro r hr
  obtain ⟨l, hl, hr'⟩ := List.mem_flatMap.1 hr
  exact h l hl r hr'

/-- `OnFromS` reads a list's place, parts and On alone: so an author's, at its own list with any A
and B, is the built list's. -/
theorem onFromS_bare {T' : Thread Bk S Cl V W Y Pb} {Said : Nat → Coins Bk → Mid W Y → Prop}
    {M : Lettered Bk S Cl V W Y Pb} {b : Nat} {len : Nat → Nat → Nat}
    (T : W → Thread Bk S Cl V W Y Pb) (Sd : W → Nat → Coins Bk → Mid W Y → Prop)
    (bs : List (Block S Cl)) (h : OnFromS T' Said M b len) :
    OnFromS T' Said (M.bare.lay T Sd bs) b len := h

end

/-! ## 3, 7, 8 and 10, at a file -/

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- **The three chains' lists, built**: with each chain's falls. -/
def laySides (F : FileDescription Xi)
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (r₁ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi))
    (r₂ : List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky))
    (r₃ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi))
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃)) :
    Sides F Bk W₀ Rc Ky Tr X₀ X :=
  { first := r₁.map fun r => r.lay T₁ S₁ F.first.blocksInOrder
    shared := r₂.map fun r => r.lay T₂ S₂ F.shared.blocksInOrder
    second := r₃.map fun r => r.lay T₃ S₃ F.second.blocksInOrder
    falls₁ := f₁, falls₂ := f₂, falls₃ := f₃ }

section
variable {F : FileDescription Xi}
  {T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {r₁ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)}
  {r₂ : List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)}
  {r₃ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)}
  {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}

/-- **The prover whose sides are the built lists has the lists' own sides**: neither A nor B is
read. -/
theorem prover_lay (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    ((laySides F T₁ T₂ T₃ S₁ S₂ S₃ r₁ r₂ r₃ f₁ f₂ f₃).prover H).first = r₁.map (·.half) ∧
      ((laySides F T₁ T₂ T₃ S₁ S₂ S₃ r₁ r₂ r₃ f₁ f₂ f₃).prover H).shared = r₂.map (·.half) ∧
      ((laySides F T₁ T₂ T₃ S₁ S₂ S₃ r₁ r₂ r₃ f₁ f₂ f₃).prover H).second = r₃.map (·.half) :=
  ⟨halves_lay T₁ S₁ F.first.blocksInOrder r₁, halves_lay T₂ S₂ F.shared.blocksInOrder r₂,
    halves_lay T₃ S₃ F.second.blocksInOrder r₃⟩

/-- **The circle, closed**: at a prover whose three lists of sides are the lists' own, the prover
whose sides are the built lists is that prover. One application of the general lemma
`Sides.prover_self` (Honest/ProverSelf.lean: at any lists G), with its hypotheses in the form that
whoever builds the lists has. -/
theorem prover_lay_self {H : Prover W₀ Rc Xi Ky Tr X₀ X} (h₁ : H.first = r₁.map (·.half))
    (h₂ : H.shared = r₂.map (·.half)) (h₃ : H.second = r₃.map (·.half)) :
    (laySides F T₁ T₂ T₃ S₁ S₂ S₃ r₁ r₂ r₃ f₁ f₂ f₃).prover H = H :=
  Sides.prover_self (h₁.trans (halves_lay T₁ S₁ F.first.blocksInOrder r₁).symm)
    (h₂.trans (halves_lay T₂ S₂ F.shared.blocksInOrder r₂).symm)
    (h₃.trans (halves_lay T₃ S₃ F.second.blocksInOrder r₃).symm)

/-- **`Sides.seated` accepts the built lists** (each is at a place of its chain), where every list's
place is a sub-protocol's. -/
theorem seated_lay (h₁ : ∀ r ∈ r₁, F.first.blocksInOrder.any (fun b => b.place == r.place) = true)
    (h₂ : ∀ r ∈ r₂, F.shared.blocksInOrder.any (fun b => b.place == r.place) = true)
    (h₃ : ∀ r ∈ r₃, F.second.blocksInOrder.any (fun b => b.place == r.place) = true) :
    (laySides F T₁ T₂ T₃ S₁ S₂ S₃ r₁ r₂ r₃ f₁ f₂ f₃).seated = true := by
  unfold Sides.seated
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun M hM => ?_, fun M hM => ?_⟩, fun M hM => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
    exact side_isSome_of_any (h₁ r hr)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
    exact side_isSome_of_any (h₂ r hr)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
    exact side_isSome_of_any (h₃ r hr)

end

/-! ## 10 The rule -/

/-- **The rule for `Owed` at a file, at lists that are built so** (`hG`): `file_owed_hands` with the
three hypotheses on A and B proved, from the plan's own test that no two sub-protocols are at one
place. `seats` is asked list by list: it follows from `seat₁` to `seat₃` ("every list's place is a
sub-protocol's"), which stay hypotheses. A conditional lemma on this folder's own definitions. Its
conclusion is a definition of this folder, a structure of hypotheses: no property, and none of the
library's goals. -/
theorem file_owed_rows {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (r₁ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi))
    (r₂ : List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky))
    (r₃ : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi))
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hG : G = laySides F T₁ T₂ T₃ S₁ S₂ S₃ r₁ r₂ r₃ f₁ f₂ f₃)
    (plan : F.planOk = true) (book : Bk.word F = none)
    (seat₁ : ∀ r ∈ r₁, F.first.blocksInOrder.any (fun b => b.place == r.place) = true)
    (seat₂ : ∀ r ∈ r₂, F.shared.blocksInOrder.any (fun b => b.place == r.place) = true)
    (seat₃ : ∀ r ∈ r₃, F.second.blocksInOrder.any (fun b => b.place == r.place) = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (hand₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0 A' B'
        L.On L.bud)
    (hand₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud)
    (hand₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
        (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    {w₁ : W₀} {rc₁ : Rc} {x₁ : Xi} {k₁ : Coins Bk} {R₁ : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hone : ready F Bk (G.prover H) w₁ rc₁ x₁ k₁ = .ok R₁)
    (hbud : BudDebts F Bk G)
    (sits : ∀ w w', Sits F (G.prover H) (T₁ w) (T₂ w') (T₃ w))
    (o₁ : ∀ w, OwesS (T₁ w) (S₁ w)) (o₂ : ∀ w, OwesS (T₂ w) (S₂ w))
    (o₃ : ∀ w, OwesS (T₃ w) (S₃ w))
    (n₁ : ∀ w b, SaidNext (T₁ w) (S₁ w) b) (n₂ : ∀ w b, SaidNext (T₂ w) (S₂ w) b)
    (n₃ : ∀ w b, SaidNext (T₃ w) (S₃ w) b)
    (y₁ : ∀ w, YesS (T₁ w) (S₁ w) (fallsBy G.falls₁ F.first.blocksInOrder))
    (y₂ : ∀ w, YesS (T₂ w) (S₂ w) (fallsBy G.falls₂ F.shared.blocksInOrder))
    (y₃ : ∀ w, YesS (T₃ w) (S₃ w) (fallsBy G.falls₃ F.second.blocksInOrder))
    (a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₁ F (G.prover H) (T₁ R.own) w₀ rc x k R)
    (a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      Enters₂ F (G.prover H) (T₂ R.common) w₀ rc x k R)
    (a₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      DoorBehind F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) x k R)
    (e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ m₁ m₂ o₁ o₂, S₁ R.own F.first.blocksInOrder.length k m₁ →
        S₂ R.common F.shared.blocksInOrder.length k m₂ →
        m₁.opened = some o₁ → m₂.opened = some o₂ →
        S₃ R.own 0 k { R.start₃ (G.prover H) m₁ m₂
          with opened := some (o₁ ++ o₂) })
    (on₁ : ∀ w, ∀ L ∈ G.first, ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₁ w) (S₁ w) L b (depthAt F))
    (on₂ : ∀ w, ∀ L ∈ G.shared, ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F))
    (on₃ : ∀ w, ∀ L ∈ G.second, ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    Owed F Bk H G Rel := by
  subst hG
  obtain ⟨n1, n2, n3⟩ := places_nodup ((F.planOk_ok).1 plan).places
  exact file_owed_hands T₁ T₂ T₃ S₁ S₂ S₃ plan book (seated_lay seat₁ seat₂ seat₃) hq hroot
    hand₁ hand₂ hand₃ (forall_lay fun r _ => lay_laidAt r T₁ S₁ n1)
    (forall_lay fun r _ => lay_laidAt r T₂ S₂ n2) (forall_lay fun r _ => lay_laidAt r T₃ S₃ n3)
    input hst hone hbud sits o₁ o₂ o₃ n₁ n₂ n₃ y₁ y₂ y₃ a₁ a₂ a₃ e₁ e₂ e₃ on₁ on₂ on₃

end ProofFile.Honest

#print axioms ProofFile.Honest.borderNo_at
#print axioms ProofFile.Honest.find_at
#print axioms ProofFile.Honest.lay_laidAt
#print axioms ProofFile.Honest.lay_side_at
#print axioms ProofFile.Honest.Good.refall
#print axioms ProofFile.Honest.seated_refall
#print axioms ProofFile.Honest.hand_of_good
#print axioms ProofFile.Honest.halves_lay
#print axioms ProofFile.Honest.halves_of_lots
#print axioms ProofFile.Honest.side_isSome_of_any
#print axioms ProofFile.Honest.any_of_strays
#print axioms ProofFile.Honest.forall_lay
#print axioms ProofFile.Honest.forall_rowsOfLots
#print axioms ProofFile.Honest.onFromS_bare
#print axioms ProofFile.Honest.prover_lay
#print axioms ProofFile.Honest.prover_lay_self
#print axioms ProofFile.Honest.seated_lay
#print axioms ProofFile.Honest.file_owed_rows
#print axioms ProofFile.Honest.Unlettered
#print axioms ProofFile.Honest.Unlettered.half
#print axioms ProofFile.Honest.Unlettered.of
#print axioms ProofFile.Honest.Lettered.bare
#print axioms ProofFile.Honest.SLot
#print axioms ProofFile.Honest.SLot.toHLot
#print axioms ProofFile.Honest.rowsOfLots
#print axioms ProofFile.Honest.Unlettered.lay
#print axioms ProofFile.Honest.laySides
