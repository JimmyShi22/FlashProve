-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotClean.lean: THE FRAME's TWO TESTS ON HALVES (`twice`,
`strays`, Honest/Frame.lean) AT ALL THAT THE HONEST SIDE OF THE LOT OF THE KIND "an attention
segment's own rounds" (K5) LAYS. WITH NO PREMISE: no place bears two of its halves. CONDITIONAL, on
"the description's maker has returned" and "the ground is the one that this maker makes": none of
its halves stands at a place where no sub-protocol of the first chain stands. Theorems alone; no
definition. No property is claimed.

Why. The maker of the one honest prover (`onlineProverFromPublicFiles`, Honest/AtPure.lean) rejects a filling one of
whose halves stands at no place of its chain: it asks `strays` of the description's flat list and of
ALL lots' halves, laid one behind another (`firstOf`). A run's first tests (`readyTests`,
Honest/Frame.lean) ask `strays` and `twice` of the same list. Both can be had lot by lot. Here is
this lot's share, with the small steps from the lots' shares to the whole list.

Main names:
  `twice_of_nodup`, `strays_of_mem`   the two tests find nothing where the places have no double;
    where each half's place is a block's
  `strays_append`, `strays_firstOf`   `strays` splits over ++; it finds nothing in the lots' whole
    list where it finds nothing in any lot's own
  `firstOf_places_once`, `twice_firstOf`   no double in the whole list where no lot has one and no
    two lots share a place
  `at_most_one`, `zipIdx_once`, `filterMap_once`, `own_in_link`, `link_in_table`   small steps
    beneath: general, on lists and on the driver's table
  `seatAtK_place`, `mem_k5Places`, `k5Places_once`, `k5LotK_place`, `k5LotK_places_once`   where
    the lot's halves stand: at ⟨1, some l, 3, .K5⟩, l the number of a segment of kind 1 in the
    ground's list; no number comes twice. NO PREMISE
  **`k5LotK_no_twice`**   `twice ((k5LotK cells keyOf).halves Z G) = []`: NO PREMISE: general in
    cells, keyOf, Z and G. ONE LOT's SHARE: `readyTests` asks `twice` of all lots' halves together
  `k5LotK_apart`, `k5LotK_apart_behind`   CONDITIONAL: no half of the lot shares its place with a
    half of a list none of whose places is of the kind K5
  `k5LotK_in_table`   CONDITIONAL on hG: each half's place is in the driver's table of places
  **`k5LotK_no_strays`**   CONDITIONAL on `IM.Open` and hG:
    `strays F.first.blocksInOrder ((k5LotK cells keyOf).halves Z G) = []`. `k5LotK_no_strays_chain`: the same
    at the opening's chain. `k5LotK_no_strays_desc`: the same from "the public part is made", hG and
    "the description's maker returns": the three facts that `onlineProverFromPublicFiles` has in hand where it asks

THE PREMISES. hG: G is the ground that the description's maker makes of the public part
(`blankBy pureRoad.links Z = some G`); `onlineProverFromPublicFiles` lays that ground. `IM.Open`
(Johnson/IMR/SeatOpen.lean): the description's maker has returned, opened in its letters: at every
function that stands for the format's second hash function; no premise on scope. WHY hG: this lot reads its
places off the ground's list of segments, not off the public part. At a ground of any make a segment
of kind 1 could stand at a number that the chain has not, under the name and group of a segment
whose public data fit: its half would be astray (Law/LotCleanToy.lean evaluates the table of a
made-up chain of three links at numbers of that sort). That is a reading of the texts: no theorem
here says that the statement fails there.

CALLED: `k5LotK_kind` (Law/LotKind.lean), `seatAtK_spec` (Honest/K5/KeysFit.lean),
`IM.subs_of_kind` (Johnson/IMR/Subs.lean), `IM.places_any` (Johnson/IMR/PlacesScope.lean),
`IM.seat_open` (Johnson/IMR/SeatOpen.lean).
KIN, NOT IMPORTED. `twice_of_nodup` and `strays_of_mem` are stated, binder for binder, as
`twice_nil` and `strays_nil` in Honest/K10/LotAll.lean, and their proofs here follow that file's
nearly line for line, as `link_in_table` follows its `link_in_flat`; its two head theorems on its
own lot are the pattern of the two here. The converse of the first: `nodup_of_twice`
(Honest/Law/Rule/FileOkOf.lean), `halves_once` (Honest/K3/Law/Thread/PlacesOnce.lean). That `strays`
reads the halves' places alone: `strays_of_places` (Honest/K13/AtNowReturn.lean). `IM.k5OwnN_mem`
(Johnson/IMR/K5Seat.lean) opens the list of attention segments inside its proof as `mem_k5Places`
does.

Limits. OF THIS ONE LOT's HALVES, AND OF THEIR PLACES ALONE: of a half's parts nothing. EVERY
STATEMENT ON THE LOT HOLDS ALSO WHERE THE LOT LAYS NOTHING. WHICH HALVES IT LAYS HANGS ON keyOf: it
lays a half at a segment only where the maker's three tests pass at what keyOf yields; at a keyOf
that fails them it lays none, and the statements are met for nothing. That it lays a half anywhere
is not said here (Law/LotCleanHead.lean has twelve at `keyOfK3`, under the hypothesis on the public
input). That the prover's list holds this lot's halves, that another lot's halves are no strays,
have no double or stand at places of other kinds, the description's own test on the places, the
tests on the range and on the book, the two other chains: none is given. That the description's
maker, or `onlineProverFromPublicFiles`, returns anywhere is not shown here. The tests are asked as "the list is empty"
(`isEmpty`); the statements say "= []": one rewriting lies between. The description stands at
`ProofFile.Inst`, the halves at a letter Xi: a caller lays the same for both.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotKind
import Johnson.IMR.PlacesScope
import Johnson.IMR.Subs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching flatPlacesOf linkPlaces addresses)

variable {W₀ Rc Xi Tr V W X : Type}

/-! ## 1 General: on the frame's two tests -/

/-- Where the places have no double, at most one half stands at a place. -/
theorem at_most_one : ∀ hs : List (Placed V W X), (hs.map (·.place)).Nodup →
    ∀ a : Place, (hs.filter fun x => x.place == a).length ≤ 1
  | [], _, _ => Nat.zero_le _
  | x :: hs, h, a => by
    rw [List.map_cons, List.nodup_cons] at h
    by_cases e : (x.place == a) = true
    · have e0 : hs.filter (fun y => y.place == a) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hya
        refine h.1 (List.mem_map.2 ⟨y, hy, ?_⟩)
        exact (beq_iff_eq.1 hya).trans (beq_iff_eq.1 e).symm
      have e1 : (x :: hs).filter (fun y => y.place == a) = x :: hs.filter fun y => y.place == a :=
        List.filter_cons_of_pos e
      rw [e1, e0]
      exact Nat.le_refl _
    · have e1 : (x :: hs).filter (fun y => y.place == a) = hs.filter fun y => y.place == a :=
        List.filter_cons_of_neg e
      rw [e1]
      exact at_most_one hs h.2 a

/-- **`twice` finds nothing where the halves' places have no double.** -/
theorem twice_of_nodup {hs : List (Placed V W X)} (h : (hs.map (·.place)).Nodup) :
    twice hs = [] := by
  unfold twice
  rw [List.filter_eq_nil_iff.2 fun a _ hb => ?_]
  · rfl
  · have h1 := at_most_one hs h a
    have h2 : 1 < (hs.filter fun x => x.place == a).length := by simpa using hb
    omega

/-- **`strays` finds nothing where each half's place is a block's.** -/
theorem strays_of_mem {σ C : Type} {bs : List (Block σ C)} {hs : List (Placed V W X)}
    (h : ∀ x ∈ hs, x.place ∈ bs.map (·.place)) : strays bs hs = [] := by
  unfold strays
  rw [List.filter_eq_nil_iff.2 fun x hx hb => ?_]
  · rfl
  · obtain ⟨b, hb1, hb2⟩ := List.mem_map.1 (h x hx)
    have h1 : (bs.any fun b => b.place == x.place) = true :=
      List.any_eq_true.2 ⟨b, hb1, by rw [hb2]; exact beq_self_eq_true _⟩
    have h2 : (!(bs.any fun b => b.place == x.place)) = true := hb
    rw [h1] at h2
    cases h2

/-- `strays` splits over two lists laid one behind the other. -/
theorem strays_append {σ C : Type} (bs : List (Block σ C)) (hs₁ hs₂ : List (Placed V W X)) :
    strays bs (hs₁ ++ hs₂) = strays bs hs₁ ++ strays bs hs₂ := by
  unfold strays
  rw [List.filter_append, List.map_append]

/-- **`strays` finds nothing in the lots' whole list where it finds nothing in any lot's own.**
-/
theorem strays_firstOf {σ C : Type} (bs : List (Block σ C)) (Z : Pub) (G : Ground) :
    ∀ ls : List (HLot V W X), (∀ L ∈ ls, strays bs (L.halves Z G) = []) →
      strays bs (firstOf Z G ls) = []
  | [], _ => rfl
  | L :: ls, h => by
    show strays bs ((L :: ls).flatMap fun L => L.halves Z G) = []
    rw [List.flatMap_cons, strays_append, h L List.mem_cons_self, List.nil_append]
    exact strays_firstOf bs Z G ls fun M hM => h M (List.mem_cons_of_mem _ hM)

/-- **No double in the lots' whole list where no lot has one and no two lots share a place.** -/
theorem firstOf_places_once (Z : Pub) (G : Ground) :
    ∀ ls : List (HLot V W X), (∀ L ∈ ls, ((L.halves Z G).map (·.place)).Nodup) →
      (ls.Pairwise fun L M => ∀ x ∈ L.halves Z G, ∀ y ∈ M.halves Z G, x.place ≠ y.place) →
      ((firstOf Z G ls).map (·.place)).Nodup
  | [], _, _ => List.nodup_nil
  | L :: ls, h₁, h₂ => by
    have hp := List.pairwise_cons.1 h₂
    show (((L :: ls).flatMap fun L => L.halves Z G).map (·.place)).Nodup
    rw [List.flatMap_cons, List.map_append]
    refine List.nodup_append.2 ⟨h₁ L List.mem_cons_self,
      firstOf_places_once Z G ls (fun M hM => h₁ M (List.mem_cons_of_mem _ hM)) hp.2, ?_⟩
    intro a ha b hb e
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    obtain ⟨M, hM, hyM⟩ := List.mem_flatMap.1 hy
    exact hp.1 M hM x hx y hyM e

/-- **`twice` finds nothing in the lots' whole list** where no lot has a double and no two lots
share a place. -/
theorem twice_firstOf (Z : Pub) (G : Ground) (ls : List (HLot V W X))
    (h₁ : ∀ L ∈ ls, ((L.halves Z G).map (·.place)).Nodup)
    (h₂ : ls.Pairwise fun L M => ∀ x ∈ L.halves Z G, ∀ y ∈ M.halves Z G, x.place ≠ y.place) :
    twice (firstOf Z G ls) = [] :=
  twice_of_nodup (firstOf_places_once Z G ls h₁ h₂)

/-! ## 2 Where the lot's halves stand -/

/-- What the maker of the public data yields at the segment number l stands at the first chain's
link l, piece 3, kind K5. CONDITIONAL: it yields. -/
theorem seatAtK_place {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)} {Z : Pub}
    {G : Ground} {l : Nat} {nm : String} {g : Nat} {Y : Seat5}
    (h : seatAtK keyOf Z G l nm g = some Y) : Y.place = ⟨1, some l, 3, .K5⟩ := by
  have h1 := (seatAtK_spec h).1
  unfold seatAt at h1
  obtain ⟨A, -, h1⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨base, -, h1⟩ := Option.bind_eq_some_iff.1 h1
  simp only at h1
  split at h1
  · obtain rfl := Option.some.inj h1
    rfl
  · cases h1

/-- A member of the list of attention segments: its number is that of a segment of kind 1 in the
ground's list, whose name and group it bears. -/
theorem mem_k5Places {G : Ground} {y : Nat × String × Nat} (hy : y ∈ H2K5.k5Places G) :
    ∃ Xl, G.built[y.1]? = some Xl ∧ Xl.kind = 1 ∧ y.2.1 = Xl.name ∧ y.2.2 = Xl.g := by
  unfold H2K5.k5Places at hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  obtain ⟨hz1, hz2⟩ := List.mem_filter.1 hz
  obtain ⟨Xl, l⟩ := z
  refine ⟨Xl, ?_, by simpa using hz2, rfl, rfl⟩
  show G.built[l]? = some Xl
  rw [← Array.getElem?_toList]
  simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hz1)

/-- The numbers that `zipIdx` lays beside a list's members: none below the start, none twice. -/
theorem zipIdx_once {α : Type} : ∀ (l : List α) (n : Nat),
    (∀ x ∈ l.zipIdx n, n ≤ x.2) ∧ ((l.zipIdx n).map (·.2)).Nodup
  | [], _ => ⟨fun _ h => absurd h (by simp), List.nodup_nil⟩
  | a :: l, n => by
    obtain ⟨h1, h2⟩ := zipIdx_once l (n + 1)
    show (∀ x ∈ (a, n) :: l.zipIdx (n + 1), n ≤ x.2) ∧
      (((a, n) :: l.zipIdx (n + 1)).map (·.2)).Nodup
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (h1 x hx)
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, h2⟩
      obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
      have h3 := h1 x hx
      have e' : x.2 = n := e
      omega

/-- **No segment's number comes twice in the list of attention segments.** No premise. -/
theorem k5Places_once (G : Ground) : ((H2K5.k5Places G).map (·.1)).Nodup := by
  unfold H2K5.k5Places
  rw [List.map_map]
  exact ((List.filter_sublist (l := G.built.toList.zipIdx)).map (·.2)).nodup
    (zipIdx_once G.built.toList 0).2

/-- Members made one by one, each bearing its maker's mark: no mark twice where no maker's mark
comes twice. -/
theorem filterMap_once {ι α κ : Type} (f : ι → Option α) (k : ι → κ) (m : α → κ)
    (hm : ∀ i x, f i = some x → m x = k i) :
    ∀ l : List ι, (l.map k).Nodup → ((l.filterMap f).map m).Nodup
  | [], _ => List.nodup_nil
  | i :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    have ih := filterMap_once f k m hm l h.2
    cases hi : f i with
    | none =>
      rw [List.filterMap_cons_none hi]
      exact ih
    | some x =>
      rw [List.filterMap_cons_some hi, List.map_cons, List.nodup_cons]
      refine ⟨fun hx => h.1 ?_, ih⟩
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hx
      obtain ⟨j, hj, hfj⟩ := List.mem_filterMap.1 hy
      exact List.mem_map.2 ⟨j, hj, by rw [← hm j y hfj, e, hm i x hi]⟩

/-- **Each half that the lot lays stands at ⟨1, some l, 3, .K5⟩, l the number of a segment of kind 1
in the ground's list.** No premise. -/
theorem k5LotK_place (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground) :
    ∀ x ∈ (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G,
      ∃ l Xl, G.built[l]? = some Xl ∧ Xl.kind = 1 ∧ x.place = ⟨1, some l, 3, .K5⟩ := by
  intro x hx
  have hx' : x ∈ (H2K5.k5Places G).filterMap fun y =>
      (seatAtK keyOf Z G y.1 y.2.1 y.2.2).map (k5Half cells) := hx
  obtain ⟨y, hy, hf⟩ := List.mem_filterMap.1 hx'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hf
  obtain ⟨Xl, h1, h2, -, -⟩ := mem_k5Places hy
  exact ⟨y.1, Xl, h1, h2, seatAtK_place hY⟩

/-- **Of all that the lot lays no two stand at one place.** No premise. -/
theorem k5LotK_places_once (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground) :
    (((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G).map
      (·.place)).Nodup := by
  have h1 : (((H2K5.k5Places G).filterMap fun y =>
      (seatAtK keyOf Z G y.1 y.2.1 y.2.2).map
        (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells)).map
      fun x => x.place.link.getD 0).Nodup := by
    refine filterMap_once _ (·.1) _ (fun y x hf => ?_) _ (k5Places_once G)
    obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hf
    show (Y.place.link.getD 0) = y.1
    rw [seatAtK_place hY]
    rfl
  refine List.Nodup.of_map (fun a : Place => a.link.getD 0) ?_
  rw [List.map_map]
  exact h1

/-! ## 3 No place twice -/

/-- **THE FRAME's `twice` FINDS NOTHING AMONG ALL THAT THE LOT LAYS.** No premise: general in the
reader of the witness, the key points' reader, the public part and the ground. One lot's share: a
caller asks the test of all lots' halves together (`twice_firstOf`). -/
theorem k5LotK_no_twice (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground) :
    twice ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G) = [] :=
  twice_of_nodup (k5LotK_places_once cells keyOf Z G)

/-- No half of the lot shares its place with a half whose place is of another kind. CONDITIONAL: no
member of the other list stands at a place of the kind K5. -/
theorem k5LotK_apart {V' W' X' : Type} (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    {hs : List (Placed V' W' X')} (h : ∀ y ∈ hs, y.place.kind ≠ .K5) :
    ∀ x ∈ (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G,
      ∀ y ∈ hs, x.place ≠ y.place := by
  intro x hx y hy e
  exact h y hy (by rw [← e]; exact k5LotK_kind cells keyOf Z G x hx)

/-- The same with the other list in front. CONDITIONAL: as above. -/
theorem k5LotK_apart_behind {V' W' X' : Type} (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    {hs : List (Placed V' W' X')} (h : ∀ y ∈ hs, y.place.kind ≠ .K5) :
    ∀ y ∈ hs, ∀ x ∈ (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G,
      y.place ≠ x.place :=
  fun y hy x hx e => k5LotK_apart cells keyOf Z G h x hx y hy e.symm

/-! ## 4 No half astray -/

/-- The driver's table of places holds, at an attention link, the place of the link's own rounds. -/
theorem own_in_link (l : Nat) : (⟨1, some l, 3, .K5⟩ : Place) ∈ linkPlaces l .attention := by
  unfold linkPlaces addresses kindsBeforeBatching
  simp [VerifiableInference.Desc.First.kindOfModelPart]

/-- A place of a link of the list is in the driver's table. -/
theorem link_in_table {links : List ModelPart} {several : Bool} {l : Nat} {sub : ModelPart}
    (h : links[l]? = some sub) {a : Place} (ha : a ∈ linkPlaces l sub) :
    a ∈ flatPlacesOf links several := by
  unfold flatPlacesOf
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ ?_))
  exact List.mem_flatMap.2 ⟨(sub, l), List.mk_mem_zipIdx_iff_getElem?.2 (by simpa using h), ha⟩

/-- **Each half's place is in the driver's table of places.** CONDITIONAL: hG: G is the ground that
the description's maker makes of the public part. -/
theorem k5LotK_in_table (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) {Z : Pub} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (several : Bool) :
    ∀ x ∈ (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G,
      x.place ∈ flatPlacesOf (ProofFile.subsOf Z) several := by
  intro x hx
  obtain ⟨l, Xl, h1, h2, e⟩ := k5LotK_place cells keyOf Z G x hx
  have h3 : (ProofFile.subsOf Z)[l]? = some ModelPart.attention := by
    rw [IM.subs_of_kind hG h1, h2]
    rfl
  rw [e]
  exact link_in_table h3 (own_in_link l)

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **`strays` finds nothing among all that the lot lays, at the opening's own chain.**
CONDITIONAL: `IM.Open`; hG. -/
theorem k5LotK_no_strays_chain (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) {G : Ground}
    (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    strays c.blocksInOrder ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G) =
      [] :=
  strays_of_mem fun x hx => by
    rw [IM.places_any O]
    exact k5LotK_in_table cells keyOf hG true x hx

/-- **THE FRAME's `strays` FINDS NOTHING AMONG ALL THAT THE LOT LAYS, AT THE DESCRIPTION's OWN LIST
`F.first.blocksInOrder`.** CONDITIONAL: `IM.Open`; hG. At every function that stands for the earlier hash;
no premise on scope. One lot's share: a caller asks the test of all lots' halves together
(`strays_firstOf`). -/
theorem k5LotK_no_strays (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) {G : Ground}
    (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    strays F.first.blocksInOrder
      ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G) = [] := by
  have key := k5LotK_no_strays_chain (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf O hG
  obtain rfl := O.desc
  exact key

/-- **The same from the three facts that the prover's maker has in hand where it asks the test.**
CONDITIONAL: hZ: the public part is made; hG; hF: the description's maker returns. -/
theorem k5LotK_no_strays_desc (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) {G : Ground}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    strays F.first.blocksInOrder
      ((k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).halves Z G) = [] := by
  obtain ⟨Z', Bs, base, c, A, B, O⟩ := IM.seat_open hF
  obtain rfl : Z' = Z := Except.ok.inj (O.pub.symm.trans hZ)
  exact k5LotK_no_strays cells keyOf O hG

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.at_most_one
#print axioms ProofFile.Honest.K5.twice_of_nodup
#print axioms ProofFile.Honest.K5.strays_of_mem
#print axioms ProofFile.Honest.K5.strays_append
#print axioms ProofFile.Honest.K5.strays_firstOf
#print axioms ProofFile.Honest.K5.firstOf_places_once
#print axioms ProofFile.Honest.K5.twice_firstOf
#print axioms ProofFile.Honest.K5.seatAtK_place
#print axioms ProofFile.Honest.K5.mem_k5Places
#print axioms ProofFile.Honest.K5.zipIdx_once
#print axioms ProofFile.Honest.K5.k5Places_once
#print axioms ProofFile.Honest.K5.filterMap_once
#print axioms ProofFile.Honest.K5.k5LotK_place
#print axioms ProofFile.Honest.K5.k5LotK_places_once
#print axioms ProofFile.Honest.K5.k5LotK_no_twice
#print axioms ProofFile.Honest.K5.k5LotK_apart
#print axioms ProofFile.Honest.K5.k5LotK_apart_behind
#print axioms ProofFile.Honest.K5.own_in_link
#print axioms ProofFile.Honest.K5.link_in_table
#print axioms ProofFile.Honest.K5.k5LotK_in_table
#print axioms ProofFile.Honest.K5.k5LotK_no_strays_chain
#print axioms ProofFile.Honest.K5.k5LotK_no_strays
#print axioms ProofFile.Honest.K5.k5LotK_no_strays_desc
