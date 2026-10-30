-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/HandIn.lean: CONDITIONAL: on h and hA. What K4
hands in for its simulators, at a return of the maker, general in the filling: twelve rows at
twelve places, one at each member of the kind K4; at each row `Good` at the maker's book; no part
stops; each simulator reads its own coins alone and says something at every coin. Statements and
proofs.

  `k4_sort_no_stop`, `k4_sided_no_stop`   a part of a sort has no stop of either sort, and its
      simulator reads its coins alone; so every pair of K4's row.
  `k4_sims_free`   the simulators are a function of the public data alone.
  `k4_rows_count`, `k4_rows_places`   twelve rows; no place twice.
  `k4_row_of_block`   a row at every member of the kind K4.
  `some_of_same_law`, `k4_shows_some`   what a part of a row shows is some value, at every state and list of challenges.
  `k4_rows_on_true`, `k4_rows_bud_true`   guards: On and bud are True at every row.
  `K4RowHandIn`, `K4HandIn`   what is handed in at one row and for the list: sentences.
  `k4SimulatorHandInAtMaker`, `k4SimulatorHandInAtReturn`   **they hold at a return of the maker**,
      at the head's own first chain and at the return's own description.

Limits. Those of Law/ExactFresh/AtLot.lean and AtBook.lean, of which nothing is taken back. A := B :=
False: what counts of `Good` is fits, exact and fresh. exact IS THE SPENDER's HALF; fresh IS TRUE AND
EMPTY: the weight lies on the owners' fresh, which is not said here. On and bud are True: at every
part they hold by definition, so nothing is owed for them here; Owed's fields runs and owed rest on
the threads, in which K4's plays at its twelve borders are not paid here. THE ROWS ARE THE LOT's; THAT THE
PROVER OF A FILLING HAS THEM IS `k4_first_halves` (AtHalves.lean), where the filling has the lot. At
a zero challenge of the second token sumcheck exact holds as at any other: nothing stops and the
simulator reads no challenge. WHAT THE ROWS TAKE: `k4SLot` is one term of type Pub → Ground → List
Unlettered, in the readers cells : Tr → Cells and weights : W₀ → Weights and the lookup's reader look:
functions, no index, table randomness, trace or coin among its arguments; what they read of a run
they read through these readers, inside the parts; the simulators read none (`k4_sims_free`). h: the
library's head on the public files: `P5J.head_of_live` gives one from scope, read and live. No
property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtBook
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtHalves
import Johnson.Desc.ProofFile.Honest.K4.Law.LotTwelve
import Johnson.Desc.ProofFile.Honest.K4.Law.LotSideAtKind
import Johnson.Desc.ProofFile.Honest.Law.SharesNoHid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Block)
open P5J (AtMgA TS LaidAt)

section Sorts
variable {W₀ Rc Xi Tr X : Type} (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
  (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)

/-- **A part of a sort has no stop of either sort, and its simulator reads its own coins alone and
says something at every coin**: so by `exact` the part shows something with probability one. -/
theorem k4_sort_no_stop {x : K4Kind} {i : Nat}
    {y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi}
    (h : x.Of Q cells weights tokens look i y) :
    (∀ g o, y.1.bad g o = none) ∧ (∀ v g o, y.1.hid v g o = none) ∧
      (∀ pb pb' f f' ds ds' a a' c, y.2.tell pb f ds a c = y.2.tell pb' f' ds' a' c) ∧
      ∀ pb f ds a c, (y.2.tell pb f ds a c).isSome = true := by
  cases x with
  | quiet =>
    obtain rfl : y = _ := h
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | lone n =>
    obtain ⟨f, rfl⟩ : ∃ f, y = _ := h
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | ms k =>
    obtain ⟨J, rfl, name, endName, rfl⟩ : ∃ J : SumJob K4In Unit, J.shape = k ∧ ∃ name endName,
      y = _ := h
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- **Every pair of K4's row.** -/
theorem k4_sided_no_stop {y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi}
    (hy : y ∈ k4Sided (Rc := Rc) (X := X) Q cells weights tokens look) :
    (∀ g o, y.1.bad g o = none) ∧ (∀ v g o, y.1.hid v g o = none) ∧
      (∀ pb pb' f f' ds ds' a a' c, y.2.tell pb f ds a c = y.2.tell pb' f' ds' a' c) ∧
      ∀ pb f ds a c, (y.2.tell pb f ds a c).isSome = true := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
  have ht : i < (k4KindsAll Q).length := by
    rw [← k4Sided_length (Rc := Rc) (X := X) Q cells weights tokens look]
    exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨y', hy', hof⟩ := k4_kind_all (Rc := Rc) (X := X) Q cells weights tokens look
    (List.getElem?_eq_getElem ht)
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hi)
  exact k4_sort_no_stop Q cells weights tokens look hof

end Sorts

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X' : Type}

/-- **The simulators are free of the filling**: K4's row's simulators are `k4Sims Q`, a function of
the public data alone, whatever the cells, the weights, the tokens and the lookup's reader. -/
theorem k4_sims_free {Rc Xi X : Type} {Tr₂ W₂ : Type} (Q : K4Pub) (cells : Tr₂ → Cells)
    (weights : W₂ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look).map (·.2) = k4Sims (Xi := Xi) Q := by
  unfold k4Sided
  refine List.map_snd_zip ?_
  unfold k4Row k4RowIn k4Sims k4Sorts
  cases (Q.g == 0) <;> exact Nat.le_refl _

/-- CONDITIONAL: on h and hG. **Twelve rows.** -/
theorem k4_rows_count (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    ((k4SLot (Rc := Rc) (X := X') cells weights look).rows Zp G₀).length = 12 := by
  have e := congrArg List.length (k4_rows_halves (Rc := Rc) (X := X') cells weights look Zp G₀)
  rw [List.length_map] at e
  rw [e]
  exact k4HLot_twelve h hG cells weights look

/-- **No place twice.** No hypothesis. -/
theorem k4_rows_places (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    (((k4SLot (Rc := Rc) (X := X') cells weights look).rows Zq G).map (·.place)).Nodup := by
  have e := k4HLot_places_once (Rc := Rc) (X' := X') cells weights look Zq G
  rw [← k4_rows_halves, List.map_map] at e
  exact e

/-- CONDITIONAL: on h and hG. **A row at every member of the first chain of the kind K4.** -/
theorem k4_row_of_block (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hk : b.place.kind = .K4) :
    ∃ row ∈ (k4SLot (Rc := Rc) (X := X') cells weights look).rows Zp G₀, row.place = b.place := by
  have e := k4HLot_side_at_kind (Rc := Rc) (X' := X') h hG cells weights look hb hk
  rw [← k4_rows_halves, List.map_map] at e
  obtain ⟨row, hr, er⟩ := List.mem_map.1 e
  exact ⟨row, hr, er⟩

/-- Where a law with every value in its support has the law of something that is never none, it
is never none itself. -/
theorem some_of_same_law {α β γ : Type} (p : PMF α) (q : PMF β) (hp : ∀ a, a ∈ p.support)
    (f : α → Option γ) (g : β → Option γ) (e : p.map f = q.map g)
    (hg : ∀ b, (g b).isSome = true) (a : α) : (f a).isSome = true := by
  have hin : f a ∈ (p.map f).support := (PMF.mem_support_map_iff _ _ _).2 ⟨a, hp a, rfl⟩
  rw [e] at hin
  obtain ⟨b, -, eb⟩ := (PMF.mem_support_map_iff _ _ _).1 hin
  rw [← eb]
  exact hg b

/-- The same at a uniform law. Its instances are plain implicit arguments: a caller's equation fixes
them, and nothing is searched. -/
theorem some_of_same_unif {α β γ : Type} {i : Fintype α} {j : Nonempty α} (q : PMF β)
    (f : α → Option γ) (g : β → Option γ) (e : (@PMF.uniformOfFintype α i j).map f = q.map g)
    (hg : ∀ b, (g b).isSome = true) (a : α) : (f a).isSome = true :=
  some_of_same_law _ q (fun a => @PMF.mem_support_uniformOfFintype α i j a) f g e hg a

/-- CONDITIONAL: on hS, hR, L and hG. **WHAT A PART OF A ROW SHOWS IS SOME VALUE**, at every state
and every list of challenges at which the premises of `ExactMember` hold, at all coins: the simulator
says something at every coin, and a uniform law has every coin in its support. So `exact` at these
rows is no equation of two laws on none. -/
theorem k4_shows_some (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    {row : Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hr : row ∈ (k4SLot cells weights look).rows Zp G₀) {fs : List (Fall TS)}
    {σ : Side TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hσ : Side.seated cF.blocksInOrder row.place row.row fs = some σ)
    (φ : Face (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) ProofFile.Inst)
    (chain firstTree : Nat)
    {u : Member (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hu : u ∈ σ.members) (ca : CsAll u.part.carries) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X')
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hseen : m.seen = front.seen) (hdraws : drawsFit (u.rounds.map (·.1)) ds = true)
    (hholds : front.holds chain firstTree (u.rounds.map (·.1)) ds = true)
    (c : Cs u.part.takes × CsAll u.part.spends) :
    (σ.shows φ u (c.1, c.2, ca) m ds asks).isSome = true := by
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
  have hσ' : Side.seated cF.blocksInOrder (k4Place Q)
      (k4Sided Q cells weights k4Tokens (look Zp G₀ Q)) fs = some σ := hσ
  have hm := seated_mem hσ'
  obtain ⟨hrow, hp⟩ := seated_is hσ'
  obtain ⟨he, hs⟩ := k4_member_of_lot hS hR L hG hx hQ hm hp
  have hE := k4_closed_all φ σ chain firstTree (fun _ _ _ _ => True) (fun _ _ _ => True) Q cells
    weights k4Tokens (look Zp G₀ Q) hrow (block_stated_shaped Q _ he hs) u hu
  obtain ⟨t, y, hy, rfl⟩ := membersOf_at σ.row 0 _ u hu
  have hym : y ∈ k4Sided (Rc := Rc) (X := X') Q cells weights k4Tokens (look Zp G₀ Q) := by
    rw [← hrow]
    exact List.mem_of_getElem? hy
  obtain ⟨-, hh, -, hsome⟩ := k4_sided_no_stop Q cells weights k4Tokens _ hym
  have hst := stopAt_not_hid y.1 (φ.sees m.st.input) m.loc ds fun v j => hh v _ _
  have eq := hE ca m front ds asks trivial hseen hdraws trivial hholds hst
  exact some_of_same_unif _ _ _ eq (fun _ => hsome _ _ _ _ _) c

/-- **A GUARD: At every row of the lot On is True.** Why it must stay so:
an On of K4's row that ever asks the claim, KT or "ε ≠ 0" brings the
emptiness back. Whoever turns On breaks this theorem. -/
theorem k4_rows_on_true (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    {row : Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hr : row ∈ (k4SLot cells weights look).rows Zq G) :
    row.On = fun _ _ _ _ => True := by
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Q, -, rfl⟩ := Option.map_eq_some_iff.1 e
  rfl

/-- **A GUARD: At every row of the lot bud is True.** For the same reason as `k4_rows_on_true`; K4's
rounds state no root, so no position is read. -/
theorem k4_rows_bud_true (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    {row : Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hr : row ∈ (k4SLot cells weights look).rows Zq G) :
    row.bud = fun _ _ _ => True := by
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Q, -, rfl⟩ := Option.map_eq_some_iff.1 e
  rfl

/-- **WHAT K4's HOUSE HANDS IN AT ONE ROW: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; AT
A := B := False.** At the list of sub-protocols bs and the book Bk. Sentences, none of the library's
goals. -/
structure K4RowHandIn {S Cl W₁ Rc₁ Tr₁ X₁ : Type} (bs : List (Block S Cl)) (Bk : ProverCoinCounts)
    (Zq : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (row : Unlettered (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁ ProofFile.Inst) :
    Prop where
  /-- the row's place is of the kind K4 -/
  placeIsOfTheKind : row.place.kind = .K4
  /-- guards: On and bud are True, see `k4_rows_on_true` -/
  onHolds : ∀ u ca m front, row.On u ca m front
  budHolds : ∀ n ds asks, row.bud n ds asks
  /-- it is seated, at every list of falls -/
  seated : ∀ fs : List (Fall S), ∃ σ : Side S Cl (Local W₁ Rc₁ ProofFile.Inst Tr₁)
    (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁ ProofFile.Inst, Side.seated bs row.place row.row fs = some σ
  /-- the simulators are those of the public data Q that the public part Zq and the ground G₀ make
  at the row's place, whatever the readers -/
  simulatorsAreOfThePublicData : ∃ x ∈ ProofFile.k4From Zq G₀ G₀.built.toList 0 none, ∃ Q : K4Pub,
    k4PubOf Zq x.2 = some Q ∧ row.place = k4Place Q ∧
      row.row.map (·.2) = k4Sims (Xi := ProofFile.Inst) Q
  /-- no part has a stop of either sort -/
  neverStops : ∀ y ∈ row.row, (∀ g o, y.1.bad g o = none) ∧ ∀ v g o, y.1.hid v g o = none
  /-- each simulator reads its own coins alone, and says something at every coin -/
  simulatorsReadTheirCoinsAlone : ∀ y ∈ row.row, ∀ pb pb' f f' ds ds' a a' c,
    y.2.tell pb f ds a c = y.2.tell pb' f' ds' a' c
  simulatorsSaySomething : ∀ y ∈ row.row, ∀ pb f ds a c, (y.2.tell pb f ds a c).isSome = true
  /-- `Good` at the row's side, at every pre, face, order and numbers -/
  good : ∀ (fs : List (Fall S))
    (σ : Side S Cl (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁ ProofFile.Inst),
    Side.seated bs row.place row.row fs = some σ →
    ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
      (φ : Face (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) ProofFile.Inst)
      (ord : List Place) (chain firstTree : Nat),
      Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) row.On
        row.bud
  /-- what a part shows is some value, at every state and list at which exact's premises hold -/
  showsSome : ∀ (fs : List (Fall S))
    (σ : Side S Cl (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁ ProofFile.Inst),
    Side.seated bs row.place row.row fs = some σ →
    ∀ (φ : Face (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) ProofFile.Inst)
      (chain firstTree : Nat), ∀ u ∈ σ.members, ∀ (ca : CsAll u.part.carries)
      (m : Mid (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁) (front : Before) (ds : List Fmt.Drawn)
      (asks : List (List (List Nat))), m.seen = front.seen →
      drawsFit (u.rounds.map (·.1)) ds = true →
      front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
      ∀ c : Cs u.part.takes × CsAll u.part.spends,
        (σ.shows φ u (c.1, c.2, ca) m ds asks).isSome = true

/-- **WHAT K4's HOUSE HANDS IN FOR ITS LIST OF ROWS.** -/
structure K4HandIn {S Cl W₁ Rc₁ Tr₁ X₁ : Type} (bs : List (Block S Cl)) (Bk : ProverCoinCounts)
    (Zq : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (rows : List (Unlettered (Local W₁ Rc₁ ProofFile.Inst Tr₁) (Local W₁ Rc₁ ProofFile.Inst Tr₁) X₁ ProofFile.Inst)) :
    Prop where
  rowsAreTwelve : rows.length = 12
  placesAreDistinct : (rows.map (·.place)).Nodup
  everyBlockOfTheKindHasARow : ∀ b ∈ bs, b.place.kind = .K4 → ∃ row ∈ rows, row.place = b.place
  atEveryRow : ∀ row ∈ rows, K4RowHandIn bs Bk Zq G₀ row

/-- CONDITIONAL: on h and hA. **K4's HAND-IN AT A RETURN OF THE MAKER, AT THE HEAD's OWN FIRST CHAIN:
THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; AT A := B := False**, general in the filling
and in the types of the rows. -/
theorem k4SimulatorHandInAtMaker (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₁ Rc₁ Tr₁ X₁ : Type} (cells : Tr₁ → Cells) (weights : W₁ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    K4HandIn cF.blocksInOrder A.B A.Z A.G
      ((k4SLot (Rc := Rc₁) (X := X₁) cells weights look).rows A.Z A.G) := by
  have eZ := atPure_pub_at_laid h.laid hA
  have hG := atPure_ground_at_laid h.laid hA
  refine ⟨?_, k4_rows_places cells weights look _ _, ?_, ?_⟩
  · rw [eZ]
    exact k4_rows_count h hG cells weights look
  · intro b hb hk
    rw [eZ]
    exact k4_row_of_block h hG cells weights look hb hk
  · intro row hr
    have hr' := hr
    rw [eZ] at hr'
    have hsided : ∀ y ∈ row.row, (∀ g o, y.1.bad g o = none) ∧ (∀ v g o, y.1.hid v g o = none) ∧
        (∀ pb pb' f f' ds ds' a a' c, y.2.tell pb f ds a c = y.2.tell pb' f' ds' a' c) ∧
        ∀ pb f ds a c, (y.2.tell pb f ds a c).isSome = true := by
      obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr'
      obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
      exact fun y hy => k4_sided_no_stop Q cells weights k4Tokens _ hy
    have hkind : row.place.kind = .K4 := by
      obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr'
      obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
      rfl
    have hpub : ∃ x ∈ ProofFile.k4From A.Z A.G A.G.built.toList 0 none, ∃ Q : K4Pub,
        k4PubOf A.Z x.2 = some Q ∧ row.place = k4Place Q ∧
          row.row.map (·.2) = k4Sims (Xi := ProofFile.Inst) Q := by
      obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
      obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
      exact ⟨x, hx, Q, hQ, rfl, k4_sims_free Q cells weights k4Tokens _⟩
    refine ⟨hkind, ?_, ?_, fun fs => k4_row_seated h.scope h.reads h.laid hG cells weights look hr' fs,
      hpub, fun y hy => ⟨(hsided y hy).1, (hsided y hy).2.1⟩, fun y hy => (hsided y hy).2.2.1,
      fun y hy => (hsided y hy).2.2.2,
      fun fs σ hσ pre φ ord chain firstTree =>
        k4_good_at_maker h.scope h.reads h.laid hA cells weights look hr hσ pre φ ord chain
          firstTree,
      fun fs σ hσ φ chain firstTree u hu ca m front ds asks hseen hdraws hholds c =>
        k4_shows_some h.scope h.reads h.laid hG cells weights look hr' hσ φ chain firstTree hu ca m
          front ds asks hseen hdraws hholds c⟩
    · rw [k4_rows_on_true cells weights look _ _ hr']
      exact fun _ _ _ _ => trivial
    · rw [k4_rows_bud_true cells weights look _ _ hr']
      exact fun _ _ _ => trivial

/-- CONDITIONAL: on h and hA. **THE SAME AT THE MAKER's OWN DESCRIPTION.** -/
theorem k4SimulatorHandInAtReturn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₁ Rc₁ Tr₁ X₁ : Type} (cells : Tr₁ → Cells) (weights : W₁ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    K4HandIn A.F.first.blocksInOrder A.B A.Z A.G
      ((k4SLot (Rc := Rc₁) (X := X₁) cells weights look).rows A.Z A.G) := by
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  have hm := k4SimulatorHandInAtMaker (W₁ := W₁) (Rc₁ := Rc₁) (Tr₁ := Tr₁) (X₁ := X₁) h hA cells
    weights look
  obtain ⟨AZ, AG, AF, AB, AH, Ar, Arows⟩ := A
  dsimp only at eF hm ⊢
  subst eF
  exact hm

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4_sort_no_stop
#print axioms ProofFile.Honest.K4.ExactFresh.k4_sided_no_stop
#print axioms ProofFile.Honest.K4.ExactFresh.k4_sims_free
#print axioms ProofFile.Honest.K4.ExactFresh.k4_rows_count
#print axioms ProofFile.Honest.K4.ExactFresh.k4_rows_places
#print axioms ProofFile.Honest.K4.ExactFresh.k4_row_of_block
#print axioms ProofFile.Honest.K4.ExactFresh.k4_shows_some
#print axioms ProofFile.Honest.K4.ExactFresh.k4_rows_on_true
#print axioms ProofFile.Honest.K4.ExactFresh.k4_rows_bud_true
#print axioms ProofFile.Honest.K4.ExactFresh.k4SimulatorHandInAtMaker
#print axioms ProofFile.Honest.K4.ExactFresh.k4SimulatorHandInAtReturn
