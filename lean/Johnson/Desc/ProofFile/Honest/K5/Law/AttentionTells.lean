-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionTells.lean: what a simulator of the attention segments'
own rounds (kind K5) tells, at every argument: it returns, and what it returns is its own coins laid
out in the rounds' shape. So the law of what it tells is the image of the uniform law on as many
elements of the extension field as the member's declared rounds state scalars. Under the premises of
the field exact, what the part shows is then never none, and has that same law. Statements with their
proofs. The layout and the laws by name are in Honest/K5/Law/AttentionCoinsLaid.lean.

  tell_simOf5, takes_simOf5   the three forms of simulator beside the row's parts
  tellsItsCoins_simOf5  TellsItsCoins (Honest/K5/Law/ExactAtOneTable.lean) at each of them
  attention_tells       CONDITIONAL: K5Block; the side's row: at each member, the numbers ns that its
                        declared rounds state, the simulator's count of coins, and what it tells
  attention_told_law    the same premises: the law of what the simulator tells
  attention_shows_some  CONDITIONAL: as exact_at_side; the premises of the field: at every coin the part
                        shows something
  attention_shows_law   the same premises: the law of what the part shows
  attention_showsSome_form   CONDITIONAL: as exact_at_side: ShowsSome
                        (Honest/K5/Law/ExactAtOneTable.lean) at the side
  attention_tells_at_row, attention_told_law_at_row, attention_shows_at_row,
  attention_showsSome_at_row   CONDITIONAL: the library's head (P5J.AtMgA): the same at every row of the
                        lot that has a side. That the lot has rows, each with a side, at the maker's
                        return: k5_lot_not_empty_at_return (Honest/K5/Law/LotNotEmptyAtMaker.lean)

UniformLaid is uniform on its image: the map is one to one (laidOut_wordsOf_injective).

Limits. These are equations of laws over blocks of coins taken as uniform, one part at a time. They
say nothing of where these coins come from in a run. At a member that sends nothing ns is [0]:
UniformLaid [0] is a point mass at one empty round, and what is shown there is that round.
No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionRowSeat
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionCoinsLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open OnBytes.Slice (ofE)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (shapes PartShape)
open ProofFile.Honest.SumLaw (StatedBy)
open P5J (AtMgA TS)

/-! ## 1 The three forms of simulator -/

section Forms
variable {Pb : Type}

theorem takes_simOf5 (Z : Seat5) (j : Nat) (s : PartShape) :
    (simOf5 (Pb := Pb) Z j s).takes = ⟨0, (sentOf s).sum⟩ := by
  cases s with
  | sum k => exact congrArg (Due.mk 0) (SumLaw.runOf_sum k)
  | one n =>
    cases n with
    | zero => rfl
    | succ n => exact congrArg (Due.mk 0) (by simp [sentOf])

/-- **What each form tells: its coins, laid out in the part's rounds.** -/
theorem tell_simOf5 (Z : Seat5) (j : Nat) (s : PartShape) (x : Pb) (front : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) (c : Cs (simOf5 (Pb := Pb) Z j s).takes) :
    (simOf5 (Pb := Pb) Z j s).tell x front ds asks c = some (laidOut (sentOf s) (coinsE c)) := by
  cases s with
  | sum k => rfl
  | one n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hl : (coinsE c).length = n + 1 := List.length_ofFn
      show some [(⟨(coinsE c).map fun y => .e y.triple, []⟩ : Shown)] =
        some [(⟨((coinsE c).take (n + 1)).map fun y => .e y.triple, []⟩ : Shown)]
      rw [List.take_of_length_le (by omega)]

/-- **TellsItsCoins at each form, in the part's rounds.** -/
theorem tellsItsCoins_simOf5 (Z : Seat5) (j : Nat) (s : PartShape) :
    TellsItsCoins (simOf5 (Pb := Pb) Z j s) (sentOf s) := by
  intro x front ds asks c
  have hc : (coinsE c).length = (sentOf s).sum :=
    (List.length_ofFn).trans (congrArg Due.e (takes_simOf5 Z j s))
  exact ⟨_, tell_simOf5 Z j s x front ds asks c, laidOut_counts _ _ hc.ge,
    laidOut_vals _ _ hc.le, laidOut_cols _ _⟩

end Forms

/-! ## 2 At a member -/

section Member
variable {W₀ Rc Xi Tr X S Cl : Type}

/-- **At each member: what its rounds state, how many coins its simulator takes, and what it tells.**
CONDITIONAL: hB; hr. -/
theorem attention_tells {Pb : Type}
    {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {cells : Tr → Cells} {Z : Seat5}
    {p : P.Par} (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} (hu : u ∈ σ.members) :
    ∃ ns, StatedBy ns u.rounds ∧ u.sim.takes = ⟨0, ns.sum⟩ ∧
      TellsItsCoins u.sim (u.rounds.map fun x => (x.1.items.filter (· != .root)).length) ∧
      ∀ x front ds asks (c : Cs u.sim.takes),
        u.sim.tell x front ds asks c = some (laidOut ns (coinsE c)) := by
  obtain ⟨j, s, hq, rfl⟩ := member_at hr hu
  have hst : StatedBy (sentOf s) (stretchOf σ.block Z j) := by
    have hS := stretch_like hB hq
    cases s with
    | sum k => exact hS.1
    | one n => exact hS
  refine ⟨sentOf s, hst, takes_simOf5 Z j s, ?_, fun x front ds asks c => tell_simOf5 Z j s x front
    ds asks c⟩
  show TellsItsCoins _ ((stretchOf σ.block Z j).map fun x =>
    (x.1.items.filter (· != .root)).length)
  rw [stated_counts _ _ hst]
  exact tellsItsCoins_simOf5 Z j s

/-- **At each member the law of what the simulator tells is the uniform law on as many elements as its
rounds state, laid out in these rounds.** CONDITIONAL: hB; hr. -/
theorem attention_told_law {Pb : Type}
    {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {cells : Tr → Cells} {Z : Seat5}
    {p : P.Par} (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} (hu : u ∈ σ.members) :
    ∃ ns, StatedBy ns u.rounds ∧ ∀ x front ds asks,
      ToldLaw u.sim x front ds asks = UniformLaid ns := by
  obtain ⟨ns, hs, ht, -, hc⟩ := attention_tells hB hr hu
  exact ⟨ns, hs, fun x front ds asks => told_law_of u.sim ns ht x front ds asks
    fun c => hc x front ds asks c⟩

variable {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} {cells : Tr → Cells}
  {Z : Seat5} {p : P.Par}

/-- **Under the premises of the field exact, at every coin the part shows something.** CONDITIONAL:
hB; hr; hx; the field's premises, at On := True, bud := k5Bud. -/
theorem attention_shows_some (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) {index : W₀} {table : Rc} {x : Xi} {trace : Tr}
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hu : u ∈ σ.members)
    (ca : CsAll u.part.carries) (m : Mid (Local W₀ Rc Xi Tr) X) (front : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hm : m.st.input = ⟨index, table, x, trace⟩) (hs : m.seen = front.seen)
    (ho : m.opened = front.opened (readsBefore pre front))
    (hd : drawsFit (u.rounds.map (·.1)) ds = true) (hb : k5Bud u.number ds asks)
    (hh : front.holds 0 0 (u.rounds.map (·.1)) ds = true)
    (hst : u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid)
    (c : Cs u.part.takes × CsAll u.part.spends) :
    (σ.shows .own u (c.1, c.2, ca) m ds asks).isSome = true := by
  obtain ⟨ns, -, -, -, hc⟩ := attention_tells hB hr hu
  exact shows_some_of_law (s := u.sim) (x := x) (front := front)
    (exact_at_side hB hr hx pre index table x trace u hu ca m front ds asks hm trivial hs ho hd hb
      hh hst) (fun b => by
    rw [hc x front ds asks b]
    rfl) c

/-- **Under the same premises what the part shows has the uniform law on as many elements as its rounds
state, laid out in these rounds.** CONDITIONAL: as attention_shows_some. -/
theorem attention_shows_law (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) {index : W₀} {table : Rc} {x : Xi} {trace : Tr}
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hu : u ∈ σ.members)
    (ca : CsAll u.part.carries) (m : Mid (Local W₀ Rc Xi Tr) X) (front : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hm : m.st.input = ⟨index, table, x, trace⟩) (hs : m.seen = front.seen)
    (ho : m.opened = front.opened (readsBefore pre front))
    (hd : drawsFit (u.rounds.map (·.1)) ds = true) (hb : k5Bud u.number ds asks)
    (hh : front.holds 0 0 (u.rounds.map (·.1)) ds = true)
    (hst : u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid) :
    ∃ ns, StatedBy ns u.rounds ∧ ShownLaw .own σ u ca m ds asks = UniformLaid ns := by
  obtain ⟨ns, hs', hl⟩ := attention_told_law hB hr hu
  have e : ShownLaw .own σ u ca m ds asks = ToldLaw u.sim x front ds asks :=
    exact_at_side hB hr hx pre index table x trace u hu ca m front ds asks hm trivial hs ho hd hb hh
      hst
  exact ⟨ns, hs', e.trans (hl x front ds asks)⟩

/-- **ShowsSome at a side with K5's row.** CONDITIONAL: hB; hr; hx. -/
theorem attention_showsSome_form (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ShowsSome σ (fun _ _ _ _ => True) k5Bud pre :=
  fun _ hu ca m front ds asks _ hs ho hd hb hh hst c =>
    attention_shows_some hB hr hx pre hu ca m front ds asks rfl hs ho hd hb hh hst c

end Member

/-! ## 3 At the rows of the lot, under the library's head -/

section Head
variable {Zf : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Xi Tr X : Type}

/-- **At every member of every row of the lot the simulator tells its coins, in the shape that the
member's rounds state.** CONDITIONAL: h; hG; hr; hσ. -/
theorem attention_tells_at_row {Pb : Type} (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x₀) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀) :
    ∀ u ∈ σ₀.members, ∃ ns, StatedBy ns u.rounds ∧ u.sim.takes = ⟨0, ns.sum⟩ ∧
      TellsItsCoins u.sim (u.rounds.map fun x => (x.1.items.filter (· != .root)).length) ∧
      ∀ x front ds asks (c : Cs u.sim.takes),
        u.sim.tell x front ds asks c = some (laidOut ns (coinsE c)) := by
  obtain ⟨Y, p, -, hrow, hB, -⟩ := seat_of_row h hG hr hσ
  exact fun u hu => attention_tells hB hrow hu

/-- **At every member of every row of the lot the law of what the simulator tells is the uniform law on
as many elements as the member's rounds state, laid out in these rounds.** CONDITIONAL: h; hG; hr; hσ. -/
theorem attention_told_law_at_row {Pb : Type} (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x₀)
    {G : Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀) :
    ∀ u ∈ σ₀.members, ∃ ns, StatedBy ns u.rounds ∧ ∀ x front ds asks,
      ToldLaw u.sim x front ds asks = UniformLaid ns := by
  obtain ⟨Y, p, -, hrow, hB, -⟩ := seat_of_row h hG hr hσ
  exact fun u hu => attention_told_law hB hrow hu

/-- **At every member of every row of the lot, under the premises of the field exact at the row's own
On and bud, at every coin the part shows something, and what it shows has the law that its simulator
tells.** CONDITIONAL: h; hG; hr; hσ; the field's premises. -/
theorem attention_shows_at_row (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x₀) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀ Rc Xi Tr X Xi} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hσ : Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) {index : W₀} {table : Rc} {x : Xi} {trace : Tr}
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hu : u ∈ σ₀.members)
    (ca : CsAll u.part.carries) (m : Mid (Local W₀ Rc Xi Tr) X) (front : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hm : m.st.input = ⟨index, table, x, trace⟩) (hs : m.seen = front.seen)
    (ho : m.opened = front.opened (readsBefore pre front))
    (hd : drawsFit (u.rounds.map (·.1)) ds = true) (hb : r.bud u.number ds asks)
    (hh : front.holds 0 0 (u.rounds.map (·.1)) ds = true)
    (hst : u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid) :
    (∀ c : Cs u.part.takes × CsAll u.part.spends,
      (σ₀.shows .own u (c.1, c.2, ca) m ds asks).isSome = true) ∧
    ∃ ns, StatedBy ns u.rounds ∧ ShownLaw .own σ₀ u ca m ds asks = UniformLaid ns := by
  obtain ⟨Y, p, rfl, hrow, hB, hx⟩ := seat_of_row h hG hr hσ
  exact ⟨attention_shows_some hB hrow hx pre hu ca m front ds asks hm hs ho hd hb hh hst,
    attention_shows_law hB hrow hx pre hu ca m front ds asks hm hs ho hd hb hh hst⟩

/-- **ShowsSome at every side of every row of the lot, at the row's own On and bud.** CONDITIONAL: h; hG;
hr; hσ. -/
theorem attention_showsSome_at_row (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x₀) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀ Rc Xi Tr X Xi} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hσ : Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) : ShowsSome σ₀ r.On r.bud pre := by
  obtain ⟨Y, p, rfl, hrow, hB, hx⟩ := seat_of_row h hG hr hσ
  exact attention_showsSome_form hB hrow hx pre

end Head

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.takes_simOf5
#print axioms ProofFile.Honest.K5.tell_simOf5
#print axioms ProofFile.Honest.K5.tellsItsCoins_simOf5
#print axioms ProofFile.Honest.K5.attention_tells
#print axioms ProofFile.Honest.K5.attention_told_law
#print axioms ProofFile.Honest.K5.attention_shows_some
#print axioms ProofFile.Honest.K5.attention_shows_law
#print axioms ProofFile.Honest.K5.attention_showsSome_form
#print axioms ProofFile.Honest.K5.attention_showsSome_at_row
#print axioms ProofFile.Honest.K5.attention_tells_at_row
#print axioms ProofFile.Honest.K5.attention_told_law_at_row
#print axioms ProofFile.Honest.K5.attention_shows_at_row
