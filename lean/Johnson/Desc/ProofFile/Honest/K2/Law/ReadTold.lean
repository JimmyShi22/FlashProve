-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ReadTold.lean: the kind "the code switch" (K2): THE WIDTH THAT
A SWITCH's LIST `read` STATES FOR A TREE IS THE WIDTH THAT THE WRITTEN PLAN TELLS OF THAT TREE, and
so, at a tree of K1's, what K1's job states; with it the clause of "the widths" at a tree of K1's,
at the joined Script, without `PlayedTo`. One definition; one closed fact by evaluation in Lean's
kernel, with a control; three laws.

  `readToldB`, `readToldW`   THE TEST, BY LEAN's KERNEL, at each written place: the switch reads
                    three trees, and each has the width that the written list `toldFull` tells at
                    its number; the control: every width raised by one: no
  `told_at_member`   under the written cut: the written list at a member's tree is the block's own
  `read_width_k1`   at a tree of K1's: the width in `read` is what K1's job states
  `width_k1_read_at_join`   THE CLAUSE, at the joined Script

By: `toldOf_of_cut` (Johnson/Top/H0/K2Ties/ToldAt.lean) · `six_at_head`
(Johnson/Desc/K2/Honest/Returns/TiedReached.lean) · `treesTo_at_head`, `places_at_head`
(Honest/K2/Law/PlacesWritten.lean) · `HashBuild.flatten_at` (Johnson/Desc/AtSeats/DeclHalfOf.lean),
all sealed; ours: `numsW_at_head` (PublicAtHead.lean) · `width_k1_at_join` (WidthK1AtJoin.lean).
Kin, ours: `readFrontW` (WidthAtJoin.lean), `readOwnW` (ReadOwn.lean): the widths of the like lists
against the switch in front's own numbers; `readToldW` takes every tree that a place reads.

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM THE LAWS THAT NAME THEM HOLD EMPTILY. hsh (K1's block states K1's oracle messages) IS A
PREMISE: the third limb of the field shape of the sealed record `K1Seated`; its payers, in scope,
under the opening, not called here: `k1_two_inScope`, `k1_fifty_inScope`
(Honest/K1/Law/MemberInScope.lean). F AND hc ARE PREMISES, AS IN WidthK1AtJoin.lean. WHICH TREE A
SWITCH READS AT WHICH MEMBER IS NOT SAID: the tree's number is laid as e. A CLOSED FACT BY LEAN's
KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. NOT IN FRONT OF A LAW OVER COINS. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.WidthK1AtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.Desc.K2.Honest.Returns.TiedReached
import Johnson.Top.H0.K2Ties.ToldAt
import Johnson.Desc.AtSeats.DeclHalfOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Oracle)
open VerifiableInference.Desc.First (S treesTold toldOf)
open VerifiableInference.Desc.First.K2Ties (toldFull toldOf_of_cut)
open VerifiableInference.Desc.K2.Honest.Returns (six_at_head)
open OnBytes.Maker (WholeD)
open P5J (AtMg TS F0T)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1

/-- **The test**, at the written plan. shift: 0 is the test; another number is a control. -/
def readToldB (shift : Nat) : Bool :=
  placesW.all fun p => (numsW p.place.link).any fun n =>
    n.read.length == 3 && n.read.all fun t =>
      (toldFull.flatten[t.1]?).any fun o => o.words + shift == t.2.2

set_option maxRecDepth 1000000 in
/-- **Its yes, and a control**: with every width raised by one it says no. -/
theorem readToldW : readToldB 0 = true ∧ readToldB 1 = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}

/-- **Under the written cut: the written list at a member's tree is the block's own.** -/
theorem told_at_member (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) {b τ : Nat} {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[b]? = some blk) (hτ : τ < blk.oracles.flatten.length) :
    toldFull.flatten[treesTold toldFull b + τ]? = blk.oracles.flatten[τ]? := by
  have e : toldFull = cF.blocksInOrder.map fun x => x.oracles.flatten := (toldOf_of_cut hcut).symm
  have hl : toldFull[b]? = some blk.oracles.flatten := by
    rw [e, List.getElem?_map, hb]
    rfl
  unfold treesTold
  exact HashBuild.flatten_at toldFull b τ _ hl hτ

/-- **At a tree of K1's the width in a switch's list is what K1's job states.** hsh: the block
states K1's oracle messages. -/
theorem read_width_k1 (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) {Pp : P1K2.Prep} {n : P1K2.Nums}
    (hP : P1K2.prepOf Zp Bs.G₀ = some Pp) (hn : P1K2.numsAt Pp p.place.link = some n)
    {t : Nat × Nat × Nat} (ht : t ∈ n.read) {b τ : Nat} {blk : Block TS ProofFile.Cl}
    {J : VerifiableInference.Desc.K1.Par}
    (hb : cF.blocksInOrder[b]? = some blk) (hsh : blk.oracles = VerifiableInference.Desc.K1.oracles J)
    {tr : OnBytes.TreeShape} (hτ : J.trees[τ]? = some tr) (e : t.1 = treesTo cF.blocksInOrder b + τ) :
    tr.mainWidth + tr.maskWidth = t.2.2 := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h O]
    exact hp
  have w := List.all_eq_true.1 readToldW.1 p hpW
  rw [numsW_at_head h O hP, hn] at w
  simp only [Option.any_some, Bool.and_eq_true] at w
  have a := List.all_eq_true.1 w.2 t ht
  obtain ⟨-, hcut, -⟩ := six_at_head h O
  have hlen : τ < J.trees.length := (List.getElem?_eq_some_iff.1 hτ).1
  have hfl : blk.oracles.flatten[τ]?.map (·.words) = some (tr.mainWidth + tr.maskWidth) := by
    rw [hsh]
    simp [VerifiableInference.Desc.K1.oracles, List.getElem?_map, List.getElem?_zipIdx, hτ]
  have hτ' : τ < blk.oracles.flatten.length := by
    rw [hsh]
    simpa [VerifiableInference.Desc.K1.oracles] using hlen
  rw [e, treesTo_at_head h O, told_at_member hcut hb hτ'] at a
  cases ho : blk.oracles.flatten[τ]? with
  | none =>
    rw [ho] at a
    cases a
  | some o =>
    rw [ho] at a hfl
    simp only [Option.any_some, beq_iff_eq, Nat.add_zero, Option.map_some,
      Option.some.injEq] at a hfl
    exact hfl.symm.trans a

variable {Bk : ProverCoinCounts} {Wl Xi X Cells Tok V X' Pb : Type} {front : Nat}
  {arr : Nat → Nat → Nat} {seats : List (Nat × Nat)} {wit : Wl → PlaceIn Xi} {own₀ : X}
  {jobs : List (Nat × SendJob (PlaceIn Xi) X)} {Oth : Others Bk Wl}

/-- **THE CLAUSE OF "THE WIDTHS" AT A TREE OF K1's**, at a thread whose four fields are the joined
Script's: no `PlayedTo` is asked. -/
theorem width_k1_read_at_join (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) {Pp : P1K2.Prep} {n : P1K2.Nums}
    (hP : P1K2.prepOf Zp Bs.G₀ = some Pp) (hn : P1K2.numsAt Pp p.place.link = some n)
    {t : Nat × Nat × Nat} (ht : t ∈ n.read)
    (F : JoinFit cF.blocksInOrder front arr seats wit own₀ jobs Oth)
    (cells : Wl → Cells) (tok : Wl → Tok) (T : Thread Bk S ProofFile.Cl V Wl X' Pb)
    (hbs : T.bs = cF.blocksInOrder) (hfr : T.front = front)
    (htab : T.table = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs Oth).fixed)
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[x.1]? = some blk)
    (hsh : blk.oracles = VerifiableInference.Desc.K1.oracles x.2.P) {τ : Nat}
    {tr : OnBytes.TreeShape} (hτ : x.2.P.trees[τ]? = some tr)
    (e : t.1 = treesTo cF.blocksInOrder x.1 + τ)
    (Said : Nat → Coins Bk → Mid Wl X' → Prop) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid Wl X'} {E : Env} (hb : x.1 < b) (hT : ThrS T Said b k s m E)
    {c : Cs (dueR x.2.P x.2.ride)}
    (hc : lentCut k 0 ⟨x.2.P.place, 0⟩ (dueR x.2.P x.2.ride) = some c) :
    (T.tableAt (.own t.1) k m).2.words = t.2.2 := by
  have hτr : ∀ blk', cF.blocksInOrder[x.1]? = some blk' → τ < (blk'.oracles.flatMap id).length := by
    intro blk' hb'
    obtain rfl : blk = blk' := Option.some.inj (hblk.symm.trans hb')
    rw [hsh]
    simpa [VerifiableInference.Desc.K1.oracles] using (List.getElem?_eq_some_iff.1 hτ).1
  have q := width_k1_at_join F cells tok T hbs hfr htab hfix hx hτ hτr Said hb hT hc
  rw [hbs, ← e] at q
  exact q.trans (read_width_k1 h O hp hP hn ht hblk hsh hτ e)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.readToldB
#print axioms ProofFile.Honest.K2.Law.readToldW
#print axioms ProofFile.Honest.K2.Law.told_at_member
#print axioms ProofFile.Honest.K2.Law.read_width_k1
#print axioms ProofFile.Honest.K2.Law.width_k1_read_at_join
