-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtLot.lean: CONDITIONAL: on hS, hR, L, hG and a
premise on the book. `Good` (Honest/Side.lean) at every row of K4's lot with its simulators
(`k4SLot`, Law/SLot.lean), at the member of the description's first chain that stands at the row's
place, at whatever falls, at every pre, at A := B := THE SENTENCE THAT NEVER HOLDS (False). hS, hR,
L: the public files are in scope, they are read, and the library's value is laid at them (`LaidAt`):
T3's own premises (`online_exact_of_owed`). hG: the ground that is made of the public part, which
asks nothing beyond L. Statements and proofs.

  `entries_not_seed`   no entry of the verifier's table of K4's rounds is named "SEND seed".
  `k4_block_of_lot`   at a row of the lot a member of the first chain stands at the row's place,
      with the entries of the verifier's table at the row's public data, and it passes the
      description's test on its shape.
  `k4_member_of_lot`   every member at that place is that one.
  `k4_row_seated`   each row of the lot is seated, at every list of falls.
  `k4_good_lot`   **`Good` at a row of the lot.**

OVER WHICH ROW. Over K4's row as laws.14's Honest/K4/Part.lean has it: no part of it stops; at a zero
challenge of the second token sumcheck the prover plays on and K4's own block refuses at its end
(`k4Fall`). The lot has twelve rows under the library's head: `k4SLot_toHLot`
(Law/SLot.lean) with `k4HLot_twelve` (Law/LotTwelve.lean); `k4HLot_side_at_kind`
(Law/LotSideAtKind.lean) has a half at every member of the kind K4.

Limits. plays AND acc OF THE TERM HOLD FOR NOTHING (A := False): `Good` is asked at some A and B by
`hand_of_house` (Honest/Thread/RowsMore.lean), the rule reads fits, exact and fresh alone, and
Honest/Law/Rule/Mute.lean closes plays and acc so. THAT IS Owed's FIELD good ALONE: Owed's fields runs
and owed want what the threads give, and K4 owes its plays at its twelve borders there.
fresh IS AN IDENTITY THAT HOLDS OF ANY PART OF WHICH NOTHING IS SPENT: TRUE AND EMPTY. Freshness of
the runs that K4 spends is the debt of their owners, the sender of each segment's mask row and the
sender of the index-mask message, AND FOR THE SPENDER 11 · 9, WHOSE JOB READS WHAT 9 · 7 HAS SENT, IT
IS OWED TOGETHER WITH THE BLOCK THAT 9 · 7 HAS SPENT (the owner's `fresh` at p := that part holds that
block in `Bk.knownBy`).
exact: one equation of two laws at one member by itself, AT EVERY STATE, TRUE CLAIM OR FALSE: the
masked sumcheck's law reads no claim. On and bud are True: K4's rounds state no root, so no position
is read, and `OnDebts` and `BudDebts` at these rows are trivial.
WHAT A CALLER STILL OWES, FROM Law/ExactFresh/Whole.lean's HEAD: the condition on a job that reads
what has been seen · at the merge the two runs are of two messages and are sampled as a product in
the equation: THAT THEY ARE SO WHERE THEY ARE SPENT IS NOT SAID · that the book lends these runs and
that no coin stands in two runs · `exact` at the parts that carry these coins later (K10 at ‹l›:11
and the next switch) · cells, weights and look are free letters and the masked sumcheck's law holds
AT EVERY JOB, RIGHT OR WRONG: a row that sends its mask entries over zeros meets this law as well.
No filling is named here: that a filling lays these rows is another statement, at the halves.
READ, NOT CALLED: beta, the factor of the end values' mask entries, is other than 0 at every typed
challenge under scope, live and `LaidAt`, by `due_atFiles` (E2E/BridgePaidAtFiles.lean:107) with
`nonZero_atFiles` (E2E/BridgeNonZero.lean:139): so `drawsFit` in `exact` excludes no challenge that
the typed verifier's randomness can yield; the step from the chain's `Draws.due` to the member's own
list is named by no law. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SLot
import Johnson.Desc.ProofFile.Honest.K4.Law.LotPlace
import Johnson.Desc.ProofFile.Honest.K4.Law.LotOnce
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtLaid
import Johnson.IMR.K4Seat
import Johnson.P5J.LaidOpens
import Johnson.IMR.PlacesScope
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatIx
import Johnson.IMR.BorderW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Block)
open P5J (TS LaidAt)
open ProofFile.Honest.Small (noneSpent)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {W₀ Rc Tr X' : Type}

/-- No entry of the verifier's table of K4's rounds is named "SEND seed". -/
theorem entries_not_seed (Q : K4Pub) :
    ∀ e ∈ OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g, e.name ≠ "SEND seed" := by
  intro e he
  unfold OnBytes.Desc.First.K4.entries at he
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
  show d.name.name ≠ "SEND seed"
  cases d.name <;> decide

/-- CONDITIONAL: on hS, hR, L and hG. **At a row of the lot a member of the first chain stands at the
row's place, with the entries of the verifier's table at the row's public data; it passes the
description's test on its shape.** -/
theorem k4_block_of_lot (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {x : Bool × Par}
    (hx : x ∈ ProofFile.k4From Zp G₀ G₀.built.toList 0 none) {Q : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Q) :
    ∃ b ∈ cF.blocksInOrder, b.place = k4Place Q ∧
      b.rounds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g ∧ b.shaped = true := by
  obtain ⟨Bs, base, O⟩ := L.opened
  obtain ⟨hg, el, ep, -⟩ := IM.k4_seated_scope hS hR L.pub hG hx
  obtain ⟨Lk, b, x', e1, e2, hx', hla, el', -, -, -, -, -⟩ := IM.k4_of hS hR O x.2.g hg
  have eG : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  rw [eG] at hx'
  have ex : x' = x := List.inj_on_of_nodup_map
    (k4From_links_once Zp G₀ G₀.built.toList 0 none) hx' hx (by
      show x'.2.link = x.2.link
      rw [el', el])
  rw [ex] at hla
  have hp : b.place = k4Place Q := by
    rw [IM.alone_place hla, k4PubOf_place hQ]
    show IM.k4Place x.2.g = (⟨1, some x.2.link, x.2.piece, .K4⟩ : Place)
    rw [el, ep]
  have hQ' : Q.P = x.2.P ∧ Q.hp = x.2.hp ∧ Q.g = x.2.g := by
    unfold k4PubOf at hQ
    obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 hQ
    exact ⟨rfl, rfl, rfl⟩
  exact ⟨b, List.mem_of_getElem? (IM.hear_at_flat e1 e2), hp, laid_entries_pub hla hQ',
    laid_shaped hla⟩

/-- CONDITIONAL: on hS, hR, L and hG. **Every member of the first chain at the place of a row of the
lot has the entries of the verifier's table at the row's public data, and passes the test on its
shape.** -/
theorem k4_member_of_lot (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {x : Bool × Par}
    (hx : x ∈ ProofFile.k4From Zp G₀ G₀.built.toList 0 none) {Q : K4Pub} (hQ : k4PubOf Zp x.2 = some Q)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hp : b.place = k4Place Q) :
    b.rounds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g ∧ b.shaped = true := by
  obtain ⟨Bs, base, O⟩ := L.opened
  have hn : (cF.blocksInOrder.map (·.place)).Nodup := by
    rw [IM.places_scope hS hR O]
    exact IM.places_nodup
  obtain ⟨b', hm, hp', he, hs⟩ := k4_block_of_lot hS hR L hG hx hQ
  obtain rfl : b = b' := List.inj_on_of_nodup_map hn hb hm (hp.trans hp'.symm)
  exact ⟨he, hs⟩

/-- CONDITIONAL: on hS, hR, L and hG. **Each row of the lot is seated**, at every list of falls: the
law below does not speak of nothing. -/
theorem k4_row_seated (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    {row : Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hr : row ∈ (k4SLot cells weights look).rows Zp G₀) (fs : List (Fall TS)) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst,
      Side.seated cF.blocksInOrder row.place row.row fs = some σ := by
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
  obtain ⟨b, hm, hp, -, -⟩ := k4_block_of_lot hS hR L hG hx hQ
  have hs : (cF.blocksInOrder.find? fun c => c.place == k4Place Q).isSome = true :=
    List.find?_isSome.2 ⟨b, hm, beq_iff_eq.2 hp⟩
  refine Option.isSome_iff_exists.1 ?_
  show ((cF.blocksInOrder.find? fun c => c.place == k4Place Q).map _).isSome = true
  rw [Option.isSome_map]
  exact hs

/-- CONDITIONAL: on hS, hR, L, hG and hB. **`Good` AT A ROW OF K4's LOT WITH ITS SIMULATORS**, at the
side that `Side.seated` makes of the first chain at whatever falls, at every pre, at A := B := False.
hB: no entry spends a coin of a member with no round "SEND seed". -/
theorem k4_good_lot (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    {row : Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hr : row ∈ (k4SLot cells weights look).rows Zp G₀) {fs : List (Fall TS)}
    {σ : Side TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X' ProofFile.Inst}
    (hσ : Side.seated cF.blocksInOrder row.place row.row fs = some σ)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) ProofFile.Inst) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat)
    (hB : ∀ b ∈ cF.blocksInOrder, (∀ d ∈ b.rounds, d.entry.name ≠ "SEND seed") → ∀ j,
      noneSpent Bk ⟨b.place, j⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) row.On
      row.bud := by
  obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
  have hσ' : Side.seated cF.blocksInOrder (k4Place Q)
      (k4Sided Q cells weights k4Tokens (look Zp G₀ Q)) fs = some σ := hσ
  have hm := seated_mem hσ'
  have hp := (seated_is hσ').2
  obtain ⟨he, hs⟩ := k4_member_of_lot hS hR L hG hx hQ hm hp
  exact k4_good_seated pre φ σ Bk ord chain firstTree Q cells weights k4Tokens (look Zp G₀ Q) hσ'
    (block_count Q _ he) (oracles_of_shaped σ.block hs (block_roots Q _ he)).1
    (block_stated_shaped Q _ he hs) (fun u _ =>
      hB _ hm (fun d hd => entries_not_seed Q _ (he ▸ List.mem_map_of_mem hd)) _)

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.entries_not_seed
#print axioms ProofFile.Honest.K4.ExactFresh.k4_block_of_lot
#print axioms ProofFile.Honest.K4.ExactFresh.k4_member_of_lot
#print axioms ProofFile.Honest.K4.ExactFresh.k4_row_seated
#print axioms ProofFile.Honest.K4.ExactFresh.k4_good_lot
