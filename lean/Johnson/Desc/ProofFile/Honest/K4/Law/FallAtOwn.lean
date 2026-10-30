-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FallAtOwn.lean: CONDITIONAL. WHERE THE FIRST FALL OF THE
LAYERS' OWN ROUNDS (kind K4; `k4Fall`, Honest/K4/Part.lean) IS COUNTED AT A MEMBER, THAT MEMBER IS
K4's OWN; AND THE FALL's SENTENCE THERE, AT STRINGS OF HASH BLOCKS.

What is here. A LAW ON THE DESCRIPTION's FIRST CHAIN: no prover, no run, no coin and no input is in
it. The frame counts a fall at a member b where the fall's place is b's own or that of a member
without a round right behind b (`repsAt`, Honest/Law/CoverReps.lean). Statements and proofs.

  `k4_counted_at_own`: **a fall at K4's place of group gk, counted at a member b: b is the lot's
      own sub-protocol, seated alone at that place**, at parameters x with the ground's layers and
      its plan of that group. By the library's `IM.k4_of` (Johnson/IMR/K4Seat.lean: which member
      stands at that place), the places being distinct, and K4's member having a round: so it is no
      member "without a round right behind" another. That b has a round is not asked. THAT THE FALL
      IS COUNTED THERE is not said: the frame's `mem_repsAt` has it for a fall of the list.
  `k4_fallDebt_counted`: **the first fall's sentence (`FallDebt`, Honest/Law/CoverJoin.lean) at
      that member**, at the kit `Run.ckP .two`, at data that fit the member's declared rounds
      (`KindFits`), AT EVERY LIST OF FALLS fs, EVERY ft, ALL MEMBERS t' BEHIND, EVERY SENTENCE P,
      AND EVERY q FROM THE BOUND ON (`k4ZeroBound`, Law/FallCount.lean: kapSl 128 ^ 3 * 1 / p ^ 3).
      The two fields of the fall's public data that it does not read are letters. At K4's own member
      the data have the round at which the test reads (`k4_coin_of_kindFits`, Law/CoinRow.lean), so
      the arm `k4_zeroCount_short` is idle there.

Not shown here. THE HYPOTHESES ARE PAID NOWHERE HERE: hS · hR: the public files lie in the goals'
scope and are read · O: the description is opened, with the format's second hash function itself in
the place that its maker keeps for it · hnd: the places of the chain's members are distinct (the
frame's `places_nodup`, Honest/Law/Cuts.lean, has it from the description's own test on its places)
· hall: b is a member of the chain · hk: the group's number is below 12 · hpl: the fall stands at
K4's place of that group · hh: the ground has the plan hp at that group · hg: the fall is counted at
b · hfit · hq. THE FULL SIZE ALONE (the scope). THE BOUND IS NOT THE FALL's STATED SHARE: it is the
library's factor kapSl 128 ^ 3 times it. The library's lemma's own limit holds: the uniform law on
one round's messages is named, not derived. NO NUMBER IS EVALUATED. MET FOR NOTHING at q of 1 or
more and at P := fun _ _ => False. All limits of Law/Falls.lean and Law/FallCount.lean hold here
too. No example of the hypotheses together has been through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FallCount
import Johnson.Desc.ProofFile.Honest.K4.Law.CoinRow
import Johnson.Desc.ProofFile.Honest.Law.CoverReps
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open scoped ENNReal
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- CONDITIONAL: on all eight hypotheses. **WHERE A FALL AT K4's PLACE IS COUNTED AT A MEMBER, THAT
MEMBER IS K4's OWN.** -/
theorem k4_counted_at_own (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂)
    (hnd : (c.blocksInOrder.map (·.place)).Nodup) {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl}
    (hall : c.blocksInOrder = A ++ b :: t) {fs : List (Fall S)} {g : Fall S}
    (hg : g ∈ repsAt c.blocksInOrder fs b) {gk : ℕ} (hk : gk < 12) (hpl : g.place = IM.k4Place gk) :
    ∃ x : Bool × OnBytes.Desc.First.K4.Par,
      IM.LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) b.name (IM.k4Place gk) ∧ x.2.g = gk ∧
        x.2.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[gk]? = some x.2.hp := by
  have hm : g.place ∈ groupPlaces c.blocksInOrder b.place := of_decide_eq_true (List.mem_filter.1 hg).2
  rw [groupPlaces_at hnd hall] at hm
  obtain ⟨d, hd, hdp⟩ := List.mem_map.1 hm
  obtain ⟨Lk, b₀, x, e1, e2, -, hla, -, eg, eP, ehp, -, -⟩ := IM.k4_of hS hR O gk hk
  have hb₀ : b₀ ∈ c.blocksInOrder := List.mem_of_getElem? (IM.hear_at_flat e1 e2)
  unfold groupOf at hd
  have hd' : d ∈ c.blocksInOrder := by
    rw [hall]
    rcases List.mem_cons.1 hd with e | h
    · rw [e]
      exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ (List.mem_cons_of_mem _
        ((List.takeWhile_prefix (fun d : Block S ProofFile.Cl => d.rounds.isEmpty) (l := t)).subset h))
  have e0 : d = b₀ :=
    List.inj_on_of_nodup_map hnd hd' hb₀ (hdp.trans (hpl.trans (IM.alone_place hla).symm))
  rcases List.mem_cons.1 hd with e | h
  · rw [← e, e0]
    exact ⟨x, hla, eg, eP, ehp⟩
  · exfalso
    have hr : d.rounds = [] := List.isEmpty_iff.1
      (List.mem_takeWhile_imp (p := fun d : Block S ProofFile.Cl => d.rounds.isEmpty) h)
    rw [e0, IM.alone_rounds hla] at hr
    have hr' : ((OnBytes.Desc.First.K4.rounds x.2.P x.2.hp x.2.g).map
        OnBytes.Desc.First.K4.entryOf).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) = [] := hr
    have h0 := List.map_eq_nil_iff.1 (List.map_eq_nil_iff.1 hr')
    obtain ⟨d', hd'', -⟩ := k4CoinRound_row (⟨x.2.P, x.2.hp, x.2.g, 0, 0, 0, 0⟩ : K4Pub)
    have hd3 : (OnBytes.Desc.First.K4.rounds x.2.P x.2.hp x.2.g)[k4CoinRound
        (⟨x.2.P, x.2.hp, x.2.g, 0, 0, 0, 0⟩ : K4Pub)]? = some d' := hd''
    rw [h0] at hd3
    cases hd3

/-- CONDITIONAL: on all ten hypotheses. **THE FIRST FALL's SENTENCE WHERE THE FALL IS COUNTED**,
at strings of hash blocks. a, s: the two fields that the fall does not read. -/
theorem k4_fallDebt_counted (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂)
    (hnd : (c.blocksInOrder.map (·.place)).Nodup) {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl}
    (hall : c.blocksInOrder = A ++ b :: t) {fs : List (Fall S)} {gk : ℕ}
    {hp : OnBytes.Model.Layer.HPlan2} (hk : gk < 12) (hh : Bs.G₀.W.G[gk]? = some hp) (a s : ℕ)
    (hg : (k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, a, s⟩ : Fall S) ∈ repsAt c.blocksInOrder fs b)
    (dsb : List RDT) (hfit : List.Forall₂ KindFits dsb b.rounds) (ft : ℕ)
    (t' : List (Block S ProofFile.Cl)) (q : ℝ≥0∞)
    (hq : k4ZeroBound ≤ q)
    (Pr : List Fmt.Drawn → S → Prop) :
    FallDebt (_root_.Run.ckP .two) (k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, a, s⟩) ft b t' dsb []
      Pr q := by
  obtain ⟨x, hla, eg, eP, ehp⟩ := k4_counted_at_own hS hR O hnd hall hg hk rfl
  have ehp' : x.2.hp = hp := Option.some.inj (ehp.symm.trans hh)
  have hr : b.rounds = (OnBytes.Desc.First.K4.entries Bs.G₀.W.layers hp gk).map
      (fun e => ({ entry := e } : Fmt.DeclaredRound)) := by
    rw [IM.alone_rounds hla, ← eP, ← ehp', ← eg]
    rfl
  have hK := hfit
  rw [hr] at hK
  obtain ⟨hent, hkind⟩ := ent_of_kindFits dsb _ hK
  exact k4_coinZero_debt_fits ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, a, s⟩ ft b t' dsb hfit
    (fun d hd => k4_coin_h1 ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, a, s⟩ dsb hent hkind hd) q hq Pr

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_counted_at_own
#print axioms ProofFile.Honest.K4.k4_fallDebt_counted
