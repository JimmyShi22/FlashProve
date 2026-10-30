-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveToBatch.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): FROM THE TEST `k5Reads` ON WHAT THE OWN ROUNDS OF AN
ATTENTION SEGMENT DREW (Johnson/Desc/K5/Honest/Law/ReadRounds.lean) TO THE STATE IN FRONT OF THE
SEGMENT's BATCHING: there the list of tables holds, on each of the matrices NAs and NAs + 3, a
table, laid in vector number 2, no entry of whose weights below its own length is the word 0
(`Live2`). On the verifier's chain alone: no honest side, no promise in it.

The five sub-protocols, by their numbers in the first chain's flat list, l := 2 g + 1:
  14 l + 4  the segment's own rounds: its yes lays what it heard;
  14 l + 5  the sending of the reads with the quiet step that makes and closes the list;
  14 l + 6  the smallness test's draw;  14 l + 7  the sending of the digits;
  14 l + 8  the lookup on the digits: these three leave the list and its mark "closed".
Behind them stands the batching (the library's list of a segment's kinds,
Johnson/Desc/First/Driver/Chain.lean: `kindsBeforeBatching`).

The statement takes the five decisions' yes as five premises, each at its own rounds: whoever holds
a fold or a walk over these members unrolls it so. No state need be known to be reached: a yes of
the first says itself that an attention segment is open.

Main names:
  `lstF`: the reading (closed, list), which the lookup on the digits does not touch.
  `Live2`, `live2_read`: the end, and that it hangs on the library's `readTl` of that reading alone.
  `heard_of_k5`: a yes of the member at + 4: what stands behind.
  `live_behind_reads`: to the state behind + 5.
  `lst_leaves`: the three that leave the list: ONE CALL OF THE LIBRARY's `stretch_leaves`.
  `live_at_batch`: **the whole.**

How. THE LIBRARY HAS THE LAW ON THE THREE MEMBERS, GENERAL IN THE READING: `Keeps4` g (g reads none
of the four fields that the lookup on the digits lays) and `theStated_leaves_tl`
(Johnson/Desc/First/K8/LawWideK3.lean); `KeepsDraw` g, `hear_leaves_read` and `stretch_leaves`
(Johnson/Desc/First/Link/Law/PlannedToBatch.lean): every entry of the flat list from the smallness
test's draw to the last in front of the batching leaves `readTl` g. It is called at g := (closed,
list), where both premises hold by unfolding. `heard_of_k5` finds the block at 14 l + 4 as
`k5_member` does (Johnson/Desc/ProofFile/Honest/K5/Law/Member.lean, which stands over the proof
file's frame and so cannot be imported here): its end is one direction of the field `decides` of
that file's structure `DecidesAs`, opened by `k5_yes_is`. `Live2` says "is not the word 0"; whoever
counts on the weights wants "does not read 0": `Live2V`, Johnson/Desc/K5/Honest/Law/LiveValAt.lean.

Limits. The head is a hypothesis. `Live2` does not say that the list is closed. The other matrices
of the segment are not spoken of. A yes of the test is not shown here; that the five decisions' yes
and the test's yes hold together at any run is not shown here; how often the test says no is not
shown. hc (c holds what the rounds drew) is the caller's. That the batching stands next behind the
fifth: `batch_place` (Johnson/Desc/K5/Honest/Law/BatchPlace.lean), on the written list of places. At
the function `OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.DrawAt
import Johnson.Desc.K5.Honest.Law.ReadRounds
import Johnson.Desc.K5.Honest.Law.PublicAtHead
import Johnson.Desc.K5.Honest.Law.Returns
import Johnson.Desc.First.K8.HearMeans
import Johnson.IMR.K1Seat
import Johnson.Desc.First.Link.Law.PlannedToBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att (readsAtSO)
open VerifiableInference.Desc.First.Att.P (Geo Heard hear behind)
open P5J (AtMgA TS)

/-- The reading: the mark "closed" and the list of tables. -/
def lstF (tl : HTailF2) : Bool × Array HFun := (tl.funClosed, tl.funs)

/-- **On the matrices NAs and NAs + 3 the state's list holds a table in vector number 2 no entry of
whose weights, below the table's own length, is the word 0.** -/
def Live2 (g : Geo) (s : S) : Prop :=
  ∃ tl, s.tl? = some tl ∧
    (∃ Fn ∈ tl.funs.toList, Fn.mat = g.NAs ∧ Fn.len = g.T ∧ Fn.tree = 2 ∧
      ∀ c < Fn.len, isZeroE (Fn.phi.getD c zeroE) = false) ∧
    ∃ Fn ∈ tl.funs.toList, Fn.mat = g.NAs + 3 ∧ Fn.len = 2 ^ g.la ∧ Fn.tree = 2 ∧
      ∀ x < Fn.len, isZeroE (Fn.phi.getD x zeroE) = false

/-- It hangs on the reading alone. Conditional: e: the reading behind is the reading in front;
hL. -/
theorem live2_read {g : Geo} {s s' : S} (e : K8.readTl lstF s' = K8.readTl lstF s)
    (hL : Live2 g s) : Live2 g s' := by
  obtain ⟨tl, ht, h1, h2⟩ := hL
  unfold K8.readTl at e
  rw [ht] at e
  obtain ⟨tl', ht', ef⟩ := Option.map_eq_some_iff.1 e
  have ef2 : tl'.funs = tl.funs := (Prod.mk.inj ef).2
  refine ⟨tl', ht', ?_, ?_⟩
  · rw [ef2]
    exact h1
  · rw [ef2]
    exact h2

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **A yes of the member at 14 l + 4**: an attention segment stands open, the hearing has returned
on the decision's rounds, and the state behind holds what it heard. Conditional: the head; hg; ea;
f4: which member; d4: its yes. -/
theorem heard_of_k5 {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) {s4 s5 : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (d4 : b4.decide s4 rs gs = .ok s5) :
    ∃ att hd G, s4.here = .att att ∧ hear a.own (att.F, rs, 0) = some (hd, G, [], 0) ∧
      s5 = behind s4 att hd G := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h4, g', hg', e⟩ := Att.P.att_only O.pub O.blank
    (IM.subs_att h.scope h.reads O.pub O.blank hg)
  obtain rfl : g' = g := by omega
  obtain ⟨Lk, Eb, b', e1, e2, hat, hla⟩ := Att.P.k5_alone O h4 hg'
  have e3 := IM.flatIx_scope h.scope h.reads O (l := 2 * g' + 1) (by omega) 2
  have hfl : cF.blocksInOrder[14 * (2 * g' + 1) + 4]? = some Eb := by
    have hfl0 := IM.hear_at_flat e1 e2
    rw [e3, show 14 * (2 * g' + 1) + 2 + 2 = 14 * (2 * g' + 1) + 4 by omega] at hfl0
    exact hfl0
  obtain rfl : Eb = b4 := Option.some.inj (hfl.symm.trans f4)
  have hd' := ((IM.yes_alone hla (fun e => nomatch e) s4 s5 rs gs).1 d4).1
  obtain ⟨a', ea', eb⟩ := Att.P.k5AtN_is _ _ _ _ _ hat
  rw [O.W] at ea'
  obtain rfl : a' = a := Option.some.inj (ea'.symm.trans ea)
  subst eb
  exact k5_yes_is (Att.P.parO Bs.G₀.W (2 * g' + 1) a' _) hd'

/-- **To the state behind the quiet step.** Conditional: the head; hg; ea; f4, f5: which members;
d4, d5: their yes; hc: c holds what the rounds of the first drew; hk: the test. -/
theorem live_behind_reads {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5) {s4 s5 s6 : S} {rs4 rs5 : List Fmt.RoundView}
    {gs4 gs5 : List (List (ℕ × List UInt64))} (d4 : b4.decide s4 rs4 gs4 = .ok s5)
    (d5 : b5.decide s5 rs5 gs5 = .ok s6) (c : Chal) (hc : Reads c rs4)
    (hk : k5Reads a.own (Att.P.parCOf a).geo c = true) :
    Live2 (Att.P.parCOf a).geo s6 ∧ ∃ a6, s6.here = .att a6 := by
  obtain ⟨att, hd, G, e4, hh, rfl⟩ := heard_of_k5 h hg ea f4 d4
  have Pu := public_at_head h hg ea
  have hR : heardReads (Att.P.parCOf a).geo hd = true :=
    heardReads_of_plan ⟨a.S, a.own⟩ c hh hc Pu.sized Pu.planned hk
  obtain ⟨G₀, Xl, pd, reads, digits, b, M⟩ := member_at_head h hg
  have hA : G₀.W.A[Xl.g]? = some a := by
    rw [M.group, M.pubW]
    exact ea
  obtain rfl : b = b5 := Option.some.inj (M.flat.symm.trans f5)
  rw [M.is] at d5
  obtain ⟨m, h1, hm⟩ := seated_reads_inv Zp G₀ (2 * g + 1) Xl reads b.name M.kind hA d5
  obtain ⟨L', F', em, _, _, _⟩ := k1_leaves h1 (a₀ := { att with F := G, heard5 := some hd }) rfl
  have h5 : m.heard5? = some hd := by
    unfold S.heard5?
    rw [em]
  refine ⟨funs_live a hm h5 hR, ?_⟩
  obtain ⟨a0, _, _, _, t, _, _, _, _, _, _, _, _, rfl⟩ := (readsAtSO_iff a m s6).1 hm
  exact ⟨_, rfl⟩

/-- **The three members between the quiet step and the batching leave the reading (closed, list).**
The library's law, called. Conditional: the head; hg; j: one of the numbers + 6, + 7, + 8; fj. -/
theorem lst_leaves {g : ℕ} (hg : g < 12) {j : ℕ} (h1 : 14 * (2 * g + 1) + 6 ≤ j)
    (h2 : j < 14 * (2 * g + 1) + 9) {b : Block S ProofFile.Cl} (fj : cF.blocksInOrder[j]? = some b) :
    b.Leaves (K8.readTl lstF) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  exact LinkJoin.stretch_leaves h.scope h.reads O hx lstF (fun _ _ _ _ _ => rfl)
    (fun _ _ _ => rfl) j (by show 14 * (2 * g + 1) + 4 + 2 ≤ j; omega)
    (by show j < 14 * (2 * g + 1) + 4 + 2 + (2 + 1); omega) b fj

/-- **FROM THE TEST ON WHAT THE SEGMENT's OWN ROUNDS DREW TO THE STATE IN FRONT OF THE BATCHING.**
Conditional: the head; hg; ea; f4 … f8: which five members; d4 … d8: their yes, each at its own
rounds; hc: c holds what the rounds of the first drew; hk: the test. -/
theorem live_at_batch {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) (c : Chal) (hc : Reads c rs4)
    (hk : k5Reads a.own (Att.P.parCOf a).geo c = true) : Live2 (Att.P.parCOf a).geo s9 := by
  have L6 := (live_behind_reads h hg ea f4 f5 d4 d5 c hc hk).1
  have L7 := live2_read (lst_leaves h hg (by omega) (by omega) f6 _ _ _ _ d6) L6
  have L8 := live2_read (lst_leaves h hg (by omega) (by omega) f7 _ _ _ _ d7) L7
  exact live2_read (lst_leaves h hg (by omega) (by omega) f8 _ _ _ _ d8) L8

end

end H2K5.Honest

#print axioms H2K5.Honest.live2_read
#print axioms H2K5.Honest.heard_of_k5
#print axioms H2K5.Honest.live_behind_reads
#print axioms H2K5.Honest.lst_leaves
#print axioms H2K5.Honest.live_at_batch
