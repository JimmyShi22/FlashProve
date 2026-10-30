-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveVal.lean: CONDITIONAL: THE LAWS OF
Johnson/Desc/K5/Honest/Law/LiveToBatch.lean ONCE MORE, AT VALUES: from the test on what the own
rounds of an attention segment drew to the state in front of the segment's batching: there the two
tables' weights do not READ 0 (`Live2V`, Johnson/Desc/K5/Honest/Law/LiveValAt.lean, which says why
the value is wanted).

Main names:
  `live2_of_V`: `Live2V` gives the elder end `Live2`.
  `live2V_read`: it hangs on the library's reading `readTl` of (closed, list) alone.
  `live_behind_readsV`, `live_at_batchV`: **to the state in front of the batching.**

How. The texts are the elder file's, the end exchanged. The three members between the quiet step and
the batching leave the reading (closed, list): the elder file's `lst_leaves`, one call of the
library's `stretch_leaves` (Johnson/Desc/First/Link/Law/PlannedToBatch.lean).

Limits. As the elder file's, and as LiveValAt.lean's: the matrix is the plan's, not the state's.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.LiveToBatch
import Johnson.Desc.K5.Honest.Law.LiveValAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.Road (pt)
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts hear behind)
open K5Law (Table layFrom laidBy)
open P5J (AtMgA TS)

/-- It gives the elder end. -/
theorem live2_of_V {g : Geo} {mats : Array TMat} {s : S} (h : Live2V g mats s) : Live2 g s := by
  obtain ⟨tl, ht, ⟨F1, m1, a1, a2, a3, _, _, a6⟩, F2, m2, b1, b2, b3, _, _, b6⟩ := h
  exact ⟨tl, ht, ⟨F1, m1, a1, a2, a3, fun c hc => notZero_of_val Reading.gl (a6 c hc)⟩,
    F2, m2, b1, b2, b3, fun c hc => notZero_of_val Reading.gl (b6 c hc)⟩

/-- It hangs on the reading alone. Conditional: e: the reading behind is the reading in front;
hL. -/
theorem live2V_read {g : Geo} {mats : Array TMat} {s s' : S}
    (e : K8.readTl lstF s' = K8.readTl lstF s) (hL : Live2V g mats s) : Live2V g mats s' := by
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

/-- **To the state behind the quiet step, at values.** Conditional: as `live_behind_reads`. -/
theorem live_behind_readsV {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5) {s4 s5 s6 : S} {rs4 rs5 : List Fmt.RoundView}
    {gs4 gs5 : List (List (ℕ × List UInt64))} (d4 : b4.decide s4 rs4 gs4 = .ok s5)
    (d5 : b5.decide s5 rs5 gs5 = .ok s6) (c : Chal) (hc : Reads c rs4)
    (hk : k5Reads a.own (Att.P.parCOf a).geo c = true) :
    Live2V (Att.P.parCOf a).geo a.mats s6 ∧ ∃ a6, s6.here = .att a6 := by
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
  refine ⟨funs_liveV a hm h5 hR, ?_⟩
  obtain ⟨a0, _, _, _, t, _, _, _, _, _, _, _, _, rfl⟩ := (readsAtSO_iff a m s6).1 hm
  exact ⟨_, rfl⟩

/-- **FROM THE TEST ON WHAT THE SEGMENT's OWN ROUNDS DREW TO THE STATE IN FRONT OF THE BATCHING, AT
VALUES.** Conditional: as `live_at_batch`. -/
theorem live_at_batchV {g : ℕ} (hg : g < 12) {a : Attention.Plan}
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
    (hk : k5Reads a.own (Att.P.parCOf a).geo c = true) :
    Live2V (Att.P.parCOf a).geo a.mats s9 := by
  have L6 := (live_behind_readsV h hg ea f4 f5 d4 d5 c hc hk).1
  have L7 := live2V_read (lst_leaves h hg (by omega) (by omega) f6 _ _ _ _ d6) L6
  have L8 := live2V_read (lst_leaves h hg (by omega) (by omega) f7 _ _ _ _ d7) L7
  exact live2V_read (lst_leaves h hg (by omega) (by omega) f8 _ _ _ _ d8) L8

end

end H2K5.Honest

#print axioms H2K5.Honest.live2_of_V
#print axioms H2K5.Honest.live2V_read
#print axioms H2K5.Honest.live_behind_readsV
#print axioms H2K5.Honest.live_at_batchV
