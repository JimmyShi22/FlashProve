-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsOfPts.lean: kind K5: THE SLOTS THAT leftP LOOKS UNDER (EndsInP,
Claims/LeftBack.lean) LIE IN THE STRETCHES OF WHICH THE RECORD PtsSlots (Claims/SlotsIn.lean) SPEAKS: so one
record on the slots serves both "the runs return at the earlier ledger what they return at the later"
and "every slot that a form names meets Ps".
NOT SAID: that leftP looks only under slots that a form NAMES. It does not: the second end value of each
member of the sumcheck "atIndex" is looked under, and no form written in Att/RunsP.lean names it.

Main names:
  endsIn_of_pts: PointsAre g zk h L p, PtsSlots Ps g p and two sizes give EndsInP Ps g zk h. General in Ps.
  om_sizes: the two sizes (h.om and h.om'' have g.NP members) from Said (Att/K5SaidAll.lean) and GeoFits
    (Att/K05PtsSlots.lean).
  ptsFrom_back': ptsFrom's return at the later ledger is its return at the earlier, under ShownBack and
    PtsSlots at what it returned.
IS IT EMPTY HERE? As Claims/LeftBack.lean. PtsSlots is shown of nothing here. In ptsFrom_back' the record
  speaks of p, WHICH THE LATER RETURN GIVES: whoever pays it must pay it at that p.
Spent of PtsSlots: scores' second clause, scE, vpm, vpd, scF, scd, scH. The other fields are not used.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.LeftBack
import Johnson.Desc.First.Att.K05PtsSlots
import Johnson.Desc.First.Att.K05Row
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts)
open VerifiableInference.Desc.Part

theorem mem_zip_left {α β : Type} : ∀ {as : List α} {bs : List β}, as.length ≤ bs.length →
    ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs
  | [], _, _, _, h => nomatch h
  | _ :: _, [], hle, _, _ => absurd hle (by simp)
  | x :: as, y :: bs, hle, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨y, by rw [List.zip_cons_cons]; exact List.mem_cons_self⟩
    · obtain ⟨b, hb⟩ := mem_zip_left (Nat.le_of_succ_le_succ hle) a h
      exact ⟨b, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb⟩

variable {Ps : ℕ → Prop} {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}

/-- **The slots that leftP looks under lie in the stretches of which PtsSlots speaks.** -/
theorem endsIn_of_pts (H : PointsAre g zk h L p) (hP : PtsSlots Ps g p) (h1 : h.om.size = g.NP)
    (h2 : h.om''.size = g.NP) : EndsInP Ps g zk h := by
  refine ⟨fun x hx i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · have hle : (g.scores.toArray.zip h.scores).toList.length ≤ L.scores.toList.length := by
      have a1 := H.nH
      have a2 := H.nL
      simp only [Array.length_toList, Array.size_zip, List.size_toArray]
      omega
    obtain ⟨r, hr⟩ := mem_zip_left hle x hx
    have hr' : (x, r) ∈ ((g.scores.toArray.zip h.scores).zip L.scores).toList := by
      rw [Array.toList_zip]; exact hr
    obtain ⟨k, hk, ⟨hsc, _, _, hpw⟩, _⟩ := P.forall2_left H.units.flip (x, r) hr'
    have := (hP.scores k hk).2 i (by rw [hpw, P.pieces_size, ← P.weights_size x.1 (zk.getD x.1.call #[])]; exact hi)
    rw [hsc] at this
    exact this
  · have := hP.scE i hi; rw [H.scE] at this; exact this
  · have := hP.vpm i hi; rw [H.vpm] at this; exact this
  · have := hP.vpd i hi; rw [H.vpd] at this; exact this
  · have := hP.scF i (by rw [← h1]; exact hi); rw [H.scF] at this; exact this
  · have := hP.scd i hi; rw [H.scd] at this; exact this
  · have := hP.scH i (by rw [← h2]; exact hi); rw [H.scH] at this; exact this

/-- The two sizes, of what a hearing has said. -/
theorem om_sizes {x : Params.AttentionRounds} {G : Fork} {Ls : P.Lists} (hs : P.Said x h G Ls)
    (gf : P.GeoFits g x) : h.om.size = g.NP ∧ h.om''.size = g.NP := by
  refine ⟨?_, ?_⟩
  · rw [hs.om, List.size_toArray, MaskedSum.powersFrom_len, gf.NP]
  · rw [hs.om'', List.size_toArray, MaskedSum.powersFrom_len, gf.NP]

/-- **One record for both.** -/
theorem ptsFrom_back' {F G' : Fork} (B : ShownBack Ps F G') (e : P.ptsFrom g zk h G' = some p)
    (hP : PtsSlots Ps g p) (h1 : h.om.size = g.NP) (h2 : h.om''.size = g.NP) :
    P.ptsFrom g zk h F = some p := by
  have e' := e
  unfold P.ptsFrom at e'
  obtain ⟨L, _, hq⟩ := Option.bind_eq_some_iff.1 e'
  exact ptsFrom_back B (endsIn_of_pts (points_are hq) hP h1 h2) e

end K5Law

#print axioms K5Law.endsIn_of_pts
#print axioms K5Law.om_sizes
#print axioms K5Law.ptsFrom_back'
