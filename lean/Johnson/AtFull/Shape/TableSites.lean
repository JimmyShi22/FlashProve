-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableSites.lean: THE TABLE MEETS THE FRAMES: ALL FIFTY LOOKUPS. Under the head
P5J.AtMgA. Nothing is evaluated.

  **`site_found`**: under the head the table's search (Tab.siteAt) finds a site at each of the
    fifty addresses, and what it finds is a site of that link and flag (by site_made_at,
    SitesAtHead.lean).
  `tab_calls` (l < 24: at 14 l + 3), `tab_calls_head` (340), `tab_look_digits` (l < 24: at 14 l +
    8), `tab_look_head` (345; the table's test on values there is headVals): Both
    (TableFrames.lean): over look_calls_frame_free (LookFree.lean), look_digits_frame_free
    (DigitsFree.lean) and look_head_frame_vals (HeadDigitsFree.lean), each of which holds at every
    site of its sort: so at the one that the search finds.

Limits. As the frames': two premises of the rule for acceptance; no state is shown at which a step
returns. lookSites has a silent default (no spots: the empty list); under the head site_made_at says
that a site is made at each address. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. At the format's second hash
function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableFramesV
import Johnson.AtFull.Shape.DigitsFree
import Johnson.AtFull.Shape.HeadDigitsFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest.K3 (Site lookSites)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)
open ProofFile.Honest (Carries Returns)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- Under the head the table's search finds a site at each address, and what it finds is a site of
that link and flag. -/
theorem site_found (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) :
    ∃ s, Tab.siteAt Zp l d = some s ∧ s ∈ lookSites Zp ∧ s.link = l ∧ s.digits = d := by
  obtain ⟨s₀, hm, e1, e2⟩ := site_made_at h l hl d
  unfold Tab.siteAt
  cases hf : (lookSites Zp).find? fun s => s.link == l && s.digits == d with
  | none =>
    have := List.find?_eq_none.1 hf s₀ hm
    simp [e1, e2] at this
  | some s =>
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨s, rfl, List.mem_of_find?_eq_some hf, hp.1, hp.2⟩

theorem tab_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (l : Nat)
    (hl : l < 24) : Both cF Zp G (14 * l + 3) := fun ft => by
  obtain ⟨s, hs, hm, rfl, hd⟩ := site_found h l (by omega) false
  have hc : Tab.cells Zp G (14 * s.link + 3) = Tab.lookCalls Zp s.link :=
    cells_link Zp G s.link 2 hl (by omega) rfl
  unfold Tab.lookCalls at hc
  rw [hs] at hc
  have hn : lookNo s.link false = 14 * s.link + 3 := by
    unfold lookNo
    rw [k3_no, if_neg (by omega)]
    rfl
  have := look_calls_frame_free h s hm hd ft _ (Tab.vals Zp G) (hn ▸ cell_g hc)
  rwa [hn] at this

theorem tab_calls_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 340 := fun ft => by
  obtain ⟨s, hs, hm, hl, hd⟩ := site_found h 24 (by omega) false
  have hc : Tab.cells Zp G 340 = Tab.lookCalls Zp 24 := cells_head Zp G 3 (by omega) rfl
  unfold Tab.lookCalls at hc
  rw [hs] at hc
  have hn : lookNo s.link false = 340 := by
    rw [hl]
    rfl
  have := look_calls_frame_free h s hm hd ft _ (Tab.vals Zp G) (hn ▸ cell_g hc)
  rwa [hn] at this

theorem tab_look_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (l : Nat)
    (hl : l < 24) : Both cF Zp G (14 * l + 8) := fun ft => by
  obtain ⟨s, hs, hm, rfl, hd⟩ := site_found h l (by omega) true
  obtain ⟨u, c, e1, hf⟩ := look_digits_frame_free h s hm hd hl
  have hc : Tab.cells Zp G (14 * s.link + 8) = Tab.lookDigits Zp s.link :=
    cells_link Zp G s.link 7 hl (by omega) rfl
  unfold Tab.lookDigits at hc
  rw [hs, e1] at hc
  have hn : lookNo s.link true = 14 * s.link + 8 := by
    unfold lookNo
    rw [k3_no, if_neg (by omega)]
    rfl
  have := hf ft _ (Tab.vals Zp G) (hn ▸ cell_g hc)
  rwa [hn] at this

theorem tab_look_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 345 := fun ft => by
  obtain ⟨s, hs, hm, hl, hd⟩ := site_found h 24 (by omega) true
  have hc : Tab.cells Zp G 345 = Tab.lookHead Zp := cells_head Zp G 8 (by omega) rfl
  unfold Tab.lookHead at hc
  rw [hs] at hc
  obtain ⟨h1, h2⟩ := (look_head_frame_vals h s hm hl hd).2 ft _ (Tab.vals Zp G) (cell_g hc)
  refine ⟨h1, h2 fun st rs cols hv => ?_⟩
  rw [cell_v hc] at hv
  exact hv

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tab_look_digits
#print axioms Johnson.AtFull.Shape.tab_look_head
#print axioms Johnson.AtFull.Shape.site_found
#print axioms Johnson.AtFull.Shape.tab_calls
#print axioms Johnson.AtFull.Shape.tab_calls_head
