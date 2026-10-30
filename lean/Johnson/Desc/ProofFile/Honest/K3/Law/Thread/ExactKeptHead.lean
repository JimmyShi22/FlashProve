-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExactKeptHead.lean: the kind "lookup" (K3): under the
library's hypothesis at the full size, `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): there are sites; at
every site a side is seated over the row that passes its tables on (`rowPairsKeep`,
Honest/K3/Law/Keep/SideKeep.lean); and `ExactMember` (Honest/Small/Field.lean) holds at all its
members. Theorems; no definition.

Never to be retold as "the row that passes its tables on is simulated".

What is shown, each conditional on `P5J.AtMgA`.
  `seated_head`: at every site a side is seated at the chain's flat list, over whatever row: earned
    by this folder's laws on coverage (`site_in_written`, `places_head`,
    Honest/K3/Law/Thread/CoverageAtHead.lean): a sub-protocol of the chain stands at the site's
    place.
  `rowStated_keep_head`: `RowStated` at the seated side, without `k3Fits`: the description's return
    by the hypothesis; the lot's sub-protocol by `lot_of_site`; its plan's test by `IM.plan_flat`
    (Johnson/IMR/PlanAt.lean); that the face passes its own test by `face_ok_site`
    (Johnson/AtFull/Shape/FaceAtSites.lean).
  `k3_exact_kept_head`: **the sites are not none; at every site a side is seated; `ExactMember`
    holds at all its members**, at every On' and bud.
  `k3_exact_kept_head_fast`: the same at the letters `fastFillKeep row wit`, row and wit free:
    without hK.

Hypotheses that remain. h: `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`. Conditional on the head
`P5J.AtMgA`. That it holds at the goals' two named sets of public files is a sealed theorem
(`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own limits; this file
does not call it: AtFullSide/Honest/K3/KeptAtNamed.lean [not in this library] does. hK: the jobs are
shaped as the stages' calls, at every site. The lens: hgs and hsg.

Imported: this folder's files named above, with ExactKeptFits.lean; and
Johnson/AtFull/Shape/FaceAtSites.lean.

Limits. Under the hypothesis, at letters: at no public part that is written out. The side is seated
over this folder's own definition: that a filling of the honest side's frame lays this side is typed
by nobody: "`exact` at the filling" is not had. Of `Good`'s other fields nothing. At jobs right or
wrong: nothing on what is sent. In `k3_exact_kept_head_fast` row, each site's table, stays a free
function: wherever these letters are counted as a filling, row is to be a named, closed, public
term: that is not laid in here. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.ExactKeptFits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CoverageAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberAtSite
import Johnson.AtFull.Shape.FaceAtSites
import Johnson.IMR.PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E)
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.Small (ExactMember)
open Johnson.AtFull.Shape (face_ok_site)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {V W X Pb : Type}

/-- Conditional on `P5J.AtMgA` and the site: a side is seated there, over whatever row. -/
theorem seated_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (row : List (Part V W X × Sim Pb)) (fs : List (Fall TS)) (s : Site) (hs : s ∈ lookSites Zp) :
    ∃ σ' : Side TS ProofFile.Cl V W X Pb, Side.seated cF.blocksInOrder s.at_.place row fs = some σ' := by
  have hp : s.at_.place ∈ cF.blocksInOrder.map (·.place) := by
    rw [places_head h]
    exact site_in_written h s hs
  obtain ⟨b, hb, e⟩ := List.mem_map.1 hp
  cases hf : cF.blocksInOrder.find? (fun b => b.place == s.at_.place) with
  | some b' => exact ⟨_, seated_of_find row cF.blocksInOrder s.at_.place fs b' hf⟩
  | none =>
    exact absurd (by rw [e]; exact beq_self_eq_true _) (List.find?_eq_none.1 hf b hb)

/-- Conditional on `P5J.AtMgA`, the site, hK and the side: `RowStated` there. No `k3Fits`. -/
theorem rowStated_keep_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (A : FillKeep W)
    (get : X → RowOwn) (set : X → RowOwn → X) (s : Site) (hs : s ∈ lookSites Zp)
    (hK : (A.keeps s).Shaped s.at_.face) (fs : List (Fall TS)) (σ' : Side TS ProofFile.Cl V W X Pb)
    (hσ : Side.seated cF.blocksInOrder s.at_.place (rowPairsKeep A get set s) fs = some σ') :
    RowStated s.at_.face σ' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, hb, hbs⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hs
  obtain ⟨hf, _, _⟩ := block_of_seated _ cF.blocksInOrder s.at_.place fs σ' hσ
  have hm : σ'.block ∈ cF.blocksInOrder := List.mem_of_find?_eq_some hf
  have hp : σ'.block.place = s.at_.place := by simpa using List.find?_some hf
  have hmp : σ'.block.place = b.place := hp.trans hbs.symm
  have hk : σ'.block.planOk = true := IM.plan_flat O h.laid.planOk _ hm
  obtain ⟨_, e1, _, e3, e4⟩ :=
    site_block _ _ _ _ _ Zp Bs base cF _ _ O s hs b σ'.block hb hbs hm hmp hk
  obtain ⟨_, g1, g2, _⟩ := memberAtSite _ _ _ _ _ Zp Bs base cF _ _ O b hb σ'.block hm hmp
  exact rowStated_keep_of A get set s hK cF.blocksInOrder fs σ' hσ (s.p.entries.getD []) (g1.trans e3)
    (g2.trans e4) e1 (face_ok_site Zp s hs)

/-- Never to be retold as "the row that passes its tables on is simulated". **Conditional on
`P5J.AtMgA`, hK at every site and the lens: the sites are not none; at every site a side is seated
over the row that passes its tables on; `ExactMember` holds at all its members.** -/
theorem k3_exact_kept_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (φ : Face V W Pb)
    (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X)
    (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x)
    (hK : ∀ s ∈ lookSites Zp, (A.keeps s).Shaped s.at_.face) (fs : List (Fall TS))
    (chain firstTree : Nat)
    (On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    lookSites Zp ≠ [] ∧ ∀ s ∈ lookSites Zp, ∃ σ' : Side TS ProofFile.Cl V W X Pb,
      Side.seated cF.blocksInOrder s.at_.place (rowPairsKeep A get set s) fs = some σ' ∧
        ∀ u' ∈ σ'.members, ExactMember φ σ' chain firstTree On' bud u' := by
  refine ⟨fun e => ?_, fun s hs => ?_⟩
  · have k := sites_fifty_head h
    rw [e] at k
    exact absurd k (by decide)
  · obtain ⟨σ', hσ⟩ := seated_head h (rowPairsKeep (Pb := Pb) A get set s) fs s hs
    exact ⟨σ', hσ, k3_exact_kept φ (A.keeps s) (A.wit s) get set s.at_ hgs hsg (hK s hs)
      (row_of_seatedKeep A get set s cF.blocksInOrder fs σ' hσ)
      (rowStated_keep_head h A get set s hs (hK s hs) fs σ' hσ) chain firstTree On' bud⟩

/-- The same at the letters `fastFillKeep row wit`, row and wit free: without hK. That row is a
named, closed, public term is not laid in here: see the head. -/
theorem k3_exact_kept_head_fast (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (φ : Face V W Pb)
    (row : Site → E → Nat → E) (wit : Site → W → Ask) (get : X → RowOwn) (set : X → RowOwn → X)
    (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x) (fs : List (Fall TS))
    (chain firstTree : Nat)
    (On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    lookSites Zp ≠ [] ∧ ∀ s ∈ lookSites Zp, ∃ σ' : Side TS ProofFile.Cl V W X Pb,
      Side.seated cF.blocksInOrder s.at_.place (rowPairsKeep (fastFillKeep row wit) get set s) fs =
          some σ' ∧
        ∀ u' ∈ σ'.members, ExactMember φ σ' chain firstTree On' bud u' :=
  k3_exact_kept_head h φ (fastFillKeep row wit) get set hgs hsg
    (fun s _ => fastKeeps_shaped theReads (row s) s.at_) fs chain firstTree On' bud

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.seated_head
#print axioms ProofFile.Honest.K3.Law.AtThr.rowStated_keep_head
#print axioms ProofFile.Honest.K3.Law.AtThr.k3_exact_kept_head
#print axioms ProofFile.Honest.K3.Law.AtThr.k3_exact_kept_head_fast
