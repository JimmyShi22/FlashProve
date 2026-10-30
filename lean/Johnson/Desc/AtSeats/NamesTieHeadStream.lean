-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/NamesTieHeadStream.lean: THE NAMES' TIE AT THE OUTPUT HEAD's SEGMENT, AT ITS
EIGHTH MATRIX (the stream, which the last feed-forward segment has sent), AND SO AT ALL EIGHT: in
the goals' scope, where the public part is computed: the name that the public part's own built
segment 24 lists at the matrix's tree is (owner, name) by the public parameters' label: at the
eighth: (22, "M7"). WITH Johnson/Desc/AtSeats/NamesTieHead.lean (the seven own matrices) AND
`names_tie` (NamesTie.lean), `names_tie_att` (K5NamesTie.lean): THE TIE STANDS AT ALL 25 SEGMENTS,
WHOLE. Statements with their proofs. THE ROAD IS ANOTHER FILE's, PORTED: the arm of `names_at_links`
(NamesAtLinks.lean) for the matrix that a later group reads from the group before, at the head in
that later group's place: the general laws of Johnson/Road/K4/Names/ are CALLED (`declared_names`:
what `foreign` lays; `shapeF_names`, third arm; `borderMeans_cut`, second half; `group_at`;
`shapeF_last`). New here: the head's plan's side. `ownerHeld_place`, `planH2_place`: the record
  number 0 of what planH2 returns names the last group as the owner and, as the place, the last of
  the owner's arrays that another sub-proof reads. `matsH_stream`: the eighth entry of the head's
  list of matrices is of kind 1 and reads record 0. `owner_is_last`: the owner that the head's
  planner is handed bears the last group's plan's record. `names_at_head_stream`: the tie over any
  list of links that bears the two plans at 22 and 24. `names_tie_head_stream`: in scope.
  `names_tie_head_all`: at every μ < 8.
What is not claimed. That the public part is computed at any files in scope. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.AtSeats.NamesTieHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.HeadNames
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH buildLinksH declareLinks matrixName layersLink)
open OnBytes.Road.K4.Names
open Fo.BatRows (bindE_ok)
open _root_.Meaning (labAt ownerK ownerA nameOf matsAt tlAt ownerOf)

theorem ownerHeld_place {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') :
    ∃ pl, tl'.plFor[0]? = some pl ∧ pl.owner = some (NGr - 1) ∧
      pl.rootIndex = some (O.tl.pkMat.size + O.tl.ix.TX.size - 1) := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hB, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := Except.ok.inj e
    exact (borderMeans_cut hB).2
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-- **The record number 0 of the head's plan.** -/
theorem planH2_place {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : Nat} {hp : Head.HPlanH2}
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    ∃ pl, hp.tl.plFor[0]? = some pl ∧ pl.owner = some (NGr - 1) ∧
      pl.rootIndex = some (O.tl.pkMat.size + O.tl.ix.TX.size - 1) := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨st, hst, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact ownerHeld_place hO
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem matsH_stream (h : Head.Shape) (L : Head.HL) (b : Head.Border) (gid sid : Nat)
    (hN : h.NHf = 4) : ((Head.matsH h L b gid sid).getD 7 {}).kind = 1 ∧
      ((Head.matsH h L b gid sid).getD 7 {}).foreign = some 0 := by
  unfold Head.matsH
  rw [hN]
  exact ⟨rfl, rfl⟩

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- The owner that the head's planner is handed bears the last group's plan's record. -/
theorem owner_is_last (h : publicOf pol KL lay = .ok X) (hs : X.G.size = 12) {Oo : Layer.HPlan2}
    (hOo : X.G[11]? = some Oo) : X.owner.tl = Oo.tl := by
  have ho := (publicOf_cut pol KL lay X h).2.2.2.1
  unfold Verify.ownerOf at ho
  have hb : X.G.back? = some Oo := by
    rw [Array.back?_eq_getElem?, hs]
    exact hOo
  rw [hb] at ho
  rw [← Except.ok.inj ho]

/-- **The tie at the stream, over any list of links that bears the two plans.** -/
theorem names_at_head_stream (h : publicOf pol KL lay = .ok X)
    (C : OnBytes.Road.Hd.PublicCore X.P) (h4 : X.p4 = true) (hN12 : X.NGr = 12)
    (hs : X.G.size = 12) {l₀ : Array LinkH} {ws : WsLay} {first : Params.First} {B : LinksH}
    {Y : LinkH} (hY : l₀[24]? = some Y) (eY : Y.tl = X.H.tl)
    (hl0 : ∀ hp, X.G[11]? = some hp → ∃ Yo, l₀[22]? = some Yo ∧ Yo.tl = hp.tl)
    (hB : buildLinksH l₀ X.NGr X.p4 ws first = .ok B) :
    ((B.links.map (·.arrayOf)).getD 24 #[])[X.H.tl.gtTree.getD 7 0]? =
      some (ownerK (labAt X 24 7), nameOf (ownerA (labAt X 24 7))) := by
  have Bc := (OnBytes.Road.Hd.eleven_of_core h C (OnBytes.Road.Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head).NHf
  obtain ⟨_, i7, _⟩ := _root_.Meaning.ix_of_core h C
  obtain ⟨H0, h0, eH⟩ := public_H h
  have etl : X.H.tl = H0.tl := by rw [eH]
  obtain ⟨sid, f, tl0, hsh, same⟩ := planH2_names h0
  obtain ⟨pl, p1, p2, p3⟩ := planH2_place h0
  obtain ⟨declared, hd⟩ := built_declared hB
  obtain ⟨ar, har, -, -, N3⟩ := declared_names hd hY
  have eL : (B.links.map (·.arrayOf)).getD 24 #[] = ar := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, har]
    rfl
  rw [eY, etl] at N3
  have hμm : 7 < (matsAt X 24).size := by
    rw [_root_.Meaning.size_head h C]
    omega
  have ol := _root_.Meaning.owner_label h C (by omega : 24 < 25) hμm
  have oo : ownerOf X 24 7 = (22, 7) := by
    unfold _root_.Meaning.ownerOf
    rw [if_pos rfl, hN, if_pos rfl, i7]
  rw [oo] at ol
  have eK : ownerK (labAt X 24 7) = 22 := congrArg Prod.fst ol
  have eA : ownerA (labAt X 24 7) = 7 := congrArg Prod.snd ol
  obtain ⟨-, -, S3⟩ := shapeF_names hsh (μ := 7) (by rw [matsH_size _ _ _ _ _ hN]; omega)
  rw [← same.ix, ← same.gtTree] at S3
  obtain ⟨k1, kf⟩ := matsH_stream X.hS X.HLy (Verify.borderOf X.layers.y) (1 + X.layers.y.NGr) sid
    hN
  obtain ⟨f1, _⟩ := S3 k1 0 kf
  obtain ⟨owner, ri, Yo, mu, a1, a2, a3, a4, a5⟩ := N3 _ (mem_zipT f1 p1)
  have hNy : X.layers.y.NGr = 12 := hN12
  rw [hNy] at p2
  obtain rfl : 12 - 1 = owner := Option.some.inj (p2.symm.trans a1)
  obtain rfl : X.owner.tl.pkMat.size + X.owner.tl.ix.TX.size - 1 = ri :=
    Option.some.inj (p3.symm.trans a2)
  have eLk : layersLink X.p4 (12 - 1) = 22 := by
    unfold layersLink
    rw [h4, if_pos rfl]
  rw [eLk] at a3 a5
  obtain ⟨Oo, hOo⟩ := _root_.Meaning.planG_there h C (g := 11) (by omega)
  obtain ⟨Yo', hYo, eYo⟩ := hl0 Oo hOo
  obtain rfl : Yo' = Yo := Option.some.inj (hYo.symm.trans a3)
  rw [eYo, owner_is_last h hs hOo, show Oo.tl.pkMat.size + Oo.tl.ix.TX.size - 1 -
    Oo.tl.pkMat.size = Oo.tl.ix.TX.size - 1 by omega] at a4
  obtain ⟨matsO, txO, ftO, tlO, Go⟩ := group_at h C h4 hN12 (g := 11) (by omega) hOo
  have k7 : (matsO.getD 7 {}).kind = 0 := by
    rw [Go.kind 7 (by omega), if_neg (by simp)]
  have hlast := shapeF_last Go.shape (μ := 7) (by rw [Go.size]; omega)
    (by
      unfold isPX
      rw [Go.tx 7 (by omega), k7]
      rfl)
    (fun k h1 h2 => by
      rw [Go.size] at h2
      obtain rfl : k = 8 := by omega
      unfold isPX
      rw [Go.tx 8 (by omega)]
      simp)
  rw [← Go.same.ix, ← Go.same.pxMat] at hlast
  obtain rfl : mu = 7 := Option.some.inj (a4.symm.trans hlast)
  rw [eL, etl, eK, eA]
  exact a5

/-- **In the goals' scope, where the public part is computed.** -/
theorem names_tie_head_stream {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {Z : ProofFile.Pub} (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) :
    ((Z.p.built.links.map (·.arrayOf)).getD 24 #[])[Z.p.X.H.tl.gtTree.getD 7 0]? =
      some (ownerK (labAt Z.p.X 24 7), nameOf (ownerA (labAt Z.p.X 24 7))) := by
  have hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public
      (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z from hZ)
  obtain ⟨k4, kN, _, hA⟩ := _root_.Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4] at h₀
  obtain ⟨sG, _, _, p0, e⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  rw [kN] at e sG
  rw [Array.size_map] at sG
  refine names_at_head_stream hpub C k4 kN sG e rfl (fun hp hgp => ?_) hB
  obtain ⟨a, ha, _⟩ := hA 11 (by omega)
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[11]? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[11]? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨q0, _⟩ := p0 11 _ _ s0 t0
  exact ⟨_, q0, rfl⟩

/-- **At all eight.** -/
theorem names_tie_head_all {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) {μ : ℕ} (hμ : μ < 8) :
    ((Z.p.built.links.map (·.arrayOf)).getD 24 #[])[Z.p.X.H.tl.gtTree.getD μ 0]? =
      some (ownerK (labAt Z.p.X 24 μ), nameOf (ownerA (labAt Z.p.X 24 μ))) := by
  by_cases e : μ = 7
  · subst e
    exact names_tie_head_stream hS hR hZ
  · exact names_tie_head hS hR hZ (by omega)

end VerifiableInference.Desc.K1.HeadNames
