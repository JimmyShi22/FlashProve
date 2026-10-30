-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/NamesTieHead.lean: THE NAMES' TIE AT THE OUTPUT HEAD's SEGMENT, AT ITS SEVEN
OWN MATRICES: in the goals' scope, where the public part is computed: at segment 24 and each
matrix μ < 7, the name that the public part's own built segment lists at the matrix's tree (the
field arrayOf) is (owner, name) by the public parameters' label: (24, "M" μ). THE SENTENCE THAT
OTHER FILES PROVE AT THE TWELVE FEED-FORWARD SEGMENTS (`names_tie`,
Johnson/Road/K4/NamesTie.lean) AND AT THE TWELVE ATTENTION SEGMENTS (`names_tie_att`,
Johnson/Desc/First/Att/Door/Law/K5NamesTie.lean), AT THE LAST SEGMENT. Statements with their
proofs. THE GENERAL LAWS ARE THOSE OF Johnson/Road/K4/Names/: what declareLinks lays
(`declared_names`), which tree is which matrix's by shapeF (`shapeF_names`), what addTreesF and
borderMeans keep (`addTreesF_sameN`, `borderMeans_cut`), `built_declared`, `mem_zipT`: CALLED. THE
PATTERN IS THE ARM `names_at_att` OF K5NamesTie.lean. THE UNFOLDING OF THE HEAD's PLANNER IS
THAT OF `planH2_ownLaid` and `ownerHeld_sameL` (Johnson/IMR/OwnLaidPlans.lean),
line by line, at another relation: said plainly. New here: the head's plan's side.
  `ownerHeld_sameN`, `planH2_names`: what planH2 returns has the four lists (ix, gtTree, pkMat,
  pxMat) of what shapeF returns at the head's own list of matrices, with no matrix read by another
  sub-proof. `matsH_size`, `matsH_kind`: that list has eight entries where the head has four wide
  matrices, and the first seven are of kind 0. `names_at_head`: the tie over any list of links
  whose last bears the head's plan. `names_tie_head`: in scope, where the public part is computed.
NOT HERE: the eighth matrix (the stream, which the last feed-forward segment has sent).
What is not claimed. That the public part is computed at any files in scope. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.NamesTie
import Johnson.Goal.Meaning.HidSeatsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.HeadNames
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH LinksH buildLinksH declareLinks matrixName)
open OnBytes.Road.K4.Names
open Fo.BatRows (bindE_ok)
open _root_.Meaning (labAt ownerK ownerA nameOf matsAt tlAt ownerOf)

theorem ownerHeld_sameN {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : SameN tl tl' := by
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
    exact (borderMeans_cut hB).1
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-- **The head's plan has the four lists of what shapeF returns at the head's own matrices.** -/
theorem planH2_names {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : Nat} {hp : Head.HPlanH2}
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    ∃ (sid : Nat) (f : Array T2Foreign) (tl0 : HTailF2),
      ({ tau := g.tau, lidb := g.lidb } : HTailF2).shapeF (Head.matsH h L b (1 + NGr) sid)
        (Array.replicate (Head.matsH h L b (1 + NGr) sid).size none) f
        #[false, false, true, false] g.tau = .ok tl0 ∧ SameN tl0 hp.tl := by
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
    exact ⟨_, _, tl, hS, (addTreesF_sameN hA).trans (ownerHeld_sameN hO)⟩
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

theorem matsH_size (h : Head.Shape) (L : Head.HL) (b : Head.Border) (gid sid : Nat)
    (hN : h.NHf = 4) : (Head.matsH h L b gid sid).size = 8 := by
  unfold Head.matsH
  rw [hN]
  rfl

theorem matsH_kind (h : Head.Shape) (L : Head.HL) (b : Head.Border) (gid sid : Nat)
    (hN : h.NHf = 4) {μ : Nat} (hμ : μ < 7) : ((Head.matsH h L b gid sid).getD μ {}).kind = 0 := by
  unfold Head.matsH
  rw [hN]
  interval_cases μ <;> rfl

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **The tie, over any list of links whose entry number 24 bears the head's plan.** -/
theorem names_at_head (h : publicOf pol KL lay = .ok X) (C : OnBytes.Road.Hd.PublicCore X.P)
    {l₀ : Array LinkH} {NGr : Nat} {p4 : Bool} {ws : WsLay} {first : Params.First} {B : LinksH}
    {Y : LinkH} (hY : l₀[24]? = some Y) (eY : Y.tl = X.H.tl)
    (hB : buildLinksH l₀ NGr p4 ws first = .ok B) {μ : Nat} (hμ : μ < 7) :
    ((B.links.map (·.arrayOf)).getD 24 #[])[X.H.tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X 24 μ), nameOf (ownerA (labAt X 24 μ))) := by
  have Bc := (OnBytes.Road.Hd.eleven_of_core h C (OnBytes.Road.Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head).NHf
  obtain ⟨H0, h0, eH⟩ := public_H h
  have etl : X.H.tl = H0.tl := by rw [eH]
  obtain ⟨sid, f, tl0, hsh, same⟩ := planH2_names h0
  obtain ⟨declared, hd⟩ := built_declared hB
  obtain ⟨ar, har, N1, -, -⟩ := declared_names hd hY
  have eL : (B.links.map (·.arrayOf)).getD 24 #[] = ar := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, har]
    rfl
  rw [eY, etl] at N1
  have hμm : μ < (matsAt X 24).size := by
    rw [_root_.Meaning.size_head h C]
    omega
  have ol := _root_.Meaning.owner_label h C (by omega : 24 < 25) hμm
  have oo : ownerOf X 24 μ = (24, μ) := by
    unfold _root_.Meaning.ownerOf
    rw [if_pos rfl, hN, if_neg (by omega)]
  rw [oo] at ol
  have eK : ownerK (labAt X 24 μ) = 24 := congrArg Prod.fst ol
  have eA : ownerA (labAt X 24 μ) = μ := congrArg Prod.snd ol
  obtain ⟨S1, -, -⟩ := shapeF_names hsh (μ := μ) (by rw [matsH_size _ _ _ _ _ hN]; omega)
  rw [← same.ix, ← same.gtTree, ← same.pkMat] at S1
  have t0 : (Array.replicate (Head.matsH X.hS X.HLy (Verify.borderOf X.layers.y)
      (1 + X.layers.y.NGr) sid).size (none : Option ℕ)).getD μ none = none := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  obtain ⟨r, r1, r2⟩ := S1 (matsH_kind _ _ _ _ _ hN hμ) t0
  rw [eL, etl, eK, eA]
  exact N1 _ (mem_zipT r1 r2)

/-- **The names' tie at the head's segment, in the goals' scope, where the public part is
computed.** -/
theorem names_tie_head {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) {μ : ℕ} (hμ : μ < 7) :
    ((Z.p.built.links.map (·.arrayOf)).getD 24 #[])[Z.p.X.H.tl.gtTree.getD μ 0]? =
      some (ownerK (labAt Z.p.X 24 μ), nameOf (ownerA (labAt Z.p.X 24 μ))) := by
  have hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public
      (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z from hZ)
  obtain ⟨k4, kN, _, _⟩ := _root_.Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4] at h₀
  obtain ⟨_, _, _, _, e⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  rw [kN] at e
  exact names_at_head hpub C e rfl hB hμ

end VerifiableInference.Desc.K1.HeadNames
