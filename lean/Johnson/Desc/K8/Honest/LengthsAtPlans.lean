-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LengthsAtPlans.lean: THE SMALLNESS TEST: THE LENGTHS OF THE VECTORS OF READS
THAT THE PROOF FILE's LOT HANDS THE TEST (`ProofFile.k8NU`, Johnson/Desc/ProofFile/Lot/K8.lean: the plan's
own field nU) ARE THE LENGTHS THAT STAND IN THE TEST's DATA (the field nUF): AT EACH OF THE 25 BUILT
SEGMENTS, OUTRIGHT, AND SO AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A
SEGMENT's BATCHING, IN THE GOALS' SCOPE. It is what the verifier's run of self tests asks first (nU
== tl.nUF), and the second of the two facts of `FrontLeftN`
(Johnson/Desc/ProofFile/Honest/K8/RestJoinOk.lean). Lemmas; none of the library's goals.

  `lengths_made` behind the routine that lays the arrays, at lengths of the form #[0, 0, x]: these
                   are what it writes into the data
  `planG_lengths`, `planA_lengths`, `planH2_lengths` at the three plans: each lays its arrays at
                   lengths of that form and keeps them as its field nU
  `public_G_lengths`, `public_A_lengths`, `public_H_lengths` so at every member of what
                   Verify.publicOf returns
  **`lengths_at_built`** (ProofFile.k8NU Bs.G₀ Xl == Xl.tl.nUF) = true at each built segment
  **`lengths_lot_at_batch`** (ProofFile.k8NU Bs.G₀ Xl == tl.nUF) = true at a reached state, all 25
By: the library's `addTreesF_record` (OnBytes/Tie/Pv/Tail/EndRuns.lean) · IM.ground_named
(Johnson/IMR/PureJoin.lean), IM.ground_tails (K8Seat.lean) · `public_G`, `public_H`, `publicOf_cut`,
`planA_rows0`, `seamPlan_cut` (Fo) · `seamPlan_nU`, `owners_sameU`, `ownerHeld_sameU`
(Johnson/P1K8R/UnitsAtPlans.lean), `borderMeans_tabs` (UnitsAtPlan.lean) · `lengths_at_batch`
(Johnson/Desc/K8/Honest/FrontSharper.lean).
WRITTEN A FURTHER TIME: the walks through the three plans and through publicOf are those of
`planG_units`, `planA_units`, `planH2_units`, `public_A_units` (Johnson/P1K8R/UnitsAtPlan.lean,
UnitsAtPlans.lean), and the cases of `lengths_at_built` those of `units_at_batch` and its two likes
(UnitsAtBatch.lean, UnitsAtBatchAll.lean), whose test `unitsLaid` holds the third length alone.
Limits. IN SCOPE ALONE in the last two: the full size's 25 segments; under an opening of the
description; in the last the first chain and the family of states from the description's own first
state. Nothing says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.FrontSharper
import Johnson.P1K8R.UnitsAtBatchAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Fo (pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
open _root_.P1K8 (SameU owners_sameU ownerHeld_sameU seamPlan_nU borderMeans_tabs)

/-- Behind the routine that lays the arrays, at lengths of the form #[0, 0, x]: these are the
lengths that it writes into the data, at whatever agrees in that field. -/
theorem lengths_made {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {x : Nat} {aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T #[0, 0, x] aTX hb hbLine = .ok (tl', G, T'))
    (tlc : HTailF2) (h3 : tlc.nUF = tl'.nUF) : ((#[0, 0, x] : Array Nat) == tlc.nUF) = true := by
  rw [h3, (OnBytes.Tie.Pv.Tail.addTreesF_record tl tl' F G T T' _ aTX hb hbLine ha).1]
  simp

/-- **At the plan of a feed-forward sub-proof.** -/
theorem planG_lengths (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : (hp.nU == hp.tl.nUF) = true := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact lengths_made hA _ rfl
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact lengths_made hA _ (borderMeans_tabs hB).2.2
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- At the plan of an attention sub-proof, at whatever agrees in the field. -/
theorem planA_lengths (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : tlc.nUF = P.seam.tl.nUF) : (P.seam.nU == tlc.nUF) = true := by
  obtain ⟨seam0, -, h1, -⟩ := planA_rows0 settings i cf P e
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  rw [seamPlan_nU h1]
  exact lengths_made hA tlc hr

/-- At the plan of the head's sub-proof. -/
theorem planH2_lengths (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : (hp.nU == hp.tl.nUF) = true := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact lengths_made hA _ (ownerHeld_sameU hO).nUF
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_lengths (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) : (hp.nU == hp.tl.nUF) = true :=
  planG_lengths X.layers g _ hp (public_G h g hp hg)

theorem public_H_lengths (h : Verify.publicOf pol KL layout = .ok X) :
    (X.H.nU == X.H.tl.nUF) = true := by
  obtain ⟨H0, h0, e⟩ := public_H h
  have k := planH2_lengths _ _ _ _ _ _ _ H0 h0
  rw [e]
  exact k

theorem public_A_lengths (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : (a.seam.nU == a.seam.tl.nUF) = true := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameU k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show (a0.seam.nU == s.tl.nUF) = true
    rw [f3] at f2
    exact planA_lengths _ _ _ a0 m2 s.tl f2.nUF
  · simp at e1

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EACH OF THE 25 BUILT SEGMENTS: the lot's own lengths are the data's.** -/
theorem lengths_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    (ProofFile.k8NU Bs.G₀ Xl == Xl.tl.nUF) = true := by
  obtain ⟨hN, X24, n24, k24, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨hT, X24', t24, tl24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : X24 = Xl := Option.some.inj (n24.symm.trans e3)
    obtain rfl : X24' = X24 := Option.some.inj (t24.symm.trans e3)
    have hnU : ProofFile.k8NU Bs.G₀ X24' = Bs.G₀.W.H.nU := by
      unfold ProofFile.k8NU
      simp [k24]
    rw [hnU, tl24]
    exact public_H_lengths O.public
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    have hg12 : g < 12 := by omega
    obtain ⟨X, X', a3, hk, hXg, -, a3', hk', hXg', -⟩ := hN g hg12
    obtain ⟨hp, q, Y, Y', ehp, eq, b3, htl, -, -, -, -, b3', htl', -⟩ := hT g hg12
    rcases hg with rfl | rfl
    · obtain rfl : X = Xl := Option.some.inj (a3.symm.trans e3)
      obtain rfl : Y = X := Option.some.inj (b3.symm.trans e3)
      have hnU : ProofFile.k8NU Bs.G₀ Y = hp.nU := by
        unfold ProofFile.k8NU
        simp [hk, hXg, ehp]
      rw [hnU, htl]
      exact public_G_lengths O.public g hp ehp
    · obtain rfl : X' = Xl := Option.some.inj (a3'.symm.trans e3)
      obtain rfl : Y' = X' := Option.some.inj (b3'.symm.trans e3)
      have hnU : ProofFile.k8NU Bs.G₀ Y' = q.seam.nU := by
        unfold ProofFile.k8NU
        simp [hk', hXg', eq]
      rw [hnU, htl']
      exact public_A_lengths O.public g q eq

/-- **SO AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING, AT ALL 25.** -/
theorem lengths_lot_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : (ProofFile.k8NU Bs.G₀ Xl == tl.nUF) = true := by
  rw [lengths_at_batch hS hR O hl e3 h ht]
  exact lengths_at_built hS hR O hl e3

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.lengths_made
#print axioms VerifiableInference.Desc.First.K8.Honest.planG_lengths
#print axioms VerifiableInference.Desc.First.K8.Honest.planA_lengths
#print axioms VerifiableInference.Desc.First.K8.Honest.planH2_lengths
#print axioms VerifiableInference.Desc.First.K8.Honest.public_G_lengths
#print axioms VerifiableInference.Desc.First.K8.Honest.public_H_lengths
#print axioms VerifiableInference.Desc.First.K8.Honest.public_A_lengths
#print axioms VerifiableInference.Desc.First.K8.Honest.lengths_at_built
#print axioms VerifiableInference.Desc.First.K8.Honest.lengths_lot_at_batch
