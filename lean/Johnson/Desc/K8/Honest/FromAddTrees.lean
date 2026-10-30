-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FromAddTrees.lean: THE SMALLNESS TEST: THE DATA AND THE PLANNED LEDGER OF
EVERY SEGMENT, TOGETHER, ARE WHAT ONE CALL OF addTreesF (OnBytes/Model/Tail.lean) RETURNED: the data
but for the two lists of places (`SameL`, Johnson/P1K8R/MadeAtPlans.lean), the ledger as it was
returned or with its weights freed (Fork.trimL). So a sentence that ties the data to the ledger at
addTreesF's return, reads neither list, and reads of the ledger nothing that the freeing touches,
holds at every plan that Verify.publicOf returns, and in the goals' scope at each of the 25 built
segments, WITHOUT A WALK OF ITS OWN. One definition and lemmas; none of the library's goals.

  `FromAdd tlc Fc`   there is a return (tl', G, T') of addTreesF with SameL tl' tlc and Fc = G or Fc
                   = G.trimL
  `fromAdd_of`   from a return and the two ties
  `planG_fromAdd`, `planA_fromAdd`, `planH2_fromAdd`   at what each of the three planners returns
  `public_G_fromAdd`, `public_A_fromAdd`, `public_H_fromAdd`, **`public_fromAdd`**   at every plan
                   in what Verify.publicOf returns
  **`built_fromAdd`**   in the goals' scope, under an opening of the description: at each of the 25
                   built segments
KIN: `Made tlc` (MadeAtPlans.lean) says the like OF THE DATA ALONE, with shapeF's return in front;
its laws on the later routines (`ownerIs_sameL`, `borderMeans_sameL`, `ownerHeld_sameL`,
`owners_sameL`) are called here; `made_at_built` (Johnson/P1K8R/SecondLaidAtBatch.lean) carries it
to the 25 built segments by the same cut as `built_fromAdd`. WHAT THIS ADDS: the ledger stands in
the same sentence.
WRITTEN A FURTHER TIME: the walks are, cut for cut, those of Johnson/P1K8R/ZzRowsAtPlans.lean, which
carry one sentence on the digits' array the same way, and behind them those of the library's
`planG_zMine`, `planH2_zMine`, `public_A_zMine` (OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean,
FoZPublic.lean).
By: `planA_rows0` (BatRows.lean) · `seamPlan_cut` (FoZMade.lean) · `public_G`, `public_H`,
`publicOf_cut` (FoPublic.lean) · `config_at`, `group_plan` (FoPublicA.lean) · IM.ground_tails
(Johnson/IMR/K8Seat.lean).
Limits. THE PLANS AND THE BUILT SEGMENTS ALONE: nothing on the data or the ledger of any state. From
which data, ledger and list the call was made is hidden behind "there is". The full size's 25
segments in `built_fromAdd`. That publicOf returns anywhere is not said.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.P1K8R.MadeAtPlans
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Fo (pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
open _root_.P1K8 (SameL ownerIs_sameL borderMeans_sameL ownerHeld_sameL owners_sameL)

/-- The data and the ledger are what one call of addTreesF returned, but for the two lists of places
and the freeing of the weights. -/
def FromAdd (tlc : HTailF2) (Fc : Fork) : Prop :=
  ∃ (tl tl' : HTailF2) (F G : Fork) (T T' : Tail2) (nU aTX : Array Nat) (hb hbLine : Nat),
    tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T') ∧ SameL tl' tlc ∧
      (Fc = G ∨ Fc = G.trimL)

theorem fromAdd_of {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T'))
    (tlc : HTailF2) (hr : SameL tl' tlc) (Fc : Fork) (hF : Fc = G ∨ Fc = G.trimL) :
    FromAdd tlc Fc :=
  ⟨tl, tl', F, G, T, T', nU, aTX, hb, hbLine, ha, hr, hF⟩

theorem planG_fromAdd (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : FromAdd hp.tl hp.Fp := by
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
    exact fromAdd_of hA _ (ownerIs_sameL tl1 g) _ (Or.inr rfl)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact fromAdd_of hA _ ((ownerIs_sameL tl1 g).trans (borderMeans_sameL hB)) _ (Or.inr rfl)
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem planA_fromAdd (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameL P.seam.tl tlc) : FromAdd tlc P.seam.Fp := by
  obtain ⟨seam0, -, h1, -⟩ := planA_rows0 settings i cf P e
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  exact fromAdd_of hA tlc hr P.seam.Fp (Or.inl rfl)

theorem planH2_fromAdd (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) (Fc : Fork)
    (hF : Fc = hp.Fp ∨ Fc = hp.Fp.trimL) : FromAdd hp.tl Fc := by
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
    exact fromAdd_of hA _ (ownerHeld_sameL hO) Fc hF
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_fromAdd (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : FromAdd hp.tl hp.Fp :=
  planG_fromAdd X.layers g _ hp (public_G h g hp hg)

theorem public_H_fromAdd (h : Verify.publicOf pol KL layout = .ok X) : FromAdd X.H.tl X.H.Fp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_fromAdd _ _ _ _ _ _ _ H0 h0 _ (Or.inr rfl)

theorem public_A_fromAdd (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : FromAdd a.seam.tl a.seam.Fp := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameL k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show FromAdd s.tl a0.seam.Fp
    rw [f3] at f2
    exact planA_fromAdd _ _ _ a0 m2 s.tl f2
  · simp at e1

/-- **At every plan in what publicOf returns.** -/
theorem public_fromAdd (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → FromAdd hp.tl hp.Fp) ∧
    (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → FromAdd a.seam.tl a.seam.Fp) ∧
      FromAdd X.H.tl X.H.Fp :=
  ⟨public_G_fromAdd h, public_A_fromAdd h, public_H_fromAdd h⟩

end

/-- **At each of the 25 built segments.** -/
theorem built_fromAdd {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) : FromAdd Xl.tl Xl.Fp := by
  obtain ⟨hT, X24, e24, h24, f24, -⟩ := IM.ground_tails hS hR O.pub O.blank
  by_cases hh : l = 24
  · subst hh
    obtain rfl : X24 = Xl := Option.some.inj (e24.symm.trans e3)
    rw [h24, f24]
    exact (public_fromAdd O.public).2.2
  · obtain ⟨g, hg, rfl | rfl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
      ⟨l / 2, by omega, by omega⟩
    · obtain ⟨hp, -, X', -, ehp, -, e3', htl, hfp, -⟩ := hT g hg
      obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
      rw [htl, hfp]
      exact (public_fromAdd O.public).1 g hp ehp
    · obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, hfp, -⟩ := hT g hg
      obtain rfl : X' = Xl := Option.some.inj (e3'.symm.trans e3)
      rw [htl, hfp]
      exact (public_fromAdd O.public).2.1 g q eq

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fromAdd_of
#print axioms VerifiableInference.Desc.First.K8.Honest.planG_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.planA_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.planH2_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.public_G_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.public_H_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.public_A_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.public_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.built_fromAdd
