-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/NamedOfHeld.lean: «THE DESCRIPTION IS MADE ⟹ namedThere», PIECE (P): IN THE GOALS'
SCOPE, AT THE SECOND HASH FUNCTION: where the public part Z of the proof file's description is made,
and the making of the links holds each own matrix's array against the layout (OwnHeld: what piece
(Q) is to give), the test Meaning.namedThere (Johnson/Goal/Meaning/LaidCovered.lean) accepts at
Z.p.X, sizesOf Z.p.X and Z.first.layout. NO PIN. Statements and proofs.

  built_link        (S7) a built link has the record tl and the planned state Fp of the request's own link
  ownLaid_built     (S7) in scope, at each of the 25: the built link is there, its tl is Meaning.tlAt, and OwnLaid holds of its tl and Fp
  OwnHeld layout links   (Q)'s end, in the form in which (P) takes it
  own_named         at an entry of kind 0: the array "M" ++ its number lies in the layout of its own link, with its rows of symbols and its columns
  owner_own         in scope every entry's label names an entry (k', a') of kind 0 with the entry's rows and columns
  **namedThere_of_held**

How. At the 24 readers' entries the label names the OWNER's own entry (owner_cases, Johnson/Goal/Meaning/HidOwner.lean), and in scope the reader's rows and columns are the owner's (planFit_of_core, HidPlanFit.lean): so only own entries are walked: nothing of the routine foreign is read.
What is not claimed. OwnHeld at any files. Nothing outside the goals' scope or at another hash than the older one. Nothing on seatsNamedC. No soundness.

-/
import Johnson.IMR.OwnLaidPlans
import Johnson.IMR.OwnKinds
import Johnson.Goal.Meaning.NamedAskLaw
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.ProofFile.Law.PlainIsPlanned
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import OnBytes.Tie.Pv.Keeps.LinksBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.Own

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Road Meaning
open OnBytes.Model.Verify (publicOf linksOf builtOf)
open OnBytes.Model.Layer (matIx)
open OnBytes.L5.LinksOrder (builtOf_at linksOf_layers linksOf_attention linksOf_head)
open VerifiableInference.PlanWritten (publicOfO_older)

/-- **(S7) A built link has the record and the planned state of the request's own link.** -/
theorem built_link {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∃ ls0, linksOf Z.p.X default = .ok ls0 ∧ ∀ (j : ℕ) (Y : LinkH), ls0[j]? = some Y →
      ∃ Y', Z.p.built.links[j]? = some Y' ∧ Y'.tl = Y.tl ∧ Y'.Fp = Y.Fp := by
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf h
  obtain ⟨ls0, h0, -, a2⟩ := builtOf_at hb
  refine ⟨ls0, h0, fun j Y hj => ?_⟩
  obtain ⟨ar, h1⟩ := a2 j Y hj
  rw [← e]
  show ∃ Y', (b.links.map ProofFile.Law.blank)[j]? = some Y' ∧ _
  rw [Array.getElem?_map, h1]
  exact ⟨_, rfl, rfl, rfl⟩

section Scope
variable {W : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Z : ProofFile.Pub}

/-- **(S7) In scope, at each of the 25 links.** -/
theorem ownLaid_built (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z) {k : ℕ} (hk : k < 25) :
    ∃ Y, Z.p.built.links[k]? = some Y ∧ Y.tl = tlAt Z.p.X k ∧ OwnLaid Y.tl Y.Fp := by
  have hX : publicOf W.pol W.KL (some W.lay) = .ok Z.p.X :=
    (publicOfO_older W.pol W.KL (some W.lay)).symm.trans (ProofFile.Law.pub_public h)
  have C := Hd.core_of_scope hW hR hX
  obtain ⟨h4, h12, -, hA⟩ := scope_plans hW hR hX
  obtain ⟨ls0, h0, L⟩ := built_link h
  by_cases h24 : k = 24
  · subst h24
    have q := linksOf_head h0
    rw [h4, h12] at q
    obtain ⟨Y, e, t1, t2⟩ := L 24 _ q
    refine ⟨Y, e, ?_, ?_⟩
    · rw [t1]
      unfold tlAt
      rw [if_neg (by omega), if_pos rfl]
      rfl
    · rw [t1, t2]
      exact public_H_ownLaid hX
  · by_cases hev : k % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g := ⟨k / 2, by omega⟩
      obtain ⟨P, eP⟩ := planG_there hX C (by omega : g < 12)
      have q := linksOf_layers h0 g P eP
      unfold layersLink at q
      rw [h4, if_pos rfl] at q
      obtain ⟨Y, e, t1, t2⟩ := L (2 * g) _ q
      refine ⟨Y, e, ?_, ?_⟩
      · rw [t1]
        unfold tlAt
        rw [if_neg (by omega), if_neg h24, if_pos hev, show 2 * g / 2 = g by omega, eP]
        rfl
      · rw [t1, t2]
        exact public_G_ownLaid hX g P eP
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g + 1 := ⟨k / 2, by omega⟩
      obtain ⟨a, ea, -⟩ := hA g (by omega)
      have q := linksOf_attention h0 h4 g a ea
      obtain ⟨Y, e, t1, t2⟩ := L (2 * g + 1) _ q
      refine ⟨Y, e, ?_, ?_⟩
      · rw [t1]
        unfold tlAt
        rw [if_neg (by omega), if_neg h24, if_neg hev, show (2 * g + 1) / 2 = g by omega, ea]
        rfl
      · rw [t1, t2]
        exact public_A_ownLaid hX g a ea

end Scope

/-- **(Q)'s end, in the form in which (P) takes it**: at every built link, every pair (array,
matrix) of the two lists of own matrices: the array of that matrix's name lies in the layout of that
link, with the rows and columns of the planned array. -/
def OwnHeld (layout : Params.ReqLayout) (links : Array LinkH) : Prop :=
  ∀ (l : ℕ) (Y : LinkH) (tree mu : ℕ), links[l]? = some Y →
    (tree, mu) ∈ zipT Y.tl.ix.PK.toList Y.tl.pkMat.toList ++
      zipT Y.tl.ix.TX.toList Y.tl.pxMat.toList →
    ∃ (A : Params.ReqArray) (tr : HTree),
      VerifiableInference.Desc.arrayOf layout l (matrixName mu) = some A ∧
      Y.Fp.trees[tree]? = some tr ∧ A.sizeI = tr.R ∧ A.sizeC = tr.K

theorem mem_zipT {α β : Type} {a : Array α} {b : Array β} {i : ℕ} {x : α} {y : β}
    (ha : a[i]? = some x) (hb : b[i]? = some y) : (x, y) ∈ zipT a.toList b.toList := by
  rw [zipT_eq]
  refine List.mem_of_getElem? (i := i) ?_
  rw [List.getElem?_zip_eq_some]
  exact ⟨by simpa using ha, by simpa using hb⟩

theorem pairFit_parts {X : Verify.Public} {k a k' a' : ℕ} (h : pairFit X k a k' a' = true) :
    a' < (matsAt X k').size ∧ ((matsAt X k).getD a {}).m = ((matsAt X k').getD a' {}).m ∧
      ((matsAt X k).getD a {}).k = ((matsAt X k').getD a' {}).k ∧
      labAt X k a = labAt X k' a' := by
  unfold pairFit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **In scope every entry's label names an entry of kind 0, with the entry's rows and columns.** -/
theorem owner_own {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k a : ℕ} (hk : k < 25)
    (ha : a < (matsAt X k).size) :
    ∃ k' a', k' < 25 ∧ a' < (matsAt X k').size ∧ ownerK (labAt X k a) = k' ∧
      ownerA (labAt X k a) = a' ∧ ((matsAt X k').getD a' {}).kind = 0 ∧
      ((matsAt X k).getD a {}).m = ((matsAt X k').getD a' {}).m ∧
      ((matsAt X k).getD a {}).k = ((matsAt X k').getD a' {}).k := by
  have F := planFit_of_core h C
  unfold planFit at F
  rw [Bool.and_eq_true, List.all_eq_true] at F
  have fin : ∀ k' a', k' < 25 → pairFit X k a k' a' = true → ownerK (labAt X k a) = k' →
      ownerA (labAt X k a) = a' → ∃ k' a', k' < 25 ∧ a' < (matsAt X k').size ∧
      ownerK (labAt X k a) = k' ∧ ownerA (labAt X k a) = a' ∧
      ((matsAt X k').getD a' {}).kind = 0 ∧
      ((matsAt X k).getD a {}).m = ((matsAt X k').getD a' {}).m ∧
      ((matsAt X k).getD a {}).k = ((matsAt X k').getD a' {}).k := by
    intro k' a' hk' hp o1 o2
    obtain ⟨p1, p2, p3, p4⟩ := pairFit_parts hp
    exact ⟨k', a', hk', p1, o1, o2, kind_own h C hk' p1 (by rw [← p4]; exact o1), p2, p3⟩
  rcases owner_cases h C hk ha with ⟨o1, o2⟩ | ⟨g, g0, hg, rfl, rfl, o1, o2⟩ |
      ⟨g, hg, rfl, rfl, o1, o2⟩ | ⟨rfl, rfl, o1, o2⟩
  · exact ⟨k, a, hk, ha, o1, o2, kind_own h C hk ha o1, rfl, rfl⟩
  · have Fg := F.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true, Bool.or_eq_true] at Fg
    rcases Fg.1 with e | e
    · exact absurd (beq_iff_eq.1 e) (by omega)
    · exact fin _ _ (by omega) e o1 o2
  · have Fg := F.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true] at Fg
    exact fin _ _ (by omega) Fg.2 o1 o2
  · exact fin _ _ (by omega) F.2 o1 o2

section Scope2
variable {W : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Z : ProofFile.Pub}

/-- At an entry of kind 0: its array lies in the layout of its own link, with its rows of symbols and
its columns. -/
theorem own_named (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (Q : OwnHeld Z.first.layout Z.p.built.links) {k a : ℕ} (hk : k < 25)
    (ha : a < (tlAt Z.p.X k).NM) (h0 : ((matsAt Z.p.X k).getD a {}).kind = 0) :
    ∃ A, VerifiableInference.Desc.arrayOf Z.first.layout k (matrixName a) = some A ∧
      A.sizeI = (((matsAt Z.p.X k).getD a {}).m + 2) / 3 ∧
      A.sizeC = ((matsAt Z.p.X k).getD a {}).k := by
  obtain ⟨Y, e, t, OL⟩ := ownLaid_built hW hR h hk
  obtain ⟨i, tree, w, s1, s2, s3⟩ := OL a (by rw [t]; exact ha) (by rw [t]; exact h0)
  have hm : (tree, a) ∈ zipT Y.tl.ix.PK.toList Y.tl.pkMat.toList ++
      zipT Y.tl.ix.TX.toList Y.tl.pxMat.toList := by
    rcases w with ⟨w1, w2⟩ | ⟨w1, w2⟩
    · exact List.mem_append_left _ (mem_zipT w2 w1)
    · exact List.mem_append_right _ (mem_zipT w2 w1)
  obtain ⟨A, tr, hA, htr, q1, q2⟩ := Q k Y tree a e hm
  have eg : Y.Fp.trees.getD tree {} = tr := by
    rw [Array.getD_eq_getD_getElem?, htr]
    rfl
  rw [eg, t] at s2 s3
  exact ⟨A, hA, q1.trans s2, q2.trans s3⟩

/-- The light test accepts. -/
theorem namedB_of_held (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (Q : OwnHeld Z.first.layout Z.p.built.links) :
    NamedAsk.namedB Z.p.X Z.first.layout = true := by
  have hX : publicOf W.pol W.KL (some W.lay) = .ok Z.p.X :=
    (publicOfO_older W.pol W.KL (some W.lay)).symm.trans (ProofFile.Law.pub_public h)
  have C := Hd.core_of_scope hW hR hX
  have hF := NamedAsk.fullShaped_scope hW hR hX
  unfold NamedAsk.namedB
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 25 := List.mem_range.1 hk
  rw [List.all_eq_true]
  intro a ha
  have ha' := List.mem_range.1 ha
  have eL : NamedAsk.labK Z.p.X k a = labAt Z.p.X k a := by
    unfold NamedAsk.labK labAt matsAt
    rw [NamedAsk.tlK_eq hF hk']
  rw [NamedAsk.tlK_eq hF hk'] at ha' ⊢
  rw [eL]
  have hs : a < (matsAt Z.p.X k).size := by
    have := nm_of_core hX C hk'
    unfold VerifiableInference.Desc.K3Asks.nMat at ha'
    rw [this] at ha'
    exact ha'
  obtain ⟨k', a', hk2, ha2, o1, o2, kd, em, ek⟩ := owner_own hX C hk' hs
  obtain ⟨A, hA, s1, s2⟩ := own_named hW hR h Q hk2
    (by rw [nm_of_core hX C hk2]; exact ha2) kd
  have hN : VerifiableInference.Desc.arrayOf Z.first.layout
      (NamedAsk.linkK (labAt Z.p.X k a / 256)) (NamedAsk.nameK (labAt Z.p.X k a % 256)) =
      some A := by
    show VerifiableInference.Desc.arrayOf Z.first.layout (ownerK (labAt Z.p.X k a))
      (matrixName (ownerA (labAt Z.p.X k a))) = some A
    rw [o1, o2]
    exact hA
  rw [hN]
  show (A.sizeI == (((matsAt Z.p.X k).getD a {}).m + 2) / 3 &&
    A.sizeC == ((matsAt Z.p.X k).getD a {}).k) = true
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, em, ek]
  exact ⟨s1, s2⟩

/-- **(P): namedThere, WHERE THE DESCRIPTION IS MADE AND THE MAKING OF THE LINKS HOLDS EACH OWN
MATRIX's ARRAY AGAINST THE LAYOUT.** In the goals' scope, at the second hash function. No pin. -/
theorem namedThere_of_held (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (Q : OwnHeld Z.first.layout Z.p.built.links) :
    Meaning.namedThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true :=
  NamedAsk.named_of_B
    (NamedAsk.fullShaped_scope hW hR ((publicOfO_older W.pol W.KL (some W.lay)).symm.trans
      (ProofFile.Law.pub_public h)))
    (namedB_of_held hW hR h Q)

end Scope2

end IM.Own

#print axioms IM.Own.built_link
#print axioms IM.Own.ownLaid_built
#print axioms IM.Own.owner_own
#print axioms IM.Own.own_named
#print axioms IM.Own.namedThere_of_held
