-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/ReadsByMake.lean: THE NAMED TEST readsP OF K4's ROW (readsArrayP,
Johnson/Road/K4/Rec/ReadsArray.lean) IS A THEOREM, BY THE MAKE OF THE PUBLIC PART: it accepts
wherever the plain road returns the public part Z, publicOf returns Z's public parameters, at
profile 4, at each group g that has its entries in X.G and X.A. Two statements with their proofs.
NO NUMERAL OF THE SCOPE AND NO WRITTEN VALUE IS READ.

  `held_u3`: where heldAgainst accepts and a declared segment's second moment is one array a: the
    layout has an array of a's name at that segment, with a's rows and columns, in an oracle
    message of moment 1 of the request's shape. By Fo.heldAgainst_cut and the texts of
    linkHeld and arrayHeld.
  **`readsP_public`**: readsArrayP hp Z.first.shape Z.first.layout ‹the built segment 2 g's list
    arrayOf› (2 * g) ‹the looks of its planned arrays› = true. Premises: h (publicOf returns
    Z.p.X) · hZ (pubPlain returns Z: an opening's field pub) · h4 (profile 4) · hgp, ha (the
    group's two entries: in scope Meaning.scope_plans and K4Here's field G).
WHY IT HOLDS: the array of the reads is number 0 of the plan's list, one row, nU[2] columns, one
virtual row from column 0 (planG_u3, look_u3: Johnson/Road/K4/Rec/U3Tree.lean); the segment declares
it as "U3" alone in its second moment, with these sizes (declared_u3:
Johnson/Road/K4/Rec/U3Links.lean); the maker of the built segments has held the layout and the
shape against the declarations (plain_cut: Johnson/Road/K4/Rec/BuiltTests.lean).
CAN IT BE EMPTY? Its premises are met wherever K4Here is (in scope, at an opening). The test was
evaluated true x12 at the full size, with a negative test (in a file of evaluations not named here).
Limits. A test on public data: at no meaning. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Rec.U3Tree
import Johnson.Road.K4.Rec.U3Links
import Johnson.Road.K4.Rec.BuiltTests
import Johnson.Road.K4.Rec.ReadsArray

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc.First.FillSent (treesAt looksOf)
open VerifiableInference.Desc.First.RecordPlan (oneRowP readsThereP atMoment1P)

/-- **What heldAgainst's accept says of a second moment that is one array.** -/
theorem held_u3 {declared : Array FrameLink} {p : Params.First} {l : Nat} {Dl : FrameLink}
    (h : heldAgainst declared p = .ok ()) (hD : declared[l]? = some Dl)
    (h1 : 1 < Dl.moment.size) {a : FrameArray} (hm : Dl.moment.getD 1 #[] = #[a]) :
    ∃ A L m, reqArray p.layout l a.name = some A ∧ p.shape.link[l]? = some L ∧
      L.messages[A.message]? = some m ∧ A.sizeI = a.rows ∧ A.sizeC = a.columns ∧
      m.moment = 1 := by
  obtain ⟨e1, e2, e3⟩ := Fo.heldAgainst_cut h
  have hl : l < declared.size := (Array.getElem?_eq_some_iff.1 hD).1
  obtain ⟨L, hL⟩ : ∃ L, p.shape.link[l]? = some L :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨As, hA⟩ : ∃ As, p.layout.link[l]? = some As :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hh := e3 l _ L As hD hL hA
  unfold linkHeld at hh
  simp only [Bool.and_eq_true] at hh
  obtain ⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩ := hh
  rw [List.all_eq_true] at h3
  have hmem : (Dl.moment.getD 1 #[], 1) ∈ Dl.moment.toList.zipIdx := by
    refine List.mk_mem_zipIdx_iff_getElem?.2 ?_
    rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1]
    rfl
  have h4 := h3 _ hmem
  dsimp only at h4
  rw [hm] at h4
  have h5 : arrayHeld L.messages As 1 a = true := by simpa using h4
  unfold arrayHeld at h5
  split at h5
  · cases h5
  · rename_i A hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h5
    obtain ⟨⟨⟨⟨s1, s2⟩, _⟩, _⟩, h6⟩ := h5
    split at h6
    · cases h6
    · rename_i m hm'
      simp only [Bool.and_eq_true, beq_iff_eq] at h6
      refine ⟨A, L, m, ?_, hL, hm', s1, s2, h6.1.1⟩
      unfold reqArray
      rw [hA]
      exact hf

/-- **THE TEST readsP ACCEPTS, BY THE MAKE OF THE PUBLIC PART.** -/
theorem readsP_public {o : ProofFile.SecondHashFunctionArgument} {pol lay KL pol' KL' : ByteArray}
    {layout : Option ByteArray} {Z : ProofFile.Pub}
    (h : Verify.publicOf pol' KL' layout = .ok Z.p.X) (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (h4 : Z.p.X.p4 = true) {g : ℕ} {hp : Layer.HPlan2} {a : Attention.Plan}
    (hgp : Z.p.X.G[g]? = some hp) (ha : Z.p.X.A[g]? = some a) :
    readsArrayP hp Z.first.shape Z.first.layout
      ((Z.p.built.links.map (·.arrayOf)).getD (2 * g) #[]) (2 * g)
      (treesAt Z.p.built.links (2 * g)) = true := by
  obtain ⟨eU, eT⟩ := planG_u3 _ _ _ _ (Fo.Pub.public_G h g hp hgp)
  obtain ⟨l₀, declared, h₀, hd, hh, _⟩ := plain_cut hZ
  unfold ProofFile.Plain.linksPlain at h₀
  rw [h4] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨q0, _⟩ := p0 g _ _ s0 t0
  obtain ⟨ar, t, n, hn, har, ht, _, hl, h1, hm⟩ := declared_u3 hd q0 eU
  obtain rfl : trimT (u3Tree (hp.nU.getD 2 0)) = t := Option.some.inj (eT.symm.trans ht)
  have hD : declared[2 * g]? = some (declared.getD (2 * g) {}) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
    rfl
  obtain ⟨A, L, m, hA, hL, hmm, s1, s2, s3⟩ := held_u3 hh hD h1 hm
  have hA' : reqArray Z.first.layout (2 * g) nameU3 = some A := hA
  have s1' : A.sizeI = 1 := s1
  have s2' : A.sizeC = hp.nU.getD 2 0 := s2
  have hu : hp.tl.ix.U.getD 2 none = some 0 := by
    rw [eU]
    rfl
  have hT : (treesAt Z.p.built.links (2 * g))[0]? =
      some (1, hp.nU.getD 2 0, [(0, hp.nU.getD 2 0)]) := by
    unfold treesAt
    rw [hn]
    exact look_u3 eT
  have hAr : (Z.p.built.links.map (·.arrayOf)).getD (2 * g) #[] = ar := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, hn]
    rfl
  have hR : readsThereP Z.first.shape Z.first.layout ar (2 * g) 0 (hp.nU.getD 2 0) = true := by
    unfold readsThereP
    rw [har]
    dsimp only
    rw [hA']
    dsimp only
    unfold atMoment1P
    dsimp only
    rw [hL]
    simp [hmm, s1', s2', s3]
  have hK : ((hp.Fp.trees[0]?).map (·.K)).getD 0 = hp.nU.getD 2 0 := by
    rw [eT]
    rfl
  unfold readsArrayP
  rw [hu, hAr]
  dsimp only
  rw [hR, hK]
  unfold oneRowP
  rw [hT]
  simp

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.held_u3
#print axioms OnBytes.Road.K4.Rec.readsP_public
