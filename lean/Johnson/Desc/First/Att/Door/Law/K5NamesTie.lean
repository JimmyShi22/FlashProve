-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5NamesTie.lean: kind K5: **THE NAMES' TIE AT THE TWELVE ATTENTION SEGMENTS**: in the goals' scope, at an opening of the IOP as written in Lean, at each attention segment 2 g + 1 and each of its five
matrices, the name that the public part's own built segment lists at the matrix's tree (the field arrayOf) is (owner, name) by the public parameters' label. The sentence that another file proves at the twelve feed-forward segments
(names_tie, Johnson/Road/K4/NamesTie.lean), at the odd numbers. It is the first conjunct of the test entryTieB (Johnson/Goal/Meaning/ReadingsOne.lean).
The general laws are those of the files below Johnson/Road/K4/Names/: what declareLinks lays (declared_names, Johnson/Road/K4/Names/DeclaredNames.lean) · which tree is which matrix's by shapeF (shapeF_names, ShapeNames.lean; shapeF_px, ShapePx.lean) · what addTreesF and
borderMeans keep (PlanNames.lean) · one group's lists (group_at, NamesAtLinks.lean). New here: the attention plan's side.

Main names:
  Placed G g r · ownerPlace_placed · ownerPlaces_placed · owners_placed: where attentionOwners (OnBytes/Model/VerifyCross.lean) returns r: at each g the record number 0 of the plan r[g] names group g as the owner and, as the place, the
    number of the owner's arrays that no other sub-proof reads.
  seamShape_shapeF · seamPlan_sameN · planA_names: a member a of X.A: a.seam.tl has the four lists (ix · gtTree · pkMat · pxMat) of what shapeF returns at the plan's own list of matrices, with no matrix read by another sub-proof.
  placed_at: the record at a member of X.A. own_kind · qa_kind: the kinds in the list of matrices. px_first: the first of a layers' plan's matrices that another sub-proof reads is number 6.
  **names_at_att**: the tie over any list of links that bears the plans at their places. **names_tie_att_plain**: in scope, where the public part is computed (ProofFile.pubPlain … = .ok Z). names_tie_att: so at an opening.
IS IT EMPTY HERE? That the public part is computed at any files in scope is shown by no theorem.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.K4.NamesTie
import Johnson.Road.K4.Names.ShapePx
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicASeam
import Johnson.Road.Lane5AttOwn
import Johnson.Road.Lane5AttLabel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Names
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf SubPlan)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH buildLinksH declareLinks matrixName layersLink)
open OnBytes.Road.K4.Names
open OnBytes.Road.L5 (fixed jp_ok bind_ok matrices_qa)
open Fo.BatRows (bindE_ok)
open Meaning (labAt ownerK ownerA nameOf matsAt tlAt ownerOf)

/-! ## What attentionOwners lays -/

/-- At g: the record number 0 of the plan r[g] names group g and the number of the owner's arrays that no other sub-proof reads. -/
def Placed (G : Array SubPlan) (g : ℕ) (r : Array SubPlan) : Prop :=
  ∃ O X' pl, G[g]? = some O ∧ r[g]? = some X' ∧ X'.tl.plFor[0]? = some pl ∧ pl.owner = some g ∧
    pl.rootIndex = some O.tl.pkMat.size

theorem ownerPlace_placed {g : ℕ} {O X X' : SubPlan} (h : Verify.attentionOwnerPlace g O X = .ok X') :
    ∃ pl, X'.tl.plFor[0]? = some pl ∧ pl.owner = some g ∧ pl.rootIndex = some O.tl.pkMat.size := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact (borderMeans_cut h1).2

theorem ownerPlaces_placed (G : Array SubPlan) : ∀ (l : List ℕ) (out r : Array SubPlan), l.Nodup →
    l.foldlM (fun (out : Array SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r →
    (∀ g ∈ l, Placed G g r) ∧ ∀ i, i ∉ l → r[i]? = out[i]?
  | [], out, r, _, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact ⟨fun g hg => absurd hg (List.not_mem_nil), fun _ _ => rfl⟩
  | g :: l, out, r, hn, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    obtain ⟨hgl, hnl⟩ := List.nodup_cons.1 hn
    obtain ⟨I1, I2⟩ := ownerPlaces_placed G l out1 r hnl h
    split at h1
    · rename_i O X hO hX
      obtain ⟨X', h2, h1⟩ := bindE_ok h1
      obtain rfl := Except.ok.inj h1
      have hlt : g < out.size := (Array.getElem?_eq_some_iff.1 hX).1
      have e : (out.set! g X')[g]? = some X' := by
        simp [Array.set!, hlt]
      refine ⟨fun g' hg' => ?_, fun i hi => ?_⟩
      · rcases List.mem_cons.1 hg' with hh | hm
        · subst hh
          obtain ⟨pl, p1, p2, p3⟩ := ownerPlace_placed h2
          exact ⟨O, X', pl, hO, (I2 _ hgl).trans e, p1, p2, p3⟩
        · exact I1 g' hm
      · have hig : i ≠ g := fun k => hi (List.mem_cons.2 (Or.inl k))
        have hil : i ∉ l := fun k => hi (List.mem_cons.2 (Or.inr k))
        have e' : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [I2 i hil, e']
    · cases h1

theorem owners_placed {NGr : ℕ} {G A r : Array SubPlan} (h : Verify.attentionOwners true NGr G A = .ok r) :
    ∀ g, g < NGr → Placed G g r := by
  unfold Verify.attentionOwners at h
  rw [if_pos rfl] at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  exact fun g hg => (ownerPlaces_placed G _ A r List.nodup_range h).1 g (List.mem_range.2 hg)

/-! ## The attention plan's lists -/

theorem seamShape_shapeF {g : Model.Settings} {m : Array TMat} {tau col0F ktO aO : ℕ} {s : Attention.Seam}
    (h : Attention.Seam.shape g m tau col0F ktO aO = Except.ok s) :
    ∃ f : T2Foreign, ({ tau := g.tau, lidb := g.lidb } : HTailF2).shapeF (m.map fixed)
      (Array.replicate (m.map fixed).size none) #[f] #[false, false, true, false] tau = .ok s.tl := by
  unfold Attention.Seam.shape at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨tl, ht, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨_, ht⟩

theorem seamPlan_sameN {s s' : Attention.Seam} {nU3 hb hbLine : ℕ} (h : s.plan nU3 hb hbLine = Except.ok s') :
    SameN s.tl s'.tl := by
  unfold Attention.Seam.plan at h
  obtain ⟨r, hr, h⟩ := bind_ok h
  have k : SameN s.tl r.1 := addTreesF_sameN (tl' := r.1) (F' := r.2.1) (T' := r.2.2) hr
  obtain ⟨tl, Fp, T⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨Tp, -, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact k

section
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **A member of X.A has the four lists of what shapeF returns at the plan's own list of matrices.** -/
theorem planA_names (h : publicOf pol KL lay = .ok X) {g : ℕ} {a : Attention.Plan} (ha : X.A[g]? = some a) :
    ∃ (i : Attention.In) (f : T2Foreign) (tl0 : HTailF2),
      ({ tau := X.P.settings.tau, lidb := X.P.settings.lidb } : HTailF2).shapeF ((Attention.matrices a.S i).map fixed)
        (Array.replicate ((Attention.matrices a.S i).map fixed).size none) #[f] #[false, false, true, false]
        X.P.settings.tau = .ok tl0 ∧ SameN tl0 a.seam.tl := by
  obtain ⟨seam0, s1, h0, h1, e⟩ := Fo.PubA.public_A_seam_at h g a ha
  obtain ⟨f, hf⟩ := seamShape_shapeF h0
  have k := seamPlan_sameN h1
  have e1 : a.seam.tl.ix = s1.tl.ix := by conv_lhs => rw [e]
  have e2 : a.seam.tl.gtTree = s1.tl.gtTree := by conv_lhs => rw [e]
  have e3 : a.seam.tl.pkMat = s1.tl.pkMat := by conv_lhs => rw [e]
  have e4 : a.seam.tl.pxMat = s1.tl.pxMat := by conv_lhs => rw [e]
  exact ⟨_, f, seam0.tl, hf, ⟨e1.trans k.ix, e2.trans k.gtTree, e3.trans k.pkMat, e4.trans k.pxMat⟩⟩

/-- **The record of the array that an attention sub-proof borrows, at a member of X.A.** -/
theorem placed_at (h : publicOf pol KL lay = .ok X) (h4 : X.p4 = true) {g : ℕ} (hg : g < X.NGr) {a : Attention.Plan}
    (ha : X.A[g]? = some a) :
    ∃ hp pl, X.G[g]? = some hp ∧ a.seam.tl.plFor[0]? = some pl ∧ pl.owner = some g ∧
      pl.rootIndex = some hp.tl.pkMat.size := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := Fo.Pub.publicOf_cut pol KL lay X h
  rw [k7] at ha
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at ha
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 ha
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, _, e2, e3⟩ := hz
  have h4' : X.layers.y.h.p4 = true := h4
  rw [h4'] at k6
  obtain ⟨O, X', pl, q1, q2, q3, q4, q5⟩ := owners_placed k6 g hg
  obtain rfl : X' = s := Option.some.inj (q2.symm.trans e2)
  unfold Fo.Pub.seenG at q1
  rw [Array.getElem?_map] at q1
  obtain ⟨hp, hhp, rfl⟩ := Option.map_eq_some_iff.1 q1
  refine ⟨hp, pl, hhp, ?_, q4, q5⟩
  rw [e3]
  exact q3

end

/-! ## The kinds in the list of matrices -/

theorem fixed_kind (M : TMat) : (fixed M).kind = M.kind := by
  unfold fixed
  split <;> rfl

theorem own_kind (S : Attention.Shape) (i : Attention.In) {μ : ℕ} (hμ : μ < S.cf.NAs + 3) :
    (((Attention.matrices S i).map fixed).getD μ {}).kind = 0 := by
  have key : ∃ M, (Attention.matrices S i)[μ]? = some M ∧ M.kind = 0 := by
    by_cases hq : μ < S.cf.NAs
    · refine ⟨Attention.ownMatrix i ("as" ++ toString μ) (2 ^ S.cf.lmS) (S.kAs / S.cf.NAs) μ i.wpS, ?_, rfl⟩
      unfold Attention.matrices
      rw [Array.getElem?_append_left (by simpa using hq)]
      simp [hq]
    · obtain ⟨j, rfl⟩ : ∃ j, μ = S.cf.NAs + j := ⟨μ - S.cf.NAs, by omega⟩
      have t := Meaning.matrices_tail S i j
      have c : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases c with rfl | rfl | rfl
      · exact ⟨Attention.ownMatrix i "ah" (S.cf.wcH * S.T) (S.fillH / S.cf.wcH) S.cf.NAs i.wph, t.trans rfl, rfl⟩
      · exact ⟨Attention.ownMatrix i "ao" (S.cf.wcO * S.T) (S.fillO / S.cf.wcO) (S.cf.NAs + 1) i.wpo, t.trans rfl, rfl⟩
      · exact ⟨Attention.ownMatrix i "bA" (2 ^ S.cf.lmb) S.kbA (S.cf.NAs + 2) i.wpbA, t.trans rfl, rfl⟩
  obtain ⟨M, hM, hk⟩ := key
  have e : ((Attention.matrices S i).map fixed)[μ]? = some (fixed M) := by
    rw [Array.getElem?_map, hM]
    rfl
  rw [Meaning.getD_of e, fixed_kind, hk]

theorem qa_kind (S : Attention.Shape) (i : Attention.In) :
    (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 3) {}).kind = 1 ∧
      (((Attention.matrices S i).map fixed).getD (S.cf.NAs + 3) {}).foreign = some 0 := by
  have e : ((Attention.matrices S i).map fixed)[S.cf.NAs + 3]? =
      some (fixed { name := "qa", m := S.cf.wcQ * S.T, k := S.fillQ / S.cf.wcQ, kind := 1,
                    foreign := some 0, aId := i.midQ, wp := i.wpq }) := by
    rw [Array.getElem?_map, matrices_qa]
    rfl
  rw [Meaning.getD_of e]
  exact ⟨rfl, rfl⟩

/-! ## The join -/

section
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **The first of a layers' plan's matrices that another sub-proof reads is number 6.** -/
theorem px_first (h : publicOf pol KL lay = .ok X) (C : OnBytes.Road.Hd.PublicCore X.P) (h4 : X.p4 = true) (hN : X.NGr = 12) {g : ℕ}
    (hg : g < 12) {hp : Layer.HPlan2} (hgp : X.G[g]? = some hp) : hp.tl.pxMat[0]? = some 6 := by
  obtain ⟨mats, txOf, ft, tl0, Go⟩ := group_at h C h4 hN hg hgp
  have k6 : (mats.getD 6 {}).kind = 0 := by
    rw [Go.kind 6 (by omega), if_neg (by simp)]
  have t6 : (txOf.getD 6 none).isSome = true := by
    rw [Go.tx 6 (by omega), k6]
    rfl
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 t6
  obtain ⟨-, S2, -⟩ := shapeF_names Go.shape (μ := 6) (by rw [Go.size]; omega)
  obtain ⟨-, r2⟩ := S2 k6 i hi
  have ei : i = cntX mats txOf 6 := (shapeF_px Go.shape).2.2 6 (by rw [Go.size]; omega) k6 i hi
  have e0 : cntX mats txOf 6 = cntX mats txOf 0 :=
    cntX_flat mats txOf 0 6 (Nat.zero_le _) fun k _ hk => by
      unfold isPX
      rw [Go.tx k (by omega)]
      have a7 : (k == 7) = false := beq_false_of_ne (by omega)
      have a6 : (k == 6) = false := beq_false_of_ne (by omega)
      rw [a7, a6]
      simp
  have z : cntX mats txOf 0 = 0 := rfl
  rw [ei, e0, z, ← Go.same.pxMat] at r2
  exact r2

/-- **The names' tie at the attention segments, over a list of links that bears the plans at their places.** -/
theorem names_at_att (h : publicOf pol KL lay = .ok X) (C : OnBytes.Road.Hd.PublicCore X.P) (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hA : ∀ g, g < 12 → ∃ a, X.A[g]? = some a ∧ a.S = OnBytes.Road.Hd.shapeA X g) {l₀ : Array LinkH} {ws : WsLay} {first : Params.First}
    {B : LinksH}
    (hlE : ∀ g hp, g < 12 → X.G[g]? = some hp → ∃ Y, l₀[2 * g]? = some Y ∧ Y.tl = hp.tl)
    (hlO : ∀ g a, g < 12 → X.A[g]? = some a → ∃ Y, l₀[2 * g + 1]? = some Y ∧ Y.tl = a.seam.tl)
    (hB : buildLinksH l₀ X.NGr X.p4 ws first = .ok B) {g : ℕ} (hg : g < 12) {μ : ℕ}
    (hμ : μ < (_root_.Meaning.sizesOf X (2 * g + 1)).NM) :
    ((B.links.map (·.arrayOf)).getD (2 * g + 1) #[])[(tlAt X (2 * g + 1)).gtTree.getD μ 0]? =
      some (ownerK (labAt X (2 * g + 1) μ), nameOf (ownerA (labAt X (2 * g + 1) μ))) := by
  obtain ⟨i6, _, _⟩ := Meaning.ix_of_core h C
  obtain ⟨a, ha, eS⟩ := hA g hg
  obtain ⟨_, _, n1, _⟩ := Meaning.matsAt_att_gid h C hg
  have nA : a.S.cf.NAs = 1 := by rw [eS]; exact n1
  have hk : 2 * g + 1 < 25 := by omega
  have hμm : μ < (matsAt X (2 * g + 1)).size := by
    rw [← (Meaning.follows_of_core h C).NM _ hk]
    exact hμ
  have hμ5 : μ < 5 := by
    rw [Meaning.size_odd h C hg] at hμm
    exact hμm
  have etl : tlAt X (2 * g + 1) = a.seam.tl := by
    unfold Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, ha]
    rfl
  obtain ⟨Y, hY, eY⟩ := hlO g a hg ha
  obtain ⟨declared, hd⟩ := built_declared hB
  obtain ⟨ar, har, N1, -, N3⟩ := declared_names hd hY
  have eL : (B.links.map (·.arrayOf)).getD (2 * g + 1) #[] = ar := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, har]
    rfl
  rw [eY] at N1 N3
  obtain ⟨i, f, tl0, hsh, same⟩ := planA_names h ha
  have hsz : ((Attention.matrices a.S i).map fixed).size = 5 := by
    rw [Array.size_map, Meaning.matrices_size, nA]
  have ol := Meaning.owner_label h C hk hμm
  obtain ⟨S1, -, S3⟩ := shapeF_names hsh (μ := μ) (by rw [hsz]; exact hμ5)
  rw [← same.ix, ← same.gtTree, ← same.pkMat] at S1
  rw [← same.ix, ← same.gtTree] at S3
  rw [eL, etl]
  by_cases hc : μ = 4
  · subst hc
    obtain ⟨k1, kf⟩ := qa_kind a.S i
    rw [nA] at k1 kf
    obtain ⟨f1, _⟩ := S3 k1 0 kf
    obtain ⟨hp, pl, hgp, p1, p2, p3⟩ := placed_at h h4 (by rw [hN]; exact hg) ha
    obtain ⟨owner, ri, Yo, mu, a1, a2, a3, a4, a5⟩ := N3 _ (mem_zipT f1 p1)
    obtain rfl : g = owner := Option.some.inj (p2.symm.trans a1)
    obtain rfl : hp.tl.pkMat.size = ri := Option.some.inj (p3.symm.trans a2)
    have eLk : layersLink X.p4 g = 2 * g := by
      unfold layersLink
      rw [h4, if_pos rfl]
    rw [eLk] at a3 a5
    obtain ⟨Yo', hYo, eYo⟩ := hlE g hp hg hgp
    obtain rfl : Yo' = Yo := Option.some.inj (hYo.symm.trans a3)
    rw [eYo, Nat.sub_self, px_first h C h4 hN hg hgp] at a4
    obtain rfl : 6 = mu := Option.some.inj a4
    have oo : ownerOf X (2 * g + 1) 4 = (2 * g, 6) := by
      unfold Meaning.ownerOf
      rw [if_neg (by omega), if_pos (by omega), show (2 * g + 1) / 2 = g by omega, n1, if_pos rfl, i6,
        show 2 * g + 1 - 1 = 2 * g by omega]
    rw [oo] at ol
    have eK : ownerK (labAt X (2 * g + 1) 4) = 2 * g := congrArg Prod.fst ol
    have eA : ownerA (labAt X (2 * g + 1) 4) = 6 := congrArg Prod.snd ol
    rw [eK, eA]
    exact a5
  · have k0 : (((Attention.matrices a.S i).map fixed).getD μ {}).kind = 0 := own_kind a.S i (by rw [nA]; omega)
    have t0 : (Array.replicate ((Attention.matrices a.S i).map fixed).size (none : Option ℕ)).getD μ none = none := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    have oo : ownerOf X (2 * g + 1) μ = (2 * g + 1, μ) := by
      unfold Meaning.ownerOf
      rw [if_neg (by omega), if_pos (by omega), show (2 * g + 1) / 2 = g by omega, n1, if_neg (by omega)]
    rw [oo] at ol
    have eK : ownerK (labAt X (2 * g + 1) μ) = 2 * g + 1 := congrArg Prod.fst ol
    have eA : ownerA (labAt X (2 * g + 1) μ) = μ := congrArg Prod.snd ol
    rw [eK, eA]
    obtain ⟨r, r1, r2⟩ := S1 k0 t0
    exact N1 _ (mem_zipT r1 r2)

end

/-! ## In scope, at an opening -/

section
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE NAMES' TIE AT THE ATTENTION SEGMENTS, IN THE GOALS' SCOPE, WHERE THE PUBLIC PART IS COMPUTED.** -/
theorem names_tie_att_plain (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) {g : ℕ} (hg : g < 12) {μ : ℕ}
    (hμ : μ < (_root_.Meaning.sizesOf Z.p.X (2 * g + 1)).NM) :
    ((Z.p.built.links.map (·.arrayOf)).getD (2 * g + 1) #[])[(Meaning.tlAt Z.p.X
        (2 * g + 1)).gtTree.getD μ 0]? =
      some (ownerK (labAt Z.p.X (2 * g + 1) μ), nameOf (ownerA (labAt Z.p.X (2 * g + 1) μ))) := by
  have hpub : publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public hZ
  obtain ⟨k4, kN, _, hA⟩ := Meaning.scope_plans hS hR hpub
  have C := OnBytes.Road.Hd.core_of_scope hS hR hpub
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Pb.pol ly Pb.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [k4] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  have both : ∀ g' hp a, g' < 12 → Z.p.X.G[g']? = some hp → Z.p.X.A[g']? = some a →
      (∃ Y, l₀[2 * g']? = some Y ∧ Y.tl = hp.tl) ∧ ∃ Y, l₀[2 * g' + 1]? = some Y ∧ Y.tl = a.seam.tl := by
    intro g' hp a _ hgp ha
    have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
        ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
           run := ProofFile.Plain.notToBeRun } : SubPlanH))[g']? =
        some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
               run := ProofFile.Plain.notToBeRun } := by
      rw [Array.getElem?_map, hgp]
      rfl
    have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
        ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
           run := ProofFile.Plain.notToBeRun } : SubPlanH))[g']? =
        some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
               run := ProofFile.Plain.notToBeRun } := by
      rw [Array.getElem?_map, ha]
      rfl
    obtain ⟨q0, q1⟩ := p0 g' _ _ s0 t0
    exact ⟨⟨_, q0, rfl⟩, ⟨_, q1, rfl⟩⟩
  refine names_at_att hpub C k4 kN hA (fun g' hp hg' hgp => ?_) (fun g' a hg' ha => ?_) hB hg hμ
  · obtain ⟨a, ha, _⟩ := hA g' hg'
    exact (both g' hp a hg' hgp ha).1
  · obtain ⟨hp, hgp⟩ := Meaning.planG_there hpub C hg'
    exact (both g' hp a hg' hgp ha).2

/-- The same at an opening. -/
theorem names_tie_att (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {μ : ℕ}
    (hμ : μ < (_root_.Meaning.sizesOf Z.p.X (2 * g + 1)).NM) :
    ((Z.p.built.links.map (·.arrayOf)).getD (2 * g + 1) #[])[(Meaning.tlAt Z.p.X
        (2 * g + 1)).gtTree.getD μ 0]? =
      some (ownerK (labAt Z.p.X (2 * g + 1) μ), nameOf (ownerA (labAt Z.p.X (2 * g + 1) μ))) :=
  names_tie_att_plain hS hR O.pub hg hμ

end

end H2K5.Names

#print axioms H2K5.Names.owners_placed
#print axioms H2K5.Names.planA_names
#print axioms H2K5.Names.placed_at
#print axioms H2K5.Names.own_kind
#print axioms H2K5.Names.qa_kind
#print axioms H2K5.Names.px_first
#print axioms H2K5.Names.names_at_att
#print axioms H2K5.Names.names_tie_att_plain
#print axioms H2K5.Names.names_tie_att
