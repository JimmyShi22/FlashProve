-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ArmPlanesHost.lean: THE OUTPUT HEAD's HALF OF THE PREMISE hArm AT THE RUN
"planes": THE CLAUSE hHostC (PlanesLeft5, Johnson/Desc/K1/Law/ArmPlanesLen.lean: the three clauses
`K3HostPlanes` in the world of the committed data behind the sending of the head's reads), FROM THE
TIE OF THE APPROXIMATE RANGE PROOF at the state behind. Statements with their proofs; nothing is
evaluated.

CAN THE CLAUSE BE MET AT EVERY WITNESS THAT MEETS THE TIE? YES, under the sentences named below: the
tie's third clause speaks of EVERY table of the closed list, the planes' three among them: so the
entries of the array of the reads at these tables are the reads in truth of the integers behind the
symbols (`readsAll_of_tie_cells`, `k6_host_planes`); and by the tie's first two
clauses these integers, at the planes' matrix, are the ones that the stated function reads off the
data in front (`own_of_packs`), where that matrix's symbol array bears its label and rides.

  `packs_at`   `packs_in_front` (Johnson/Desc/Kinds/Law/FourRunsTie.lean) with a
      letter for the columns in the place of the four ranges': its proof, word for word
  `planesLeft5_of_tie`   **the clause**, at letters

THE PREMISES THAT STAY, EACH SMALLER THAN THE CLAUSE: none reads the tie or the reads' entries:
  hthere   the ledger in front has an array at the number of the array of the reads
  hheard   what the head's hearing holds of the lookup on the calls is what the lookup heard
  hsh      what the lookup heard has the public parameters' shape
  hlabP    the part's list of arrays names the planes' matrix's symbol array by the matrix's label
  hrideP   the cells of that array are read alike in the committed data behind and in front
(hlabP and hrideP are the clauses hlab and hride of the four runs, at one matrix more.)
harr, hwide, hCome, htie, hA, hArr: as in `armCellIn_K6_of_tie`; inside the fence they have payers.

What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmPlanesLen
import Johnson.Desc.Kinds.Law.FourRunsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Sound (dataQ worldOwn)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders planesAt_readers)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff p8K6 nuK6 readsOf TablesCome
  own_of_packs k6_host_planes k6_numbers k6_NM k6_places_below k6_mats_below tables_pos symD)
open _root_.Meaning.Reads (cellA cellZ tie_named readsAll_of_tie_cells)
open OnBytes.Tie.Pv.Tail (Port.u3Of)

/-- The tie's first two clauses, read in the data in front of the sending, in the columns Cols. -/
theorem packs_at (Cols : ℕ → ℕ → Prop) (X : Verify.Public) (D : K9L.Bound Cb.Gl.E) {tl : HTailF2}
    (hm : tl.mats = X.H.tl.mats) (hNM : tl.NM = X.H.tl.NM) {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (htie : First.K8.TieOf tl A)
    (hsym : ∀ μ c i', μ < X.H.tl.NM → c < (_root_.Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((_root_.Meaning.sizesOf X 24).m μ) → Cols μ c →
      A (tl.gtTree.getD μ 0) i' c =
        D.cell (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ))
          (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ))) i' c) :
    (∀ (μ : Fin (_root_.Meaning.sizesOf X 24).NM) (c : Fin ((_root_.Meaning.sizesOf X 24).k μ)),
      Cols μ.val c.val → ∀ i : Fin ((_root_.Meaning.sizesOf X 24).m μ),
        |cellZ tl A μ.val i.val c.val| < 2 * ((_root_.Meaning.sizesOf X 24).beta : Int)) ∧
    (∀ (μ : Fin (_root_.Meaning.sizesOf X 24).NM) (c : Fin ((_root_.Meaning.sizesOf X 24).k μ)),
      Cols μ.val c.val → ∀ i' : Fin (Alg.symRows ((_root_.Meaning.sizesOf X 24).m μ)),
        D.cell (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ.val))
            (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ.val)))
            i'.val c.val =
          ((Alg.pack ((_root_.Meaning.sizesOf X 24).rad : Int)
            (fun i : Fin ((_root_.Meaning.sizesOf X 24).m μ) => cellZ tl A μ.val i.val c.val) i' :
            Int) : Cb.Gl.E)) := by
  obtain ⟨g1, g2, _⟩ := tie_named htie
  have em : tl.mats = (_root_.Meaning.tlAt X 24).mats := by
    rw [hm, Kinds.Head.Law.Came.tlAt_head]
  have eN : tl.NM = (_root_.Meaning.tlAt X 24).NM := by rw [hNM, Kinds.Head.Law.Came.tlAt_head]
  rw [em, eN] at g1 g2
  have eN' : (_root_.Meaning.tlAt X 24).NM = X.H.tl.NM := by rw [Kinds.Head.Law.Came.tlAt_head]
  refine ⟨fun μ c _ i => g1 μ.val μ.isLt c.val c.isLt i.val i.isLt, fun μ c hc i' => ?_⟩
  rw [← hsym μ.val c.val i'.val (eN' ▸ μ.isLt) c.isLt i'.isLt hc]
  exact g2 μ.val μ.isLt c.val c.isLt i'.val i'.isLt

/-- **The clause hHostC, from the tie.** -/
theorem planesLeft5_of_tie {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (hX : Verify.publicOf pol KL lay = .ok X) (own own' : List (ℕ × ℕ)) (s s' : S)
    (a b : K9.Part) (rdW : ℕ × ℕ → Sound.MsgQ) (harr : b.L.arrayOf = a.L.arrayOf)
    (hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → X.H.nU.getD 2 0 ≤ tr.K)
    (hthere : ∀ e F, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      ∃ tr, F.trees[readsOf X]? = some tr)
    (hCome : TablesCome X s s') {Wt : Type} (A : Wt → ℕ → ℕ → ℕ → Cb.Gl.E) (w : Wt)
    (htie : First.K8.TieAt A s' w)
    (hA : ∀ t c r i, b.L.arrayOf[t]? = some c → A w t r i = (dataQ own' b rdW).cell c.1 c.2 r i)
    (cU : ℕ × String) (hArr : a.L.arrayOf[readsOf X]? = some cU)
    (hheard : ∀ (o : HeadOwn) x gk, s.here = .head o → o.x = some x → s.lookHeard? = some gk →
      x.g1 = gk)
    (hsh : ∀ gk, s.lookHeard? = some gk → gk.shape = X.HLy.fs)
    (hlabP : a.L.arrayOf[X.H.tl.gtTree.getD (X.hS.NHf + 2) 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 (X.hS.NHf + 2)),
        _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 (X.hS.NHf + 2)))))
    (hrideP : ∀ c i', c < (_root_.Meaning.sizesOf X 24).k (X.hS.NHf + 2) →
      i' < Alg.symRows ((_root_.Meaning.sizesOf X 24).m (X.hS.NHf + 2)) →
      (dataQ own' b rdW).cell (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 (X.hS.NHf + 2)))
          (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 (X.hS.NHf + 2))))
          i' c =
        (dataQ own a rdW).cell (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 (X.hS.NHf + 2)))
          (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 (X.hS.NHf + 2))))
          i' c) :
    PlanesLeft5 X own own' s a b rdW := by
  refine ⟨fun e r gk he hr hgk => ?_⟩
  obtain ⟨tl, htl, ht⟩ := htie
  obtain ⟨a0, cov, x0, t0, hs0, hop, hcov, hx0, ht0, rfl⟩ := (withTables_iff _ _ _).1 he
  obtain ⟨e2, e4, e3, e11, e10⟩ := hCome _ _ t0 tl he rfl rfl htl
  have hF : ({ s with here := .head { a0 with t := some t0 } } : S).fork? = some a0.F := by
    simp [S.fork?, hop]
  obtain ⟨tr, htr⟩ := hthere _ a0.F he hF
  have hK := hwide _ a0.F tr he hF htr
  have hpos : 0 < X.H.nU.getD 2 0 := tables_pos ht0
  have hK0 : tr.K ≠ 0 := by omega
  have hgk' : s.lookHeard? = some gk := by
    have e0 : ({ s with here := .head { a0 with t := some t0 } } : S).lookHeard? =
        s.lookHeard? := by
      simp [S.lookHeard?, hs0]
    rw [← e0]
    exact hgk
  obtain rfl : x0.g1 = gk := hheard a0 x0 gk hs0 hx0 hgk'
  have hr' := planesAt_readers (readsOf X)
    (s := ({ s with here := .head { a0 with t := some t0 } } : S)) rfl hF rfl htr hK0
  obtain rfl := Option.some.inj (hr.symm.trans hr')
  obtain ⟨hm, hk⟩ := k6_numbers hX (hsh _ hgk')
  have hix : Port.u3Of tl = readsOf X := by
    unfold Port.u3Of
    rw [e11]
    rfl
  have hNM4 : X.hS.NHf + 4 ≤ tl.NM := by rw [e3, k6_NM hX]
  have he : ∀ pos < tr.K, (worldOwn b [] (dataQ own' b rdW)).entry (Port.u3Of tl) 0 pos =
      A w (Port.u3Of tl) 0 pos := by
    intro pos _
    rw [hix]
    show (match b.L.arrayOf[readsOf X]? with
      | some q => (dataQ own' b rdW).cell q.1 q.2 0 pos
      | none => 0) = _
    rw [harr, hArr]
    exact (hA _ cU 0 pos (by rw [harr]; exact hArr)).symm
  have hAll := readsAll_of_tie_cells ht tr.K (k6_places_below ht0 tl e2 e4 hK)
    (fun f hf _ => k6_mats_below ht0 tl e2 hNM4 f hf) (worldOwn b [] (dataQ own' b rdW)).entry he
  have eK : ((a0.F.trees[readsOf X]?).map (·.K)).getD 1 = tr.K := by
    rw [htr]
    rfl
  rw [e4, e2, hix, ← eK] at hAll
  have hμ : X.hS.NHf + 2 < (_root_.Meaning.sizesOf X 24).NM := by
    show _ < (_root_.Meaning.tlAt X 24).NM
    rw [Kinds.Head.Law.Came.tlAt_head, k6_NM hX]
    omega
  obtain ⟨p1, p2⟩ := packs_at (fun μ _ => μ = X.hS.NHf + 2) X (dataQ own a rdW) e4 e3 ht
    (fun μ c i' _ hk' hi hcol => by
      subst hcol
      rw [e10, hA _ _ i' c (by rw [harr]; exact hlabP)]
      exact hrideP c i' hk' hi)
  have h4 : ∀ r < 2 ^ X.hS.lmbH, ∀ c < _root_.Fo.planeCols x0.g1.shape X.hS.lmbH,
      cellA tl (A w) (X.hS.NHf + 1 + 1) r c = nuK6 X s (dataQ own a rdW) (.cell r c) := by
    intro r hr c hc
    have hc' : c < (_root_.Meaning.sizesOf X 24).k (X.hS.NHf + 2) := by
      show c < ((_root_.Meaning.tlAt X 24).mats.getD (X.hS.NHf + 2) {}).k
      rw [Kinds.Head.Law.Came.tlAt_head]
      exact Nat.lt_of_lt_of_le hc hk
    have hr' : r < (_root_.Meaning.sizesOf X 24).m (X.hS.NHf + 2) := by
      show r < ((_root_.Meaning.tlAt X 24).mats.getD (X.hS.NHf + 2) {}).m
      rw [Kinds.Head.Law.Came.tlAt_head]
      by_contra hcon
      have hlt : (X.H.tl.mats.getD (X.hS.NHf + 1 + 1) {}).m < 2 ^ X.hS.lmbH := by
        have h0 : (X.H.tl.mats.getD (X.hS.NHf + 2) {}).m ≤ r := Nat.le_of_not_lt hcon
        exact Nat.lt_of_le_of_lt h0 hr
      rw [Nat.div_eq_of_lt hlt] at hm
      cases hm
    show ((cellZ tl (A w) (X.hS.NHf + 2) r c : ℤ) : Cb.Gl.E) =
      ((_root_.Meaning.ownOf (_root_.Meaning.sizesOf X)
        (symD X (_root_.Meaning.sizesOf X) (dataQ own a rdW)) 24 (X.hS.NHf + 2) r c : Int) :
        Cb.Gl.E)
    rw [own_of_packs X _ (cellZ tl (A w)) ⟨X.hS.NHf + 2, hμ⟩ ⟨c, hc'⟩ (p1 ⟨_, hμ⟩ ⟨c, hc'⟩ rfl)
      (p2 ⟨_, hμ⟩ ⟨c, hc'⟩ rfl) ⟨r, hr'⟩]
  exact k6_host_planes Reading.gl ht0 hm hk _ h4 _ hAll

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.packs_at
#print axioms VerifiableInference.Desc.K1.planesLeft5_of_tie
