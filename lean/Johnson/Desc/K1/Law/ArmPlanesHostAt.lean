-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ArmPlanesHostAt.lean: THE CLAUSE hHostC AND THE PREMISE hPl' (PlanesLeft4,
Johnson/Desc/K1/Law/ArmHeadBare.lean) OF THE LAW ON THE SUB-PROTOCOL K1, INSIDE THE FENCE AT THE
OUTPUT HEAD's READS' PLACE: `planesLeft5_of_tie` (ArmPlanesHost.lean, this folder) called there: its
premises paid by what lies (the fence's tie; `rides_at_reads`, `tablesCome_at_reads`,
`arrays_at342`, `wide_at342`, `shape_at342`, `cellsAt_name`, `cell_wider`,
`cell_rides`), or moved to sentences on public data, but for three clauses ON THE STATE IN FRONT: NO
CLAUSE THAT STAYS READS THE WITNESS. Definitions (one structure) and statements with their proofs.

  `there_at342`   the ledger in front has an array wherever the written list of the ledger's arrays
      has one (the public item "ledger.treesAre", as in `wide_at342`)
  `heard_of_look`   where the state's two homes of what the lookup on the calls heard agree, the
      head's hearing holds what the lookup heard
  `ride_at`   `ride_of_seated` (Johnson/Desc/Kinds/Law/FourRunsTie.lean) with a
      letter for the columns in the place of the four ranges': its proof, word for word
  `PlanesLeft6`   WHAT STAYS OF hHostC: three clauses on the verifier's state in front:
      hlk      look? = lookHeard? (it holds behind an accept of the head's
               own sub-protocol: Johnson/Desc/Kinds/Law/RowPins.lean; and stays: PlanesStay.lean)
      hlay     the open segment's rows' layout is lay6
      hMatsP   `MatsSeated` (Johnson/Desc/Kinds/Law/DataSeatedOfLaid.lean) AT THE PLANES' MATRIX
               (number NHf + 2): the four runs' clause at one matrix more
  `planesLeft5_at342`   **hHostC inside the fence**, from PlanesLeft6
  `planesLeft4_at342`   **PlanesLeft4 inside the fence** (hPl''s end), from the same and hLen
ON PUBLIC DATA ALONE (each could be a test with code, or a theorem on the reader of the files):
  hU, hK    the premises hU and hKw of the law · hTh: the written list of segment 24's ledger's
            arrays has an entry at the number of the array of the reads · T: hLaid6
  hShape    the shape of the lookup on the calls at segment 24 is the head's layout's own
  hLabP     segment 24's written list of arrays names the planes' matrix's symbol array by the
            matrix's label

What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmPlanesHost
import Johnson.Desc.K1.Law.ArmHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Strs)
open VerifiableInference.Desc.First (S HeadOwn Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase seatTab dataQ
  cellsAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff p8K6 readsOf TablesCome
  MatsSeated cell_wider k6_NM)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

/-- The ledger in front has an array wherever the written list has one. -/
theorem there_at342 (i : ℕ) (hT : ∃ t, (Dm.pubD.dS.trees 24)[i]? = some t)
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) (P : K8.ReadsQuiet.PH) :
    ∀ e F, withTables P x.2 = some e → e.fork? = some F → ∃ tr, F.trees[i]? = some tr := by
  intro e F he hF
  obtain ⟨a, cov, xx, tt, ha, hop, _, _, _, rfl⟩ := (withTables_iff P x.2 e).1 he
  have e1 : ({ x.2 with here := .head { a with t := some tt } } : S).fork? = x.2.fork? := by
    unfold S.fork?
    rw [ha]
  rw [e1] at hF
  have h0 := pub_at342 Dm dk (.more (some 24) "ledger.treesAre")
    (Bool.and_eq_true_iff.1 open342).2 hIn
  rw [First.pubAll_more_treesAre] at h0
  unfold First.FillSent.treesAreB at h0
  rw [hF] at h0
  have h1 : F.trees.toList.map First.FillSent.treeLook = Dm.pubD.dS.trees 24 := by
    simpa using h0
  obtain ⟨t, ht⟩ := hT
  rw [← h1, List.getElem?_map, Array.getElem?_toList] at ht
  obtain ⟨tr, htr, _⟩ := Option.map_eq_some_iff.1 ht
  exact ⟨tr, htr⟩

end

/-- Where the two homes agree, the head's hearing holds what the lookup heard. -/
theorem heard_of_look {s : S} (hlk : s.look? = s.lookHeard?) :
    ∀ (o : HeadOwn) x gk, s.here = .head o → o.x = some x → s.lookHeard? = some gk →
      x.g1 = gk := by
  intro o x gk ho hx hg
  have h1 : s.look? = some gk := hlk.trans hg
  unfold S.look? at h1
  rw [ho] at h1
  cases hop : o.opened with
  | false =>
    simp [hop] at h1
  | true =>
    simp [hop, hx] at h1
    exact h1

/-- The cells of the symbol arrays of the matrices with a column in Cols are read alike behind,
through a longer list of seats, and in front. -/
theorem ride_at (Cols : ℕ → ℕ → Prop) (X : Verify.Public) (own own' : List (ℕ × ℕ))
    (a b : K9.Part) (rd : ℕ × ℕ → Sound.MsgQ) (hsub : ∀ x ∈ own, x ∈ own')
    (hR : Sound.Rides own a b) (arr : ℕ → ℕ → ℕ) (N : Numbers) (num : ℕ → ℕ → ℕ)
    (lay : ReqLayout) (T : _root_.Meaning.laidThere X (_root_.Meaning.sizesOf X) lay = true)
    (hlay : a.L.check.rows.layout = lay) (hM : MatsSeated Cols arr N X own a num lay) :
    ∀ μ c i', μ < X.H.tl.NM → c < (_root_.Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((_root_.Meaning.sizesOf X 24).m μ) → Cols μ c →
      (dataQ own' b rd).cell (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ))
          (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ))) i' c =
        (dataQ own a rd).cell (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ))
          (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ))) i' c := by
  intro μ c i' hμ hc hi hcol
  have hμ' : μ < (_root_.Meaning.sizesOf X 24).NM := by
    show μ < (_root_.Meaning.tlAt X 24).NM
    rw [Kinds.Head.Law.Came.tlAt_head]
    exact hμ
  obtain ⟨A, rp, hA, _, _, _, _⟩ := _root_.Meaning.seat_of_laidThere T num (k := 24) (by decide)
    (⟨μ, hμ'⟩ : Fin (_root_.Meaning.sizesOf X 24).NM) hi hc
  obtain ⟨o, x, m3, _, m5, _, _⟩ := hM ⟨μ, hμ'⟩ c hc hcol A hA
  subst hlay
  have hAa : OnBytes.reqArray a.L.check.rows.layout
      (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ), _root_.Meaning.nameOf
        (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ))).1
      (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ), _root_.Meaning.nameOf
        (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ))).2 = some A := hA
  exact (cell_wider own own' hsub b rd (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ),
      _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ))) A o x
      (by rw [hR.rows]; exact hAa) (hR.sent _ _ _ m3)
      (K9.seatAt_rides own a.d.book b.d.book o x (hR.book o) m5) i' c).trans
    (Sound.cell_rides own a b rd hR (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 μ),
      _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 μ))) A o x hAa m3 m5
      i' c)

/-- **What stays of hHostC**: three clauses on the verifier's state in front. -/
structure PlanesLeft6 (X : OnBytes.Model.Verify.Public) (own : List (ℕ × ℕ)) (s : S) (a : K9.Part)
    (arr : ℕ → ℕ → ℕ) (N : Numbers) (num : ℕ → ℕ → ℕ) (lay6 : ReqLayout) : Prop where
  hlk : s.look? = s.lookHeard?
  hlay : a.L.check.rows.layout = lay6
  hMatsP : MatsSeated (fun μ _ => μ = X.hS.NHf + 2) arr N X own a num lay6

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **hHostC inside the fence.** -/
theorem planesLeft5_at342 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (J : S → Prop) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds) (cU : ℕ × String) (num6 : ℕ → ℕ → ℕ)
    (lay6 : ReqLayout)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t → XV.H.nU.getD 2 0 ≤ t.2.1)
    (hTh : ∃ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t)
    (hShape : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h = XV.HLy.fs)
    (hLabP : (Dm.pubD.d3.arrayOf.getD 24 #[])[XV.H.tl.gtTree.getD (XV.hS.NHf + 2) 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)),
        _root_.Meaning.nameOf
          (_root_.Meaning.ownerA (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)))))
    {X : Stages.LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S} {y y' : Strs}
    {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B)
    (L : PlanesLeft6 XV (Dm.N.sent 24 0) x.2 A Dm.arr Dm.N num6 lay6) :
    PlanesLeft5 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w) := by
  have hr := rides_at_reads Fc
  have hTC : TablesCome XV x.2 x'.2 := by
    obtain ⟨_, rs, gs, hfit, hd⟩ := Fc.yes
    have hlen : (rs.map noDigest).length = 2 := by
      rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
    rw [← hWX]
    exact tablesCome_at_reads Z Bs.G₀ X Fc.built _ arrs x.2 x'.2 _ gs hlen hd
  have eA := arrays_at342 Dm dk Fc.inAt Fc.front
  obtain ⟨p0, h0, hp0, hs0, hg0⟩ := shape_at342 Dm dk Fc.inAt
  exact planesLeft5_of_tie (hWX ▸ O.public) _ _ x.2 x'.2 A B _ hr.arrays
    (wide_at342 Dm dk _ _ hK Fc.inAt _) (there_at342 Dm dk _ hTh Fc.inAt _) hTC
    (cellsAt Dm.cs Dm.arr Dm.ms Dm.N 24 (x'.1, x'.2)) w Fc.tie
    (fun t c r i hc => Sound.cellsAt_name Dm.cs Dm.arr Dm.ms Dm.N 24 x'.1 x'.2 w B Fc.behind t c hc
      r i)
    cU (by rw [eA]; exact hU) (heard_of_look L.hlk)
    (fun gk hgk => (hg0 gk hgk).trans (hShape p0 h0 hp0 hs0)) (by rw [eA]; exact hLabP)
    (fun c i' hc hi => ride_at (fun μ _ => μ = XV.hS.NHf + 2) XV _ _ A B _
      (fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)) hr Dm.arr Dm.N num6 lay6 T
      L.hlay L.hMatsP _ c i' (by rw [k6_NM (hWX ▸ O.public)]; omega) hc hi rfl)

/-- **PlanesLeft4 inside the fence**: the end of the premise hPl'. -/
theorem planesLeft4_at342 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (J : S → Prop) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds) (cU : ℕ × String) (num6 : ℕ → ℕ → ℕ)
    (lay6 : ReqLayout)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t → XV.H.nU.getD 2 0 ≤ t.2.1)
    (hTh : ∃ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t)
    (hShape : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h = XV.HLy.fs)
    (hLabP : (Dm.pubD.d3.arrayOf.getD 24 #[])[XV.H.tl.gtTree.getD (XV.hS.NHf + 2) 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)),
        _root_.Meaning.nameOf
          (_root_.Meaning.ownerA (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)))))
    (hLen : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h.NC * 2 ^ (h.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH))
    {X : Stages.LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S} {y y' : Strs}
    {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B)
    (L : PlanesLeft6 XV (Dm.N.sent 24 0) x.2 A Dm.arr Dm.N num6 lay6) :
    PlanesLeft4 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w) :=
  planesLeft4_of Dm dk hLen Fc.inAt
    (planesLeft5_at342 Dm dk J O hWX aN R₁ R₂ R₃ cU num6 lay6 T hU hK hTh hShape hLabP Fc L)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.there_at342
#print axioms VerifiableInference.Desc.K1.heard_of_look
#print axioms VerifiableInference.Desc.K1.ride_at
#print axioms VerifiableInference.Desc.K1.planesLeft5_at342
#print axioms VerifiableInference.Desc.K1.planesLeft4_at342
