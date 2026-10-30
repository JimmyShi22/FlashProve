-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmAttMats.lean: THE FIELD hM OF THE ATTENTION LINKS' HALF OF THE EXCHANGE (AttLeft2,
Johnson/Desc/K1/Law/ArmAttEntry.lean: "small integers that pack to the committed symbols behind the second
commitment are the matrices made of the data in front of it") IS NO PREMISE ON THE WITNESS: it follows from
its own antecedents, under ONE clause on the state in front and one sentence on letters.
OBJECT: `Sound.matsOfData` (Johnson/Desc/Sound/DataMats.lean) at `dataQ (N.sent l 0) A (seatTab … w)`.
USER: whoever calls arm_at_reads | arm_at_reads_three.
  `matsOfData_of_packs`   general: in a column to whose symbols, read in the data, small integers pack, the
                   matrices made of the data are these (the library's `Cb.Pv.Tail.packs_unique`,
                   `packs_cellsOf`, `OnBytes.Tie.Pv.Tail.sizeOf_uniq`: as own_of_packs,
                   Johnson/Desc/Kinds/Law/FourRunsTie.lean, has it at its own letters)
  `cell_back`        a cell of an array that is seated in front, read behind through the longer list of seats,
                   is the cell in front (`cell_wider`; `Sound.cell_rides`)
  `tlLike_over_reads`   over an accept at an attention link's reads the parameters stay alike (
                   `K5Law.block4_closes`; `K8.Order.close_lays`)
  `SymsIn own a tl`  THE CLAUSE, A TEST WITH CODE ON THE PART IN FRONT: every symbol array of tl's matrices is
                   named in the link's list, laid in the layout, sent, and seated at a seat of own
                   (`K9.arrayIn`)
  `attLeft2_of`      **the field hM**: AttLeft2 from hin and SymsIn, behind the fence, under hsub (on letters: the
                   first commitment's seats are among the group's)
  `JAtt W N s`       what stays of the attention links' half, a clause for the letter J, on the state in front
                   alone: hin · SymsIn
  `hAtt2_ofJ'` | `hAtt2_ofJ`   **THE FIELD hAtt'' of k01_fifty_paid (K01FiftyPaid.lean),
                   IN ITS OWN TYPE** (its text taken by program), under hJa, hsub
  `hAtt_ofJ'` | `hAtt_ofJ`   **the premise hAtt of arm_at_reads, to the letter: no pointwise premise of its own
                   stays**: under hJt hJl hJa (three clauses of J) and hW hSec hsub (on letters)
What is not claimed. SymsIn at any state. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmAttEntry
import Johnson.Desc.Kinds.Law.FourRunsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S AttOwn)
open VerifiableInference.Desc.First.Look (szOf cellJ)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ matsOfData symOfData dataByAddr)
open VerifiableInference.Desc.K9L (Bound)

/-- **In a column to whose symbols, read in the data, small integers pack, the matrices made of the data
are these.** -/
theorem matsOfData_of_packs (tl : HTailF2) (arrayOf : Array (ℕ × String)) (D : Bound GQ)
    (aI : ℕ → ℕ → ℕ → ℤ) (μ r c : ℕ) (hμ : μ < tl.NM) (hr : r < (tl.mats.getD μ {}).m)
    (hc : c < (tl.mats.getD μ {}).k)
    (h1 : ∀ i, i < (tl.mats.getD μ {}).m → |aI μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ))
    (h2 : ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
      dataByAddr arrayOf D (.cell (tl.gtTree.getD μ 0) i' c) =
        ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => aI μ i c) i' : ℤ) : GQ)) :
    matsOfData tl arrayOf D μ r c = ((aI μ r c : ℤ) : GQ) := by
  have hj : μ < (szOf tl).NM ∧ c < (szOf tl).k μ ∧ r < (szOf tl).m μ := ⟨hμ, hc, hr⟩
  have ha : Cb.Pv.Tail.Packs (Cb.Pv.Tail.symL GQ (szOf tl)) (symOfData tl arrayOf D) ⟨μ, hj.1⟩
      ⟨c, hj.2.1⟩ (fun i => aI μ i.val c) :=
    ⟨fun i => h1 i.val i.isLt, fun i' => h2 i'.val i'.isLt⟩
  have e := Cb.Pv.Tail.packs_unique (Cb.Pv.Tail.symL GQ (szOf tl)) Cb.Gl.p
    (OnBytes.Tie.Pv.Tail.sizeOf_uniq tl) (fun _ => rfl) ha
    (Cb.Pv.Tail.packs_cellsOf (Cb.Pv.Tail.symL GQ (szOf tl)) ⟨_, ha⟩)
  unfold matsOfData cellJ
  rw [dif_pos hj]
  show ((Cb.Pv.Tail.cellsOf (Cb.Pv.Tail.symL GQ (szOf tl)) (symOfData tl arrayOf D) ⟨μ, hj.1⟩
    ⟨c, hj.2.1⟩ ⟨r, hj.2.2⟩ : ℤ) : GQ) = _
  rw [← congrFun e ⟨r, hj.2.2⟩]

/-- Every symbol array of tl's matrices is named, laid, sent and seated at a seat of own. -/
def SymsIn (own : List (ℕ × ℕ)) (a : K9.Part) (tl : HTailF2) : Prop :=
  ∀ μ, μ < tl.NM → (K9.arrayIn own a (tl.gtTree.getD μ 0)).isSome = true

/-- A cell of an array that is seated in front, read behind through a longer list of seats, is the cell
in front. -/
theorem cell_back (own own' : List (ℕ × ℕ)) (hsub : ∀ x ∈ own, x ∈ own') (a b : K9.Part)
    (rd : ℕ × ℕ → MsgQ) (hR : Sound.Rides own a b) (t : ℕ)
    (hin : (K9.arrayIn own a t).isSome = true) :
    ∃ cn, a.L.arrayOf[t]? = some cn ∧ ∀ r i,
      (dataQ own' b rd).cell cn.1 cn.2 r i = (dataQ own a rd).cell cn.1 cn.2 r i := by
  obtain ⟨Ar, hAr⟩ := Option.isSome_iff_exists.1 hin
  obtain ⟨cn, o, x, h1, h2, h3, h4⟩ := K9.arrayIn_some own a t Ar hAr
  refine ⟨cn, h1, fun r i => ?_⟩
  exact (Kinds.Head.Law.cell_wider own own' hsub b rd cn Ar o x (by rw [hR.rows]; exact h2)
      (hR.sent _ _ _ h3) (K9.seatAt_rides own a.d.book b.d.book o x (hR.book o) h4) r i).trans
    (Sound.cell_rides own a b rd hR cn Ar o x h2 h3 h4 r i)

/-! ## Over the reads' accept -/

section
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K8.ReadsQuiet (layers_ok head_ok)
open OnBytes.Model.Stages (LinkH)

theorem TlLike.trans {t t' t'' : HTailF2} (h : TlLike t t') (k : TlLike t' t'') : TlLike t t'' :=
  ⟨k.NM.trans h.NM, k.mats.trans h.mats, k.ix.trans h.ix, k.gtTree.trans h.gtTree⟩

/-- **Over an accept at an attention link's reads the parameters stay alike.** -/
theorem tlLike_over_reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (hX : G.built[l]? = some X) (pr : ℕ) (reads : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') (a₀ : AttOwn)
    (hs : s.here = .att a₀) : ∃ tl', s'.tl? = some tl' ∧ TlLike a₀.tl tl' := by
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes _ _ _ _ _ (IM.k1Quiet G l X) s s' r₁ r₂ gs h
  obtain ⟨_, F, _, y, _, _, _, e, _⟩ := commitAtS_slots h1
  have hs₁ := K5Law.here_commit hs y.w y.L y.F
  rw [← e] at hs₁
  have hk : ∃ z : Block S Unit, First.Att.readsAtO G.W l X.g = some z ∧ IM.k1Quiet G l X = z := by
    revert h3
    unfold IM.k1Quiet
    dsimp only
    cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
    | none => exact fun h => nomatch h
    | some q =>
      intro h3
      have h3' : q.decide s₁ rs₂ gs₂ = .ok s' := h3
      rcases readsQuietAt_cases hq with hz | hz
      · exact ⟨q, hz, rfl⟩
      · exfalso
        rcases blockAt_cases hX hz with ⟨hp, hg, rfl⟩ | rfl
        · obtain ⟨a', own, tl', ha', _⟩ := layers_ok h3'
          rw [hs₁] at ha'
          cases ha'
        · obtain ⟨a', cov, x, t, tl', ha', _⟩ := head_ok h3'
          rw [hs₁] at ha'
          cases ha'
  obtain ⟨z, hz, ez⟩ := hk
  have hz' := hz
  unfold First.Att.readsAtO at hz'
  obtain ⟨Ap, hAp, _⟩ := Option.map_eq_some_iff.1 hz'
  have hw : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).andThen
      (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).name (IM.k1Quiet G l X)).decide s
      [r₁, r₂] gs = .ok s' := h
  rw [ez] at hw
  obtain ⟨tl', funs, e1, hc⟩ :=
    K5Law.block4_closes G.first (gpOf Z) l pr 1 reads _ G.W l X.g _ hz hAp hw hs
  refine ⟨tl', e1, ?_⟩
  rw [First.K8.Order.close_lays a₀.tl tl' funs hc]
  exact ⟨rfl, rfl, rfl, rfl⟩

end

/-! ## The field hM -/

open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn linkNo ArmCellIn cellsAt cellsAt_name)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.First.Att.P (plannedK inOf seatCO parCOf)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **AttLeft2 from hin and SymsIn.** -/
theorem attLeft2_of {J : S → Prop} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {c : Chain S Cl} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S}
    {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B)
    (hsub : ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) {a₀ : AttOwn} {Ap : Attention.Plan}
    {tl' : HTailF2} (hs : x.2.here = .att a₀) (hL : TlLike Ap.seam.tl a₀.tl)
    (htl : x'.2.tl? = some tl') {i : First.Att.P.Runs.In}
    (hin : inOf (seatCO (parCOf Ap)) (parCOf Ap) x.2 = some (i, plannedK Ap))
    (hSy : SymsIn (Dm.N.sent l 0) A Ap.seam.tl) :
    AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) := by
  refine ⟨hin, fun aI hb hsy μ r cn hμ hr hc => ?_⟩
  obtain ⟨_, rs, gs, hfit, hd⟩ := Fc.yes
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨tl₂, e2, L2⟩ := tlLike_over_reads Z Bs.G₀ l X Fc.built _ arrs x.2 x'.2 _ gs hlen hd a₀ hs
  obtain rfl : tl₂ = tl' := Option.some.inj (e2.symm.trans htl)
  have L := hL.trans L2
  have hr' := rides_at_reads Fc
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some Fc.front
  have harr : ((x.2.link?.map (·.arrayOf)).getD #[]) = A.L.arrayOf := by rw [hLa]; rfl
  rw [harr]
  rw [L.NM] at hμ
  rw [L.mats] at hr hc
  refine matsOfData_of_packs Ap.seam.tl A.L.arrayOf _ aI μ r cn hμ hr hc (fun i hi => ?_)
    fun i' hi' => ?_
  · exact hb μ (by rw [L.NM]; exact hμ) cn (by rw [L.mats]; exact hc) i (by rw [L.mats]; exact hi)
  · obtain ⟨nm, hn, hcell⟩ := cell_back (Dm.N.sent l 0) (Dm.N.group l) hsub A B
      (seatTab Dm.cs Dm.arr Dm.ms w) hr' _ (hSy μ hμ)
    have h0 := hsy μ (by rw [L.NM]; exact hμ) cn (by rw [L.mats]; exact hc) i'
      (by rw [L.mats]; exact hi')
    rw [L.gtTree, L.mats] at h0
    show (match A.L.arrayOf[Ap.seam.tl.gtTree.getD μ 0]? with
      | some b => (dataQ (Dm.N.sent l 0) A (seatTab Dm.cs Dm.arr Dm.ms w)).cell b.1 b.2 i' cn
      | none => 0) = _
    rw [hn]
    dsimp only
    rw [← hcell, ← h0]
    exact (cellsAt_name Dm.cs Dm.arr Dm.ms Dm.N l x'.1 x'.2 w B Fc.behind _ nm
      (by rw [hr'.arrays]; exact hn) i' cn).symm

/-- **WHAT STAYS OF THE ATTENTION LINKS' HALF, A CLAUSE FOR THE LETTER J**: on the state in front alone: the
claims' seat's reading returns, at the plan's number of columns; the symbol arrays are seated. -/
def JAtt (W : Verify.Public) (N : Numbers) (s : S) : Prop :=
  ∀ a₀ Ap A, s.here = .att a₀ → W.A[linkNo s / 2]? = some Ap → K9.segAt? s = some A →
    (∃ i, inOf (seatCO (parCOf Ap)) (parCOf Ap) s = some (i, plannedK Ap)) ∧
      SymsIn (N.sent (linkNo s) 0) A Ap.seam.tl

/-- **THE FIELD hAtt'' OF k01_fifty_paid, IN ITS OWN TYPE**, at a letter Mg₀. -/
theorem hAtt2_ofJ' (J : S → Prop) (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (c : Chain S Cl) (hJa : ∀ s, J s → JAtt XV Dm.N s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc _ a₀ Ap tl' hs hA hL htl
  have hno : linkNo x.2 = l :=
    linkNo_of_promise Dm dk Mg₀ hM l Fc.lt x y (inAt_down _ _ _ _ _ _ _ _ _ Fc.inAt) A Fc.front
  obtain ⟨⟨i, hin⟩, hSy⟩ := hJa _ Fc.inv a₀ Ap A hs (by rw [hno]; exact hA) Fc.front
  rw [hno] at hSy
  exact ⟨i, attLeft2_of Dm dk Mg₀ Fc (hsub l Fc.lt) hs hL htl hin hSy⟩

/-- **THE FIELD hAtt'' OF k01_fifty_paid, IN ITS OWN TYPE.** -/
theorem hAtt2_ofJ (J : S → Prop) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (c : Chain S Cl)
    (hJa : ∀ s, J s → JAtt XV Dm.N s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) :=
  hAtt2_ofJ' Dm dk mgBase J rfl Z Bs c hJa aN R₁ R₂ R₃ hsub

/-- **The premise hAtt of arm_at_reads_of: no pointwise premise of its own stays.** -/
theorem hAtt_ofJ' (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJt : ∀ s, J s → TlIsPlan XV s) (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hJa : ∀ s, J s → JAtt XV Dm.N s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) :=
  hAtt_of2' Dm dk Mg₀ J hM hS hR O hWX hJt shp lay₀ hJl aN R₁ R₂ R₃ hW hSec
    (hAtt2_ofJ' Dm dk Mg₀ J hM Z Bs c hJa aN R₁ R₂ R₃ hsub)

/-- **THE PREMISE hAtt OF arm_at_reads, TO THE LETTER: NO POINTWISE PREMISE OF ITS OWN STAYS.** -/
theorem hAtt_ofJ (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJt : ∀ s, J s → TlIsPlan XV s) (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hJa : ∀ s, J s → JAtt XV Dm.N s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) :=
  hAtt_ofJ' Dm dk mgBase J rfl hS hR O hWX hJt shp lay₀ hJl hJa aN R₁ R₂ R₃ hW hSec hsub

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.matsOfData_of_packs
#print axioms VerifiableInference.Desc.K1.cell_back
#print axioms VerifiableInference.Desc.K1.tlLike_over_reads
#print axioms VerifiableInference.Desc.K1.attLeft2_of
#print axioms VerifiableInference.Desc.K1.hAtt2_ofJ'
#print axioms VerifiableInference.Desc.K1.hAtt2_ofJ
#print axioms VerifiableInference.Desc.K1.hAtt_ofJ'
#print axioms VerifiableInference.Desc.K1.hAtt_ofJ
