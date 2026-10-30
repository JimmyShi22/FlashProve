-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmAttPaid.lean: **hAtt_of**: the premise hAtt of arm_at_reads
(Johnson/Desc/K1/Law/ArmAtReads.lean), to the letter, from the like with four of AttRest's eight fields:
hA hNM htab hu3 ARE PAID, by calls. No law of another kind's files is typed.
OBJECT: `AttRest` (Johnson/Desc/K1/Law/ArmHalves.lean) at an attention link's reads.
USER: whoever calls arm_at_reads | arm_at_reads_three.
LETTERS: arm_at_reads's.
  `TlLike t t'`      t' has t's matrices, their number, the numbers of the arrays of reads and of the symbol
                   arrays (four fields)
  `TlIsPlan W s`     ONE CLAUSE FOR THE LETTER J: in an attention link the state's parameters of the
                   approximate range proof are like the plan's. NOT THE EQUATION
                   a₀.tl = Ap.seam.tl (attention's files' htl, Johnson/Desc/First/Att/ArmAttPublic.lean):
                   the link's opening lays { tl₀ with funClosed := false, foldDrawn := 0 }
                   (`attFirstQuiet`, Johnson/Desc/First/Walk/FirstQuiet.lean): that the plan's own two
                   fields are so is said nowhere: the equation might be met by no reached state. What
                   the exchange reads is asked, and no more
  `AttLeft4`         AttRest less hA hNM htab hu3: hin hW hE hM
  `attIsOdd`         [by evaluation] an attention link's number is 2 g + 1, g < 12
  `group_att`        in the goals' scope the built link at an attention link l has the group l / 2
                   (`IM.ground_named`, Johnson/IMR/PureJoin.lean)
  `hAtt_of'` | `hAtt_of`   **the premise hAtt**, at a letter Mg₀ | at mgBase
PAID, BY CALLS: hA (hWX, group_att) · hNM (`K5Law.ofPlan_size` at `K5Law.public_ofPlan` at
`IM.Open.public`) · hu3 (`K5Law.ofPlan_u3Of`) · htab (one term under TlIsPlan).
PREMISES LEFT: hS hR O (the top's own) · hWX : Bs.G₀.W = XV · hJ : ∀ s, J s → TlIsPlan XV s · hAtt' (pointwise,
behind the fence, at one named entry: a letter i with AttLeft4; the plan is handed as XV.A[l / 2]? = some Ap
and the state's parameters as like the plan's).
IS IT EMPTY HERE? NO MEMBER IS SHOWN. TlIsPlan ALONG THE STATES THAT THE VERIFIER REACHES: NOBODY's YET.
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmAtReads
import Johnson.Desc.First.Att.ArmAttPublic
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

section
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ linkNo)
open K5Law (Cov)

/-- t' has t's matrices, their number, the numbers of the arrays of reads and of the symbol arrays. -/
structure TlLike (t t' : HTailF2) : Prop where
  NM : t'.NM = t.NM
  mats : t'.mats = t.mats
  ix : t'.ix = t.ix
  gtTree : t'.gtTree = t.gtTree

/-- **In an attention link the state's parameters of the approximate range proof are the plan's**, as
far as the exchange reads them. -/
def TlIsPlan (W : Verify.Public) (s : First.S) : Prop :=
  ∀ a₀ Ap, s.here = .att a₀ → W.A[linkNo s / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl

theorem TlLike.tabAt {t t' : HTailF2} (h : TlLike t t') (Fn : HFun) (c sg : ℕ) :
    t.tabAt Fn c sg = t'.tabAt Fn c sg := by
  unfold HTailF2.tabAt
  rw [h.NM, h.mats]

theorem TlLike.u3Of {t t' : HTailF2} (h : TlLike t t') :
    OnBytes.Tie.Pv.Tail.Port.u3Of t' = OnBytes.Tie.Pv.Tail.Port.u3Of t := by
  unfold OnBytes.Tie.Pv.Tail.Port.u3Of
  rw [h.ix]

/-- AttRest less hA hNM htab hu3. -/
structure AttLeft4 (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : First.S)
    (a : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (A : Attention.Plan) (i : Runs.In)
    (tl' : HTailF2) (Ac : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop where
  hin : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, plannedK A)
  hW : A.nW ≤ plannedK A
  hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, Cov A.iU3 (plannedK A) A.nW f
  hM : ∀ aI : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k → ∀ i, i < (tl'.mats.getD μ {}).m →
        |aI μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) →
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          Ac (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m => aI μ i c) i' : ℤ) :
              Cb.Gl.E)) →
      ∀ μ r c, μ < tl'.NM → r < (tl'.mats.getD μ {}).m → c < (tl'.mats.getD μ {}).k →
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) (dataQ own a rd) μ r c =
          ((aI μ r c : ℤ) : Cb.Gl.E)

end

open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MsgQ MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn linkNo ArmCellIn)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

theorem attIsOdd : ∀ l < 25, (linksFull[l]?).getD .layers = ModelPart.attention →
    l = 2 * (l / 2) + 1 ∧ l / 2 < 12 := by decide

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- In scope the built link at an attention link l has the group l / 2. -/
theorem group_att {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (l : ℕ) (hl : l < 25) (hsub : (linksFull[l]?).getD .layers = ModelPart.attention) (X : LinkH)
    (hX : Bs.G₀.built[l]? = some X) : X.g = l / 2 := by
  obtain ⟨e, hg⟩ := attIsOdd l hl hsub
  obtain ⟨nam, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨_, l', _, _, _, _, h', _, hg', _⟩ := nam (l / 2) hg
  rw [← e, hX] at h'
  obtain rfl := Option.some.inj h'
  exact hg'

/-- **The premise hAtt of arm_at_reads_of.** -/
theorem hAtt_of' (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJ : ∀ s, J s → TlIsPlan XV s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hAtt' : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttLeft4 (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl'
        (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsub a₀ Ap tlF tl' hs hg htlF htl e cc hN
  have hA : XV.A[l / 2]? = some Ap := by
    rw [← hWX, ← group_att hS hR O l Fc.lt hsub X Fc.built]
    exact hg
  have hno : linkNo x.2 = l :=
    linkNo_of_promise Dm dk Mg₀ hM l Fc.lt x y (inAt_down _ _ _ _ _ _ _ _ _ Fc.inAt) A Fc.front
  have htlp : TlLike Ap.seam.tl a₀.tl := hJ _ Fc.inv a₀ Ap hs (by rw [hno]; exact hA)
  have etl : tlF = a₀.tl := by
    have h2 : x.2.tl? = some a₀.tl := by
      unfold S.tl?
      rw [hs]
    exact Option.some.inj (htlF.symm.trans h2)
  have hP := K5Law.public_ofPlan O.public X.g Ap hg
  obtain ⟨i, L⟩ := hAtt' l X arrs x x' y y' w p A B Fc hsub a₀ Ap tl' hs hA htlp htl e cc hN
  exact ⟨i, ⟨hA, L.hin, K5Law.ofPlan_size hP, L.hW, L.hE, fun Fn cn sg => by
      rw [etl]
      exact htlp.tabAt Fn cn sg,
    by rw [etl, htlp.u3Of]; exact K5Law.ofPlan_u3Of hP, L.hM⟩⟩

/-- **THE PREMISE hAtt OF arm_at_reads, TO THE LETTER.** -/
theorem hAtt_of (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJ : ∀ s, J s → TlIsPlan XV s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hAtt' : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttLeft4 (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl'
        (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) :=
  hAtt_of' Dm dk mgBase J rfl hS hR O hWX hJ aN R₁ R₂ R₃ hAtt'

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.attIsOdd
#print axioms VerifiableInference.Desc.K1.group_att
#print axioms VerifiableInference.Desc.K1.hAtt_of'
#print axioms VerifiableInference.Desc.K1.hAtt_of
