-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadLab.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm: THE CLAUSE hlab (the open
segment's list of arrays names the symbol arrays of the four ranges' matrices by the matrices' labels),
BY A CALL OF lab_of_calls (Johnson/Desc/Kinds/Law/FourRunsTie.lean), whose premise hL on the
state is paid off the promise in front of the reads' place (arrays_at342,
Johnson/Desc/K1/Law/ArmHeadPromise.lean). IT FALLS TO TWO SENTENCES ON LETTERS: T (the layout lays the
matrices' symbols: a test with code) and hC (CallsSeated: the caller's public letters are tied to the
table's). Statements with their proofs: calls.

Main names:
  hlab_at342          **the clause.**
  HeadLeft5 · hK6_of4 **the premise hK6 of arm_at_reads_three** from hT hRun hride.
What is not claimed. T, hC; the three clauses that stay. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.ArmHeadBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase Mem seatTab dataQ)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6 ColFour CallsSeated lab_of_calls)
open VerifiableInference.Desc.First.Look (sigListCalls)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

/-- **The clause hlab.** -/
theorem hlab_at342 (msR : List Mem) (lay6 : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ)
    (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls Dm.sent rad 24).length → ℕ × ℕ)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hC : CallsSeated (ColFour XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num Dm.sent rad
      24 seatT) {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) {A : K9.Part}
    (hA : K9.segAt? x.2 = some A) :
    ∀ μ c i', μ < XV.H.tl.NM → c < (_root_.Meaning.sizesOf XV 24).k μ →
      i' < Alg.symRows ((_root_.Meaning.sizesOf XV 24).m μ) →
      ColFour XV.hS XV.HLy (borderOf XV.y) μ c →
      A.L.arrayOf[XV.H.tl.gtTree.getD μ 0]? = some (_root_.Meaning.ownerK (_root_.Meaning.labAt XV 24 μ),
        _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt XV 24 μ))) :=
  lab_of_calls XV A Dm.arr msR Dm.N lay6 num Dm.sent rad 24 seatT T (arrays_at342 Dm dk hIn hA) hC

end

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)

/-- **HeadRest less KS, hRd, hwide, hArr, hbare and hlab.** -/
structure HeadLeft5 {Cells Tok : Type} (X : OnBytes.Model.Verify.Public)
    (own : List (Nat × Nat)) (s : S) (a b : K9.Part) (cs : OnBytes.Codes)
    (arr : Nat → Nat → Nat) (ms : List Mem) (N : Numbers) (m : Nat) (w : Wit Cells Tok MsgT) :
    Prop where
  hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s
  hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩)
  hride : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      (dataQ (N.group m) b (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c =
        (dataQ own a (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM THREE CLAUSES.** -/
theorem hK6_of4 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (msR : List Mem) (lay6 : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ)
    (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls Dm.sent rad 24).length → ℕ × ℕ)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hC : CallsSeated (ColFour XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num Dm.sent rad
      24 seatT)
    (hK6' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      HeadLeft5 XV (Dm.N.sent 24 0) x.2 A B Dm.cs Dm.arr Dm.ms Dm.N 24 w) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU :=
  hK6_of3 Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK
    fun X arrs x x' y y' w p A B Fc hn =>
      have L := hK6' X arrs x x' y y' w p A B Fc hn
      ⟨L.hT, L.hRun, hlab_at342 Dm dk msR lay6 num rad seatT T hC Fc.inAt Fc.front, L.hride⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hlab_at342
#print axioms VerifiableInference.Desc.K1.hK6_of4
