-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadRide.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm: THE CLAUSE hride (the cells
of the symbol arrays of the four ranges' matrices are read alike behind the reads' place, through the
group's list of seats, and in front, through the first commitment's), BY A CALL OF
ride_of_seated (Johnson/Desc/Kinds/Law/FourRunsTie.lean) at rides_at_reads
(Johnson/Desc/K1/Law/ArmAtReads.lean). A CLAUSE THAT READS THE WITNESS AND BOTH PARTS IS TURNED INTO TWO
THAT READ THE PART IN FRONT ALONE (hlay, hMats) AND ONE ON LETTERS (hsub). Statements with their proofs:
calls.

Main names:
  hride_at342         **the clause.**
  HeadLeft6 · hK6_of5 **the premise hK6 of arm_at_reads_three** from hT hRun hlay hMats: EACH READS THE
                      STATE IN FRONT ALONE: each can be a conjunct of the letter J of ArmOk.
What is not claimed. hsub; the four clauses that stay. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.ArmHeadLab

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
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6 ColFour CallsSeated MatsSeated ride_of_seated)
open VerifiableInference.Desc.First.Look (sigListCalls)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)

/-- **What stays of HeadRest: four clauses on the state in front alone.** lay6, num: letters. -/
structure HeadLeft6 (X : OnBytes.Model.Verify.Public) (own : List (Nat × Nat)) (s : S)
    (a : K9.Part) (arr : Nat → Nat → Nat) (N : Numbers) (num : Nat → Nat → Nat)
    (lay6 : OnBytes.Params.ReqLayout) : Prop where
  hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s
  hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩)
  hlay : a.L.check.rows.layout = lay6
  hMats : MatsSeated (ColFour X.hS X.HLy (borderOf X.y)) arr N X own a num lay6

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM FOUR CLAUSES ON THE STATE IN FRONT ALONE.** -/
theorem hK6_of5 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
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
    (hsub : ∀ x ∈ Dm.N.sent 24 0, x ∈ Dm.N.group 24)
    (hK6' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      HeadLeft6 XV (Dm.N.sent 24 0) x.2 A Dm.arr Dm.N num lay6) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU :=
  hK6_of4 Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK msR lay6 num rad seatT T hC
    fun X arrs x x' y y' w p A B Fc hn =>
      have L := hK6' X arrs x x' y y' w p A B Fc hn
      ⟨L.hT, L.hRun, ride_of_seated XV (Dm.N.sent 24 0) (Dm.N.group 24) A B _ hsub
        (rides_at_reads Fc) Dm.arr Dm.N num lay6 T L.hlay L.hMats⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hK6_of5
