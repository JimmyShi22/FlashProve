-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmLayIn.lean: **hLay_ofB**: THE FIELD hLay OF k01_fifty_paid
(Johnson/Desc/K1/Law/K01FiftyPaid.lean), IN ITS OWN TYPE (its text taken by program), over hLay_ofJ
(Johnson/Desc/K1/Law/ArmLayMats.lean): JLay's clause SymsIn falls to the test on public data symsSeatedB
(Johnson/Desc/K1/Law/ArmSyms.lean) and the two general clauses of J that the attention links' half has too
(LiveIs · JFirst, Johnson/Desc/K1/Law/ArmAttIn.lean).
  `JLay2 Dm s`       what stays that is the feed-forward links' own, on the state in front alone: the plan's number
                   of the reads is the state's · each entry of the second commitment that a form of one of the
                   row's runs names is (the reads' number, row 0, a place with an owner among the tables heard)
  `hLay_ofB`         **the field hLay**
PREMISES LEFT: hS hR O · hWX · hJl hJf hJ2 (three clauses of J) · ON LETTERS: hUL hnm hsub (hLay_ofJ's) · hB (the test, at
each feed-forward link's plan).
HOW: hLay_ofJ's own steps, with SymsIn had inside the fence (symsIn_at_reads), where the promise gives the written
list of arrays; layM_of is called.
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmAttIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ matsOfData linksFull MsgT MgData CellsQ mgAll mgBase d13
  rowQ seatTab UFn linkNo)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open OnBytes.Road.K4 (uLay InRange)
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

/-- **What stays that is the feed-forward links' own.** -/
def JLay2 (s : S) : Prop :=
  ∀ b₀ o hp A, s.here = .lay b₀ → b₀.own = some o → XV.G[linkNo s / 2]? = some hp →
    K9.segAt? s = some A →
    u3Of hp.tl = o.v.iU3 ∧
      ∀ p e cc, (∃ j n, Item.formsT (linkNo s) j n ∈
          (rowQ linksFull (flatPlacesOf linksFull true) (noL (linkNo s) false)).ins ∧
          p ∈ Dm.runs (linkNo s) j n) →
        NamedEntry (Dm.Rd (linkNo s)) (Dm.N.sent (linkNo s) 0) p.1 p.2 s A e cc →
        e.tree = o.v.iU3 ∧ e.row = 0 ∧
          ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ hp.tl.tabAt z.1 z.2.1 z.2.2 = some e.idx

/-- **THE FIELD hLay OF k01_fifty_paid, IN ITS OWN TYPE.** -/
theorem hLay_ofB (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀) (hWX : Bs.G₀.W = XV)
    (shp : ReqShape) (lay₀ : ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hJf : ∀ s, J s → JFirst Dm.N s) (hJ2 : ∀ s, J s → JLay2 Dm s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (names : ℕ → Array (ℕ × String))
    (hUL : ∀ l X hp, (linksFull[l]?).getD .layers = .layers → Bs.G₀.built[l]? = some X →
      Bs.G₀.W.G[X.g]? = some hp →
      Dm.uL l = uLay hp.tl fun _ D => matsOfData hp.tl (names l) D)
    (hnm : ∀ l, l < 25 → names l = Dm.pubD.d3.arrayOf.getD l #[])
    (hB : ∀ l hp, l < 25 → (linksFull[l]?).getD .layers = .layers → XV.G[l / 2]? = some hp →
      symsSeatedB (Dm.pubD.d3.arrayOf.getD l #[]) lay₀ shp l hp.tl = true)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsb b₀ o hp tl' hs ho hg htl e cc hN
  have hno : linkNo x.2 = l :=
    linkNo_of_promise Dm dk mgBase rfl l Fc.lt x y (inAt_down _ _ _ _ _ _ _ _ _ Fc.inAt) A Fc.front
  have hg2 : XV.G[l / 2]? = some hp := by
    rw [← hWX, ← group_lay hS hR O l Fc.lt hsb X Fc.built]
    exact hg
  obtain ⟨h3, hE⟩ := hJ2 _ Fc.inv b₀ o hp A hs ho (by rw [hno]; exact hg2) Fc.front
  rw [hno] at hE
  obtain ⟨e1, e2, z, z1, z2⟩ := hE p e cc Fc.run hN
  have hF := hJf _ Fc.inv A Fc.front
  rw [hno] at hF
  have hSy := symsIn_at_reads Dm dk mgBase rfl Fc hJl (hB l hp Fc.lt hsb hg2) hF
  have harr := arrays_at_reads Dm dk mgBase rfl l Fc.lt x y Fc.inAt A Fc.front
  refine ⟨fun _ D => matsOfData hp.tl (names l) D, e.idx + 1, by rw [hUL l X hp hsb Fc.built hg],
    oneEntry_all (P := fun u => u.tree = o.v.iU3 ∧ u.row = 0 ∧ u.idx < e.idx + 1 ∧
      ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ hp.tl.tabAt z.1 z.2.1 z.2.2 = some u.idx)
      ⟨e1, e2, Nat.lt_succ_self _, z, z1, z2⟩ p.1 p.2 x.2, h3, ?_⟩
  show InRange tl' (matsOfData hp.tl (names l) _) _
  rw [hnm l Fc.lt, ← harr]
  exact layM_of Dm dk mgBase Fc (hsub l Fc.lt) hs hg htl hSy

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hLay_ofB
