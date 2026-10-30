-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadBare.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm: BOTH CLAUSES hbare (the
form that the lookup on the calls left for the join names no entry · the start form of its sumcheck over
the leaves names none) READ OFF THE PROMISE IN FRONT OF THE READS' PLACE: the public item leftOn 24 is
open there, and what it says beside its Bool (Meaning.pubP) is the lookups' own sentence
k3LeftOnItemAt (Johnson/Desc/First/Look/K3LeftItem.lean). No fact along reached states, no premise on
letters. Statements with their proofs: calls.

Main names:
  leftOpen342 [kernel] · leftOpen342_fails
  leftOn_at342        the lookups' sentence at the state in front.
  bareEnd_at342 · bareLeaves_at342   **the two clauses.**
  HeadLeft4 · hK6_of3 **the premise hK6 of arm_at_reads_three** from hT hRun hlab hride.
  PlanesLeft4 · hPl_of3   **the premise hPl** from hlen hHostC.
What is not claimed. The clauses that stay. Nothing on soundness, on an honest prover or on hiding.
THE RECURSION LIMIT IS RAISED IN THIS FILE (maxRecDepth 1000000): for the kernel's evaluations'
elaboration alone.

-/
import Johnson.Desc.K1.Law.ArmHeadPaid2
import Johnson.Desc.K1.Law.ALeftOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase Mem seatTab dataQ)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

theorem leftOpen342 :
    ((First.pubSets mwMore linksFull (flatPlacesOf linksFull true))[noL 24 false]?.getD []).contains
      (.leftOn 24) = true := by
  decide +kernel

/-- The test can fail. -/
theorem leftOpen342_fails :
    ((First.pubSets mwMore linksFull (flatPlacesOf linksFull true))[noL 24 false]?.getD []).contains
      (.leftOn 23) = false := by
  decide +kernel

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

/-- The lookups' sentence at the state in front of the output head's reads' place. -/
theorem leftOn_at342 {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) : k3LeftOnItemAt XV 24 x.2 := by
  have hin : Pub.leftOn 24 ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull
      (flatPlacesOf linksFull true))[noL 24 false]?.getD [] := by
    have e : (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more = mwMore :=
      plus13_more_closed Dm dk mgBase rfl
    rw [e]
    exact List.contains_iff_mem.1 leftOpen342
  have h0 := inAt_pubP hIn _ hin
  rw [(fillsK1_mw1 Dm dk mgBase).pubP] at h0
  exact h0

/-- **The form left for the join names no entry.** -/
theorem bareEnd_at342 {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∀ gk, x.2.lookHeard? = some gk → gk.cEnd.ents = #[] := by
  intro gk hg
  obtain ⟨p, _, ⟨h, _, F, F', G, g, rs, _, _, hK, hh, _⟩, _⟩ := leftOn_at342 Dm dk hIn
  obtain rfl : g = gk := Option.some.inj (hh.symm.trans hg)
  exact hK.cEndEnts

/-- **The start form of the sumcheck over the leaves names no entry.** -/
theorem bareLeaves_at342 {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∀ gk, x.2.lookHeard? = some gk → gk.leaves.start.ents = #[] := by
  obtain ⟨p, _, _, hb⟩ := leftOn_at342 Dm dk hIn
  exact hb

end

/-! ## What stays -/

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)
open VerifiableInference.Desc.Kinds.Head.Law.Planes

/-- **HeadRest less KS, hRd, hwide, hArr and hbare.** -/
structure HeadLeft4 {Cells Tok : Type} (X : OnBytes.Model.Verify.Public)
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
  hlab : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      a.L.arrayOf[X.H.tl.gtTree.getD μ 0]? = some (Meaning.ownerK (Meaning.labAt X 24 μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ)))
  hride : ∀ μ c i', μ < X.H.tl.NM → c < (Meaning.sizesOf X 24).k μ →
      i' < Alg.symRows ((Meaning.sizesOf X 24).m μ) → ColFour X.hS X.HLy (borderOf X.y) μ c →
      (dataQ (N.group m) b (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c =
        (dataQ own a (seatTab cs arr ms w)).cell (Meaning.ownerK (Meaning.labAt X 24 μ))
          (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X 24 μ))) i' c

/-- **PlanesLeft less hSt, hRd, hArr, hwide and hbare.** -/
structure PlanesLeft4 (X : OnBytes.Model.Verify.Public) (own own' : List (Nat × Nat))
    (s : S) (a b : K9.Part) (rdW : Nat × Nat → Sound.MsgQ) : Prop where
  hlen : ∀ gk, s.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - (p8K6 X 24).h.lmbH) ≤
        ((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).m / 2 ^ (p8K6 X 24).h.lmbH)
  hHostC : ∀ e r gk, withTables (p8K6 X 24) s = some e →
      callerReaders (planesAt (readsOf X)) e = some r → e.lookHeard? = some gk →
      Meaning.Planes.K3HostPlanes gk.shape (p8K6 X 24).h.lmbH (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) (nuK6 X s (Sound.dataQ own a rdW))
        (fun f => f.value Reading.gl (worldOwn b [] (Sound.dataQ own' b rdW)))
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {})

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM FOUR CLAUSES.** -/
theorem hK6_of3 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (hK6' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      HeadLeft4 XV (Dm.N.sent 24 0) x.2 A B Dm.cs Dm.arr Dm.ms Dm.N 24 w) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU :=
  hK6_of2 Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK
    fun X arrs x x' y y' w p A B Fc hn =>
      have L := hK6' X arrs x x' y y' w p A B Fc hn
      ⟨L.hT, bareEnd_at342 Dm dk Fc.inAt, L.hRun, L.hlab, L.hride⟩

/-- **THE PREMISE hPl OF arm_at_reads_three, FROM TWO CLAUSES.** -/
theorem hPl_of3 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (hPl' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      PlanesLeft4 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w)) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU :=
  hPl_of2 Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK
    fun X arrs x x' y y' w p A B Fc hn =>
      have L := hPl' X arrs x x' y y' w p A B Fc hn
      ⟨L.hlen, bareLeaves_at342 Dm dk Fc.inAt, L.hHostC⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.leftOpen342
#print axioms VerifiableInference.Desc.K1.leftOpen342_fails
#print axioms VerifiableInference.Desc.K1.leftOn_at342
#print axioms VerifiableInference.Desc.K1.bareEnd_at342
#print axioms VerifiableInference.Desc.K1.bareLeaves_at342
#print axioms VerifiableInference.Desc.K1.hK6_of3
#print axioms VerifiableInference.Desc.K1.hPl_of3
