-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadPaid2.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm, WITH ALL THAT IS PAID
LAID IN: of HeadRest's nine clauses FIVE stay (HeadLeft3), of PlanesLeft's seven THREE (PlanesLeft3);
and THE CLAUSE «NO TABLES ARE LAID» OF THE LETTER J IS PAID ALONG THE REACHED STATES, FROM THE SCOPE
AND THE PROMISE: so ArmOk NoTables holds at all hundred borders. Statements with their proofs: calls.

Main names:
  noTables_front_low  in front of the reads' place of a segment l < 24 the state stands in no head (off
                      the promise's stand: stand_of_promise).
  noTables_at_reads   **NoTables at the reached states in front of all 25 reads' places**: at link 24 by
                      no_tables_342 (Johnson/Desc/AtSeats/TablesAtHead.lean).
  armOk_noTables      **ArmOk NoTables at all hundred borders** (Johnson/Desc/AtSeats/ArmAtRch.lean:
                      armOk_at_rch).
  HeadLeft3 · hK6_of2 **the premise hK6 of arm_at_reads_three** from hT hbare hRun hlab hride.
  PlanesLeft3 · hPl_of2   **the premise hPl** from hlen hbare hHostC.
PREMISES OF hK6_of2 | hPl_of2 BESIDE THESE: hJ (J gives NoTables) · hS hR O hDlk hlk hWX · ON LETTERS:
  hU : the written list of link 24's arrays has an entry at the number of the array of reads ·
  hK : the plan's list of the ledger's arrays' looks has, at that number, a width of at least
  XV.H.nU[2].
What is not claimed. The clauses that stay; hU; hK. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.ArmHeadPromise
import Johnson.Desc.AtSeats.TablesAtHead
import Johnson.Desc.AtSeats.ArmAtRch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf standOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase Mem seatTab
  dataQ onQ Frame)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open IM (k1Ix)
open ProofFile (Cl)

/-! ## 1 «No tables are laid» along the reached states -/

theorem noTables_front_low {Pp W : Type} {N : Numbers} {Mg : Meaning Pp W} (l : ℕ) (hl : l < 24)
    (x : Pp × S) (y : Strs)
    (hIn : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l false) x y) :
    NoTables x.2 := by
  intro a ha
  exfalso
  have hs := stand_of_promise l (by omega) x y hIn
  unfold standOf at hs
  rw [ha] at hs
  dsimp only at hs
  split at hs
  · exact absurd (First.Stand.link.inj hs).symm (low_not_head l hl)
  · cases hs

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **NoTables at the reached states in front of all 25 reads' places.** -/
theorem noTables_at_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {W : Type} {Fr : Frame}
    (N : Numbers) (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → NoTables a.1.2 := by
  intro l hl a hr hon hm
  by_cases h24 : l = 24
  · subst h24
    exact no_tables_342 hS hR O a.1 (rchAt_raw hr)
  · exact noTables_front_low l (by omega) a.1 _ ⟨hon, hm⟩

/-- **ArmOk NoTables at all hundred borders.** -/
theorem armOk_noTables (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {W : Type} {Fr : Frame}
    (N : Numbers) (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        j a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
      ArmOk NoTables a.1.2 :=
  armOk_at_rch NoTables hS hR O N Mg (noTables_at_reads hS hR O N Mg)

end

/-! ## 2 What stays of HeadRest and of PlanesLeft -/

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

/-- **HeadRest less KS, hRd, hwide and hArr.** -/
structure HeadLeft3 {Cells Tok : Type} (X : OnBytes.Model.Verify.Public)
    (own : List (Nat × Nat)) (s : S) (a b : K9.Part) (cs : OnBytes.Codes)
    (arr : Nat → Nat → Nat) (ms : List Mem) (N : Numbers) (m : Nat) (w : Wit Cells Tok MsgT) :
    Prop where
  hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s
  hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[]
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

/-- **PlanesLeft less hSt, hRd, hArr and hwide.** -/
structure PlanesLeft3 (X : OnBytes.Model.Verify.Public) (own own' : List (Nat × Nat))
    (s : S) (a b : K9.Part) (rdW : Nat × Nat → Sound.MsgQ) : Prop where
  hlen : ∀ gk, s.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - (p8K6 X 24).h.lmbH) ≤
        ((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).m / 2 ^ (p8K6 X 24).h.lmbH)
  hbare : ∀ gk, s.lookHeard? = some gk → gk.leaves.start.ents = #[]
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

/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM FIVE CLAUSES.** -/
theorem hK6_of2 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (hK6' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      HeadLeft3 XV (Dm.N.sent 24 0) x.2 A B Dm.cs Dm.arr Dm.ms Dm.N 24 w) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU :=
  hK6_of Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ fun X arrs x x' y y' w p A B Fc hn =>
    have L := hK6' X arrs x x' y y' w p A B Fc hn
    ⟨cU, L.hT, L.hbare, wide_at342 Dm dk _ _ hK Fc.inAt (p8K6 XV 24), L.hRun,
      by rw [arrays_at342 Dm dk Fc.inAt Fc.front]; exact hU, L.hlab, L.hride⟩

/-- **THE PREMISE hPl OF arm_at_reads_three, FROM THREE CLAUSES.** -/
theorem hPl_of2 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (hPl' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      PlanesLeft3 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w)) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU :=
  hPl_of Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ fun X arrs x x' y y' w p A B Fc hn =>
    have L := hPl' X arrs x x' y y' w p A B Fc hn
    ⟨cU, by rw [arrays_at342 Dm dk Fc.inAt Fc.front]; exact hU,
      wide_at342 Dm dk _ _ hK Fc.inAt (p8K6 XV 24), L.hlen, L.hbare, L.hHostC⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.noTables_front_low
#print axioms VerifiableInference.Desc.K1.noTables_at_reads
#print axioms VerifiableInference.Desc.K1.armOk_noTables
#print axioms VerifiableInference.Desc.K1.hK6_of2
#print axioms VerifiableInference.Desc.K1.hPl_of2
