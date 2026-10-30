-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmPlanesPaid.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm AT THE RUN "planes"
(Johnson/Desc/K1/Law/ArmHead.lean: hPl asks PlanesLeft inside the fence at link 24): TWO OF ITS SEVEN
CLAUSES PAID: hSt (what link 24's second hearing sub-protocol states under "planes") FROM THE SCOPE;
hRd (what the readers answer) FROM «NO TABLES ARE LAID IN FRONT» (NoTables). Statements with their
proofs: calls, and a peeling of the lookup's makers' texts.

Main names:
  placeAt_lm          at the output head's link the lookup on the calls has the head's own lm.
  planesStates_seated **hSt, from the scope.**
  PlanesLeft2         PlanesLeft less hSt and hRd. planesLeft_of.
  hPl_of              **the premise hPl of arm_at_reads_three, from the like with PlanesLeft2**, at any
                      J that gives NoTables.
What is not claimed. PlanesLeft2's five clauses. NoTables at a reached state. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ArmHeadPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase rowQ Mem
  seatTab dataQ)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf LinkHoles statesOfLink readersOfLink
  holesAt phAt)
open VerifiableInference.Desc.Kinds.Head (seatAt planesAt callerReaders asClaim seatedClaims
  blockClaims)
open VerifiableInference.Desc.Kinds.Head.Law (withTables k6Silent p8K6 PlanesStates)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

/-- At the output head's link the lookup on the calls has the head's own lm. -/
theorem placeAt_lm (W : Verify.Public) (l : ℕ) (hl : headLink W = l) {p : First.Look.P}
    (h : First.Look.placeAt W l false = some p) : p.lm = W.hS.lmbH := by
  unfold First.Look.placeAt at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  show x.lm = W.hS.lmbH
  unfold First.Look.lookAt at hx
  have e : (l == (if W.p4 then 2 else 1) * W.NGr) = true := by
    rw [show (if W.p4 then 2 else 1) * W.NGr = l from hl]
    exact beq_self_eq_true l
  simp only [e, if_true, Bool.false_eq_true, if_false] at hx
  rw [← Option.some.inj hx]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **hSt, from the scope.** -/
theorem planesStates_seated (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (lk : Link S Cl)
    (eL : c.links[24]? = some lk) :
    PlanesStates (Kinds.Head.Law.readsOf Bs.G₀.W) Bs.G₀.W.hS.lmbH (statesOfLink lk) 2 := by
  have hW := headLink_open hS hR O
  -- the head's array of reads has a number
  obtain ⟨_, _, _, ms, -, -, -, k6, -, -⟩ := IM.k6_of hS hR O
  unfold seatedClaims at k6
  obtain ⟨_, h0, -⟩ := Option.map_eq_some_iff.1 k6
  unfold blockClaims at h0
  obtain ⟨iU3, hu, -⟩ := Option.map_eq_some_iff.1 h0
  have hr : Kinds.Head.Law.readsOf Bs.G₀.W = iU3 := by
    unfold Kinds.Head.Law.readsOf
    rw [hu]
    rfl
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have e2' : lk.hear[2]? = some b := e2
  have hh : K3.isHead Bs.G₀.W 24 = true := by
    show (24 == (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr) = true
    rw [show (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr = 24 from hW]
    rfl
  have h' : K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape
      (IM.k3Place 24 false) = some b' := k3
  unfold K3.theStated at h'
  obtain ⟨b₀, h₀, h'⟩ := Option.bind_eq_some_iff.1 h'
  have n0 : ∀ r ∈ b₀.claims, r.1 ≠ "planes" :=
    theWhole_calls_of (fun c => c.1 ≠ "planes") K3Lot.ofForm
      (fun piece laid sent p c hc => by
        have hc' : c ∈ [("objects", K9.objectsCalls), ("guests", K9.guestsNone)] := hc
        have : c = ("objects", K9.objectsCalls) ∨ c = ("guests", K9.guestsNone) := by
          simpa using hc'
        rcases this with e | e <;> rw [e] <;> decide) Bs.G₀.W _ _ _ (by decide) b₀ h₀
  have hpc : ((IM.k3Place 24 false).piece != K3.pieceAt Bs.G₀.W 24 false) = false := by
    unfold K3.pieceAt
    rw [hh]
    rfl
  have hrd : K3Lot.readersAt Bs.G₀.W 24 = some (callerReaders (planesAt iU3)) := by
    simp only [K3Lot.readersAt, hh, if_true, hu, Option.map_some]
  have h'' : (First.Look.placeAt Bs.G₀.W 24 false).map (fun p =>
      K3.withCaller (K3.seatCalls K3Lot.ofForm) p (callerReaders (planesAt iU3)) b₀) = some b' := by
    have h2 : (if ((IM.k3Place 24 false).piece != K3.pieceAt Bs.G₀.W 24 false) = true then some b₀
        else
          match K3Lot.readersAt Bs.G₀.W 24 with
          | none => some b₀
          | some r => (First.Look.placeAt Bs.G₀.W 24 false).map fun p =>
              K3.withCaller (K3.seatCalls K3Lot.ofForm) p r b₀) = some b' := h'
    rw [if_neg (by rw [hpc]; exact Bool.false_ne_true), hrd] at h2
    exact h2
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h''
  have hlm := placeAt_lm Bs.G₀.W 24 hW hp
  have hs : statesOfLink lk 2 = (b₀.claims ++ [("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm)
      p.lm (callerReaders (planesAt iU3)))]).map
        fun c => (c.1, IM.guardRun ProofFile.sameReply c.2) := by
    unfold statesOfLink
    rw [e2']
    show b.claims = _
    rw [IM.claims_alone la]
    rfl
  refine ⟨IM.guardRun ProofFile.sameReply (K3.planesRun (K3.seatCalls K3Lot.ofForm) p.lm
          (callerReaders (planesAt iU3))), ?_, fun k t y hy => ?_⟩
  · rw [hs, List.map_append, List.find?_append]
    have hnone : (b₀.claims.map fun c => (c.1, IM.guardRun ProofFile.sameReply c.2)).find?
        (fun r => r.1 == "planes") = none := by
      rw [List.find?_eq_none]
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      simpa using n0 q hq
    rw [hnone]
    rfl
  · rw [hr, ← hlm]
    exact ((IM.guardRun_yes _ k t y).1 hy).1

end

/-! ## PlanesLeft, less what is paid -/

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)
open VerifiableInference.Desc.Kinds.Head.Law.Planes

/-- **PlanesLeft (Johnson/Desc/K1/Law/ArmHead.lean) less hSt and hRd.** -/
structure PlanesLeft2 (X : OnBytes.Model.Verify.Public) (own own' : List (Nat × Nat))
    (s : S) (a b : K9.Part) (rdW : Nat × Nat → Sound.MsgQ) (cU : Nat × String) : Prop where
  hArr : a.L.arrayOf[readsOf X]? = some cU
  hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → (p8K6 X 24).hp.nU.getD 2 0 ≤ tr.K
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

theorem planesLeft_of {X : OnBytes.Model.Verify.Public} {Rd : Readers} {own own' : List (Nat × Nat)}
    {blk : Nat} {s : S} {a b : K9.Part} {rdW : Nat × Nat → Sound.MsgQ}
    {states : Nat → List (RunOf S)} {cU : Nat × String}
    (L : PlanesLeft2 X own own' s a b rdW cU)
    (hSt : PlanesStates (readsOf X) (p8K6 X 24).h.lmbH states blk)
    (hRd : Rd.forms blk "planes" s = k6Silent (p8K6 X 24) states blk "planes" s) :
    PlanesLeft X Rd own own' blk s a b rdW states cU :=
  ⟨hSt, hRd, L.hArr, L.hwide, L.hlen, L.hbare, L.hHostC⟩

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

/-- **THE PREMISE hPl OF arm_at_reads_three, FROM THE LIKE WITH PlanesLeft2**, at any J that gives
NoTables. -/
theorem hPl_of (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hPl' : ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ cU, PlanesLeft2 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) cU) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU := by
  intro X arrs x x' y y' w p A B Fc hn
  obtain ⟨cU, L⟩ := hPl' X arrs x x' y y' w p A B Fc hn
  obtain ⟨lk, _, _, _, eL, -⟩ := IM.k6_of hS hR O
  have hX : headLink XV = 24 := hWX ▸ headLink_open hS hR O
  have hp : p.1 = 2 := by
    refine (block_of_run ?_).2 hn
    obtain ⟨j, n, h1, h2⟩ := Fc.run
    refine ⟨j, n, h1, ?_⟩
    have h2' : p ∈ runsAt Dm.links 24 j n := h2
    rw [hDlk] at h2'
    exact h2'
  have hSt := planesStates_seated hS hR O lk eL
  rw [hWX] at hSt
  refine ⟨statesOfLink lk, cU, planesLeft_of L (hp ▸ hSt) ?_⟩
  rw [hp]
  exact hRd_at24 Dm hX lk ((hlk 24 (by decide)).trans eL) 2 "planes" (by decide)
    (tabled_head2 hS hR O lk eL) x.2 (hJ _ Fc.inv)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.placeAt_lm
#print axioms VerifiableInference.Desc.K1.planesStates_seated
#print axioms VerifiableInference.Desc.K1.planesLeft_of
#print axioms VerifiableInference.Desc.K1.hPl_of
