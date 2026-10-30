-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K11WorthCell.lean: the open items `worth 24 8 "planes"` and
`worth 24 8 "keys"` of the first chain's invariant pass over the merge of the claims on the weights
(kind K11, number 346). No definition.

The two items say that what lies under the slots of the output head's lookup on the digits is worth
the planes' matrix and the key vectors. They speak at whatever ledger and heard record the
verifier's state holds. The merge leads to a later ledger. The library shows that such an item
passes back from a later ledger to an earlier one. The way forward needs that the forms which the
heard record names are filled at the earlier ledger (`Fo.Tp.PadNames`). Three lemmas of other
authors give it:
  * `worth_planes_over_merge`, `worth_keys_over_merge` (Johnson/Desc/K8/Honest/WorthOverMerge.lean,
    by the authors of K8's and K11's lemmas): the items pass forward over the merge's accepting
    decision, under `PadNames` at the state before it
  * `padNames_346` (Honest/K3/Law/NamedAt346.lean, by the authors of K3's lemmas): `PadNames` at
    every state reached at border 346
This file joins them at the invariant.

One line, `attribute [-instance] Inst.Model.Scl.ref`, takes the library's default instance for the
scales out of the instance search within this file. The files that this file calls have the same
line (Johnson/Top/H0/MergeLaw/WorthAtMerge.lean, WorthOverMerge.lean, Honest/K3/Law/WorthOn.lean).
It stands here so that their statements are read under the instances under which they were stated.
Whether this file compiles without the line has not been tried.

  1  `worthAt_full`, `worthAt_control`, `worth_k11_place`   a closed test by Lean's kernel on the
     written lists: a place of the kind K11 has the number 346, and an item `worth` that is open on
     both sides of it is one of the two. The negative test: with "planes" alone the test fails
  2  `worth_rides_346`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the two items,
     for every `Kp` whose clause at 346 gives an accepting decision of the merge
  3  `cell_worth_k11`   the hypothesis `RidesPastAtS` (Honest/Thread/SharesS.lean) by the kind of
     the place, at `kpBy fHeadG`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that an item's statement holds at any state of a run. Who shows the two items
    after the lookup on the digits (number 345) is not treated here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG
import Johnson.Desc.ProofFile.Honest.Thread.OpenNext
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.K3.Law.NamedAt346
import Johnson.Desc.K8.Honest.WorthOverMerge
import Johnson.Top.H0.MergeLaw.WorthAtMerge
import Johnson.K11R.DigThere
import Johnson.IMR.RootsWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item Meaning)
open VerifiableInference.Desc.First.Look (digAt)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase)
open VerifiableInference.OnPublicFiles (k3At_mgAll headLink)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The closed test -/

set_option maxRecDepth 1000000 in
/-- Where a place of the kind K11 stands, and which items `worth` are open on both sides of it. -/
theorem worthAt_full : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K11) || (b == 346 &&
      ((IM.openAt P5J.At.links P5J.At.ps 346).filter fun i =>
        (IM.openAt P5J.At.links P5J.At.ps 347).contains i).all fun i =>
        match i with
        | .worth m k ρ => m == 24 && k == 8 && (ρ == "planes" || ρ == "keys")
        | _ => true)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with "planes" alone the same test fails. -/
theorem worthAt_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K11) || (b == 346 &&
      ((IM.openAt P5J.At.links P5J.At.ps 346).filter fun i =>
        (IM.openAt P5J.At.links P5J.At.ps 347).contains i).all fun i =>
        match i with
        | .worth m k ρ => m == 24 && k == 8 && (ρ == "planes")
        | _ => true)) = false := by
  decide +kernel

/-- The test at a place. -/
theorem worth_k11_place {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K11) :
    b = 346 ∧ ∀ m k ρ, Item.worth m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps 346 →
      Item.worth m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps 347 →
      m = 24 ∧ k = 8 ∧ (ρ = "planes" ∨ ρ = "keys") := by
  have t := List.all_eq_true.1 worthAt_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · rw [hk] at t0
    exact absurd t0 (by decide)
  · simp only [Bool.and_eq_true] at t1
    refine ⟨eq_of_beq t1.1, fun m k ρ ho ho' => ?_⟩
    have t2 : (m == 24 && k == 8 && (ρ == "planes" || ρ == "keys")) = true :=
      List.all_eq_true.1 t1.2 _ (List.mem_filter.2 ⟨ho, List.contains_iff_mem.2 ho'⟩)
    simp only [Bool.and_eq_true, Bool.or_eq_true] at t2
    exact ⟨eq_of_beq t2.1.1, eq_of_beq t2.1.2, t2.2.imp eq_of_beq eq_of_beq⟩

/-! ## 2 and 3 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The two items pass over the merge. -/
theorem worth_rides_346 (P : HeadMergeP)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      ∃ rs, headMergeDecide P s rs = .ok s')
    {ρ : String} (hρ : ρ = "planes" ∨ ρ = "keys") :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346
      (Item.worth 24 8 ρ) := by
  intro k s mm E s' ps v hT hK h0
  obtain ⟨rs, hy⟩ := hk s s' hK
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨xd, tl, hx⟩ : ∃ xd tl, digAt (P5J.At.X Zp) 24 = some (xd, tl) :=
    K11Live.digThere_in_scope h.scope h.reads O h.laid.planOk
  have hH : headLink (P5J.At.X Zp) = 24 := P5J.headLink_in_scope h.scope h.reads h.pubOne
  have hp := VerifiableInference.Desc.First.MergeLaw.pieceAt_head (X := P5J.At.X Zp) hH
  have hlen : 346 ≤ cF.blocksInOrder.length := by
    rw [Meaning.Carry.flat_len h.scope h.reads O]
    decide
  have N := ProofFile.Honest.K3.Law.padNames_346 h (fun _ => ()) _ s
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT)
  rcases hρ with rfl | rfl
  · have q : Meaning.worth
        (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase)
        24 8 "planes" (mm.st.input.x.pub, s)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v := h0
    have h1 := VerifiableInference.Desc.First.K8.Honest.worth_planes_over_merge
      (k3At_mgAll _ mgBase) (fun _ => ()) 24 hx P hy N mm.st.input.x.pub mm.st.input.x.pub
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v
      (by rw [hp]; exact q)
    rw [hp] at h1
    exact h1
  · have q : Meaning.worth
        (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase)
        24 8 "keys" (mm.st.input.x.pub, s)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v := h0
    have h1 := VerifiableInference.Desc.First.K8.Honest.worth_keys_over_merge
      (k3At_mgAll _ mgBase) (fun _ => ()) 24 hx P hy N mm.st.input.x.pub mm.st.input.x.pub
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v
      (by rw [hp]; exact q)
    rw [hp] at h1
    exact h1

variable (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- The item `worth m k r` at a place of the kind K11. -/
theorem cell_worth_k11 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K11) {m k : Nat} {ρ : String}
    (hi : Item.worth m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.worth m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.worth m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨rfl, hf⟩ := worth_k11_place hb hp hk
  obtain ⟨rfl, rfl, hρ⟩ := hf m k ρ ho ho'
  exact ridesPastAtS_of _ _ (worth_rides_346 h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w P11
    (fun s s' hK => ((((kpBy_at _ hk s s').1
      ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp s s').1 hK)).1.1).2).2) hρ)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.worthAt_full
#print axioms ProofFile.Honest.FirstThread.worthAt_control
#print axioms ProofFile.Honest.FirstThread.worth_k11_place
#print axioms ProofFile.Honest.FirstThread.worth_rides_346
#print axioms ProofFile.Honest.FirstThread.cell_worth_k11
