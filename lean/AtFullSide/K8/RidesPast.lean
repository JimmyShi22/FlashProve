-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/RidesPast.lean: the debt «rides past» at the smallness test's draw (the kind K8), at the
first chain's letters with the list csHead and the family fHeadJ. An item that is open at the draw and
that its row neither shuts nor owes passes over it.

  drawn_of_keeps, drawn_back   the kind's clause gives the library's relation Drawn, in both
                      directions: the clause lays back two fields of the test's data, and laying back
                      the old two undoes it
  wo_fwd, forms_fwd, wt_fwd   the library's mg_back reads the claim on the weights, the forms and the
                      sentence "weights" from behind the draw to in front of it; these three read
                      them from in front to behind
  k8_keepsM           the kind's arm of fHead
  ridesPastAt_wo_draw, ridesPastAt_forms_draw   the two items at the thread
  k8_ridesPastS       RidesPastS, item by item over the sorts of RidesSorts.lean

Limits. The library's head is a premise. Nothing here says that any item holds at any state.
-/
import AtFullSide.K8.KeepsBehind
import AtFullSide.K8.RidesSorts
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.RowPileRides
import Johnson.Goal.HonestTrace.ConstrAtThread
import Johnson.P1K8R.BlindAtMg
import Johnson.P1K8R.WtBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (Chain KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item tlP tlP_lawful)
open VerifiableInference.Desc.First.K8 (drawAt Drawn TlBlind blind_st blind_book blind_out blind_leftOf
  blind_segAt blind_mergeOf)
open VerifiableInference.Desc.First.K8.Honest (K8Keeps K8KeepsM)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open P1K8T (pcOf runs_not_ahead blind_rows blind_rw13)

/-- The kind's clause gives the library's relation. -/
theorem drawn_of_keeps {s t : S} (h : K8Keeps s t) : Drawn s t := by
  obtain ⟨tl, cf, first, ht, -, -, -, -, e⟩ := h
  exact ⟨tl, cf, first, ht, e⟩

/-- **And in the other direction**: to lay back the two old fields undoes the draw. -/
theorem drawn_back {s t : S} (h : K8Keeps s t) : Drawn t s := by
  obtain ⟨tl, cf, first, ht, -, -, -, -, rfl⟩ := h
  exact ⟨{ tl with cfF := cf, cfFirst := first }, tl.cfF, tl.cfFirst,
    tlP_lawful.get_set s _ tl ht,
    ((tlP_lawful.set_set s _ tl).trans (tlP_lawful.set_get s tl ht)).symm⟩

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {𝔇 : MgData Xi P Tok rows cols nR X}

/-- **The claim on the weights passes from in front of the draw to behind it.** -/
theorem wo_fwd (m : ℕ) (z : P) {s t : S} (hd : Drawn s t) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (hp : VerifiableInference.Desc.First.FillP1.woAt 𝔇.d1 𝔇.rw13 m (z, s) y w) :
    VerifiableInference.Desc.First.FillP1.woAt 𝔇.d1 𝔇.rw13 m (z, t) y' w := by
  unfold VerifiableInference.Desc.First.FillP1.woAt at hp ⊢
  intro r hr
  have e : 𝔇.rw13 (z, t) = 𝔇.rw13 (z, s) := blind_rw13 𝔇 z s t hd
  rw [e]
  refine hp r ?_
  have e2 : Johnson.Desc.First.Walk.Law.rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin t =
      Johnson.Desc.First.Walk.Law.rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin s := by
    unfold Johnson.Desc.First.Walk.Law.rowAt Johnson.Desc.First.Walk.Law.rowBy
    rw [blind_leftOf s t hd, blind_out s t hd, blind_st s t hd]
  exact e2.symm.trans hr

/-- **The forms of a run in front of the draw pass from in front of it to behind it.** -/
theorem forms_fwd {l k : ℕ} {r : String} (hl : l ≤ 24) (hL : 𝔇.links = linksFull)
    (hk : k < pcOf l) (hR : ∀ p ∈ 𝔇.runs l k r, TlBlind ((𝔇.Rd l).forms p.1 p.2))
    (z : P) {s t : S} (hd : Drawn s t) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hw : 𝔇.wt l (z, s) y w → 𝔇.wt l (z, t) y' w)
    (hp : (∀ p ∈ 𝔇.runs l k r,
        if 𝔇.ah p.1 p.2 = true then
          formsQA (𝔇.N.sent l) (𝔇.N.group l) (𝔇.Rd l) p.1 p.2 s (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)
        else formsQ (𝔇.Rd l) (𝔇.N.group l) p.1 p.2 s (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
        (r = "weights" → 𝔇.wt l (z, s) y w)) :
    (∀ p ∈ 𝔇.runs l k r,
        if 𝔇.ah p.1 p.2 = true then
          formsQA (𝔇.N.sent l) (𝔇.N.group l) (𝔇.Rd l) p.1 p.2 t (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)
        else formsQ (𝔇.Rd l) (𝔇.N.group l) p.1 p.2 t (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
        (r = "weights" → 𝔇.wt l (z, t) y' w) := by
  refine ⟨fun p hpm => ?_, fun e => hw (hp.2 e)⟩
  have hB := hR p hpm
  have ha : 𝔇.ah p.1 p.2 = false := runs_not_ahead hl k r hk p (by
    have hpm' : p ∈ runsAt 𝔇.links l k r := hpm
    rw [hL] at hpm'
    exact hpm')
  have h1 := hp.1 p hpm
  have hn : ¬ 𝔇.ah p.1 p.2 = true := by rw [ha]; exact Bool.false_ne_true
  rw [if_neg hn] at h1 ⊢
  obtain ⟨a, R, e1, e2, e3, e4⟩ := h1
  refine ⟨a, R, (blind_segAt s t hd).trans e1, (hB s t hd).trans e2, e3, ?_⟩
  rw [blind_mergeOf s t hd]
  exact e4

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The sentence "weights" passes from in front of the draw to behind it.** -/
theorem wt_fwd (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (z : ProofFile.InstPub) {s t : S}
    (hd : Drawn t s) (y y' : Strs) (w : WtF) (H : h.𝔇.wt l (z, s) y w) :
    h.𝔇.wt l (z, t) y' w := by
  have H' : VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (P5J.At.cs Zp) (P5J.At.arr Zp)
      (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 l (z, s) y w := H
  show VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (P5J.At.cs Zp) (P5J.At.arr Zp)
      (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)
      (P5J.At.num Zp 24 0) 0 l (z, t) y' w
  intro h24 hr
  exact P1K8T.weightAt_back _ hd (H' h24 hr)

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : VerifiableInference.Desc.Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The claim on the weights passes over a member whose keeps gives the library's relation. -/
theorem ridesPastAt_wo_draw {b : Nat} (m : ℕ)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' → Drawn s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b (Item.wo m) := by
  intro k s mm E s' ps v _ hK h0
  exact wo_fwd (𝔇 := { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }) m
    mm.st.input.x.pub (hk s s' hK)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

/-- The forms of a run in front of the draw of segment l pass over the draw's member. -/
theorem ridesPastAt_forms_draw {b l k : ℕ} {ρ : String} (hl : l ≤ 24) (hkl : k < pcOf l)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' → K8Keeps s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b (Item.forms l k ρ) := by
  intro κ s mm E s' ps v _ hK h0
  obtain ⟨base, hbase⟩ := ProofFile.Honest.K8.below_some (VerifiableInference.Desc.First.sampledIn
          (P5J.At.N Zp cF) ((VerifiableInference.Desc.First.openSets linksFull
            (VerifiableInference.Desc.First.flatPlacesOf linksFull true)
            (VerifiableInference.Desc.First.start linksFull))[P1K8T.ixOf l]?.getD []))
  have O := P1K8T.blindOwes_of_fence h hl base hbase
  have hK8 := hk s s' hK
  have hL : h.𝔇.links = linksFull := P1K8T.const_links _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact forms_fwd (𝔇 := { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX })
    hl hL hkl (O.readers k ρ hkl) mm.st.input.x.pub
    (drawn_of_keeps hK8)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v
    (wt_fwd h l mm.st.input.x.pub (drawn_back hK8)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v) h0

end

/-- **The kind's arm of fHead**, from the member's keeps. -/
theorem k8_keepsM (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) {s s' : TS}
    (hK : (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.keeps b s s') :
    K8KeepsM s s' := by
  have a : fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD pl.kind pl s s' :=
    (head_keeps h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w ha s s').1 hK
  have a1 : fHead Zp cF G take P11 p12 P13 pl.kind pl s s' := a.1.1.1.1.1
  rw [hk] at a1
  exact a1

/-- **The debt «rides past» at a member of the kind.** -/
theorem k8_ridesPastS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b := by
  obtain ⟨l, hl, rfl⟩ := k8_number ha hk
  have hKM : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.keeps (drawAt l) s s' → K8KeepsM s s' :=
    fun s s' hK => k8_keepsM h H Q test carryX item n₁ n₂ Vd ν st R G take P11 p12 P13 w ha hk hK
  refine ridesPastS_shares _ _ fun i h1 h2 h3 => ?_
  rcases k8_open_cases hl h1 h2 h3 with e | e | e | e | ⟨c, e⟩ | e | ⟨k, ρ, hkl, e⟩ | ⟨m, q, hq, e⟩ <;>
    rw [e]
  · exact ridesPastAtS_of _ _ (ridesPastAt_unmarked h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
      fun s s' hK => (hKM s s' hK).2)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinW h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w _)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pile h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
      fun s s' hK => by
        have hd := drawn_of_keeps (hKM s s' hK).1
        exact ⟨blind_st s s' hd, blind_book s s' hd, blind_rows s s' hd⟩)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinI h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
      fun s s' hK => blind_st s s' (drawn_of_keeps (hKM s s' hK).1))
  · exact ridesPastAtS_of _ _ (ridesPastAt_row h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w l c
      fun s s' hK => by
        have hd := drawn_of_keeps (hKM s s' hK).1
        exact ⟨blind_st s s' hd, blind_book s s' hd⟩)
  · exact ridesPastAtS_of _ _ (ridesPastAt_wo_draw h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w l
      fun s s' hK => drawn_of_keeps (hKM s s' hK).1)
  · exact ridesPastAtS_of _ _ (ridesPastAt_forms_draw h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hl hkl
      fun s s' hK => (hKM s s' hK).1)
  · exact ridesPastAtS_of _ _ (OnBytes.HonestTrace.ridesPastAt_constr h H Q test carryX item n₁ n₂
      339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w _ m hq)

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.drawn_of_keeps
#print axioms AtFullSide.K8.Term.drawn_back
#print axioms AtFullSide.K8.Term.wo_fwd
#print axioms AtFullSide.K8.Term.forms_fwd
#print axioms AtFullSide.K8.Term.wt_fwd
#print axioms AtFullSide.K8.Term.ridesPastAt_wo_draw
#print axioms AtFullSide.K8.Term.ridesPastAt_forms_draw
#print axioms AtFullSide.K8.Term.k8_keepsM
#print axioms AtFullSide.K8.Term.k8_ridesPastS
