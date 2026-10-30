-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LaterStretch.lean: "WHAT IS FILLED IN THE LEDGER STAYS FILLED" FROM THE
BORDER BEHIND A SEGMENT's OWN KIND UP TO THE FRONT OF ITS BATCHING, AT EVERY REACHED STATE. A
definition, and theorems: joins of other files' lemmas.
Why. The clauses of a link's Ok (OkOne.lean) on filled slots (front, back at a layers' link; k6,
join at the head's) are held by their files at their own kind's accept. The batching stands four or
five sub-protocols on. StretchParts.lean walks that stretch back a step at a time, for any relation
that each step's decision keeps.
  `LaterZ s s'`: where s holds a ledger WITH ITS SIZES, s' holds one, and it is a later state of it
    (`PscRun.Later`). `laterZ_of_laterS`: `LaterS` (Johnson/Desc/First/LedgerLater.lean) gives it.
    `laterZ_refl`, `laterZ_trans`.
WHY THE SIZES. Across the lookup on the digits "later" is had from `decide_exact`
(Johnson/Top/H/Keep/PadExact.lean), which gives it under `Sized` of the ledger in front. So
`StretchKeeps`' field k3 (StretchBack.lean: every address, no premise on the plan) is not met: the
steps are walked one at a time here.
  `k11_laterS`: the merge's decision keeps `LaterS`: `decide_fork_later`
    (Johnson/Top/H0/MergeLaw/StepsFo.lean). `later_behind_digits`: **a yes of `K3.theStated`'s value
    at the digits' address, its test on the plan passed, from a ledger with its sizes: a later
    ledger behind.** `back_k3_later`: so one step back over it, at every l < 25.
  `laterZ_back`: **from 14 l + 9 back to 14 l + 6** (l < 24). `laterZ_back_layers`: **from 28 g + 9
    back to 28 g + 5** (g < 12). `laterZ_back_head`: **from 347 back to 343.**
PREMISES. The scope (hS, hR, `IM.Open`); hp: every sub-protocol of the first chain passes its test
on the plan; "reached".
Limits. THAT A LEDGER WITH ITS SIZES STANDS AT THE EARLIER STATE IS NOT SAID: without it `LaterZ`
says nothing. On the decisions alone: nothing on the runs of claims. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Desc.First.Link.Law.FourAtBatch
import Johnson.Top.H0.MergeLaw.StepsFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S LaterS)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.OnPublicFiles (theStated_yes_digits quietAt_ledger decide_exact seatDigits_keeps)
open Johnson.Desc.First.ForkMerge (headMergeDecide headClaimMergeKind)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- **Where s holds a ledger with its sizes, s' holds one, and it is a later state of it.** -/
def LaterZ (s s' : S) : Prop :=
  ∀ F, s.fork? = some F → Sized F → ∃ F', s'.fork? = some F' ∧ PscRun.Later F F'

theorem laterZ_of_laterS {s s' : S} (h : LaterS s s') : LaterZ s s' := fun F hF _ => h F hF

theorem laterZ_refl (s : S) : LaterZ s s := laterZ_of_laterS (LaterS.refl s)

theorem laterZ_trans (a b c : S) (h : LaterZ a b) (k : LaterZ b c) : LaterZ a c := by
  intro F hF hz
  obtain ⟨G, hG, l1⟩ := h F hF hz
  obtain ⟨H, hH, l2⟩ := k G hG (l1.sized hz)
  exact ⟨H, hH, l1.trans l2⟩

/-- Another count of planned claims: a later ledger. -/
theorem later_plan (F : Fork) (k : ℕ) : PscRun.Later F { F with planClaimsF := k } :=
  ⟨Nat.le_refl _, rfl, fun h => h, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- **The merge's decision.** -/
theorem k11_laterS (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Decides LaterS (headClaimMergeKind P) := fun s rs _ s' h F hF =>
  First.MergeLaw.decide_fork_later P (show headMergeDecide P s rs = .ok s' from h) F hF

/-- **BEHIND A YES OF THE SEATED LOOKUP ON THE DIGITS THE LEDGER IS A LATER ONE.** -/
theorem later_behind_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (s c : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) {F : Fork}
    (hF : s.fork? = some F) (hS : Sized F) : ∃ G, c.fork? = some G ∧ PscRun.Later F G := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨F₁, y, hF₁, hn, e, hE⟩ :=
    decide_exact (K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans hF₁)
  have hsome : ((K3.seatDigits claim).fork s).isSome = true := by
    rw [hF₁]
    rfl
  have hy : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact ⟨y.2, hy, (hE hS).2⟩
  · obtain ⟨F₂, k, hF₂, hG₂, -⟩ := quietAt_ledger X i f hf s' c hfs
    obtain rfl : y.2 = F₂ := Option.some.inj (hy.symm.trans hF₂)
    exact ⟨_, hG₂, (hE hS).2.trans (later_plan y.2 k)⟩

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **One step back over the digits' seated sub-protocol.** -/
theorem back_k3_later (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2) (z, s) ∧ LaterZ s s' := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  have hOk : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  exact back_of (R := LaterZ) hS hR O (by omega) e1 e2 e4 (fun h => nomatch h)
    (fun s rs gs t hd G hG hz => later_behind_digits _ _ _ _ _ _ b' e3 hOk l rfl
      (piece_digits _ _ _ _ _ _ b' e3 l rfl h7) s t rs gs hd hG hz) h

/-- **FROM THE BATCHING's BORDER BACK TO THE BORDER BEHIND THE SENDING OF THE READS.** -/
theorem laterZ_back (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + 6) (z, s) ∧ LaterZ s s' := by
  have n24 : l ≠ 24 := by omega
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    simp [n24]
  have i1 : IM.k1Ix l true = 5 := by
    show (if true = true then 5 else 3) + (if l = 24 then 1 else 0) = 5
    simp [n24]
  have i8 : k8Ix l = 4 := by
    show 4 + (if l = 24 then 1 else 0) = 4
    simp [n24]
  obtain ⟨s₃, r3, q3⟩ := back_k3_later hS hR O hp (l := l) (by omega) (z := z) (s' := s')
    (by rw [i3]; exact h)
  rw [i3] at r3
  obtain ⟨s₂, r2, q2⟩ := back_k1_of (R := LaterS)
    (fun q gp a b d e x rs gs y hd => (k1_ownLater q gp a b d e x rs gs y hd).2) hS hR O
    (l := l) (by omega) (z := z) (s' := s₃) (by rw [i1]; exact r3)
  rw [i1] at r2
  obtain ⟨s₁, r1, q1⟩ := back_k8_of (R := LaterS)
    (fun p x rs gs y hd => (k8_ownLater p x rs gs y hd).2) hS hR O
    (l := l) (by omega) (z := z) (s' := s₂) (by rw [i8]; exact r2)
  rw [i8] at r1
  exact ⟨s₁, r1, laterZ_trans _ _ _ (laterZ_of_laterS (LaterS.trans _ _ _ q1 q2)) q3⟩

/-- **AT A LAYERS' SEGMENT: BACK TO THE BORDER BEHIND THE LAYERS' OWN KIND's SUB-PROTOCOL.** -/
theorem laterZ_back_layers (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ LaterZ s s' := by
  have i3 : IM.k3Ix (2 * g) true = 6 := by
    show (if true = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    rfl
  have e9 : 28 * g + 9 = 14 * (2 * g) + IM.k3Ix (2 * g) true + 2 + 1 := by
    rw [i3]
    omega
  rw [e9] at h
  obtain ⟨s₃, r3, q3⟩ := back_k3_later hS hR O hp (l := 2 * g) (by omega) h
  have e8 : 14 * (2 * g) + IM.k3Ix (2 * g) true + 2 = 28 * g + 8 := by
    rw [i3]
    omega
  rw [e8] at r3
  obtain ⟨s₀, r0, q0⟩ := ownLater_back hS hR O hg r3
  exact ⟨s₀, r0, laterZ_trans _ _ _ (laterZ_of_laterS q0.2) q3⟩

/-- **AT THE HEAD's SEGMENT: FROM 347 BACK TO 343.** -/
theorem laterZ_back_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start 343 (z, s) ∧ LaterZ s s' := by
  obtain ⟨s₄, r4, q4⟩ := back_k11_of (R := LaterS) k11_laterS hS hR O h
  obtain ⟨s₃, r3, q3⟩ := back_k3_later hS hR O hp (l := 24) (by omega) (z := z) (s' := s₄) r4
  obtain ⟨s₂, r2, q2⟩ := back_k1_of (R := LaterS)
    (fun q gp a b d e x rs gs y hd => (k1_ownLater q gp a b d e x rs gs y hd).2) hS hR O
    (l := 24) (by omega) (z := z) (s' := s₃) r3
  obtain ⟨s₁, r1, q1⟩ := back_k8_of (R := LaterS)
    (fun p x rs gs y hd => (k8_ownLater p x rs gs y hd).2) hS hR O
    (l := 24) (by omega) (z := z) (s' := s₂) r2
  exact ⟨s₁, r1, laterZ_trans _ _ _ (laterZ_of_laterS (LaterS.trans _ _ _ q1 q2))
    (laterZ_trans _ _ _ q3 (laterZ_of_laterS q4))⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.laterZ_of_laterS
#print axioms VerifiableInference.Desc.LinkJoin.laterZ_refl
#print axioms VerifiableInference.Desc.LinkJoin.laterZ_trans
#print axioms VerifiableInference.Desc.LinkJoin.later_plan
#print axioms VerifiableInference.Desc.LinkJoin.k11_laterS
#print axioms VerifiableInference.Desc.LinkJoin.later_behind_digits
#print axioms VerifiableInference.Desc.LinkJoin.back_k3_later
#print axioms VerifiableInference.Desc.LinkJoin.laterZ_back
#print axioms VerifiableInference.Desc.LinkJoin.laterZ_back_layers
#print axioms VerifiableInference.Desc.LinkJoin.laterZ_back_head
