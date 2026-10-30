-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/StretchParts.lean: THE STEPS OF StretchBack.lean's WALK ONE BY ONE, EACH
UNDER ITS OWN ONE
PREMISE (that file's steps take the whole `StretchKeeps R`, K3's and K11's fields too); AND A SECOND
RELATION CARRIED: "what a layers' segment's own rounds returned stays, and the ledger is a later
one",
past the sending of the reads with its quiet step, K8 and the sending of the digits. In the goals'
scope. Statements and proofs: calls.

  `back_k8_of`, `back_k1_of`, `back_k3_of` (every segment l < 25), `back_k11_of` (the head),
    `back_readsL_of` (a layers' segment): each: the one text's decision keeps R ⊢ what is reached
    behind the seated sub-protocol comes of a state reached in front of it, R between the two.
  `OwnLater s s'`: s'.own? = s.own? ∧ `LaterS s s'` (Johnson/Desc/First/LedgerLater.lean: where s
holds a
    ledger, s' holds one, and it is a later state of it: no slot is taken back; what is filled
    stays filled, with the same shown scalar and factor; "next" only grows).
  `k1_ownLater`, `k8_ownLater`, `quietLayers_ownLater`: the three texts' decisions keep it: by
    `commitAtS_later`, `layers_later`, `hear_leaves_fork`, `hear_leaves_own`.
  `ownLater_back`: **g < 12: reached at 28 g + 8 (in front of the lookup on the digits) ⊢ there is a
    state reached at 28 g + 5 (behind K4's sub-protocol), with the same public part, OwnLater
    between the two.**
Limits. ON THE DECISIONS ALONE. Nothing past the lookup on the digits: that the ledger behind K3's
hearing is a later one is not shown here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.StretchBack
import Johnson.Desc.First.LedgerLater
import Johnson.Desc.First.K8.LawFunsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S LaterS)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S} {R : S → S → Prop}

theorem back_k3_of
    (h3 : ∀ (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
      (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S ProofFile.Cl},
      K3.theStated claim readers X codes shape a = some b → Decides R b)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2) (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  exact back_of hS hR O (by omega) e1 e2 e4 (fun h => nomatch h) (h3 _ _ _ _ _ _ e3) h

theorem back_k1_of
    (h1 : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
      (arrays : Option (List ℕ)),
      Decides R (K1.laterAt (Cl := Unit) q gp link piece moment arrays))
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + IM.k1Ix l true + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + IM.k1Ix l true + 2) (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, _, _, e4⟩ := IM.k1_digits_of hS hR O l hl
  exact back_of hS hR O (by omega) e1 e2 e4 (fun h => nomatch h)
    (fun s rs gs s' hd => h1 _ _ _ _ _ _ s rs gs s' hd) h

theorem back_k8_of (h8 : ∀ p : First.K8.ParW, Decides R (First.K8.whole p))
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + k8Ix l + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + k8Ix l + 2) (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, Xl, e1, e2, _, _, e4⟩ := IM.k8_alone O l (IM.subAt l) (IM.subs_scope hS hR O l hl)
    (k8Ix l) (k8_kind_at l) (by
      show 2 ≤ 4 + (if l = 24 then 1 else 0) + 1 ∧ 4 + (if l = 24 then 1 else 0) + 1 ≤ 9
      by_cases h24 : l = 24 <;> simp [h24])
  exact back_of hS hR O (by omega) e1 e2 e4 (fun h => nomatch h) (h8 _) h

theorem back_k11_of
    (h11 : ∀ P : Johnson.Desc.First.ForkMerge.HeadMergeP,
      Decides R (Johnson.Desc.First.ForkMerge.headClaimMergeKind P))
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start 346 (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, e1, e2, e4, _⟩ := IM.k11_of hS hR O
  exact back_of hS hR O (l := 24) (i := 8) (by omega) e1 e2 e4 (fun h => nomatch h)
    (fun s rs gs s' hd => h11 _ s rs gs s' hd) h

/-- At a layers' segment: the sending of the reads, with its quiet step. -/
theorem back_readsL_of (ht : ∀ a b c, R a b → R b c → R a c)
    (h1 : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
      (arrays : Option (List ℕ)),
      Decides R (K1.laterAt (Cl := Unit) q gp link piece moment arrays))
    (hq : ∀ P : K8.ReadsQuiet.PG, Decides R (K8.ReadsQuiet.layers P))
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 6) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, k0, _, _, e4⟩ := IM.k1_reads_layers hS hR O g hg
  have e6 : 28 * g + 6 = 14 * (2 * g) + 3 + 2 + 1 := by omega
  have e5 : 14 * (2 * g) + 3 + 2 = 28 * g + 5 := by omega
  rw [e6] at h
  rw [← e5]
  refine back_of hS hR O (l := 2 * g) (i := 3) (by omega) e1 e2 e4 (fun h => nomatch h) ?_ h
  intro s rs gs t hd
  have hd' : (IM.k1Reads Z Bs.G₀ (2 * g) Xl 4 reads).decide s rs gs = .ok t := hd
  unfold IM.k1Reads at hd'
  obtain ⟨m, a1, a2⟩ := Keeps.ebind_ok hd'
  have q1 : R s m := h1 _ _ _ _ _ _ s _ _ m a1
  have q2 : R m t := by
    unfold IM.k1Quiet at a2
    rcases First.K8.Ready.quiet_arms Bs.G₀ (2 * g) Xl _ _ _ _ a2 with ⟨k1, _⟩ | ⟨_, Y, hY, hc⟩
    · rw [k0] at k1
      exact absurd k1 (by decide)
    · rcases hc with ⟨_, hp, _, hq'⟩ | ⟨k2, _⟩
      · exact hq _ m _ _ t hq'
      · rw [← Option.some.inj (hX.symm.trans hY), k0] at k2
        exact absurd k2 (by decide)
  exact ht _ _ _ q1 q2

/-! ## A second relation -/

/-- What the layers' own rounds returned stays, and the ledger is a later one. -/
def OwnLater (s s' : S) : Prop := s'.own? = s.own? ∧ LaterS s s'

theorem ownLater_trans (a b c : S) (h : OwnLater a b) (k : OwnLater b c) : OwnLater a c :=
  ⟨k.1.trans h.1, LaterS.trans a b c h.2 k.2⟩

theorem putLink_own (s : S) (L : LinkCtx) : (s.putLink L).own? = s.own? := by
  unfold S.putLink
  split <;> (try split) <;> simp_all [S.own?]

theorem putFork_own (s : S) (G : Fork) : (s.putFork G).own? = s.own? := by
  unfold S.putFork
  split <;> (try split) <;> simp_all [S.own?]

theorem k1_ownLater (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Decides OwnLater (K1.laterAt (Cl := Unit) q gp link piece moment arrays) := by
  intro s rs gs s' h
  refine ⟨?_, K1.commitAtS_later _ _ _ _ s rs gs s' h⟩
  have h' := h
  unfold K1.laterAt K1.commitAtS at h'
  dsimp only at h'
  split at h'
  · obtain ⟨y, _, rfl⟩ := VerifiableInference.Desc.mapOk h'
    exact ((putFork_own _ _).trans (putLink_own _ _)).trans rfl
  · cases h'

theorem k8_ownLater (p : First.K8.ParW) : Decides OwnLater (First.K8.whole p) := by
  intro s rs gs s' h
  refine ⟨First.K8.hear_leaves_own (Cl := Claim) p.toPar s rs gs s' h, fun G hG => ?_⟩
  exact ⟨G, (First.K8.hear_leaves_fork (Cl := Claim) p.toPar s rs gs s' h).trans hG,
    PscRun.Later.refl G⟩

theorem quietLayers_ownLater (P : K8.ReadsQuiet.PG) :
    Decides OwnLater (K8.ReadsQuiet.layers P) := by
  intro s rs gs s' h
  refine ⟨?_, K8.ReadsQuiet.layers_later P s rs gs s' h⟩
  have h' : (match s.here with
      | .lay a => do
        let own ←
          (a.own.elim (.error "reads: the own rounds' record is not laid") .ok : Except String _)
        let tl ← K8.ReadsQuiet.closed P.tl own.funs a.L s.st
        pure { s with here := .lay { a with tl := tl } }
      | _ => .error "reads: no layers' link is open" : Except String S) = .ok s' := h
  split at h'
  · rename_i a ha
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain rfl := Except.ok.inj h'
    simp [S.own?, ha]
  · exact nomatch h'

/-- **FROM THE FRONT OF THE LOOKUP ON THE DIGITS BACK TO THE BORDER BEHIND K4's SUB-PROTOCOL.** -/
theorem ownLater_back (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 8) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ OwnLater s s' := by
  have n24 : 2 * g ≠ 24 := by omega
  have i1 : IM.k1Ix (2 * g) true = 5 := by
    show (if true = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 5
    simp [n24]
  have i8 : k8Ix (2 * g) = 4 := by
    show 4 + (if 2 * g = 24 then 1 else 0) = 4
    simp [n24]
  have e8 : 28 * g + 8 = 14 * (2 * g) + 5 + 2 + 1 := by omega
  rw [e8] at h
  obtain ⟨s₂, r2, q2⟩ := back_k1_of k1_ownLater hS hR O (l := 2 * g) (by omega) (z := z) (s' := s')
    (by rw [i1]; exact h)
  rw [i1] at r2
  obtain ⟨s₁, r1, q1⟩ := back_k8_of k8_ownLater hS hR O (l := 2 * g) (by omega) (z := z)
    (s' := s₂) (by rw [i8]; exact r2)
  rw [i8] at r1
  have e6 : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
  rw [e6] at r1
  obtain ⟨s₀, r0, q0⟩ := back_readsL_of ownLater_trans k1_ownLater quietLayers_ownLater hS hR O hg
    r1
  exact ⟨s₀, r0, ownLater_trans _ _ _ q0 (ownLater_trans _ _ _ q1 q2)⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.back_k3_of
#print axioms VerifiableInference.Desc.LinkJoin.back_k1_of
#print axioms VerifiableInference.Desc.LinkJoin.back_k8_of
#print axioms VerifiableInference.Desc.LinkJoin.back_k11_of
#print axioms VerifiableInference.Desc.LinkJoin.back_readsL_of
#print axioms VerifiableInference.Desc.LinkJoin.ownLater_trans
#print axioms VerifiableInference.Desc.LinkJoin.putLink_own
#print axioms VerifiableInference.Desc.LinkJoin.putFork_own
#print axioms VerifiableInference.Desc.LinkJoin.k1_ownLater
#print axioms VerifiableInference.Desc.LinkJoin.k8_ownLater
#print axioms VerifiableInference.Desc.LinkJoin.quietLayers_ownLater
#print axioms VerifiableInference.Desc.LinkJoin.ownLater_back
