-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/StretchBack.lean: THE STRETCH BETWEEN THE SENDING OF THE READS AND THE
BATCHING, WALKED
BACKWARD STEP BY STEP THROUGH THE SEATED SUB-PROTOCOLS, GENERAL IN THE RELATION R ON THE VERIFIER's
STATE
THAT IS CARRIED: no walk over all kinds. In the goals' scope. Statements and proofs: calls of the
seats in Johnson/IMR.

  `back_of`: THE TOOL: where the sub-protocol number i of segment l is a text, alone, whose decision
    keeps R: what is reached behind it comes of a state reached in front of it, R between the two.
  `StretchKeeps R`: what is asked of R: it passes on (trans); the decisions of K8's text, of K1's
text
    of a later moment, of K3's text with its runs stated and of K11's text keep it.
  `k8Ix`, `k8_kind_at`: K8's number in a segment.
  `back_k3`, `back_k1`, `back_k8` (every segment l < 25), `back_k11` (the head).
  `stretch_back`: **l < 24: reached at 14 l + 9 (in front of the batching) ⊢ there is a state
reached at
    14 l + 6 (behind the sending of the reads), with the same public part, R between the two.**
  `stretch_back_head`: **the like at the head: from 347 back to 343.**
  `back_reads_layers`: at a layers' segment, where the decision of the layers' quiet step keeps R
too:
    from 14 l + 6 back to 14 l + 5 (behind the segment's own kind's sub-protocol).
  `stretch_back_layers`: **so from 28 g + 9 back to 28 g + 5.**
Limits. ON THE DECISIONS ALONE. Nothing on what R is. No soundness statement.

-/
import Johnson.Desc.First.K8.LawCondK1
import Johnson.Desc.FoldKeeps
import Johnson.Road.K4.FunsThirdReached
import Johnson.IMR.K1Scope
import Johnson.IMR.K3Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.K11Seat
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S} {R : S → S → Prop}

/-- **THE TOOL.** -/
theorem back_of (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l i : ℕ} (hl : l ≤ 24)
    {Lk : Link S ProofFile.Cl} {b b' : Block S ProofFile.Cl} {name : String} {a : Place}
    (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (hA : IM.LaidAlone ProofFile.sameReply b b' name a) (hk : a.kind ≠ KindName.K7)
    (hD : Decides R b') {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + i + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + i + 2) (z, s) ∧ R s s' := by
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + i + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O hl i]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  exact ⟨s, hr, hD s rs gs _ ((IM.yes_alone hA hk s _ rs gs).1 hd).1⟩

/-- **WHAT IS ASKED OF THE RELATION.** -/
structure StretchKeeps (R : S → S → Prop) : Prop where
  trans : ∀ a b c, R a b → R b c → R a c
  k8 : ∀ p : First.K8.ParW, Decides R (First.K8.whole p)
  k1 : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)), Decides R (K1.laterAt (Cl := Unit) q gp link piece moment arrays)
  k3 : ∀ (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S ProofFile.Cl},
    K3.theStated claim readers X codes shape a = some b → Decides R b
  k11 : ∀ P : Johnson.Desc.First.ForkMerge.HeadMergeP,
    Decides R (Johnson.Desc.First.ForkMerge.headClaimMergeKind P)

/-- K8's number in segment l. -/
abbrev k8Ix (l : ℕ) : ℕ := 4 + (if l = 24 then 1 else 0)

theorem k8_kind_at (l : ℕ) :
    (kindsBeforeBatching (IM.subAt l) (l == 0))[k8Ix l]? = some KindName.K8 := by
  unfold IM.subAt
  by_cases h24 : l = 24
  · subst h24
    rfl
  · have e : k8Ix l = 4 := by
      show 4 + (if l = 24 then 1 else 0) = _
      rw [if_neg h24]
    rw [e, if_neg h24]
    by_cases he : l % 2 = 0
    · rw [if_pos he]
      cases (l == 0) <;> rfl
    · rw [if_neg he]
      cases (l == 0) <;> rfl

theorem back_k3 (K : StretchKeeps R) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok
    pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2) (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  exact back_of hS hR O (by omega) e1 e2 e4 (fun h => nomatch h) (K.k3 _ _ _ _ _ _ e3) h

theorem back_k1 (K : StretchKeeps R) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok
    pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + IM.k1Ix l true + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + IM.k1Ix l true + 2) (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, _, _, e4⟩ := IM.k1_digits_of hS hR O l hl
  exact back_of hS hR O (by omega) e1 e2 e4 (fun h => nomatch h)
    (fun s rs gs s' hd => K.k1 _ _ _ _ _ _ s rs gs s' hd) h

theorem back_k8 (K : StretchKeeps R) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok
    pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + k8Ix l + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + k8Ix l + 2) (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, Xl, e1, e2, _, _, e4⟩ := IM.k8_alone O l (IM.subAt l) (IM.subs_scope hS hR O l hl)
    (k8Ix l) (k8_kind_at l) (by
      show 2 ≤ 4 + (if l = 24 then 1 else 0) + 1 ∧ 4 + (if l = 24 then 1 else 0) + 1 ≤ 9
      by_cases h24 : l = 24 <;> simp [h24])
  exact back_of hS hR O (by omega) e1 e2 e4 (fun h => nomatch h) (K.k8 _) h

theorem back_k11 (K : StretchKeeps R) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb =
    .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start 346 (z, s) ∧ R s s' := by
  obtain ⟨Lk, b, e1, e2, e4, _⟩ := IM.k11_of hS hR O
  exact back_of hS hR O (l := 24) (i := 8) (by omega) e1 e2 e4 (fun h => nomatch h)
    (fun s rs gs s' hd => K.k11 _ s rs gs s' hd) h

/-- **FROM THE BATCHING's BORDER BACK TO THE BORDER BEHIND THE SENDING OF THE READS.** -/
theorem stretch_back (K : StretchKeeps R) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb
    = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 24) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + 6) (z, s) ∧ R s s' := by
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
  obtain ⟨s₃, r3, q3⟩ := back_k3 K hS hR O (l := l) (by omega) (z := z) (s' := s')
    (by rw [i3]; exact h)
  rw [i3] at r3
  obtain ⟨s₂, r2, q2⟩ := back_k1 K hS hR O (l := l) (by omega) (z := z) (s' := s₃)
    (by rw [i1]; exact r3)
  rw [i1] at r2
  obtain ⟨s₁, r1, q1⟩ := back_k8 K hS hR O (l := l) (by omega) (z := z) (s' := s₂)
    (by rw [i8]; exact r2)
  rw [i8] at r1
  exact ⟨s₁, r1, K.trans _ _ _ q1 (K.trans _ _ _ q2 q3)⟩

/-- **THE LIKE AT THE HEAD.** -/
theorem stretch_back_head (K : StretchKeeps R) (hS : VerifierAndGoals.InScope Pb = true) (hR :
    VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start 343 (z, s) ∧ R s s' := by
  obtain ⟨s₄, r4, q4⟩ := back_k11 K hS hR O h
  obtain ⟨s₃, r3, q3⟩ := back_k3 K hS hR O (l := 24) (by omega) (z := z) (s' := s₄) r4
  obtain ⟨s₂, r2, q2⟩ := back_k1 K hS hR O (l := 24) (by omega) (z := z) (s' := s₃) r3
  obtain ⟨s₁, r1, q1⟩ := back_k8 K hS hR O (l := 24) (by omega) (z := z) (s' := s₂) r2
  exact ⟨s₁, r1, K.trans _ _ _ q1 (K.trans _ _ _ q2 (K.trans _ _ _ q3 q4))⟩

/-- At a layers' segment: the sending of the reads, with its quiet step. -/
theorem back_reads_layers (K : StretchKeeps R)
    (hq : ∀ P : K8.ReadsQuiet.PG, Decides R (K8.ReadsQuiet.layers P)) (hS : VerifierAndGoals.InScope Pb =
    true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 24)
    (hk0 : ∀ X, Bs.G₀.built[l]? = some X → X.kind = 0) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 6) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + 5) (z, s) ∧ R s s' := by
  have n24 : l ≠ 24 := by omega
  have i1 : IM.k1Ix l false = 3 := by
    show (if false = true then 5 else 3) + (if l = 24 then 1 else 0) = 3
    simp [n24]
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, _, e4⟩ := IM.k1_reads_of hS hR O l (by omega)
  rw [i1] at e2
  refine back_of hS hR O (l := l) (i := 3) (by omega) e1 e2 e4 (fun h => nomatch h) ?_ h
  intro s rs gs t hd
  have hd' : (IM.k1Reads Z Bs.G₀ l Xl (IM.k1Ix l false + 1) reads).decide s rs gs = .ok t := hd
  unfold IM.k1Reads at hd'
  obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok hd'
  have q1 : R s m := K.k1 _ _ _ _ _ _ s _ _ m h1
  have q2 : R m t := by
    unfold IM.k1Quiet at h2
    rcases First.K8.Ready.quiet_arms Bs.G₀ l Xl _ _ _ _ h2 with ⟨k1, _⟩ | ⟨_, Y, hY, hc⟩
    · rw [hk0 Xl hX] at k1
      exact absurd k1 (fun h => nomatch h)
    · rcases hc with ⟨_, hp, _, hq'⟩ | ⟨k2, _⟩
      · exact hq _ m _ _ t hq'
      · rw [hk0 Y hY] at k2
        exact absurd k2 (fun h => nomatch h)
  exact K.trans _ _ _ q1 q2

/-- **FROM THE BATCHING's BORDER BACK TO THE BORDER BEHIND THE LAYERS' OWN KIND's SUB-PROTOCOL.** -/
theorem stretch_back_layers (K : StretchKeeps R)
    (hq : ∀ P : K8.ReadsQuiet.PG, Decides R (K8.ReadsQuiet.layers P))
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ R s s' := by
  have hk0 : ∀ X, Bs.G₀.built[2 * g]? = some X → X.kind = 0 := by
    intro X hX
    obtain ⟨m, -, fm, km, -⟩ := (IM.ground_named hS hR O.pub O.blank).1 g hg
    rw [← Option.some.inj (fm.symm.trans hX)]
    exact km
  have e9 : 28 * g + 9 = 14 * (2 * g) + 9 := by omega
  rw [e9] at h
  obtain ⟨s₁, r1, q1⟩ := stretch_back K hS hR O (l := 2 * g) (by omega) h
  obtain ⟨s₀, r0, q0⟩ := back_reads_layers K hq hS hR O (l := 2 * g) (by omega) hk0 r1
  have e5 : 14 * (2 * g) + 5 = 28 * g + 5 := by omega
  rw [e5] at r0
  exact ⟨s₀, r0, K.trans _ _ _ q0 q1⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.back_of
#print axioms VerifiableInference.Desc.LinkJoin.k8_kind_at
#print axioms VerifiableInference.Desc.LinkJoin.back_k3
#print axioms VerifiableInference.Desc.LinkJoin.back_k1
#print axioms VerifiableInference.Desc.LinkJoin.back_k8
#print axioms VerifiableInference.Desc.LinkJoin.back_k11
#print axioms VerifiableInference.Desc.LinkJoin.stretch_back
#print axioms VerifiableInference.Desc.LinkJoin.stretch_back_head
#print axioms VerifiableInference.Desc.LinkJoin.back_reads_layers
#print axioms VerifiableInference.Desc.LinkJoin.stretch_back_layers
