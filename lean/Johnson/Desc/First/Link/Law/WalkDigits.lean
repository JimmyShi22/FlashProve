-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/WalkDigits.lean: THE STRETCH FROM THE BORDER BEHIND A SEGMENT's OWN KIND
UP TO THE FRONT OF ITS BATCHING, WALKED BACK ONCE, FOR ANY RELATION THAT EACH STEP's DECISION KEEPS.
A structure, and theorems: joins of other files' lemmas.
Why. LaterStretch.lean's `laterZ_back`, `laterZ_back_layers`, `laterZ_back_head` end in "there is a
state s reached in front, with `LaterZ s s'`". A second walk for another relation would name a state
of its own, and a reached state has no one predecessor: SO TWO SUCH ENDS CANNOT BE LAID TOGETHER.
Here the walk is general in the relation, and two relations that walk, walk together.
  `WalkKeeps R`: what is asked of R: it goes on; the decisions of K8's text, K1's later text, the
    layers' step without a round and the merge keep it; and so does the decision of `K3.theStated`'s
    value AT THE DIGITS' ADDRESS, ITS TEST ON THE PLAN PASSED (StretchBack.lean's `StretchKeeps`
    asks this at every address, with no premise on the plan).
  `WalkKeeps.and`: **two relations together.** `walk_of_stretch`: from `StretchKeeps`.
    `laterZ_walks`: `LaterZ` walks. `sizesS_walks`: `SizesS` (SizesStretch.lean) walks, UNDER h3:
    the field k3 for it: SizesDigits.lean has h3 (`k3_sizesS`).
  `walkD_k3`: one step back over the digits' seated sub-protocol. `walkD_back`: **from 14 l + 9 back
    to 14 l + 6** (l < 24). `walkD_layers`: **from 28 g + 9 back to 28 g + 5** (g < 12).
    `walkD_head`: **from 347 back to 343.**
  `later_sized_back`, `later_sized_layers`, `later_sized_head`: **where the state in front of the
    batching holds a ledger with its sizes: ONE state s reached at the earlier border, whose ledger
    F has its sizes, with the later ledger a later state of F, and R s s'.**
PREMISES. The scope (hS, hR, `IM.Open`); hp: every sub-protocol of the first chain passes its test
on the plan; "reached"; in the last three: h3.
Limits. h3 is shown in SizesDigits.lean (`k3_sizesS`), not here. On the decisions alone: nothing on
the runs of claims. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LaterStretch
import Johnson.Desc.First.Link.Law.SizesStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S LaterS)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **WHAT IS ASKED OF THE RELATION.** -/
structure WalkKeeps (R : S → S → Prop) : Prop where
  trans : ∀ a b c, R a b → R b c → R a c
  k8 : ∀ p : First.K8.ParW, Decides R (First.K8.whole p)
  k1 : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)), Decides R (K1.laterAt (Cl := Unit) q gp link piece moment arrays)
  quietL : ∀ P : K8.ReadsQuiet.PG, Decides R (K8.ReadsQuiet.layers P)
  /-- at the digits' address, the test on the plan passed -/
  k3 : ∀ (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S ProofFile.Cl) (i : ℕ),
    K3.theStated claim readers X codes shape a = some B → B.planOk = true → a.link = some i →
      a.piece = K3.pieceAt X i true → Decides R B
  k11 : ∀ P : Johnson.Desc.First.ForkMerge.HeadMergeP, Decides R (headClaimMergeKind P)

/-- **TWO RELATIONS THAT WALK, WALK TOGETHER.** -/
theorem WalkKeeps.and {R R' : S → S → Prop} (h : WalkKeeps R) (k : WalkKeeps R') :
    WalkKeeps fun s s' => R s s' ∧ R' s s' where
  trans := fun a b c x y => ⟨h.trans a b c x.1 y.1, k.trans a b c x.2 y.2⟩
  k8 := fun p => decides_and (h.k8 p) (k.k8 p)
  k1 := fun q gp a b d e => decides_and (h.k1 q gp a b d e) (k.k1 q gp a b d e)
  quietL := fun P => decides_and (h.quietL P) (k.quietL P)
  k3 := fun cl rd X cs sh a B i e1 e2 e3 e4 =>
    decides_and (h.k3 cl rd X cs sh a B i e1 e2 e3 e4) (k.k3 cl rd X cs sh a B i e1 e2 e3 e4)
  k11 := fun P => decides_and (h.k11 P) (k.k11 P)

/-- From the wider structure. -/
theorem walk_of_stretch {R : S → S → Prop} (K : StretchKeeps R)
    (hq : ∀ P : K8.ReadsQuiet.PG, Decides R (K8.ReadsQuiet.layers P)) : WalkKeeps R where
  trans := K.trans
  k8 := K.k8
  k1 := K.k1
  quietL := hq
  k3 := fun cl rd X cs sh a _ _ e1 _ _ _ => K.k3 cl rd X cs sh a e1
  k11 := K.k11

/-- **`LaterZ` WALKS.** -/
theorem laterZ_walks : WalkKeeps LaterZ where
  trans := laterZ_trans
  k8 := fun p x rs gs y hd => laterZ_of_laterS (k8_ownLater p x rs gs y hd).2
  k1 := fun q gp a b d e x rs gs y hd => laterZ_of_laterS (k1_ownLater q gp a b d e x rs gs y hd).2
  quietL := fun P x rs gs y hd => laterZ_of_laterS (quietLayers_ownLater P x rs gs y hd).2
  k3 := fun cl rd X cs sh a B i e1 e2 e3 e4 s rs gs t hd _ hG hz =>
    later_behind_digits cl rd X cs sh a B e1 e2 i e3 e4 s t rs gs hd hG hz
  k11 := fun P x rs gs y hd => laterZ_of_laterS (k11_laterS P x rs gs y hd)

/-- **`SizesS` WALKS, UNDER ITS STEP OVER THE DIGITS' LOOKUP.** -/
theorem sizesS_walks
    (h3 : ∀ (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S ProofFile.Cl) (i : ℕ),
    K3.theStated claim readers X codes shape a = some B → B.planOk = true → a.link = some i →
      a.piece = K3.pieceAt X i true → Decides SizesS B) : WalkKeeps SizesS where
  trans := SizesS.trans
  k8 := k8_sizesS
  k1 := k1_sizesS
  quietL := quietLayers_sizesS
  k3 := h3
  k11 := k11_sizesS

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S} {R : S → S → Prop}

/-- **One step back over the digits' seated sub-protocol.** -/
theorem walkD_k3 (K : WalkKeeps R)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2) (z, s) ∧ R s s' := by
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
  exact back_of (R := R) hS hR O (by omega) e1 e2 e4 (fun h => nomatch h)
    (K.k3 _ _ _ _ _ _ b' l e3 hOk rfl (piece_digits _ _ _ _ _ _ b' e3 l rfl h7)) h

/-- **FROM THE BATCHING's BORDER BACK TO THE BORDER BEHIND THE SENDING OF THE READS.** -/
theorem walkD_back (K : WalkKeeps R)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s')) :
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
  obtain ⟨s₃, r3, q3⟩ := walkD_k3 K hS hR O hp (l := l) (by omega) (z := z) (s' := s')
    (by rw [i3]; exact h)
  rw [i3] at r3
  obtain ⟨s₂, r2, q2⟩ := back_k1_of (R := R) K.k1 hS hR O (l := l) (by omega) (z := z) (s' := s₃)
    (by rw [i1]; exact r3)
  rw [i1] at r2
  obtain ⟨s₁, r1, q1⟩ := back_k8_of (R := R) K.k8 hS hR O (l := l) (by omega) (z := z) (s' := s₂)
    (by rw [i8]; exact r2)
  rw [i8] at r1
  exact ⟨s₁, r1, K.trans _ _ _ q1 (K.trans _ _ _ q2 q3)⟩

/-- **AT A LAYERS' SEGMENT: BACK TO THE BORDER BEHIND THE LAYERS' OWN KIND's SUB-PROTOCOL.** -/
theorem walkD_layers (K : WalkKeeps R)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ R s s' := by
  have e9 : 28 * g + 9 = 14 * (2 * g) + 9 := by omega
  rw [e9] at h
  obtain ⟨s₁, r1, q1⟩ := walkD_back K hS hR O hp (l := 2 * g) (by omega) h
  have e6 : 14 * (2 * g) + 6 = 28 * g + 6 := by omega
  rw [e6] at r1
  obtain ⟨s₀, r0, q0⟩ := back_readsL_of (R := R) K.trans K.k1 K.quietL hS hR O hg r1
  exact ⟨s₀, r0, K.trans _ _ _ q0 q1⟩

/-- **AT THE HEAD's SEGMENT: FROM 347 BACK TO 343.** -/
theorem walkD_head (K : WalkKeeps R)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start 343 (z, s) ∧ R s s' := by
  obtain ⟨s₄, r4, q4⟩ := back_k11_of (R := R) K.k11 hS hR O h
  obtain ⟨s₃, r3, q3⟩ := walkD_k3 K hS hR O hp (l := 24) (by omega) (z := z) (s' := s₄) r4
  obtain ⟨s₂, r2, q2⟩ := back_k1_of (R := R) K.k1 hS hR O (l := 24) (by omega) (z := z) (s' := s₃)
    r3
  obtain ⟨s₁, r1, q1⟩ := back_k8_of (R := R) K.k8 hS hR O (l := 24) (by omega) (z := z) (s' := s₂)
    r2
  exact ⟨s₁, r1, K.trans _ _ _ q1 (K.trans _ _ _ q2 (K.trans _ _ _ q3 q4))⟩

/-- What the three relations together give at one pair of states. -/
theorem later_sized_of {s s' : S} (h : (LaterZ s s' ∧ SizesS s s') ∧ R s s')
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ F F', s.fork? = some F ∧ Sized F ∧ s'.fork? = some F' ∧ PscRun.Later F F' ∧ R s s' := by
  obtain ⟨G, hG, hz⟩ := h.1.2.pulls hB
  obtain ⟨F', hF', hl⟩ := h.1.1 G hG hz
  exact ⟨G, F', hG, hz, hF', hl, h.2⟩

/-- **ONE STATE: ITS LEDGER HAS ITS SIZES, THE LATER LEDGER IS A LATER STATE OF IT, AND R.** -/
theorem later_sized_back (K : WalkKeeps R)
    (h3 : ∀ (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S ProofFile.Cl) (i : ℕ),
    K3.theStated claim readers X codes shape a = some B → B.planOk = true → a.link = some i →
      a.piece = K3.pieceAt X i true → Decides SizesS B)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ s F F', Reach 0 c.blocksInOrder start (14 * l + 6) (z, s) ∧ s.fork? = some F ∧ Sized F ∧
      s'.fork? = some F' ∧ PscRun.Later F F' ∧ R s s' := by
  obtain ⟨s, r, q⟩ := walkD_back ((laterZ_walks.and (sizesS_walks h3)).and K) hS hR O hp hl h
  obtain ⟨G, G', a⟩ := later_sized_of q hB
  exact ⟨s, G, G', r, a⟩

theorem later_sized_layers (K : WalkKeeps R)
    (h3 : ∀ (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S ProofFile.Cl) (i : ℕ),
    K3.theStated claim readers X codes shape a = some B → B.planOk = true → a.link = some i →
      a.piece = K3.pieceAt X i true → Decides SizesS B)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ s F F', Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ s.fork? = some F ∧ Sized F ∧
      s'.fork? = some F' ∧ PscRun.Later F F' ∧ R s s' := by
  obtain ⟨s, r, q⟩ := walkD_layers ((laterZ_walks.and (sizesS_walks h3)).and K) hS hR O hp hg h
  obtain ⟨G, G', a⟩ := later_sized_of q hB
  exact ⟨s, G, G', r, a⟩

theorem later_sized_head (K : WalkKeeps R)
    (h3 : ∀ (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S ProofFile.Cl) (i : ℕ),
    K3.theStated claim readers X codes shape a = some B → B.planOk = true → a.link = some i →
      a.piece = K3.pieceAt X i true → Decides SizesS B)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ s F F', Reach 0 c.blocksInOrder start 343 (z, s) ∧ s.fork? = some F ∧ Sized F ∧
      s'.fork? = some F' ∧ PscRun.Later F F' ∧ R s s' := by
  obtain ⟨s, r, q⟩ := walkD_head ((laterZ_walks.and (sizesS_walks h3)).and K) hS hR O hp h
  obtain ⟨G, G', a⟩ := later_sized_of q hB
  exact ⟨s, G, G', r, a⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.WalkKeeps.and
#print axioms VerifiableInference.Desc.LinkJoin.walk_of_stretch
#print axioms VerifiableInference.Desc.LinkJoin.laterZ_walks
#print axioms VerifiableInference.Desc.LinkJoin.sizesS_walks
#print axioms VerifiableInference.Desc.LinkJoin.walkD_k3
#print axioms VerifiableInference.Desc.LinkJoin.walkD_back
#print axioms VerifiableInference.Desc.LinkJoin.walkD_layers
#print axioms VerifiableInference.Desc.LinkJoin.walkD_head
#print axioms VerifiableInference.Desc.LinkJoin.later_sized_of
#print axioms VerifiableInference.Desc.LinkJoin.later_sized_back
#print axioms VerifiableInference.Desc.LinkJoin.later_sized_layers
#print axioms VerifiableInference.Desc.LinkJoin.later_sized_head
