-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean: OkHead's CLAUSE k6 (OkOne.lean) AT EVERY STATE
REACHED IN FRONT OF THE OUTPUT HEAD's BATCHING (border 347): what the head has heard is read back
there. Joins of lemmas in the library or listed for it; one tool after StretchBack.lean's pattern.
Why. K6HeardAt is had at 342 (P4.heard_342, Johnson/P4R/Head342.lean); the batching stands five
sub-protocols on; Kinds/Law/K6Claims.lean carries it along AlikeFront (k6HeardAt_front) and leaves
"KeepsK6" to each kind's files (Johnson/Desc/Kinds/Law/K6PromiseBorder.lean).
  FrontLater s s'    SameFront s s' (FrontStays.lean) ∧ LaterZ s s' (LaterStretch.lean)
  backB_of           back_of (StretchBack.lean) over the list of the sub-protocols AS THE IOP
                     WRITTEN IN LEAN WRAPS THEM: heard_342 wants canonical rounds, which the
                     wrapped "reached" alone gives
  the five accepts   k11_frontLater (it also hands: the state in front stands in the head's segment,
                     opened) · k1Later_frontLater · k8_frontLater · k1Reads_frontLater; the lookup
                     on the digits inside the walk (k3Digits_front, later_behind_digits)
  **frontLater_back_head**   from 347 back to 342: a reached state in the head's segment, opened,
                     with FrontLater up to the state at 347
  alikeFront_of_later   AlikeFront from FrontLater, where the ledger in front has its sizes
  **k6HeardAt_347**  K6HeardAt at every state reached at 347
  **k6_at_347**      the clause k6, to the letter, at the fixed part of such a state: one call of
                     k6Ready_fixed; general in φ and kap
WHERE THE SIZES COME FROM. Out of K6HeardAt at 342 itself: the ledger that the head's hearing began
from is well laid; the hearing and what follows give later ledgers (keeps_hear; wellLaid_later).
PREMISES. The scope (hS, hR, IM.Open); hOk: the description's test on the plan; "reached" at the IOP
as written in Lean. NO PROMISE OF THE TABLE IS SPENT, AND NOT "no mark".
Limits. ON THE DECISIONS ALONE: nothing on the runs of claims. That a state is reached at 347 is
not shown. Nothing at another border. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FrontStays
import Johnson.Desc.First.Link.Law.LaterStretch
import Johnson.Desc.Kinds.Law.K6PromiseBorder
import Johnson.Desc.Kinds.Law.KeepsHear
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.P4R.Head342

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S LaterS)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Kinds.Head (seatAt parOf)
open VerifiableInference.Desc.Kinds.Head.Law (AlikeFront K6HeardAt K6Ready k6HeardAt_front
  k6Ready_fixed readsOf workOf seenOf Seen)
open Johnson.Desc.First.ForkMerge (headMergeDecide headClaimMergeKind)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide stepYes_raw RchAt)
open OnBytes.Road.K4 (reach_pred)

/-- What AlikeFront compares stays, and the ledger, where it has its sizes, is a later one. -/
def FrontLater (s s' : S) : Prop := SameFront s s' ∧ LaterZ s s'

theorem frontLater_trans (a b c : S) (h : FrontLater a b) (k : FrontLater b c) : FrontLater a c :=
  ⟨sameFront_trans _ _ _ h.1 k.1, laterZ_trans _ _ _ h.2 k.2⟩

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S} {R : S → S → Prop}

/-- **back_of (StretchBack.lean) over the list of the sub-protocols as the IOP written in Lean wraps
them.** -/
theorem backB_of (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l i : ℕ} (hl : l ≤ 24)
    {Lk : Link S ProofFile.Cl} {b b' : Block S ProofFile.Cl} {name : String} {a : Place}
    (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (hA : IM.LaidAlone ProofFile.sameReply b b' name a) (hk : a.kind ≠ KindName.K7)
    (hD : Decides R b') {z : Q} {s' : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) start (14 * l + i + 2 + 1) (z, s')) :
    ∃ s, Reach 0 (c.blocksInOrder.map Sound.below) start (14 * l + i + 2) (z, s) ∧ R s s' := by
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + i + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O hl i]
    exact IM.hear_at_flat e1 e2
  rw [List.getElem?_map, hf] at hb
  obtain rfl : Sound.below b = b₀ := Option.some.inj hb
  obtain ⟨rs, gs, hd⟩ := stepYes_decide (stepYes_raw hy)
  exact ⟨s, hr, hD s rs gs _ ((IM.yes_alone hA hk s _ rs gs).1 hd).1⟩

/-! ## The five accepts -/

theorem k11_frontLater (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Decides (fun s s' => FrontLater s s' ∧ ∃ a, s.here = .head a ∧ a.opened = true)
      (headClaimMergeKind P) := by
  intro s rs gs s' h
  refine ⟨⟨k11_front P s rs gs s' h, laterZ_of_laterS (k11_laterS P s rs gs s' h)⟩, ?_⟩
  have h' : headMergeDecide P s rs = .ok s' := h
  unfold headMergeDecide at h'
  split at h'
  · rename_i a ha
    obtain ⟨_, ho, _⟩ := K9L.ok_bind h'
    refine ⟨a, ha, ?_⟩
    by_contra hn
    simp [need, hn] at ho
  · exact nomatch h'

theorem k1Later_frontLater (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) :
    Decides FrontLater (K1.laterAt (Cl := Unit) q gp link piece moment arrays) :=
  fun s rs gs s' h => ⟨commitAtS_front _ _ _ _ s rs gs s' h,
    laterZ_of_laterS (k1_ownLater q gp link piece moment arrays s rs gs s' h).2⟩

theorem k8_frontLater (p : First.K8.ParW) : Decides FrontLater (First.K8.whole p) :=
  fun s rs gs s' h => ⟨k8_front p s rs gs s' h, laterZ_of_laterS (k8_ownLater p s rs gs s' h).2⟩

/-- The step without a round behind the reads' sending leaves the ledger. -/
theorem k1Quiet_fork (G : ProofFile.Ground) (l : Nat) (X : OnBytes.Model.Stages.LinkH) :
    Decides (fun s s' : S => s'.fork? = s.fork?) (IM.k1Quiet G l X) := by
  refine K1.k1Quiet_decides _ (fun P s rs gs s' h => ?_) (fun P s rs gs s' h => ?_)
    (fun A s s' h => ?_) G l X
  · obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
    simp [S.fork?, ha]
  · obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
    simp [S.fork?, ha]
  · obtain ⟨a, t, tl, ha, rfl⟩ := _root_.Meaning.K2.readsAtSO_eq h
    simp [S.fork?, ha]

theorem k1Reads_frontLater (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat)
    (X : OnBytes.Model.Stages.LinkH) (pr : Nat) (reads : Option (List Nat)) :
    Decides FrontLater (IM.k1Reads Z G l X pr reads) := by
  intro s rs gs t hd
  have hd' := hd
  unfold IM.k1Reads at hd'
  obtain ⟨m, a1, a2⟩ := Keeps.ebind_ok hd'
  have q1 : FrontLater s m := k1Later_frontLater _ _ _ _ _ _ s _ _ m a1
  have q2 : FrontLater m t := ⟨k1Quiet_front G l X m _ _ t a2, fun F hF _ =>
    ⟨F, (k1Quiet_fork G l X m _ _ t a2).trans hF, PscRun.Later.refl F⟩⟩
  exact frontLater_trans _ _ _ q1 q2

/-! ## The walk -/

/-- **FROM THE FRONT OF THE HEAD's BATCHING BACK TO THE BORDER BEHIND THE HEAD's OWN ROUNDS.** -/
theorem frontLater_back_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {s' : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) start 347 (z, s')) :
    ∃ s o, Reach 0 (c.blocksInOrder.map Sound.below) start 342 (z, s) ∧ s.here = .head o ∧
      o.opened = true ∧ FrontLater s s' := by
  -- 346: the merge
  obtain ⟨Lk, b, e1, e2, e4, _⟩ := IM.k11_of hS hR O
  obtain ⟨s₄, r4, q4, a4, ha4, ho4⟩ := backB_of hS hR O (l := 24) (i := 8) (by omega) e1 e2 e4
    (fun h => nomatch h) (fun s rs gs s' hd => k11_frontLater _ s rs gs s' hd) h
  -- 345: the lookup on the digits
  obtain ⟨Lk3, b3, b3', f1, f2, f3, f4⟩ := IM.k3_of hS hR O 24 (by omega) true
  have hf3 : c.blocksInOrder[14 * 24 + IM.k3Ix 24 true + 2]? = some b3 := by
    rw [← IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) (IM.k3Ix 24 true)]
    exact IM.hear_at_flat f1 f2
  have hOk3 : b3'.planOk = true := by
    rw [← IM.alone_planOk f4]
    exact hp b3 (List.mem_of_getElem? hf3)
  have h7 : 7 ≤ (IM.k3Place 24 true).piece := by decide
  have hpc := piece_digits _ _ _ _ _ _ b3' f3 24 rfl h7
  obtain ⟨s₃, r3, q3⟩ := backB_of (R := FrontLater) hS hR O (l := 24) (i := IM.k3Ix 24 true)
    (by omega) f1 f2 f4 (fun h => nomatch h)
    (fun s rs gs t hd => ⟨k3Digits_front _ _ _ _ _ _ b3' f3 hOk3 24 rfl hpc s rs gs t hd,
      fun G hG hz => later_behind_digits _ _ _ _ _ _ b3' f3 hOk3 24 rfl hpc s t rs gs hd hG hz⟩)
    r4
  -- 344: the digits' sending
  obtain ⟨Lk1, b1, Xl, pr, reads, digits, g1, g2, _, _, g4⟩ := IM.k1_digits_of hS hR O 24 (by omega)
  obtain ⟨s₂, r2, q2⟩ := backB_of (R := FrontLater) hS hR O (l := 24) (i := IM.k1Ix 24 true)
    (by omega) g1 g2 g4 (fun h => nomatch h)
    (fun s rs gs t hd => k1Later_frontLater _ _ _ _ _ _ s rs gs t hd) r3
  -- 343: the smallness test's hearing
  obtain ⟨Lk8, b8, X8, k1, k2, _, _, k4⟩ := IM.k8_alone O 24 (IM.subAt 24)
    (IM.subs_scope hS hR O 24 (by omega)) (k8Ix 24) (k8_kind_at 24) (by decide)
  obtain ⟨s₁, r1, q1⟩ := backB_of (R := FrontLater) hS hR O (l := 24) (i := k8Ix 24)
    (by omega) k1 k2 k4 (fun h => nomatch h) (k8_frontLater _) r2
  -- 342: the reads' sending
  obtain ⟨Lk0, b0, X0, pd, reads0, digits0, m1, m2, _, _, m4⟩ :=
    IM.k1_reads_of hS hR O 24 (by omega)
  obtain ⟨s₀, r0, q0⟩ := backB_of (R := FrontLater) hS hR O (l := 24) (i := IM.k1Ix 24 false)
    (by omega) m1 m2 m4 (fun h => nomatch h)
    (fun s rs gs t hd => k1Reads_frontLater _ _ _ _ _ _ s rs gs t hd) r1
  have q04 : FrontLater s₀ s₄ :=
    frontLater_trans _ _ _ q0 (frontLater_trans _ _ _ q1 (frontLater_trans _ _ _ q2 q3))
  have hfr : frontSix s₄ = frontSix s₀ := q04.1
  have hh : ∃ o, s₀.here = .head o ∧ o.opened = true := by
    unfold frontSix at hfr
    rw [ha4] at hfr
    cases hs : s₀.here with
    | head o =>
      rw [hs] at hfr
      simp only [Prod.mk.injEq, Option.some.injEq] at hfr
      exact ⟨o, rfl, hfr.1.2.2.1 ▸ ho4⟩
    | _ => rw [hs] at hfr; simp at hfr
  obtain ⟨o, ho, hop⟩ := hh
  exact ⟨s₀, o, r0, ho, hop, frontLater_trans _ _ _ q04 q4⟩

/-- **AlikeFront**, from a state in the head's segment, opened, whose ledger has its sizes. -/
theorem alikeFront_of_later {s s' : S} (h : FrontLater s s') {o : First.HeadOwn}
    (ho : s.here = .head o) (hop : o.opened = true) (hz : Sized o.F) : AlikeFront s s' := by
  have hF : s.fork? = some o.F := by simp [S.fork?, ho, hop]
  obtain ⟨F', hF', hL⟩ := h.2 o.F hF hz
  have hfr : frontSix s' = frontSix s := h.1
  unfold frontSix at hfr
  rw [ho] at hfr
  cases hs : s'.here with
  | head o' =>
    rw [hs] at hfr
    simp only [Prod.mk.injEq, Option.some.injEq] at hfr
    obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6⟩ := hfr
    have hF2 : s'.fork? = some o'.F := by simp [S.fork?, hs, e3, hop]
    obtain rfl : F' = o'.F := Option.some.inj (hF'.symm.trans hF2)
    exact ⟨o, o', ho, hs, e1, e2, e3, e4, e5, e6, hL⟩
  | _ => rw [hs] at hfr; simp at hfr

/-- **(A) WHAT THE HEAD HAS HEARD IS READ BACK AT EVERY STATE REACHED IN FRONT OF THE HEAD's
BATCHING.** -/
theorem k6HeardAt_347 {Str : Type} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (h : RchAt (P4.FD Z A B c) 347 a) :
    K6HeardAt Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) a.1.2 := by
  have h' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (a.1.1, a.1.2) := h
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
    have e := O.desc
    subst e
    exact (VerifiableInference.Desc.Keeps.planOk_blocks _ hOk).1
  obtain ⟨s, o, r, ho, hop, q⟩ := frontLater_back_head hS hR O hp h'
  have k : K6HeardAt Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) s :=
    P4.heard_342 hS hR O hOk (Str := Unit) ((a.1.1, s), ()) r
  have hz : Sized o.F := by
    obtain ⟨g, H, F0, G, rs, _, _, hW, hh, hL⟩ := k
    have e : (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s = o.F := by
      show s.fork?.getD {} = o.F
      simp [S.fork?, ho, hop]
    rw [e] at hL
    exact Kinds.Head.Law.sized_of_wellLaid (Kinds.Head.Law.Came.wellLaid_later
      (Kinds.Head.Law.Came.wellLaid_later hW (Kinds.Head.Law.keeps_hear _ _ _ _ _ hh)) hL)
  exact k6HeardAt_front _ _ _ (alikeFront_of_later q ho hop hz) k

/-- **(B) OkHead's CLAUSE k6**, at the fixed part of such a state. -/
theorem k6_at_347 {Str α : Type} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (φ : S → α) (kap : α → Option Seen) (hkap : ∀ e, kap (φ e) = seenOf e)
    (a : (ProofFile.InstPub × S) × Str) (h : RchAt (P4.FD Z A B c) 347 a) :
    ∀ z u, kap (K9L.fixed9 φ a.1.2).1 = some z →
      (K9L.fixed9 φ a.1.2).2 = some u →
      K6Ready Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) z u.F :=
  k6Ready_fixed _ _ _ φ kap hkap a.1.2 (k6HeardAt_347 hS hR O hOk a h)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frontLater_back_head
#print axioms VerifiableInference.Desc.LinkJoin.alikeFront_of_later
#print axioms VerifiableInference.Desc.LinkJoin.k6HeardAt_347
#print axioms VerifiableInference.Desc.LinkJoin.k6_at_347
