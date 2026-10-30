-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RunCores.lean: EACH RUN THAT A SEGMENT's ORDER NAMES LEAVES THE LEDGER's CORE, run by run: the
premise `cores` of the gathering theorem (Honest/K9/RunFrame.lean), paid at the seated link under the library's hypothesis
`AtMgA`. The library proves the same of the whole gatherer (`core_layers`, `core_att`, `core_head`,
Johnson/Desc/K8/Honest/CoreGathers.lean); the lists of entries inside those proofs are written out here as statements.

  `keepsCore_k8`        the smallness test's run "K8.equations" leaves the ledger's ten fields
  `coreOk_of_cut`       an order cut at "K8.equations": each run of the whole order stands under a run that keeps them
  `coreOk_layers`, `coreOk_att`, `coreOk_head`    that, under each sort's ties and order
  `runKeeps_of_coreOk`  from `SameCore` under a run to `RunKeeps` of the run at the entry
  `coreOk_seat_layers`, `coreOk_seat_att`, `coreOk_seat_head`   the ties, taken where the description is opened
  **`cores_at_head`**     at each of the 25 segments: every run that the order names satisfies `RunKeeps`

Limits. Nothing here says that a run returns. The full size and the hash function `secondHashFunction` alone, as in the hypothesis. This
file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.Desc.ProofFile.Honest.K9.GatherFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (KeepsCore CoreOk SameCore attPre headPre headPost core_objects core_idle
  core_front core_behind core_first core_keys core_second core_join core_planes core_k6 core_merge)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open P5J (AtMgA)

/-- The run "K8.equations" leaves the ledger's ten fields. -/
theorem keepsCore_k8 : KeepsCore K9L.k8Run.2 := by
  intro n t y a hy ha
  obtain ⟨c, e⟩ := y
  obtain ⟨F, tl, funs, tl', F₂, b2, b3, b4, b5, b6⟩ := K9L.k8Run_ok _ _ _ _ hy
  obtain rfl : a.F = F := Option.some.inj ((Desc.K9.get_fork _ _ ha).symm.trans b2)
  obtain ⟨x₂, hx₂, hF₂, -⟩ := K9L.get_put t a ha tl' F₂
  refine ⟨x₂, ?_, ?_⟩
  · show Desc.K9.atS.get? e = some x₂
    rw [b6]
    exact hx₂
  · rw [hF₂]
    exact SameCore.ofSide (eq_side b5)

/-- An order cut at "K8.equations". -/
theorem coreOk_of_cut (L : Link S Claim) (i : ℕ) (pre post : List (ℕ × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : CoreOk L pre) (Hpost : CoreOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2) : CoreOk L L.order := by
  intro o ho run hat
  rw [hord] at ho
  rcases List.mem_append.1 ho with h | h
  · exact Hpre o h run hat
  · rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, tEq run hat, keepsCore_k8⟩
    · exact Hpost o h run hat

/-- **At a feed-forward segment.** -/
theorem coreOk_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array ℕ)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (hord : L.order = VerifiableInference.Desc.First.orderOf .layers) : CoreOk L L.order := by
  refine coreOk_of_cut L 4
    [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] [(2, "back")]
    (by rw [hord]; rfl) ?_ ?_ ties.tEq
  · intro o ho run hat
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, tC run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 1 (by simp) run hat, core_idle⟩
    · obtain ⟨r, l, u⟩ := ties.tFront run hat
      exact ⟨r, u, core_front p4 r l⟩
    · exact ⟨_, tD run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 6 (by simp) run hat, core_idle⟩
  · intro o ho run hat
    obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
    obtain ⟨r, l, u⟩ := ties.tBack run hat
    exact ⟨r, u, core_behind p4 r l⟩

/-- **At an attention segment.** -/
theorem coreOk_att (L : Link S Claim) (c : Att.P.ParC) (nU : Array ℕ)
    (ties : LinkJoin.AttTies L c nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run →
      LinkJoin.Under run (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO c) c)))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run →
      ∃ lm, LinkJoin.Under run (Desc.K9.planesCalls lm (Att.P.readersOfK (Att.P.seatCO c) c)))
    (hord : L.order = VerifiableInference.Desc.First.orderOf .attention) : CoreOk L L.order := by
  refine coreOk_of_cut L 4 attPre [] (by rw [hord]; rfl) ?_ (fun _ ho => nomatch ho) ties.tEq
  intro o ho run hat
  simp only [attPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, tC run hat, core_objects _⟩
  · exact ⟨_, ties.tGuests 1 (by simp) run hat, core_idle⟩
  · exact ⟨_, ties.tFirst run hat, core_first c⟩
  · exact ⟨_, ties.tKeys run hat, core_keys c⟩
  · exact ⟨_, tJ run hat, core_join _⟩
  · exact ⟨_, ties.tSecond run hat, core_second c⟩
  · obtain ⟨lm, u⟩ := tP run hat
    exact ⟨_, u, core_planes lm _⟩
  · exact ⟨_, tD run hat, core_objects _⟩
  · exact ⟨_, ties.tGuests 6 (by simp) run hat, core_idle⟩

/-- **At the head's segment.** -/
theorem coreOk_head (L : Link S Claim) (hS : Model.Head.Shape) (iU3 l piece : ℕ)
    (p6 : Kinds.Head.Par) (nU : Array ℕ) (ties : LinkJoin.HeadTies L hS iU3 l piece p6 nU)
    (tC : ∀ run, LinkJoin.At L (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At L (2, "planes") run →
      ∃ lm, LinkJoin.Under run (Desc.K9.planesCalls lm (callerReaders (planesAt iU3))))
    (hord : L.order = VerifiableInference.Desc.First.orderOf .head) : CoreOk L L.order := by
  refine coreOk_of_cut L 5 headPre headPost (by rw [hord]; rfl) ?_ ?_ ties.tEq
  · intro o ho run hat
    simp only [headPre, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, tC run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 2 (by simp) run hat, core_idle⟩
    · obtain ⟨r, lr, u⟩ := ties.tK6 "norm" (by simp) run hat
      exact ⟨r, u, core_k6 hS iU3 l piece p6 "norm" r lr⟩
    · exact ⟨_, ties.tJoin run hat, core_join _⟩
    · obtain ⟨r, lr, u⟩ := ties.tK6 "policy" (by simp) run hat
      exact ⟨r, u, core_k6 hS iU3 l piece p6 "policy" r lr⟩
    · obtain ⟨lm, u⟩ := tP run hat
      exact ⟨_, u, core_planes lm _⟩
    · exact ⟨_, tD run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 7 (by simp) run hat, core_idle⟩
  · intro o ho run hat
    simp only [headPost, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · obtain ⟨r, lr, u⟩ := ties.tK6 "logits" (by simp) run hat
      exact ⟨r, u, core_k6 hS iU3 l piece p6 "logits" r lr⟩
    · exact ⟨_, ties.tMerge run hat, core_merge⟩

/-- From the ten fields, under a run, to `RunKeeps` of the run at the entry. -/
theorem runKeeps_of_coreOk {L : Link S Claim} (H : CoreOk L L.order) :
    ∀ (j : ℕ) (o : ℕ × String) (f : ClaimsRun), L.order[j]? = some o → claimsRunOf L.hear o = some f → RunKeeps f := by
  intro j o f ho hf n t z hz a ha
  obtain ⟨g, hu, hk⟩ := H o (List.mem_of_getElem? ho) f hf
  obtain ⟨b, hb, hc⟩ := hk n t z a (hu n t z.1 z.2 hz) ha
  exact ⟨b, hb, ledgerCore_of_sameCore a b hc⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
  {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Lk : Link S Claim}

/-- The ties at a feed-forward segment. -/
theorem coreOk_seat_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) (e1 : c.links[l]? = some Lk) (hord : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt l)) :
    CoreOk Lk Lk.order := by
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', p4, X, e1', -, -, ties⟩ := LPFK9.layers_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have h24 : l ≠ 24 := by
    intro e
    rw [e] at hsub
    exact absurd hsub (by decide)
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  exact coreOk_layers Lk p4 _ ties tC tD hord

/-- The ties at an attention segment. -/
theorem coreOk_seat_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .attention) (e1 : c.links[l]? = some Lk) (hord : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt l)) :
    CoreOk Lk Lk.order := by
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g, hg, rfl⟩ := Att.P.att_only O.pub O.blank hs25
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tJ : ∀ run, LinkJoin.At Lk (2, "join") run →
      LinkJoin.Under run
        (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    rw [LinkJoin.at_join_is O h4 hg hA e1 hrun]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (1, "planes") run →
      ∃ lm, LinkJoin.Under run
        (Desc.K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  exact coreOk_att Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) ties tC tD tJ tP hord

/-- The ties at the head's segment. -/
theorem coreOk_seat_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (e1 : c.links[24]? = some Lk) (hord : Lk.order = VerifiableInference.Desc.First.orderOf (IM.subAt 24)) :
    CoreOk Lk Lk.order := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hsub] at hs25 hord
  have hU3 := P1K8.head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  have tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', P1K8.objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', P1K8.objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (2, "planes") run →
      ∃ lm, LinkJoin.Under run (Desc.K9.planesCalls lm (callerReaders (planesAt 0))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  exact coreOk_head Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties tC tD tP hord

end

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Every run that the order names keeps the ledger's core, at each of the 25 segments.** -/
theorem cores_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) :
    ∀ (j : ℕ) (o : ℕ × String) (f : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some f →
      RunKeeps f := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine runKeeps_of_coreOk ?_
  cases hsub : IM.subAt l with
  | layers => exact coreOk_seat_layers h.scope h.reads O l hl hsub Sd.link Sd.order
  | attention => exact coreOk_seat_att h.scope h.reads O l hl hsub Sd.link Sd.order
  | head =>
    have e : l = 24 := by
      by_contra hne
      have : ∀ m, m < 25 → m ≠ 24 → IM.subAt m ≠ .head := by decide
      exact this l hl hne hsub
    subst e
    exact coreOk_seat_head h.scope h.reads O Sd.link Sd.order

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.keepsCore_k8
#print axioms ProofFile.Honest.K9.coreOk_of_cut
#print axioms ProofFile.Honest.K9.coreOk_layers
#print axioms ProofFile.Honest.K9.coreOk_att
#print axioms ProofFile.Honest.K9.coreOk_head
#print axioms ProofFile.Honest.K9.runKeeps_of_coreOk
#print axioms ProofFile.Honest.K9.coreOk_seat_layers
#print axioms ProofFile.Honest.K9.coreOk_seat_att
#print axioms ProofFile.Honest.K9.coreOk_seat_head
#print axioms ProofFile.Honest.K9.cores_at_head
