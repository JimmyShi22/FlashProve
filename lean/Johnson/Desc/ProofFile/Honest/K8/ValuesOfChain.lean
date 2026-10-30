-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ValuesOfChain.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE,
AT THE STANDS OF THE HONEST THREAD: THE NAMED PREMISE `ValuesAtStand`
(Johnson/Desc/ProofFile/Honest/K8/LeftFront.lean: at the state at which the tests are called, what
is left of the values) AT A SEGMENT OF EACH OF THE THREE SORTS, AT THE CHAIN's OWN LINK AND THE
LOT's OWN LENGTHS, FROM THE ONE NAMED PREMISE `ChainThread` (K8BehindTop.lean). Implications; none
of the library's goals.

  `layers_seat_k4`, `att_seat`, `head_seat` in scope, the files read, under an opening: what the
                   library holds on a segment's seat, gathered as one end a sort: the chain's link ·
                   the sort's letters with the equation that pins them · the built segment · the
                   sort's ties at ProofFile.k8NU Bs.G₀ X · the ties of the runs "objects" (two), "join",
                   "planes" · the order
  `wrapEnd_at_stand` ChainThread T b c Z l · a stand ⊢ WrapEnd Z c l s
  **`valuesAtStand_layers_of_chain`**, **`valuesAtStand_att_of_chain`**,
                   **`valuesAtStand_head_of_chain`** the scope · the files read · the opening · its
                   test on its plan · (g < 12) · c.links[l]? = some Lk · the built segment Xl ·
                   ChainThread T b c Z l ⊢ ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b, at every
                   p, φ and Ok; l = 2 g, 2 g + 1, 24
By: `valuesAtStand_layers`, `_att`, `_head` (ValuesJoin.lean) · their premise on the front:
`allFrontAtStand_of_chain` (AllFrontOfChain.lean) · what they ask of the state in front:
`layAsks_at_wrap`, `attAsks_at_wrap`, `headWants_at_wrap` (AsksAtWrap.lean) · the sort's ties: the
library's LPFK9.layers_ties_at, att_ties_at, head_ties_at (Johnson/LPFK9R/TiesWholeAt.lean) · the
runs' ties: OnPublicFiles.at_objects_is, at_planes_is, LinkJoin.at_join_is · the order: IM.k9_of ·
`reach_below` (Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean), called at its statement.
WRITTEN A FURTHER TIME: THE GATHERING AT A SEAT STANDS ALREADY inside proofs, among them the
library's Johnson/P1K8R/FallAtSeat.lean, FallAtSeatAtt.lean and FallAtSeatHead.lean. The three
lemmas
here follow these proofs line for line as far as the ties go. `objectsRun_at` and `head_u3` are
called out of the library's. KIN, NOT CALLED: `wrapEnd_of_handed` (Johnson/P1K8R/LastAtFrame.lean)
has the end of `wrapEnd_at_stand` from what another field of the frame hands, at a walk.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `simpa [a
list]` on five lines, each on one number of an entry · `omega` on eleven lines, on numbers of
segments alone.
Limits. IMPLICATIONS: `ChainThread` IS A PREMISE. NO MEMBER: that a stand exists is not shown: where
there is none, all is idle. p, φ and Ok are free: at numbers p at which no stand exists the sentence
is idle; Lk is the chain's own link at l. IN SCOPE ALONE: the full size; the first chain; at
OnBytes.secondHashFunction. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ValuesJoin
import Johnson.Desc.ProofFile.Honest.K8.AllFrontOfChain
import Johnson.Desc.ProofFile.Honest.K8.AsksAtWrap
import Johnson.P1K8R.FallAtSeatAtt
import Johnson.P1K8R.FallAtSeatHead
import Johnson.LPFK9R.TiesWholeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open _root_.P1K8

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-! ## What the library holds on a segment's seat, gathered, sort by sort -/

/-- **A feed-forward segment's seat.** -/
theorem layers_seat_k4 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ (Lk : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (X : LinkH),
      c.links[2 * g]? = some Lk ∧ LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 ∧
      Bs.G₀.built[2 * g]? = some X ∧ LinkJoin.LayersTies Lk p4 (ProofFile.k8NU Bs.G₀ X) ∧
      (∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls) ∧
      (∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits) ∧
      Lk.order = First.orderOf .layers := by
  have hl : 2 * g < 25 := by omega
  have h24 : 2 * g ≠ 24 := by omega
  have hsub : IM.subAt (2 * g) = .layers := by
    unfold IM.subAt
    rw [if_neg h24, if_pos (by omega)]
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, -, -, -, -, hord, hordA, -⟩ :=
    (IM.k9_of hS hR O).2 (2 * g) hl
  have hs25 := IM.subs_scope hS hR O (2 * g) hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', p4, X, e1', hp, hX, ties⟩ :=
    LPFK9.layers_ties_at O.made O.places O.chain (2 * g) hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  rw [Array.getElem?_toList] at hX
  refine ⟨Lk, p4, X, e1, hp, hX, ties, ?_, ?_, hord⟩
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _

/-- **An attention segment's seat.** -/
theorem att_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ (Lk : Link S Claim) (Ap : Attention.Plan) (X : LinkH),
      c.links[2 * g + 1]? = some Lk ∧ Bs.G₀.W.A[g]? = some Ap ∧
      Bs.G₀.built[2 * g + 1]? = some X ∧
      LinkJoin.AttTies Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) ∧
      (∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls) ∧
      (∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits) ∧
      (∀ run, LinkJoin.At Lk (2, "join") run → LinkJoin.Under run
        (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap)))) ∧
      (∀ run, LinkJoin.At Lk (1, "planes") run → ∃ lm, LinkJoin.Under run
        (Desc.K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap)))) ∧
      Lk.order = First.orderOf .attention := by
  have hl : 2 * g + 1 < 25 := by omega
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have hsub : IM.subAt (2 * g + 1) = .attention := by
    unfold IM.subAt
    rw [if_neg h24, if_neg (by omega)]
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, -, -, -, -, hord, hordA, -⟩ :=
    (IM.k9_of hS hR O).2 (2 * g + 1) hl
  have hs25 := IM.subs_scope hS hR O (2 * g + 1) hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain (2 * g + 1) hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g', hg', e⟩ := Att.P.att_only O.pub O.blank hs25
  obtain rfl : g = g' := by omega
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg'
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  rw [Array.getElem?_toList] at hX
  refine ⟨Lk, Ap, X, e1, hA, hX, ties, ?_, ?_, ?_, ?_, hord⟩
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  · intro run hrun
    rw [LinkJoin.at_join_is O h4 hg' hA e1 hrun]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩

/-- **The head's segment's seat.** -/
theorem head_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Claim) (X : LinkH), c.links[24]? = some Lk ∧ Bs.G₀.built[24]? = some X ∧
      LinkJoin.HeadTies Lk Bs.G₀.W.hS 0 (Bs.G₀.built.size - 1) 4
        (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) (ProofFile.k8NU Bs.G₀ X) ∧
      (∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls) ∧
      (∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits) ∧
      (∀ run, LinkJoin.At Lk (2, "planes") run →
        ∃ lm, LinkJoin.Under run (Desc.K9.planesCalls lm (callerReaders (planesAt 0)))) ∧
      Lk.order = First.orderOf .head := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, -, -, -, -, hord, hordA, -⟩ :=
    (IM.k9_of hS hR O).2 24 hl
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hsub] at hs25 hord
  have hU3 := head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  rw [Array.getElem?_toList] at hX
  refine ⟨Lk, X, e1, hX, ties, ?_, ?_, ?_, hord⟩
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩

/-! ## The three sentences, from the one named premise -/

variable {α : Type} {p : Desc.K9.Where} {φ : S → α} {Ok : α × Option Pub9 → Prop}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}

/-- A stand gives a state that the wrapped blocks reach at the thread's border. -/
theorem wrapEnd_at_stand {Lk : Link S Claim} {l : ℕ} (C : ChainThread T b c Z l)
    {κ : Coins Bk} {s : S} {m : Mid W X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List Desc.OpenedColumn} {s' : S} {x : E}
    {z : S × Desc.K9.Part × List Claim} {G : Fork}
    (hSt : BatStand Lk p T b κ s m En ds y cols s' x z G) : WrapEnd Z c l s := by
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_below T (ProofFile.startS Z) q C.len hq C.stored hSt.thr
  rw [C.ft, C.bs, C.border] at r
  exact ⟨q, r⟩

/-- **At a feed-forward segment.** -/
theorem valuesAtStand_layers_of_chain (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Lk : Link S Claim} (hLk : c.links[2 * g]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (C : ChainThread T b c Z (2 * g)) :
    ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b := by
  obtain ⟨Lk', p4, X', e1, hp, hX, ties, tC, tD, hord⟩ := layers_seat_k4 hS hR O hg
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans hLk)
  obtain rfl : X' = Xl := Option.some.inj (hX.symm.trans e3)
  exact valuesAtStand_layers p4 ties tC tD hord
    (allFrontAtStand_of_chain hS hR O hOk (by omega) C)
    (fun κ s m En ds y cols s' x z G hSt tl ht =>
      layAsks_at_wrap hS hR O hOk hg hp (wrapEnd_at_stand C hSt) ht)

/-- **At an attention segment.** -/
theorem valuesAtStand_att_of_chain (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Lk : Link S Claim} (hLk : c.links[2 * g + 1]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (C : ChainThread T b c Z (2 * g + 1)) :
    ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b := by
  obtain ⟨Lk', Ap, X', e1, hA, hX, ties, tC, tD, tJ, tP, hord⟩ := att_seat hS hR O hg
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans hLk)
  obtain rfl : X' = Xl := Option.some.inj (hX.symm.trans e3)
  exact valuesAtStand_att Ap ties tC tD tJ tP hord
    (allFrontAtStand_of_chain hS hR O hOk (by omega) C)
    (fun κ s m En ds y cols s' x z G hSt tl ht =>
      attAsks_at_wrap hS hR O hOk hg hA (wrapEnd_at_stand C hSt) ht)

/-- **At the head's segment.** -/
theorem valuesAtStand_head_of_chain (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Lk : Link S Claim} (hLk : c.links[24]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (C : ChainThread T b c Z 24) :
    ValuesAtStand Lk p φ Ok (ProofFile.k8NU Bs.G₀ Xl) T b := by
  obtain ⟨Lk', X', e1, hX, ties, tC, tD, tP, hord⟩ := head_seat hS hR O
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans hLk)
  obtain rfl : X' = Xl := Option.some.inj (hX.symm.trans e3)
  exact valuesAtStand_head _ 0 _ 4 _ ties tC tD tP hord
    (allFrontAtStand_of_chain hS hR O hOk (by omega) C)
    (fun κ s m En ds y cols s' x z G hSt tl ht =>
      headWants_at_wrap hS hR O hOk (wrapEnd_at_stand C hSt) ht)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.layers_seat_k4
#print axioms ProofFile.Honest.K8.att_seat
#print axioms ProofFile.Honest.K8.head_seat
#print axioms ProofFile.Honest.K8.wrapEnd_at_stand
#print axioms ProofFile.Honest.K8.valuesAtStand_layers_of_chain
#print axioms ProofFile.Honest.K8.valuesAtStand_att_of_chain
#print axioms ProofFile.Honest.K8.valuesAtStand_head_of_chain
