-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FourAtBatch.lean: THE CLAUSES «four» AND «ents4» OF A LINK's Ok (`OkCore`, OkOne.lean beside this file) AT EVERY STATE THAT IS REACHED RIGHT
BEHIND THE SEATED LOOKUP ON THE APPROXIMATE RANGE PROOF's DIGITS, AT ALL 25 LINKS OF THE IOP AS WRITTEN IN LEAN, IN THE GOALS' SCOPE: AT 24 LINKS THAT IS THE BATCHING's FRONT; AT THE HEAD's LINK: ONE STEP ON, OVER THE MERGE.
Theorems: one step back along «reached», then FourBehindDigits.lean.

What is said.
  `piece_digits`: an address at which `K3.theStated` returns, with a piece's number of 7 or more, is the digits' address.
  `four_behind_at`: **l < 25; a state c' reached at 14 l + k3Ix l true + 3 (behind the digits' seated sub-protocol); every sub-protocol's test on the plan accepts (hp);
    hLed: at every state reached in front of that sub-protocol, with the same public part, a ledger is open and has its sizes ⊢ `OkCore`'s clauses four and ents4,
    to the letter, at `fixed9 φ c'`.**
  `four_at_batch`: the same at l < 24, at the number 14 l + 9: in front of the batching.
  `merge_leaves_tl`: the merge's accepting step leaves the structure of the approximate range proof, and its ledger is a later one.
  `four_at_head`: **the same at the head's link, at 347: in front of its batching, behind the merge**; hLed at 345. (`four_raw_at`: the two bodies before they are brought to
    `fixed9`'s letters.)

Limits. **hLed IS A PREMISE: «THE LEDGER IS WELL LAID» IS SHOWN OF NO REACHED STATE HERE**: the table's promise says it at a border, «reached» alone does not; nobody has it along
«reached». hp follows from one accepting run (`IM.planOk_of_run`).
The premises are not shown to be satisfiable. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FourBehindDigits
import Johnson.Road.K4.FunsThirdReached
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope
import Johnson.IMR.K11Seat
import Johnson.Top.H0.MergeLaw.Keeps
import Johnson.Top.H0.MergeLaw.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)
open VerifiableInference.Desc.First.MergeLaw (decide_later isLocal)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- An address with a piece's number of 7 or more at which the seated block is there is the digits'. -/
theorem piece_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (i : ℕ) (hi : a.link = some i)
    (h7 : 7 ≤ a.piece) : a.piece = K3.pieceAt X i true := by
  obtain ⟨B₁, hB₁, -⟩ := K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, -⟩ := K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i', digits, P, sent, laid, hi', hpc', -⟩ := K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  cases digits with
  | true => exact hpc'
  | false =>
    exfalso
    unfold K3.pieceAt at hpc'
    split at hpc' <;> simp at hpc' <;> omega

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **AT EVERY STATE REACHED RIGHT BEHIND THE DIGITS' SEATED SUB-PROTOCOL: what was heard, the ledger, and the two bodies.** -/
theorem four_raw_at (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, c'))
    (hLed : ∀ s, Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2) (z, s) →
      ∃ G, s.fork? = some G ∧ Sized G) :
    ∃ g G, c'.tl?.bind (·.heard) = some g ∧ c'.fork? = some G ∧ Sized G ∧
      (∀ tl, ∀ cl ∈ four8 tl g, cl.form.ents = #[]) ∧
      ∀ H, _root_.Fo.Later G H → ∀ tl, ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled H x.1 := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.yes_alone e4 (fun h => nomatch h) s _ rs gs).1 hd).1
  have hOk : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  obtain ⟨G₀, hG₀, hz₀⟩ := hLed s hr
  exact four_behind_digits _ _ _ _ _ _ b' e3 hOk l rfl
    (piece_digits _ _ _ _ _ _ b' e3 l rfl h7) s _ rs gs hd' hG₀ hz₀

/-- **four AND ents4 AT EVERY STATE REACHED RIGHT BEHIND THE DIGITS' SEATED SUB-PROTOCOL.** -/
theorem four_behind_at (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, c'))
    (hLed : ∀ s, Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2) (z, s) →
      ∃ G, s.fork? = some G ∧ Sized G)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    (∀ v tlb g, (fixed9 φ c').2 = some v → (π (fixed9 φ c').1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1) ∧
      ∀ tlb g, (π (fixed9 φ c').1).1 = some tlb → tlb.heard = some g →
        ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row := by
  obtain ⟨g, G, h1, h2, hz, h3, h4⟩ := four_raw_at hS hR O hp hl h hLed
  exact four_fixed π φ u hπ h1 h2 hz h3 (h4 G (_root_.Fo.Later.refl G))

/-- **AT 24 LINKS: IN FRONT OF THE BATCHING.** -/
theorem four_at_batch (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, c'))
    (hLed : ∀ s, Reach 0 c.blocksInOrder start (14 * l + 8) (z, s) → ∃ G, s.fork? = some G ∧ Sized G)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    (∀ v tlb g, (fixed9 φ c').2 = some v → (π (fixed9 φ c').1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1) ∧
      ∀ tlb g, (π (fixed9 φ c').1).1 = some tlb → tlb.heard = some g →
        ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row := by
  have e : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  refine four_behind_at (start := start) hS hR O hp (by omega : l < 25) (z := z) (c' := c') ?_ ?_
    π φ u hπ
  · rw [e]
    exact h
  · rw [e]
    exact hLed

/-- The merge's accepting step leaves the structure, and its ledger is a later one. -/
theorem merge_leaves_tl {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') {G : Fork} (hG : s.fork? = some G) :
    s'.tl? = s.tl? ∧ ∃ G', s'.fork? = some G' ∧ OnBytes.PscRun.Later G G' := by
  obtain ⟨a, a', ha, ha', -, ea, -⟩ := isLocal P s rs s' h
  obtain ⟨b, b', e1, e2, hl⟩ := decide_later h
  obtain rfl : a = b := by
    rw [ha] at e1
    exact First.Here.head.inj e1
  obtain rfl : a' = b' := by
    rw [ha'] at e2
    exact First.Here.head.inj e2
  have ho' : a'.opened = a.opened := by rw [ea]
  have ht' : a'.tl = a.tl := by rw [ea]
  have ho : a.opened = true := by
    cases hq : a.opened with
    | true => rfl
    | false => simp [S.fork?, ha, hq] at hG
  have eG : a.F = G := by simpa [S.fork?, ha, ho] using hG
  refine ⟨by simp [S.tl?, ha, ha', ho, ho', ht'], a'.F, by simp [S.fork?, ha', ho', ho], ?_⟩
  rw [← eG]
  exact hl

/-- **AT THE HEAD's LINK: IN FRONT OF THE BATCHING (347): behind the merge.** -/
theorem four_at_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, c'))
    (hLed : ∀ s, Reach 0 c.blocksInOrder start 345 (z, s) → ∃ G, s.fork? = some G ∧ Sized G)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    (∀ v tlb g, (fixed9 φ c').2 = some v → (π (fixed9 φ c').1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1) ∧
      ∀ tlb g, (π (fixed9 φ c').1).1 = some tlb → tlb.heard = some g →
        ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row := by
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred (k := 346) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, e1, e2, hla, -⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  obtain rfl : b = b₀ := Option.some.inj (h3.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hm : headMergeDecide _ s rs = .ok _ := ((IM.k11_yes hla _ _ _ _).1 hd).1
  obtain ⟨g, G, a1, a2, az, a3, a4⟩ :=
    four_raw_at (start := start) hS hR O hp (l := 24) (by decide) (z := z) (c' := s) hr hLed
  obtain ⟨t1, G', t2, t3⟩ := merge_leaves_tl hm a2
  exact four_fixed π φ u hπ (by rw [t1]; exact a1) t2 (t3.sized az) a3
    (a4 G' ⟨t3.next, t3.ns, t3.keep⟩)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.piece_digits
#print axioms VerifiableInference.Desc.LinkJoin.four_raw_at
#print axioms VerifiableInference.Desc.LinkJoin.merge_leaves_tl
#print axioms VerifiableInference.Desc.LinkJoin.four_at_head
#print axioms VerifiableInference.Desc.LinkJoin.four_behind_at
#print axioms VerifiableInference.Desc.LinkJoin.four_at_batch
