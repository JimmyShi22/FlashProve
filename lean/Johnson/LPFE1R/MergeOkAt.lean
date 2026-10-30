-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/MergeOkAt.lean: THE CLAUSE "merge" OF THE HEAD's LINK's ONE
NAMED Ok (`OkHead.merge`): AT EVERY STATE REACHED AT THE HEAD's BATCHING's NUMBER (347): every slot
that the merge's one form names lies in the merge's sumcheck's window or is filled in the ledger;
and the ledger's three arrays have one entry a slot, where the table's public test on the ledger
says so. ONE STEP, NO WALK: the merge (kind K11) stands at 346, right in front. Theorems. A law
file; no running text imports it.
  `merge_ok_step`     behind a yes of the merge's decision from s to s': what the merge has left is
                    there (wo), and every slot of wo.p.rowForm wo.fvp {} lies in the window winOf
                    wo.p or is filled in the ledger behind. WHY: that form's slots are the window's
                    and the start form's one slot (rowForm_slots); the start's slot is filled IN
                    FRONT, since the merge's own yes has read its public part (filled_of_public);
                    what is filled stays filled (decide_later).
  `merge_yes_at_347`  in scope: a state reached at 347 is what a yes of the merge's decision
                    returns.
  `fork_of_part`      the part that kind K9's lens reads holds the open ledger.
  `merge_clause_347`  in scope, at a state reached at 347 where ledgerB says yes: THE CLAUSE's OWN
TEXT at q := fixed9 (phiAll u ψ) ‹the state›, at every u and ψ. CALLED: Johnson/Top/H0/MergeLaw/:
decide_inv (Says.lean) · hear_ended (Said.lean) · filled_of_public (ClosedRun.lean) · decide_later
(Keeps.lean) · rowForm_slots (MergeMakesForms.lean) · sized_of_ledgerB (KeepAtMerge.lean) ·
Johnson/IMR/: k11_of · k11_yes · hear_at_flat · flatIx_scope.

  `ledger_open_347`, `ledger_other_347`   BY THE KERNEL: the public test on segment 24's ledger is
                    asked at border 347 of the full size's written table; segment 23's is not asked
                    there.
  `ledger_at_347`     so the premise ledgerB comes out of the table's condition at border 347, at an
                    unmarked state, at the composed meaning (after ledger_at_front,
                    KeepAtMerge.lean).

Limits. In scope, at OnBytes.secondHashFunction. In merge_clause_347 ledgerB at the state is a premise:
ledger_at_347 pays it under the table's condition; the two are not joined here (their letters for
the lists of links and places differ). THE SLOT OF THE MERGE's END VALUE is named by no slot of that
form: nothing is said of it. No member. Nothing on soundness or on hiding.

-/
import Johnson.LPFE1R.PartAtBatch
import Johnson.Top.H0.MergeLaw.MergeMakesForms
import Johnson.Top.H0.MergeLaw.KeepAtMerge
import Johnson.Desc.First.Link.Law.PhiAll
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes.Model (WsForkOut Fork HTailF2)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (fixed9 pubOf)
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.PhiAll (phiAll woOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S HeadOwn ledgerB Pub Meaning Numbers pubSets openSets
  pubOfItems pubHeld flatPlacesOf pubAll_ledger)
open VerifiableInference.Desc.First.MergeLaw (decide_inv hear_ended filled_of_public decide_later
  rowForm_slots sized_of_ledgerB)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-- Behind a yes of the merge's decision. -/
theorem merge_ok_step {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') :
    ∃ (a' : HeadOwn) (wo : WsForkOut), s'.here = .head a' ∧ a'.wo = some wo ∧
      ∀ y ∈ (wo.p.rowForm wo.fvp {}).slots.toList,
        K4Values.InWin (winOf wo.p) y.1 ∨ Filled a'.F y.1 := by
  obtain ⟨a, a', tp, F, claim, x, wo, ha, ha', hcl, hx, hwo, _, hm, hF', _, _, _⟩ := decide_inv h
  obtain ⟨x₁, mu, c, beta, v, T, r1, rY, rV, qs, _, _, _, hT, hE, _⟩ := hear_ended hm
  have hL : Later a.F a'.F := by
    obtain ⟨b, b', e1, e2, hl⟩ := decide_later h
    rw [ha] at e1
    rw [ha'] at e2
    cases e1
    cases e2
    exact hl
  have hfl : Filled a.F x.sV := filled_of_public (x := x₁) hT
  refine ⟨a', wo, ha', hwo, fun y hy => ?_⟩
  rcases rowForm_slots wo.p wo.fvp #[x.sV] _ hE.start y hy with hw | hy'
  · exact Or.inl hw
  · have e : y.1 = x.sV := by simpa using hy'
    rw [e]
    exact Or.inr (hL.keep _ hfl).1

/-- The part that the lens reads holds the open ledger. -/
theorem fork_of_part {s : S} {p : K9.Part} (hp : atS.get? s = some p) : s.fork? = some p.F := by
  have hq := hp
  unfold atS at hq
  simp only [Option.bind_eq_bind, Option.pure_def] at hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨F₀, hF₀, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  rw [← Option.some.inj hq]
  exact hF₀

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- In scope: a state reached at 347 is what a yes of the merge's decision returns. -/
theorem merge_yes_at_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {a : ProofFile.InstPub × S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 a) :
    ∃ (Pm : HeadMergeP) (s : S) (rs : List Fmt.RoundView), headMergeDecide Pm s rs = .ok a.2 := by
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (346 + 1) a := h
  cases h' with
  | @succ _ z s s' b0 hr hb hy =>
    obtain ⟨R, cs, _, e⟩ := hy
    have hd := ((step_ok_iff 0 b0 s s' R cs cs.length).1 e).2.2.2
    obtain ⟨Lk, b, e1, e2, hla, _⟩ := IM.k11_of hS hR O
    have h3 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
    obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hb)
    exact ⟨_, _, _, ((IM.k11_yes hla _ _ _ _).1 hd).1⟩

/-- **The clause "merge", its own text, at every state reached at 347.** -/
theorem merge_clause_347 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {a : ProofFile.InstPub × S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 a) (hled : ledgerB a.2 = true) {β : Type} (u : HTailF2)
    (ψ : S → β) :
    ∀ wo v, (fixed9 (phiAll u ψ) a.2).1.wo = some wo → (fixed9 (phiAll u ψ) a.2).2 = some v →
      Sized v.F ∧ ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList,
        K4Values.InWin (winOf wo.p) x.1 ∨ Filled v.F x.1 := by
  intro wo v hwo hv
  obtain ⟨Pm, s, rs, hy⟩ := merge_yes_at_347 hS hR O h
  obtain ⟨a', wo', ha', hwo', hall⟩ := merge_ok_step hy
  have e1 : woOf a.2 = some wo := hwo
  unfold woOf at e1
  rw [ha'] at e1
  obtain rfl : wo' = wo := Option.some.inj (hwo'.symm.trans e1)
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 (show (atS.get? a.2).map pubOf = some v from hv)
  have hf := fork_of_part hp
  obtain ⟨F₁, hF₁, hz⟩ := sized_of_ledgerB hled
  obtain rfl : F₁ = p.F := Option.some.inj (hF₁.symm.trans hf)
  have hFa : p.F = a'.F := by
    have hf' := hf
    unfold S.fork? at hf'
    rw [ha'] at hf'
    by_cases ho : a'.opened = true
    · simp only [ho, if_true] at hf'
      exact (Option.some.inj hf').symm
    · simp [ho] at hf'
  refine ⟨hz, fun x hx => ?_⟩
  show _ ∨ Filled p.F x.1
  rw [hFa]
  exact hall x hx

/-! ## The premise ledgerB: out of the table's condition at border 347 -/

set_option maxRecDepth 1000000 in
/-- A closed fact on the table: the public test on segment 24's ledger is asked at border 347. -/
theorem ledger_open_347 : Pub.ledger 24 ∈
    (pubSets moreAll linksFull (flatPlacesOf linksFull true))[347]?.getD [] ++
      pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
        (First.start linksFull))[347]?.getD []) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line, at the same list: another segment's ledger is not asked there. -/
theorem ledger_other_347 : Pub.ledger 23 ∉
    (pubSets moreAll linksFull (flatPlacesOf linksFull true))[347]?.getD [] ++
      pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
        (First.start linksFull))[347]?.getD []) := by decide +kernel

section
variable {Xi Pz Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi Pz Tok rows cols nR X) (Mg : Meaning Pz (Wit (CellsQ rows cols) Tok MsgT))

/-- **Out of the table's condition at border 347**, at an unmarked state: the test on the ledger
accepts. -/
theorem ledger_at_347 (hM : Mg.more = {}) (Nn : Numbers) {Fr : Frame} (z : Pz) (a : S × Fr.E.Str)
    (hon : onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 347 a)
    (hf : a.1.failed = none) : ledgerB a.1 = true := by
  unfold onQ First.onAt at hon
  obtain ⟨-, hmk | ⟨hb, -⟩⟩ := hon
  · exact absurd hf hmk
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨-, hpub⟩, -⟩ := hb
    unfold pubHeld at hpub
    have hin : Pub.ledger 24 ∈
        (pubSets (mgAll D Mg).more linksFull (flatPlacesOf linksFull true))[347]?.getD [] ++
          pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
            (First.start linksFull))[347]?.getD []) := by
      rw [mgAll_more_closed D Mg hM, mgMore_is]
      exact ledger_open_347
    have h1 := List.all_eq_true.1 hpub _ hin
    rw [mgAll_pub, pubAll_ledger] at h1
    exact h1

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ledger_open_347
#print axioms VerifiableInference.Desc.LinkJoin.ledger_other_347
#print axioms VerifiableInference.Desc.LinkJoin.ledger_at_347
#print axioms VerifiableInference.Desc.LinkJoin.merge_ok_step
#print axioms VerifiableInference.Desc.LinkJoin.fork_of_part
#print axioms VerifiableInference.Desc.LinkJoin.merge_yes_at_347
#print axioms VerifiableInference.Desc.LinkJoin.merge_clause_347
