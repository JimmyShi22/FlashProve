-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RunsCarry.lean: EVERY RUN OF CLAIMS THAT A SEGMENT's ORDER NAMES CARRIES THE LEDGER ON: behind a yes of the run, what
the first lookup returned stands, and a ledger with its sizes has gone on to a later one with its sizes (`Desc.K9.CF S.lookHeard?`:
no slot is given back; what is filled stays filled, with its value and factor). At all three sorts of segment at once, with no
list of runs: the library has this law of every run that a lot's sub-protocol states (`lotsCarryLook`,
Johnson/Desc/First/K9x/KindsAtPure.lean), and each sub-protocol in front of a batching, from the first lookup on, is a lot's sub-protocol laid
alone (`IM.chain_hear_alone`, Johnson/IMR/LaidFirst.lean), its runs each behind one guard.

  **`runs_carry`**       in the goals' scope, at an opening of the description: the run at the pair o of the link l, where o names a
                      sub-protocol from the first lookup on
  `order_from_look`    every entry of each segment's order names such a sub-protocol
  **`carries_at_head`**  under the library's hypothesis `AtMgA`, at the seated link: every run that the order names

Limits. Nothing here says that a run returns. The full size and the hash function `secondHashFunction` alone. This file proves no property of a
prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.SizedAtStand
import Johnson.Desc.First.K9x.KindsAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open P5J (AtMgA)

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The run at a pair of a link carries the ledger on.** -/
theorem runs_carry (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S ProofFile.Cl} (e1 : c.links[l]? = some Lk) {o : ℕ × String} {r : ClaimsRun}
    (hr : claimsRunOf Lk.hear o = some r) (h1 : IM.k3Ix l false ≤ o.1) (h2 : o.1 < IM.nAt l) :
    ∀ n u y, r n u = .ok y → Desc.K9.CF S.lookHeard? u y.2 := by
  have hlen : o.1 < (kindsBeforeBatching (IM.subAt l) (l == 0)).length := by
    rw [IM.hear_len_at]
    unfold IM.nAt at h2
    exact h2
  have hk := List.getElem?_eq_getElem hlen
  have hb := kind_behind h1 hk
  have hi : 1 ≤ o.1 ∧ o.1 < 9 := by
    rcases ix_facts l with ⟨-, a, -, b⟩ | ⟨-, a, -, b⟩ <;> omega
  obtain ⟨Lk', b, e1', e2, sp, -, L, hL, b', hb', -, -, hla⟩ :=
    IM.chain_hear_alone O.made O.places O.chain l _ (IM.subs_scope hS hR O l hl) o.1 _ hk
      (fun e => absurd (e ▸ hb) (by decide)) (fun e => absurd (e ▸ hb) (by decide))
      ⟨by omega, by omega⟩
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  unfold claimsRunOf at hr
  rw [e2] at hr
  have hr' : b.claims.lookup o.2 = some r := hr
  rw [IM.claims_lookup hla] at hr'
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 hr'
  obtain ⟨l₁, l₂, el, -⟩ := List.lookup_eq_some_iff.1 hf
  have hm : (o.2, f) ∈ b'.claims := by
    rw [el]
    simp
  intro n u y hy
  exact (Desc.K9.lotsCarryLook OnBytes.secondHashFunction Z).blocks L hL Bs.G₀ b' hb' (o.2, f) hm n u y.1 y.2
    (guardedRun_under ProofFile.sameReply f n u y hy)

end

/-- Every entry of a segment's order names a sub-protocol from the first lookup on, in front of the batching. -/
theorem order_from_look {l : ℕ} {o : ℕ × String} (ho : o ∈ VerifiableInference.Desc.First.orderOf (IM.subAt l)) :
    IM.k3Ix l false ≤ o.1 ∧ o.1 < IM.nAt l := by
  rcases ix_facts l with ⟨rfl, a, -, b⟩ | ⟨h24, a, -, b⟩
  · rw [a, b]
    have e : IM.subAt 24 = .head := by
      unfold IM.subAt
      rw [if_pos rfl]
    rw [e] at ho
    simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
      List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  · rw [a, b]
    unfold IM.subAt at ho
    rw [if_neg h24] at ho
    split at ho
    · simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
        List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
    · simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
        List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Every run that the order names carries the ledger on, at each of the 25 segments.** -/
theorem carries_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) :
    ∀ (j : ℕ) (o : ℕ × String) (f : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some f →
      ∀ n u y, f n u = .ok y → Desc.K9.CF S.lookHeard? u y.2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro j o f ho hf
  have hm : o ∈ VerifiableInference.Desc.First.orderOf (IM.subAt l) := Sd.order ▸ List.mem_of_getElem? ho
  obtain ⟨a, b⟩ := order_from_look hm
  exact runs_carry h.scope h.reads O hl Sd.link hf a b

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.runs_carry
#print axioms ProofFile.Honest.K9.order_from_look
#print axioms ProofFile.Honest.K9.carries_at_head
