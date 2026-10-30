-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/FreeOff.lean: THE PREMISE "FREE" OF AtDesc.lean, MOVED FROM THE PLAN TO THE
RECORD. Statements and proofs.

AtDesc.lean gives `AtPlace` at a description under a premise on the plan that no test on the plan is
known to ask: the place's first free own number (π.nums.free) is the number n of roots that the
chain declares in front of the block. But the block itself asks, at run time, that π.nums.free be
THE RECORD's count of roots (`yes_free`, YesHolds.lean). So it is enough that the promise say of the
record: its count of roots is n. Where the piece never says yes nothing is to be shown; where it
says yes, π.nums.free = the record's roots = n.

  `leads_under_yes`: for every reduction: a law that stands under a proposition P stands without it,
    if the promise and a yes together give P.
  `k12_lawRecFree`, `k12_lawRecFreeO`: the two arms of PaidRec.lean with `AtPlace` | `AtPlaceOwn`
    asked only under π.nums.free = n, and "the record's count of roots is n" in the promise.
How it is called: hA := fun hfree => atPlace_first | _shared | _last … hfree … (AtDesc.lean), at
n := rootsOf pre.
Limits: those of PaidRec.lean and AtDesc.lean. NO SOUNDNESS IS CLAIMED. "The record's count of roots
is n" is a promise on the record: that the blocks in front hand it on is shown nowhere here.

-/
import Johnson.Desc.K12.Coin.PaidRec
import Johnson.Desc.K12.Coin.YesHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayRec)
open H2K.Pub (PayPub johOk batV0)
open H2K.First (batOneOk)

/-- A law that stands under P stands without it, if the promise and a yes together give P. -/
theorem leads_under_yes {A B : Type} {K : Reduction A B} {P : Prop} {on' on : A → Prop}
    {Q : A → B → Prop} {ε : Err K.shape} (h : P → K.Leads on Q ε)
    (hP : ∀ a τ b, on' a → K.out a τ = some b → P) :
    K.Leads (fun a => on' a ∧ on a) Q ε := by
  intro a ha
  by_cases hy : ∃ τ b, K.out a τ = some b
  · obtain ⟨τ, b, hb⟩ := hy
    exact h (hP a τ b ha.1 hb) a ha.2
  · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hy

/-- **The first arm, "free" off the record.** -/
theorem k12_lawRecFree (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (εt : Err (uLT (ckP .two) dt)) (n : ℕ) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hA : π.nums.free = n → AtPlace F π num L mC mS mW rad base dB dt εt)
    (r : Fmt.M1.Stage → ℕ) (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true)
    (hb1 : batOneOk π = true) :
    (pieceT F W π base dB dt (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => x.1.roots = n ∧ (FirstOpens π num no base x.1 ∧ PayRec π x.1))
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt).err :=
  leads_under_yes
    (fun hf => k12_lawRec F W π num no L mC mS mW rad rd base dB dt εt (hA hf) r hr hj hb1)
    (fun x τ b hx hb => (yes_free F π he hp base dB dt _ εt x τ b hb).trans hx)

/-- **The second arm, "free" off the record.** -/
theorem k12_lawRecFreeO (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (n : ℕ) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hA : π.nums.free = n → AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => x.1.roots = n ∧ (FirstOpensOwn π num no base x.1 ∧ PayRec π x.1))
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).err :=
  leads_under_yes
    (fun hf => k12_lawRecO F W π num no L mC mS mW rad rd base dB dt v₀ εt (hA hf) hP h1 hlog)
    (fun x τ b hx hb => (yes_free F π he hp base dB dt _ εt x τ b hb).trans hx)

/-- The first arm's form against the verifier that says yes to all: at a statement without the
group whose record's count of roots is n. -/
theorem yesAll_failsRecFree {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (n : ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hg : x.1.st.groups[x.1.g]? = none) (hn : x.1.roots = n)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ p.ior.red.Leads
      (fun x => x.1.roots = n ∧ (FirstOpens π num no base x.1 ∧ PayRec π x.1))
      (fun x _ => QN π (NTuple F π no rad rd) x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x ⟨hn, (promN_no_group F π num no rad rd base dB 0 (NTuple F π no rad rd) x hg).1,
      payRec_no_group π x.1 hg⟩))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π _ x hg (hτ b hb')

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.leads_under_yes
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawRecFree
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawRecFreeO
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsRecFree
