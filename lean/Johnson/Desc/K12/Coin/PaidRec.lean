-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/PaidRec.lean: **THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM WITH ONE
PREMISE ON THE RECORD LEFT OF THE BATCHING's CONVERSE.** Statements and proofs: each law is one call
of LawY.lean's and one of the payer's (Johnson/Desc/K12/Law/Tuple/BatValsPayAt.lean, the kind's own
law's side).

What is said. In the promise, beside `FirstOpens` | `FirstOpensOwn`, stands `PayRec` alone: at
whatever the record fixes, the test with code `combineAt` says yes at the statement behind the
batching's beginning. The layout's four numbers come off the piece's own yes; the facts on codes at
the first radius and the count come off two tests with code on the plan.

  `k12_lawRec`: the first arm: under `AtPlace`, `johOk π r = true` at the radii r, `batOneOk π =
    true`: at the first error batV0 π r times the sampler's number of "BAT"'s round.
  `k12_lawRecO`: the second arm: under `AtPlaceOwn`, `PayPub` at v₀, and the two premises on "BAT"'s
    data: at the first error v₀ times that number.
  `payRec_no_group`, `yesAll_failsRec`, `yesAll_failsRecO`: the two forms against the verifier that
    says yes to all.
What is concluded is `NTuple`: one witness within the radius of the group's word, of whose own words
all batched rows hold, and whose parts are candidates at each sampled member: NOT "every row holds
at the witness".
Limits. NO SOUNDNESS IS CLAIMED. `PayRec` is a premise: no guard of the block asks `combineAt` as
one test, and that a yes gives it is shown nowhere. `johOk`, `batOneOk`: tests on the plan whose yes
is a run's word. That the first error is small against the number of "BAT"'s challenges is not shown
here. `CodesAt`, `bears`, `FirstOpens` | `FirstOpensOwn` stay premises. The checks stand at a
statement without a group alone.

-/
import Johnson.Desc.K12.Law.BatValsPayAt
import Johnson.Desc.K12.Coin.ChecksN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayRec batAtY_pay_at batAtY_pay_yes)
open H2K.Pub (PayPub johOk batV0)
open H2K.First (batOneOk)

/-- **The first arm: `combineAt` alone is left on the record.** -/
theorem k12_lawRec (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (εt : Err (uLT (ckP .two) dt)) (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (r : Fmt.M1.Stage → ℕ) (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true)
    (hb1 : batOneOk π = true) :
    (pieceT F W π base dB dt (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => FirstOpens π num no base x.1 ∧ PayRec π x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (batV0 π r * (bsRound .two dB.entry dB.kind).w) εt).err :=
  Reduction.Leads.conseq
    (k12_lawY F W π num no L mC mS mW rad rd base dB dt _ εt (NTuple F π no rad rd) hA)
    (fun x hx => ⟨hx.1, batAtY_pay_at F W π num no L mC mS mW rad rd base dB dt εt hA r hr hj hb1
      x hx.2⟩)
    (fun _ _ _ _ _ h => h)

/-- **The second arm.** -/
theorem k12_lawRecO (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => FirstOpensOwn π num no base x.1 ∧ PayRec π x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).err :=
  Reduction.Leads.conseq
    (k12_lawYO F W π num no L mC mS mW rad rd base dB dt _ εt (NTuple F π no rad rd) hA)
    (fun x hx => ⟨hx.1, batAtY_pay_yes F W π hA.early hA.planOk no rad rd base dB dt v₀ εt x hP
      hx.2 h1 hlog⟩)
    (fun _ _ _ _ _ h => h)

theorem payRec_no_group (π : P12) (t : T12) (h : t.st.groups[t.g]? = none) : PayRec π t :=
  fun a rest G0 Ly D hf => absurd hf (fixes_no_group π t h a rest G0 Ly D)

theorem yesAll_failsRec {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (p : Piece (ckP .two) F T12 Unit W)
    (x : T12 × F.E.Str) (hg : x.1.st.groups[x.1.g]? = none)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ p.ior.red.Leads (fun x => FirstOpens π num no base x.1 ∧ PayRec π x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x ⟨(promN_no_group F π num no rad rd base dB 0 (NTuple F π no rad rd) x hg).1,
      payRec_no_group π x.1 hg⟩))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π _ x hg (hτ b hb')

theorem yesAll_failsRecO {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (p : Piece (ckP .two) F T12 Unit W)
    (x : T12 × F.E.Str) (hg : x.1.st.groups[x.1.g]? = none)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ p.ior.red.Leads (fun x => FirstOpensOwn π num no base x.1 ∧ PayRec π x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x ⟨(promNO_no_group F π num no rad rd base dB 0 (NTuple F π no rad rd) x hg).1,
      payRec_no_group π x.1 hg⟩))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π _ x hg (hτ b hb')

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_lawRec
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawRecO
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsRec
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsRecO
