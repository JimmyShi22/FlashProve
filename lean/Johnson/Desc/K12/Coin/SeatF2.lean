-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/SeatF2.lean: EVERY PLAIN LAW OF THE PROXIMITY TEST's PIECE, SEATED AT THE
FIRST CHAIN's FINISH. Statements and proofs.

Here the step is taken once, for every promise and every conclusion that reads the statement in
front:

  `leads_atFinish`: from a law of `pieceT` (the block at its own record) to the law of `pieceF2`
    (the seat `atFinish π` on the first chain's own state), at the same errors: the promise is asked
    at the record that the door lays (`recAt`); the conclusion holds there; and of the chain's state
    only the running record, the book and the count of roots turn. By `leads_seated` (Inside.lean).
  `k12_lawY_F2`, `k12_lawPaidY_F2`: the first arm's laws of LawY.lean and PaidY.lean, so seated.
  `payY_no_group`, `yesAll_failsPaidY`: the form of PaidY.lean's first law against the verifier that
    says yes to all (at a statement without the group alone).
Limits: those of LawY.lean, Paid.lean and PaidY.lean. NO SOUNDNESS IS CLAIMED. The second arm is
seated nowhere here: the first chain's finish is no place of its sort.

-/
import Johnson.Desc.K12.Coin.PaidY
import Johnson.Desc.K12.Coin.ChecksPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK (recAt)
open H2K.Pin (NTuple)

/-- **Every plain law of the piece goes over to the first chain's finish.** -/
theorem leads_atFinish (F : Frame) (W : Type) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (on Q : T12 × F.E.Str → Prop)
    (h : (pieceT F W π base dB dt e₀ εt).ior.red.Leads on (fun x _ => Q x)
      (pieceT F W π base dB dt e₀ εt).err) :
    (pieceF2 F W π base dB dt e₀ εt).ior.red.Leads
      (fun x => ∀ fo, x.1.here = .fin fo → on (recAt x.1 fo, x.2))
      (fun x y => ∃ fo, x.1.here = .fin fo ∧ x.1.noneWaits = true ∧ x.1.failed.isNone = true ∧
        Q (recAt x.1 fo, x.2) ∧
        ∃ st book roots, y.1 = { x.1 with st := st, book := book, roots := roots })
      (pieceF2 F W π base dB dt e₀ εt).err := by
  have h' := leads_seated (pieceT F W π base dB dt e₀ εt) enterFinish leaveFinish _ _ h
  refine Reduction.Leads.conseq h' ?_ ?_
  · intro x hx t ht
    obtain ⟨o, ho, _, _, rfl⟩ := Seat.enterFinish_ok x.1 t ht
    exact hx o ho
  · rintro x τ y _ _ ⟨t, t', h1, h2, h3⟩
    obtain ⟨o, ho, g1, g2, rfl⟩ := Seat.enterFinish_ok x.1 t h1
    exact ⟨o, ho, g1, g2, h3, t'.st, t'.book, t'.roots, (Seat.leaveFinish_ok _ _ _).1 h2⟩

theorem k12_lawY_F2 (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (N : ConclK F)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) :
    (pieceF2 F W π base dB dt e₀ εt).ior.red.Leads
      (fun x => ∀ fo, x.1.here = .fin fo → FirstOpens π num no base (recAt x.1 fo) ∧
        BatAtY F W π no rad rd base dB dt e₀ εt N (recAt x.1 fo, x.2))
      (fun x y => ∃ fo, x.1.here = .fin fo ∧ x.1.noneWaits = true ∧ x.1.failed.isNone = true ∧
        QN π N (recAt x.1 fo, x.2) ∧
        ∃ st book roots, y.1 = { x.1 with st := st, book := book, roots := roots })
      (pieceF2 F W π base dB dt e₀ εt).err :=
  leads_atFinish F W π base dB dt e₀ εt _ _
    (k12_lawY F W π num no L mC mS mW rad rd base dB dt e₀ εt N hA)

theorem k12_lawPaidY_F2 (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    (pieceF2 F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => ∀ fo, x.1.here = .fin fo → FirstOpens π num no base (recAt x.1 fo) ∧
        PayY π rad v₀ (recAt x.1 fo))
      (fun x y => ∃ fo, x.1.here = .fin fo ∧ x.1.noneWaits = true ∧ x.1.failed.isNone = true ∧
        QN π (NTuple F π no rad rd) (recAt x.1 fo, x.2) ∧
        ∃ st book roots, y.1 = { x.1 with st := st, book := book, roots := roots })
      (pieceF2 F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).err :=
  leads_atFinish F W π base dB dt _ εt _ _
    (k12_lawPaidY F W π num no L mC mS mW rad rd base dB dt v₀ εt hA h1 hlog)

theorem payY_no_group (π : P12) (rad : Sg → ℕ) (v₀ : ℕ) (t : T12)
    (h : t.st.groups[t.g]? = none) : PayY π rad v₀ t :=
  fun a rest G0 Ly D hf => absurd hf (fixes_no_group π t h a rest G0 Ly D)

theorem yesAll_failsPaidY {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (v₀ : ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hg : x.1.st.groups[x.1.g]? = none) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b)
    (hs : Small p.err) :
    ¬ p.ior.red.Leads (fun x => FirstOpens π num no base x.1 ∧ PayY π rad v₀ x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x ⟨(promN_no_group F π num no rad rd base dB 0 (NTuple F π no rad rd) x hg).1,
      payY_no_group π rad v₀ x.1 hg⟩))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π _ x hg (hτ b hb')

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.leads_atFinish
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawY_F2
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawPaidY_F2
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsPaidY
