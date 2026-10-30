-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/DoorFirst.lean: THE PREMISES h₁ AND hb OF THE SECOND CHAIN's START, AT EVERY Z UNDER THE
HEAD, WITH NO CLOSED LINE: along any fold of the first chain from its start the count of roots is the book's
count of trees; and without a mark the codes are the plan's. first_fold_roots, first_fold_codes, and
first_thr_ends at a state of a thread.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.DoorPublic
import Johnson.AtFull.Shape.K1ValuesHead
import Johnson.IMR.AtReach
import Johnson.IMR.CodesSeat
import Johnson.Desc.Book.ReachOwedAtHead
import Johnson.Desc.ProofFile.Honest.Thread.Thr

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Third (rootsB)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Thr Thread ProverCoinCounts Coins Mid)
open Meaning.K2 (BookLaw orderedP open_fold_all seatKeeps_sentence seatBack_sentence recv_ordered
  k12_ordered empty_ordered start_empty seatKeeps_codes seatBack_codes recAll_startS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **hb along a fold.** -/
theorem first_fold_roots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : Nat) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y) :
    rootsB y.1.roots y.1.book = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have H : BookLaw orderedP :=
    ⟨recv_ordered, fun A B r hs k => VerifiableInference.Desc.First.K2.ordered_same 0 A B r hs k, k12_ordered⟩
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := O.pub
  have q : orderedP y.1.book y.1.roots :=
    open_fold_all (seatKeeps_sentence H) (seatBack_sentence H) O trivial (fun _ _ _ => trivial)
      (plans_at h) k hf (by
        show orderedP (ProofFile.startS Zp p).book (ProofFile.startS Zp p).roots
        rw [(start_empty hZ p).1, (start_empty hZ p).2]
        exact empty_ordered)
  unfold rootsB
  exact beq_iff_eq.2 q.1

/-- The first chain's codes as read back are the codes as sized. -/
theorem codes_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Zp.first.codes = (ProofFile.pAt Zp).codes :=
  VerifiableInference.Desc.Book.codes_at_head h.toAtMg

/-- **h₁ along a fold, where the state bears no mark.** -/
theorem first_fold_codes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : Nat) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y)
    (hu : y.1.failed = none) : y.1.st.codes = (ProofFile.pAt Zp).codes := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := O.pub
  have c1 : y.1.st.codes = (ProofFile.startS Zp p).st.codes :=
    open_fold_all seatKeeps_codes seatBack_codes O trivial (fun _ _ _ => trivial)
      (plans_at h) k hf
  have hq := start_passes Zp p (start_clean h k ft p rs cols y hf hu)
  exact c1.trans ((recAll_startS hZ hq).codes.trans (codes_of_head h))

/-- **h₁ and hb at a state of a thread of the first chain.** -/
theorem first_thr_ends (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder) (zOf : W → ProofFile.InstPub)
    (hbeg : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = ProofFile.startS Zp (zOf w))
    (hform : ∀ b k s m, T.Form b k s m → s.failed = none)
    {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E}
    (hT : Thr T b k s m E) :
    s.st.codes = (ProofFile.pAt Zp).codes ∧ rootsB s.roots s.book = true := by
  have hcl := hform _ _ _ _ hT.2.2.1
  unfold Thr ProofFile.Honest.Thread.Made at hT
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hb₀, -, hfold⟩, -, -⟩ := hT
  rw [hbs, hbeg _ _ _ _ hb₀] at hfold
  exact ⟨first_fold_codes h _ _ _ _ _ _ hfold hcl, first_fold_roots h _ _ _ _ _ _ hfold⟩

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.first_fold_roots
#print axioms Johnson.AtFull.Shape.Scope.first_fold_codes
#print axioms Johnson.AtFull.Shape.Scope.first_thr_ends
