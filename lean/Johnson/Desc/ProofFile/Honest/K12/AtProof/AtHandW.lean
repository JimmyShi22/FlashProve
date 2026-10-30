-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/AtHandW.lean: a test that says whether the state on entry
of the last chain's proximity test fell back, and that at a called part it did not: AtHandO.lean at
the last chain. Two definitions with code; four theorems.

  `doorTryW`, `atHandW`, `doorW_try`   `doorLastTry` and `atHandLast` (DoorLast.lean) at a
                 description, as `doorW` lays them; `doorW` is what `doorTryW` returns, the default
                 where it refuses
  `realW_rec`   the real job's state on entry is `doorW`
  `atHandW_reads`   it reads of the input the instance's public part alone, and of the front what
                 is seen alone
  `atHandW_at_run`   at the library's description and its own way in, at a called part of the last
                 chain of a run: at every front of the form that door_own_at_called names: the
                 test says yes

Limits.
- "At hand" is "the folds and the way in return". It does not say that the state is the verifier's.
- The front is one with the stand's field: the door reads the field. Where a front holds none the
  test may say no.
- hpre: `pre` is the list that `doorW` takes: a premise.
- All hypotheses of `door_own_at_called` stay. Nothing on whether `ready` or `runC` returns or a
  part is called. Nothing is evaluated here.
- What may be said here on hiding, and no more (a rule of use for whoever builds on this file;
  no theorem): «atHandW's verdict is a function of the instance's public part, the rounds shown and
  the field: of the view, as far as the field holds the view's columns. Whoever holds these can
  compute it.» The sentence on the door stands in the head of HalfW.lean in this folder.
- `realW_rec` is at the letters Fd and `enter`, `atHandW_at_run` at the library's description and
  `enterOwn`: it speaks of `halfW`'s job only where these two letters are laid so.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfW
import Johnson.Desc.ProofFile.Honest.K12.DoorLastAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest.K12.Light (ManyJob doorW doorLast doorLastTry atHandLast colsOpened
  door_own_at_called)

variable {Xi W X : Type}

/-- `doorLastTry` as `doorW` lays it. -/
def doorTryW (F : FileDescription Xi) (xOf : W → Xi) (enter : F.S₃ → Except String T12) (a : Place)
    (w : W) (fr : Front X) : Except String T12 :=
  doorLastTry F.first.blocksInOrder F.shared.blocksInOrder (F.second.blocksInOrder.takeWhile (·.place != a)) F.lastChainFirstTreeNumber
    (fun w => F.start₁ (F.pub (xOf w))) (fun w => F.start₂ (F.pub (xOf w)))
    (fun w => F.start₃ (F.pub (xOf w))) enter colsOpened w fr

/-- `atHandLast` as `doorW` lays it. -/
def atHandW (F : FileDescription Xi) (xOf : W → Xi) (enter : F.S₃ → Except String T12) (a : Place)
    (w : W) (fr : Front X) : Bool :=
  atHandLast F.first.blocksInOrder F.shared.blocksInOrder (F.second.blocksInOrder.takeWhile (·.place != a)) F.lastChainFirstTreeNumber
    (fun w => F.start₁ (F.pub (xOf w))) (fun w => F.start₂ (F.pub (xOf w)))
    (fun w => F.start₃ (F.pub (xOf w))) enter colsOpened w fr

/-- `doorW` is what `doorTryW` returns; the default where it refuses. -/
theorem doorW_try (F : FileDescription Xi) (xOf : W → Xi) (enter : F.S₃ → Except String T12) (a : Place)
    (fall : T12) (w : W) (fr : Front X) :
    doorW F xOf enter a fall w fr = (doorTryW F xOf enter a w fr).toOption.getD fall := rfl

/-- **The test reads of the input the instance's public part alone, and of the front what is seen
alone.** -/
theorem atHandW_reads (F : FileDescription Xi) (xOf : W → Xi) (enter : F.S₃ → Except String T12)
    (a : Place) (w w' : W) (fr fr' : Front X) (hp : F.pub (xOf w) = F.pub (xOf w'))
    (hs : fr.seen = fr'.seen) : atHandW F xOf enter a w fr = atHandW F xOf enter a w' fr' := by
  simp only [atHandW, atHandLast, ProofFile.Honest.K12.Light.doorLastTry, colsOpened, hp, hs]

/-- **The real job's state on entry is `doorW`.** -/
theorem realW_rec {W₀ Rc Tr : Type} (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String T12) (pile : Pub → Ground → K13.PileOf Xi)
    (no : Place → Nat) (readers : Local W₀ Rc Xi Tr → Readers)
    (weights : Local W₀ Rc Xi Tr → Weights) (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand)
    (Z : Pub) (G : Ground) {J : TestJob (Local W₀ Rc Xi Tr) X}
    (h : realW S Fd enter pile no readers weights rand Z G = some J) :
    J.rec₀ = doorW Fd (·.x) enter placeW idleT12 := by
  unfold realW jobRealW at h
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨F, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  rfl

/-- **At a called part of the last chain, at the library's description and its own way in, the
default is not taken**, at every front of the form that `door_own_at_called` names, at the test's
place. hpre: the blocks in front are those that `doorW` takes. -/
theorem atHandW_at_run {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {c : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hpl : (P5J.F0T o Zp Np cF).planOk = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x c = .ok R)
    (σ : Side (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).second.blocksInOrder R.second σ u pre t i)
    (hpre : (P5J.F0T o Zp Np cF).second.blocksInOrder.takeWhile (·.place != placeW) = pre)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x c ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y,
      midAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.seen.length = ((P5J.F0T o Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
        ((P5J.F0T o Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length +
        (pre.flatMap (·.rounds)).length + i ∧
      ∀ (fr : Front Y) (k : ℕ),
        ((P5J.F0T o Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
          ((P5J.F0T o Zp Np cF).shared.blocksInOrder.flatMap (·.rounds)).length +
          (pre.flatMap (·.rounds)).length ≤ k →
        fr.seen.rounds = m.seen.take k → fr.seen.opened = m.opened →
          atHandW (P5J.F0T o Zp Np cF) (·.x) VerifiableInference.Desc.K12.Seat.enterOwn placeW
            m.st.input fr = true := by
  obtain ⟨m, tr, hm, hin, hl, hd⟩ := door_own_at_called hpl hR σ u pre t i S hrun hc
  refine ⟨m, hm, hl, fun fr k hk hfr hop => ?_⟩
  have e := hd (fun w : Local W₀ Rc ProofFile.Inst Tr => w.x) m.st.input fr k (by rw [hin]) hk hfr hop
  unfold atHandW
  rw [hpre]
  exact e

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.doorTryW
#print axioms ProofFile.Honest.K12.AtProof.atHandW
#print axioms ProofFile.Honest.K12.AtProof.doorW_try
#print axioms ProofFile.Honest.K12.AtProof.atHandW_reads
#print axioms ProofFile.Honest.K12.AtProof.realW_rec
#print axioms ProofFile.Honest.K12.AtProof.atHandW_at_run
