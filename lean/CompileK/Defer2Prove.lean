-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Prove.lean: one execution of the compiled prover, put together from its parts, for
the lemma on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean).
One execution of the compiled prover obeys the discipline with joint charges (`Spec.safeProveB2`:
CompileK/Defer2Star.lean), if all chains of a batch do (`Spec.safeChainT02`); each under the
hypotheses of its statement.

A definition and `safeProveB2_of`, the analogue of the theorem of
Compile/Batch/DisciplineProve.lean: the start of the slots (`safe2_initAll`,
CompileK/Defer2Init.lean), the chains, the argument strings (`safe2_finishAll`,
CompileK/Defer2Finish.lean). `Spec.safeChainT02` is stated here, proved in
CompileK/Defer2ChainAll.lean. Nothing assumed beyond the hypotheses of the statements and whatever
the arguments hold as proofs.

Words used in this file. The discipline with joint charges, orderly both ways: the paragraph "Words
used in this file." of CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Init
import CompileK.Defer2Finish
import CompileK.Defer2Star
import Compile.Batch.DisciplineProve

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules TreeTok)

/-- States, for `maxMore s A W ≤ mG`: all chains of a batch obey the rules, from a state that is
orderly both ways (`TidyBoth`) with at least n₀ tokens in which every slot stands at its start
(`SlotI2`), with different salts, if the chains cannot join (`joins` = 0) or there are 2^depthReq
slots. Their evaluations charge and hold only tokens from n₀ on, none of the old tokens is shown,
nothing is evaluated plainly; at the end every slot has what the end needs, and the shared trees
stand. -/
def Spec.safeChainT02 : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (p : Params) (mG : ℕ) (Z : Type) (t : Tag)
    (cms : List (Dig lam)) (xin : Z → Option X) (depthReq : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (q : OPos s) → OSym s q → Body L)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (σ0 : SStrat s A)
    (zs : List (SlotSt lam K Z s)) (n₀ : ℕ) (d : DSt (spec lam K L)),
    TidyBoth p mG d → n₀ ≤ d.vals.length →
    AllFrom (fun j z => SlotI2 p d n₀ [] PhT.first ⟨[], [], none, [], []⟩ j z.2) 0 zs →
    (zs.map fun z => z.2.tk).Nodup →
    (joins s A = 0 ∨ zs.length = 2 ^ depthReq) → maxMore s A W ≤ mG →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (chainT p.sMT t cms xin depthReq s A W embS embP 0 PhT.first σ0 zs ⟨[], [], none, [], []⟩) d fun out d' =>
      TidyBoth p mG d' ∧
      Run (fun u => n₀ ≤ u) (fun u => n₀ ≤ u) NoTok zr (mProveB t s A W zs.length) d d' ∧
      AllFrom (fun j acc => ∃ Op, SlotF2 d' n₀ (depthsOf s A W) Op out.2 j acc) 0 out.1 ∧
      Trees02 d' n₀ (depthsOf s A W) out.2.trees

/-- `Spec.safeProveB2` (one execution of the compiled prover obeys the rules, under its hypotheses),
if `hC`. -/
theorem safeProveB2_of (hC : Spec.safeChainT02) : Spec.safeProveB2 := by
  intro I X lam K L p mG t Y E Q Wt H wq wp embS embP xin depthReq trees w fl xs d hd htr hN hmx
  unfold proveB
  refine SafeO2.bind _ _ d ?_
  refine fun rc => ?_
  change SafeO2 _ _ _ (Step.bind _ _) d _
  refine SafeO2.bind _ _ d
    (SafeO2.mono ?_ _ d (safe2_initAll Q H wp w (wp.coin0.e rc) d.vals.length xs 0 d le_rfl hd))
  rintro zs d₁ ⟨hd₁, hr₁, hlen, hall, hnd, -⟩
  refine SafeO2.bind _ _ d₁
    (SafeO2.mono ?_ _ d₁
      (hC I X lam K L p mG _ t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1) depthReq
        Q.loc.shape Q.ann wq.sh embS embP (H.strat0 w (wp.coin0.e rc)) zs d.vals.length d₁ hd₁
        hr₁.length_le hall hnd (hN.imp_right fun h => hlen.trans h) hmx))
  rintro out d₂ ⟨hd₂, hr₂, hfin, h0⟩
  have htr₂ : ∀ tr ∈ trees, TreeOKB2 d₂ tr := fun tr h =>
    ((htr tr h).grows hr₁.grows fun _ _ hu => hu).grows hr₂.grows fun u hu hn =>
      absurd ((htr tr h).lt hu) (Nat.not_lt.mpr hn)
  refine SafeO2.mono ?_ _ d₂
    (safe2_finishAll Q H wq wp trees w d.vals.length fl (wp.coin0.e rc)
      out.2 0 out.1 d₂ hd₂ hfin h0 htr₂)
  rintro πs d₃ ⟨hd₃, hr₃⟩
  refine ⟨hd₃,
    ((hr₁.grows.mono (Ch := fun _ => False) (R := fun u => ∃ tr ∈ trees, TreeTok tr u)
          (e := fun _ => 0) (M := fun _ => 0) (fun _ h => h.elim) (fun _ h => h.elim)
          (fun _ => le_rfl) (fun _ => le_rfl)).trans
        hr₂.grows (e := fun _ => 0) (M := mProveB t Q.loc.shape Q.ann wq.sh xs.length)
        (fun _ h => Or.inr h) (fun _ h => h.elim) (fun _ => le_rfl)
        (fun o => by rw [Nat.zero_add, hlen])).trans
      hr₃.grows (fun _ h => h.elim) (fun u hu => hu.symm) (fun _ => le_rfl) (fun _ => le_rfl)⟩


end Compile.Batch.Disc
