-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineProve.lean: from a state with `TidyO` and `TreeOKB` of the given trees, one
execution of the compiled prover obeys the rules of deferred programming, if no round is shared
(`joins` = 0) or there are 2^depthReq slots; given `Spec.safeChainT0` (words of this library:
lean/GLOSSARY.md).

`Spec.safeProveB` (Compile/Batch/DisciplineStar.lean) from the start of the slots
(Compile/Batch/DisciplineInit.lean), the end (Compile/Batch/DisciplineFinish.lean) and
`Spec.safeChainT0`, stated below. An execution's tokens are numbers from n₀ on, the number of tokens
at its start; the tokens of the trees over the external strings (`TreeTok`) are smaller.

Notation:
  `cms`: a list of digests; in `chainsU` (Compile/Batch/SeedLazyDefs.lean): the roots of the trees
    over the external strings;
  `σ0`: an `SStrat s A` (Iop/Batch.lean): a strategy for the shared part: m_0 in every round;
  `zs`: the slots (`ChainInv`, Compile/Batch/DisciplineChain.lean), each a `SlotSt`: a slot with
    the rest of its strategy (Compile/Batch/Prover.lean);
  `PhT.first`: a `PhT` (Compile/Batch/Prover.lean), the phase: `first`, `loc`, `shr tk0` or `aft`;
  `⟨[], [], none, [], []⟩`: the `Acc0` whose fields `trees`, `toks`, `nons`, `dead` are empty and
    whose `req` is none;
  `out`: what `chainT` returns, a pair: `out.1`: the slots' `SlotAcc`s; `out.2`: the `Acc0`
    (Compile/Batch/Prover.lean).
-/
import Compile.Batch.DisciplineInit
import Compile.Batch.DisciplineFinish
import Compile.Batch.DisciplineStar

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules TreeTok)

/-- All chains of a batch obey the rules, from a state with `TidyO` and at least n₀ tokens in which
every slot is at its start, with different salts, if no round is shared (`joins` = 0) or there are
2^depthReq slots. Their queries charge and hold only tokens from n₀ on, no token that exists at the
start is newly shown, no ordinary query is made; at the end every slot has what the end needs, and
the shared trees are in order. -/
def Spec.safeChainT0 : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (p : Params) (Z : Type) (t : Tag) (cms : List (Dig lam))
    (xin : Z → Option X) (depthReq : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (q : OPos s) → OSym s q → Body L)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (σ0 : SStrat s A)
    (zs : List (SlotSt lam K Z s)) (n₀ : ℕ) (d : DSt (spec lam K L)),
    TidyO (rulesB K L lam p) d → n₀ ≤ d.vals.length →
    AllFrom (fun j z => SlotI p d n₀ [] PhT.first ⟨[], [], none, [], []⟩ j z.2) 0 zs →
    (zs.map fun z => z.2.tk).Nodup →
    (joins s A = 0 ∨ zs.length = 2 ^ depthReq) →
    SafeO (rulesB K L lam p) (chainT p.sMT t cms xin depthReq s A W embS embP 0 PhT.first σ0 zs ⟨[], [], none, [], []⟩) d fun out d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun u => n₀ ≤ u) (fun u => n₀ ≤ u) NoTok zr (mProveB t s A W zs.length) d d' ∧
      AllFrom (fun j acc => ∃ Op, SlotF d' n₀ (depthsOf s A W) Op out.2 j acc) 0 out.1 ∧
      Trees0 d' n₀ (depthsOf s A W) out.2.trees

/-- From `Spec.safeChainT0`: `Spec.safeProveB`. -/
theorem safeProveB_of (hC : Spec.safeChainT0) : Spec.safeProveB := by
  intro I X lam K L p t Y E Q Wt H wq wp embS embP xin depthReq trees w fl xs d hd htr hN
  unfold proveB
  refine SafeO.bind _ _ d ?_
  refine fun rc => ?_
  change SafeO _ (Step.bind _ _) d _
  refine SafeO.bind _ _ d
    (SafeO.mono ?_ _ d (safe_initAll Q H wp w (wp.coin0.e rc) d.vals.length xs 0 d le_rfl hd))
  rintro zs d₁ ⟨hd₁, hr₁, hlen, hall, hnd, -⟩
  refine SafeO.bind _ _ d₁
    (SafeO.mono ?_ _ d₁
      (hC I X lam K L p _ t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1)
        depthReq Q.loc.shape Q.ann wq.sh embS embP (H.strat0 w (wp.coin0.e rc)) zs
        d.vals.length d₁ hd₁ hr₁.length_le hall hnd (hN.imp_right fun h => hlen.trans h)))
  rintro out d₂ ⟨hd₂, hr₂, hfin, h0⟩
  have htr₂ : ∀ tr ∈ trees, TreeOKB d₂ tr := fun tr h =>
    ((htr tr h).grows hr₁.grows fun _ _ hu => hu).grows hr₂.grows fun u hu hn =>
      absurd ((htr tr h).lt hu) (Nat.not_lt.mpr hn)
  refine SafeO.mono ?_ _ d₂
    (safe_finishAll Q H wq wp trees w d.vals.length fl (wp.coin0.e rc)
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
