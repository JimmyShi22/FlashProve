-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Finish.lean: the last step of the compiled prover, for the lemma on deferred
programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). Under the hypotheses of
their statements: the fourth reveal site: the argument strings of the slots
(Compile/Batch/Prover.lean: `finishSlot`, `finishAll`) are made within the discipline with joint
charges (`SafeO2`), if the slots' records hold both ways (CompileK/Defer2Slot.lean: `SlotF2`,
`Trees02`).

The analogues for `SafeO2` (CompileK/Defer2Safe.lean) of `run_openE`, `run_opensExtB`,
`safe_finishSlot`, `safe_finishAll` (Compile/Batch/DisciplineFinish.lean). The lemmas of that file
on the list that is revealed (`mem_reveal_iff` ..) are used as they stand. Nothing assumed beyond
the hypotheses of the statements and whatever the arguments hold as proofs.

Why: the one reveal shows exactly the slot's set of tokens; `SlotF` says that this set is closed
downwards; `SlotF2`'s field up says: upwards at the vertex oracles: that is `UpClosed` of the list
(`revList`).

Limits: This file gives no instance of `SlotF2`, so as far as this file shows its theorems may hold
of nothing. This file does not settle that the slot's set is closed upwards: that no chain's token,
no root of a tree over a message, no dead try's tail is a vertex's further token, and that the
request path's tokens are held within it: that is asked where `SlotF` is established: in the chain
files (`SlotF2`: CompileK/Defer2Chain.lean, CompileK/Defer2ChainSh.lean, CompileK/Defer2Join.lean,
CompileK/Defer2ChainAll.lean).

Words used in this file. The discipline with joint charges, the vertex oracles, closed upwards, both
ways: the paragraph "Words used in this file." of CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Slot
import CompileK.Defer2E
import Compile.Batch.DisciplineFinish

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules TreeTok)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ} {Y : Type} {E : ExtSpec}

theorem run2_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) {d : DSt (spec lam K L)}
    (hd : TidyBoth p mG d) (ht : TreeOKB2 d t) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (openE (K := K) (L := L) t j a) d fun _ d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok (TreeTok t) zr zr d d' := by
  unfold openE
  split
  · rename_i s s' heq
    have hm : some (s, s') ∈ t.salts := by
      rw [List.getD_eq_getElem?_getD] at heq
      cases h : t.salts[j]? with
      | none => rw [h] at heq; exact absurd heq (by simp)
      | some x =>
        rw [h] at heq
        have hx : x = some (s, s') := heq
        exact hx ▸ List.mem_of_getElem? h
    refine ⟨(ht s s' hm).1,
      (ht s s' hm).2,
      fun T =>
        ⟨hd.reveal (ht s s' hm) T,
          (Run.ofReveal (Cc := NoTok) (Ch := NoTok) (e := zr) (M := zr) d [s, s'] T).mono
            (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun u hu => Or.inl ⟨s, s', hm, ?_⟩)
            (fun _ => le_rfl) (fun _ => le_rfl)⟩⟩
    rcases List.mem_cons.mp hu with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h1)
  · exact ⟨hd, Run.refl d⟩

theorem run2_opensExtB (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ (ps : List E.Pos) (d : DSt (spec lam K L)), TidyBoth p mG d → (∀ tr ∈ trees, TreeOKB2 d tr) →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (opensExtB (K := K) (L := L) we y trees isRead ps) d fun _ d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok (fun u => ∃ tr ∈ trees, TreeTok tr u) zr zr d d'
  | [], d, hd, _ => ⟨hd, Run.refl d⟩
  | q :: ps, d, hd, ht => by
      rw [opensExtB]
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (run2_opensExtB we y trees isRead ps d hd ht))
      rintro f d₁ ⟨hd₁, hg₁⟩
      split
      · refine SafeO2.bind _ _ d₁
          (SafeO2.mono ?_ _ d₁
            (run2_openE (trees.getD (we.which q) ⟨[], []⟩) (we.leaf q) _ hd₁
              (treeOKB2_of_mem_or (fun tr htr => (ht tr htr).grows hg₁.grows fun _ _ h => h)
                (Compile.Disc.Open.getD_mem_or trees _))))
        rintro op d₂ ⟨hd₂, hg₂⟩
        exact ⟨hd₂,
          hg₁.trans hg₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h)
            (fun u hu =>
              Or.inl
                (Compile.Disc.Open.treeTok_of_mem_or (Compile.Disc.Open.getD_mem_or trees _) hu))
            (fun _ => le_rfl) (fun _ => le_rfl)⟩
      · exact ⟨hd₁, hg₁⟩

/-! ## One slot, all slots
The list that is revealed (`revList`): Compile/Batch/DisciplineFinish.lean. -/


variable (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (trees : List (TreeH lam)) (w : Wt)

/-- The argument string of one slot. -/
theorem safe2_finishSlot (n₀ : ℕ) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (d : DSt (spec lam K L))
    (hd : TidyBoth p mG d) {Op : Tok → Prop}
    (hs : SlotF2 d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) Op a0 j acc)
    (h0 : Trees02 d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) a0.trees)
    (htr : ∀ tr ∈ trees, TreeOKB2 d tr) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (finishSlot Q H wq wp trees w c0 a0 j x cj acc) d fun _ d' =>
      TidyBoth p mG d' ∧
      Run NoTok NoTok (fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u) zr zr d d' := by
  have hl : acc.trees.length = a0.trees.length := hs.trees.length_eq.symm.trans h0.length_eq
  have hmem := mem_reveal_iff a0 j acc hl hs.ne
  unfold finishSlot
  dsimp only
  split
  · exact ⟨hd, Run.refl d⟩
  · have hc : ClosedBoth d (revList a0 j acc) :=
      ⟨⟨fun t ht => hs.cl.lt t ((hmem t).mp ht),
          fun e he hce => Or.inl ((hmem _).mpr (hs.cl.closed e he ((hmem _).mp hce)).1),
          fun e he hce u hu =>
            Or.inl ((hmem _).mpr ((hs.cl.closed e he ((hmem _).mp hce)).2 u hu))⟩,
        fun e he hJ b hb hbt => Or.inl ((hmem _).mpr (hs.up e he hJ b hb ((hmem _).mp hbt)))⟩
    refine ⟨hc.1, hc.2, fun T => ?_⟩
    have hd₁ := hd.reveal hc T
    have hr₁ := Run.ofReveal (Cc := NoTok) (Ch := NoTok) (e := zr) (M := zr) d (revList a0 j acc) T
    refine SafeO2.bind _ _ _
      (SafeO2.mono ?_ _ _
        (safe2_opensB n₀ Q.loc.shape Q.ann wq.sh _ acc.trees a0.trees _ _ hd₁
          ((hs.trees.keeps hr₁ (fun _ h => h.elim) (GJ.of_grows hr₁.grows) (fun _ h => h.elim)).alJ
            _ _ _ _)
          ((h0.keeps hr₁ (fun _ h => h.elim) (GJ.of_grows hr₁.grows) (fun _ h => h.elim)).al0
            _ _ _ _)))
    rintro f d₂ ⟨hd₂, hr₂⟩
    refine SafeO2.bind _ _ _
      (SafeO2.mono ?_ _ _
        (run2_opensExtB wq.ext (H.ext w) trees _ wq.ext.all d₂ hd₂
          (fun tr h => ((htr tr h).grows hr₁.grows fun _ _ h => h).grows hr₂.grows fun _ _ h => h)))
    rintro g d₃ ⟨hd₃, hr₃⟩
    exact ⟨hd₃,
      ((hr₁.mono (Cc := NoTok) (Ch := NoTok) (R := fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u)
            (e := zr) (M := zr) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
            (fun u hu => Or.inl (Or.inl (hs.new u ((hmem u).mp hu)))) (fun _ => le_rfl)
            (fun _ => le_rfl)).trans
          hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun u hu => Or.inl (Or.inl hu))
          (fun _ => le_rfl) (fun _ => le_rfl)).trans
        hr₃ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun u hu => Or.inl (Or.inr hu))
        (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- The argument strings of all slots. -/
theorem safe2_finishAll (n₀ : ℕ) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (d : DSt (spec lam K L)), TidyBoth p mG d →
      AllFrom (fun j acc => ∃ Op, SlotF2 d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) Op a0 j acc) j zs →
      Trees02 d n₀ (depthsOf Q.loc.shape Q.ann wq.sh) a0.trees → (∀ tr ∈ trees, TreeOKB2 d tr) →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (finishAll Q H wq wp trees w fl c0 a0 j zs) d fun _ d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok (fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u) zr zr d d'
  | _, [], d, hd, _, _, _ => ⟨hd, Run.refl d⟩
  | j, acc :: zs, d, hd, hall, h0, htr => by
      rw [finishAll]
      obtain ⟨⟨Op, hs⟩, hrest⟩ := hall
      have hone : SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (match acc.x with
          | some (x, cj) =>
            if fl j then finishSlot Q H wq wp trees w c0 a0 j x cj acc else pure none
          | none => pure none) d fun _ d' =>
            TidyBoth p mG d' ∧
            Run NoTok NoTok (fun u => n₀ ≤ u ∨ ∃ tr ∈ trees, TreeTok tr u) zr zr d d' := by
        split
        · split
          · exact safe2_finishSlot Q H wq wp trees w n₀ c0 a0 j _ _ acc d hd hs h0 htr
          · exact ⟨hd, Run.refl d⟩
        · exact ⟨hd, Run.refl d⟩
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d hone)
      rintro π d₁ ⟨hd₁, hr₁⟩
      refine SafeO2.bind _ _ d₁
        (SafeO2.mono ?_ _ d₁
          (safe2_finishAll n₀ fl c0 a0 (j + 1) zs d₁ hd₁
            (AllFrom.mono
              (fun _ _ ⟨Op', h⟩ =>
                ⟨Op', h.keeps hr₁ (fun _ hu => hu.elim)
                    (GJ.of_grows hr₁.grows) (fun _ hu => hu.elim)⟩)
              _ _ hrest)
            (h0.keeps hr₁ (fun _ hu => hu.elim) (GJ.of_grows hr₁.grows) (fun _ hu => hu.elim))
            (fun tr h => (htr tr h).grows hr₁.grows fun _ _ hu => hu)))
      rintro r d₂ ⟨hd₂, hr₂⟩
      exact ⟨hd₂,
        hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun _ => le_rfl)⟩


end Compile.Batch.Disc
