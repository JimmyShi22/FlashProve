-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Init.lean: how the compiled prover sets up its slots, before the first round, for the
lemma on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). The
start of the slots of an execution (Compile/Batch/Prover.lean: `initSlot`, in all slots), from a
state that is orderly both ways (`TidyBoth`) and has at least n₀ tokens, obeys the discipline with
joint charges (`SafeO2`) and leaves every slot's record standing both ways: here `SlotI2` gets its
first instance.

`safe2_initSlot`, `safe2_initAll`, `SlotI2.keeps_first`: the analogue for `SafeO2`
(CompileK/Defer2Safe.lean) of Compile/Batch/DisciplineInit.lean. Nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs.

Why: at the start a slot's set is {its salt}, a new token that nothing holds: so it is closed
upwards.

Words used in this file. The discipline with joint charges, orderly both ways, closed upwards, both
ways: the paragraph "Words used in this file." of CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Slot
import Compile.Batch.DisciplineInit

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules afterFresh length_afterFresh)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ} {Y : Type} {E : ExtSpec}

/-- A slot in the phase first survives a run that holds and shows none of the old tokens, from a
state that is orderly both ways (hd). -/
theorem SlotI2.keeps_first {Z : Type} {d d' : DSt (spec lam K L)} {n₀ : ℕ}
    {done : List (ℕ × ℕ)} {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Z}
    {e M : OracleName → ℕ} (h : SlotI2 p d n₀ done PhT.first a0 j acc)
    (hd : TidyBoth p mG d) (hr : Run NoTok NoTok NoTok e M d d') :
    SlotI2 p d' n₀ done PhT.first a0 j acc :=
  ⟨h.fin.keeps hr (fun _ hu => hu.elim) (GJ.of_grows hr.grows) (fun _ hu => hu.elim),
    ⟨h.cap.1.grows hr.grows (fun hu => hu) (fun hu => hu), h.cap.2.1.grows hr.grows, h.cap.2.2⟩,
    DeadW.keeps_not h.alive hd.1 h.cap.1.lt hr fun _ hu => hu.elim⟩

variable (Q : BatchInteractiveOracleProof Y E)
  {Wt : Type} (H : BatchHonestProver Q Wt) (wp : WirePB Q H) (w : Wt) (c0 : H.Coin0)

/-- One slot at the start. -/
theorem safe2_initSlot (n₀ : ℕ) (x : Option Y) (d : DSt (spec lam K L))
    (hn : n₀ ≤ d.vals.length) (hd : TidyBoth p mG d) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (initSlot (lam := lam) (K := K) (L := L) p.sFS Q H wp w c0 x) d fun z d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok NoTok zr zr d d' ∧
      z.2.tk = d.vals.length ∧ d.vals.length < d'.vals.length ∧
      ∀ j, SlotI2 p d' n₀ [] PhT.first ⟨[], [], none, [], []⟩ j z.2 := by
  unfold initSlot
  refine SafeO2.bind _ _ d ?_
  refine fun rc => ?_
  refine fun u => ?_
  have hu := Untouched.of_fresh hd.1 (List.ofFn u)
  refine ⟨hd.fresh (List.ofFn u),
    Run.ofFresh d (List.ofFn u),
    rfl, hu.lt,
    fun j =>
      ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, List.Forall₂.nil, ?_⟩,
        ⟨hu, Len.of_fresh d u, ?_⟩,
        not_deadW_last (hd.fresh (List.ofFn u)).1 (le_of_eq (length_afterFresh d (List.ofFn u)))⟩⟩
  · intro e he hV
    exact absurd (List.mem_singleton.mp (inU_start rfl rfl hV)) (hu.not_held e he).1
  · intro v hv
    rw [List.mem_singleton.mp (inU_start rfl rfl hv)]
    exact hu.lt
  · intro v hv
    exact Or.inr (Or.inl (List.mem_singleton.mp (inU_start rfl rfl hv)))
  · intro e he _ b hb hV
    exact absurd hb (List.mem_singleton.mp (inU_start rfl rfl hV) ▸ (hu.not_held e he).2)
  · intro v hv
    rw [List.mem_singleton.mp (inU_start rfl rfl hv)]
    exact hn
  · exact List.cons_ne_nil _ _
  · exact List.mem_singleton.mpr rfl

/-- All slots at the start. -/
theorem safe2_initAll (n₀ : ℕ) :
    ∀ (xs : List (Option Y)) (j : ℕ) (d : DSt (spec lam K L)), n₀ ≤ d.vals.length →
      TidyBoth p mG d →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (eachM (initSlot (lam := lam) (K := K) (L := L) p.sFS Q H wp w c0) xs) d fun zs d' =>
      TidyBoth p mG d' ∧ Run NoTok NoTok NoTok zr zr d d' ∧ zs.length = xs.length ∧
      AllFrom (fun j z => SlotI2 p d' n₀ [] PhT.first ⟨[], [], none, [], []⟩ j z.2) j zs ∧
      (zs.map fun z => z.2.tk).Nodup ∧
      ∀ z ∈ zs, d.vals.length ≤ z.2.tk
  | [], _, d, _, hd =>
    ⟨hd, Run.refl d, rfl, trivial, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: xs, j, d, hn, hd => by
      show SafeO2 _ _ _
        ((initSlot p.sFS Q H wp w c0 x).bind fun b =>
          (eachM (initSlot p.sFS Q H wp w c0) xs).bind fun r => Step.pure (b :: r))
        d _
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_initSlot Q H wp w c0 n₀ x d hn hd))
      rintro b d₁ ⟨hd₁, hr₁, htk, hlt, hsl⟩
      refine SafeO2.bind _ _ d₁
        (SafeO2.mono ?_ _ d₁ (safe2_initAll n₀ xs (j + 1) d₁ (le_trans hn hr₁.length_le) hd₁))
      rintro r d₂ ⟨hd₂, hr₂, hlen, hall, hnd, hnew⟩
      refine ⟨hd₂,
        hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun _ => le_rfl),
        by simp [hlen],
        ⟨(hsl j).keeps_first hd₁ hr₂, hall⟩,
        ?_, ?_⟩
      · rw [List.map_cons]
        refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩
        obtain ⟨z, hz, hzt⟩ := List.mem_map.mp hm
        have := hnew z hz
        rw [hzt, htk] at this
        exact absurd hlt (Nat.not_lt.mpr this)
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact le_of_eq htk.symm
        · exact le_trans hr₁.length_le (hnew z hz)


end Compile.Batch.Disc
