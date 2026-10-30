-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineInit.lean: the start of the slots of an execution obeys the rules of
deferred programming, from a state with `TidyO` and at least n₀ tokens (words of this library:
lean/GLOSSARY.md).

For `Spec.safeProveB`: `initSlot` in all slots (`eachM`) of Compile/Batch/Prover.lean. From such a
state a slot starts with coins and a new salt of sFS bits, which nothing holds. So the set of its
tokens, {salt}, is closed, its one open end is the salt, and the salt can be charged and is no dead
tail (`SlotI` in the phase `first`, Compile/Batch/DisciplineSlot.lean). The slots' salts are
different tokens.
-/
import Compile.Batch.DisciplineSlot

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules afterFresh length_afterFresh)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {Y : Type} {E : ExtSpec}

/-- At the start the tokens of a slot are those in its own list `toks`. -/
theorem inU_start {Z : Type} {j : ℕ} {acc : SlotAcc lam K Z} (ht : acc.trees = [])
    (hdd : acc.dead = []) {u : Tok} (h : InU ⟨[], [], none, [], []⟩ j acc u) : u ∈ acc.toks := by
  rcases h with h | h | ⟨tr, h, -⟩ | ⟨tr, h, -⟩ | ⟨rq, h, -⟩ | h | h
  · exact h
  · exact absurd h List.not_mem_nil
  · rw [ht] at h; exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil
  · cases h
  · rw [hdd] at h; exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil

/-- Under `TidyO`: a slot in the phase first survives a run that holds and shows none of the old
tokens. -/
theorem SlotI.keeps_first {Z : Type} {d d' : DSt (spec lam K L)} {n₀ : ℕ}
    {done : List (ℕ × ℕ)} {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Z}
    {e M : OracleName → ℕ} (h : SlotI p d n₀ done PhT.first a0 j acc)
    (hd : TidyO (rulesB K L lam p) d) (hr : Run NoTok NoTok NoTok e M d d') :
    SlotI p d' n₀ done PhT.first a0 j acc :=
  ⟨h.fin.keeps hr fun _ hu => hu.elim,
    ⟨h.cap.1.grows hr.grows (fun hu => hu) (fun hu => hu), h.cap.2.1.grows hr.grows, h.cap.2.2⟩,
    DeadW.keeps_not h.alive hd h.cap.1.lt hr fun _ hu => hu.elim⟩

variable (Q : BatchInteractiveOracleProof Y E)
  {Wt : Type} (H : BatchHonestProver Q Wt) (wp : WirePB Q H) (w : Wt) (c0 : H.Coin0)

/-- One slot at the start. -/
theorem safe_initSlot (n₀ : ℕ) (x : Option Y) (d : DSt (spec lam K L))
    (hn : n₀ ≤ d.vals.length) (hd : TidyO (rulesB K L lam p) d) :
    SafeO (rulesB K L lam p) (initSlot (lam := lam) (K := K) (L := L) p.sFS Q H wp w c0 x) d fun z d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run NoTok NoTok NoTok zr zr d d' ∧
      z.2.tk = d.vals.length ∧
      d.vals.length < d'.vals.length ∧
      ∀ j, SlotI p d' n₀ [] PhT.first ⟨[], [], none, [], []⟩ j z.2 := by
  unfold initSlot
  refine SafeO.bind _ _ d ?_
  refine fun rc => ?_
  refine fun u => ?_
  have hu := Untouched.of_fresh hd (List.ofFn u)
  refine ⟨hd.fresh (List.ofFn u),
    Run.ofFresh d (List.ofFn u),
    rfl, hu.lt,
    fun j =>
      ⟨⟨⟨?_, ?_, ?_⟩, ?_, List.Forall₂.nil, ?_⟩,
        ⟨hu, Len.of_fresh d u, ?_⟩,
        not_deadW_last (hd.fresh (List.ofFn u)) (le_of_eq (length_afterFresh d (List.ofFn u)))⟩⟩
  · intro e he hV
    exact absurd (List.mem_singleton.mp (inU_start rfl rfl hV)) (hu.not_held e he).1
  · intro v hv
    rw [List.mem_singleton.mp (inU_start rfl rfl hv)]
    exact hu.lt
  · intro v hv
    exact Or.inr (Or.inl (List.mem_singleton.mp (inU_start rfl rfl hv)))
  · intro v hv
    rw [List.mem_singleton.mp (inU_start rfl rfl hv)]
    exact hn
  · exact List.cons_ne_nil _ _
  · exact List.mem_singleton.mpr rfl

/-- All slots at the start. -/
theorem safe_initAll (n₀ : ℕ) :
    ∀ (xs : List (Option Y)) (j : ℕ) (d : DSt (spec lam K L)), n₀ ≤ d.vals.length →
      TidyO (rulesB K L lam p) d →
      SafeO (rulesB K L lam p)
        (eachM (initSlot (lam := lam) (K := K) (L := L) p.sFS Q H wp w c0) xs) d fun zs d' =>
      TidyO (rulesB K L lam p) d' ∧ Run NoTok NoTok NoTok zr zr d d' ∧ zs.length = xs.length ∧
      AllFrom (fun j z => SlotI p d' n₀ [] PhT.first ⟨[], [], none, [], []⟩ j z.2) j zs ∧
      (zs.map fun z => z.2.tk).Nodup ∧
      ∀ z ∈ zs, d.vals.length ≤ z.2.tk
  | [], _, d, _, hd =>
    ⟨hd, Run.refl d, rfl, trivial, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: xs, j, d, hn, hd => by
      show SafeO _
        ((initSlot p.sFS Q H wp w c0 x).bind fun b =>
          (eachM (initSlot p.sFS Q H wp w c0) xs).bind fun r => Step.pure (b :: r))
        d _
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_initSlot Q H wp w c0 n₀ x d hn hd))
      rintro b d₁ ⟨hd₁, hr₁, htk, hlt, hsl⟩
      refine SafeO.bind _ _ d₁
        (SafeO.mono ?_ _ d₁ (safe_initAll n₀ xs (j + 1) d₁ (le_trans hn hr₁.length_le) hd₁))
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
