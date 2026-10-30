-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ProverG.lean: how a property of programs carries through the search over nonces. Three
induction principles for `fbG`, two of them also for `fbSlotG` (Compile/Batch/Prover.lean), for
proofs by induction over the compiled prover. (Words of this library: lean/GLOSSARY.md.)

Such a proof has one lemma for each definition. For a Fiat-Shamir query without a proof-of-work
record that lemma is about `fbT`: if the property holds of what follows, for all blocks and chaining
values, it holds of the query. The search is made of `fbT` (attempt 0), `fbTw` (the later attempts,
under ghost names) and a branch: if the check passes then go on, else try again. So a property that
carries through `fbT` and through `fbTw` carries through the search:

  `Kept`   what the search guarantees of what it passes on: nc is there exactly if there is a
           record, dd has nc entries, nc is within the cap (`g.more`)
  `fbG_ind`, `fbSlotG_ind`, `fbG_indK`
      a property Φ of programs; `fbG_indK`: the same, with `Kept` as a hypothesis on what follows
  `fbG_cost`, `fbSlotG_cost`
      a property Φ n of programs with a number n that grows by at most c for each query and may be
      enlarged: the search costs (number of attempts) * c, at the worst case
  `fbG_two`   a relation between two programs that take the same steps on the same tokens (the two
              searches have the same record, the same tokens and the same plain part; what follows
              may differ)

Notation:
  at a Fiat-Shamir query (`fbT`, Compile/Batch/Prover.lean): `tk`: the token to which it is charged;
    `us`, `root`: its other tokens are us and then the root, if the component has a tree; `hd`,
    `hinj`: List Bits → Bits → Head lam X (`Head`: Compile/Batch/Oracles.lean), and that `hd vs` is
    injective for every vs; `pl`: the plain part; `k`: what follows, given `bl`, `tl`: the blocks
    and the chaining value of the answer
  `fbTG`: the search with a record g; `fbW`: the attempts after the first
    (Compile/Batch/Prover.lean); `fbG`: a Fiat-Shamir query, with a proof-of-work record or without
  `gr`, `g`: Option (GrW C P), GrW C P: the proof-of-work record (Iop/BatchWire.lean); `chal`: Blk
    lam K → C; `emb`, `α`: P → PlainPart .., P: the plain part of attempt number m is emb of α with the
    nonce for m (`g.put`)
  `nc`, `dd`: the number of the final attempt, if there is a record, and the chaining values of the
    attempts before it (`fbG`)

Limits: not covered are relations between programs with different tokens or with a state that is
carried along (the rules of deferred programming, the relations `Late`, `Skip`, `Par`): there the
induction is written out, on the pattern of the proofs here.
-/
import Compile.Batch.Counts

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {β C P : Type}

/-- What the search guarantees of what it passes on: nc, the number of the final attempt, is there
exactly if the round has a proof-of-work record; dd has as many chaining values as there are
attempts before the final one; the number is within the cap. -/
def Kept (gr : Option (GrW C P)) (nc : Option ℕ) (dd : List Tok) : Prop :=
  nc.isSome = gr.isSome ∧ dd.length = nc.getD 0 ∧ ∀ g, gr = some g → nc.getD 0 ≤ g.more

section One
variable {chal : Blk lam K → C} {t : Tag} {i : ℕ} {tk : Tok} {us : List Tok} {root : Option Tok}
  {hd : List Bits → Bits → Head lam X} {hinj : ∀ vs, Function.Injective (hd vs)}
  {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}

theorem fbW_ind {Φ : St lam K L β → Prop} (g : GrW C P)
    {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hw : ∀ j pl k', (∀ bl tl, Φ (k' bl tl)) → Φ (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ m dd bl tl, Φ (k m dd bl tl)) :
    ∀ n j dd, Φ (fbW g chal t i tk us root hd hinj emb α k n j dd)
  | 0, j, dd => hw j _ _ fun bl tl => hk _ _ bl tl
  | n + 1, j, dd => hw j _ _ fun bl tl => by
      split
      · exact hk _ _ bl tl
      · exact fbW_ind g hw hk n (j + 1) (tl :: dd)

theorem fbW_indK {Φ : St lam K L β → Prop} (g : GrW C P)
    {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hw : ∀ j pl k', (∀ bl tl, Φ (k' bl tl)) → Φ (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ m dd bl tl, dd.length = m → m ≤ g.more → Φ (k m dd bl tl)) :
    ∀ n j dd,
      dd.length = j + 1 → j + 1 + n = g.more → Φ (fbW g chal t i tk us root hd hinj emb α k n j dd)
  | 0, j, dd, h1, h2 => hw j _ _ fun bl tl => hk _ _ bl tl h1 (by omega)
  | n + 1, j, dd, h1, h2 => hw j _ _ fun bl tl => by
      split
      · exact hk _ _ bl tl h1 (by omega)
      · exact fbW_indK g hw hk n (j + 1) (tl :: dd) (by simp [h1]) (by omega)

/-- As `fbG_ind`, with the hypothesis on what follows only for what the search can pass on (`Kept`).
-/
theorem fbG_indK {Φ : St lam K L β → Prop} (gr : Option (GrW C P))
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (h0 : ∀ pl k', (∀ bl tl, Φ (k' bl tl)) → Φ (fbT t i tk us root hd hinj pl k'))
    (hw : ∀ j pl k', (∀ bl tl, Φ (k' bl tl)) → Φ (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ nc dd bl tl, Kept gr nc dd → Φ (k nc dd bl tl)) :
    Φ (fbG gr chal t i tk us root hd hinj emb α k) := by
  cases gr with
  | none => exact h0 _ _ fun bl tl => hk _ _ bl tl ⟨rfl, rfl, fun g e => by cases e⟩
  | some g =>
    have hk' : ∀ m dd bl tl,
        dd.length = m → m ≤ g.more → Φ (k (some m) dd bl tl) := fun m dd bl tl h1 h2 =>
      hk _ _ bl tl ⟨rfl, h1, fun g' e => by cases e; exact h2⟩
    show Φ (fbTG g chal t i tk us root hd hinj emb α fun m => k (some m))
    unfold fbTG
    split
    · exact h0 _ _ fun bl tl => hk' _ _ bl tl rfl (Nat.zero_le _)
    next n e =>
      refine h0 _ _ fun bl tl => ?_
      split
      · exact hk' _ _ bl tl rfl (Nat.zero_le _)
      · exact fbW_indK g hw hk' _ _ _ rfl (by omega)

/-- A property that carries through fbT and fbTw carries through fbG. -/
theorem fbG_ind {Φ : St lam K L β → Prop} (gr : Option (GrW C P))
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (h0 : ∀ pl k', (∀ bl tl, Φ (k' bl tl)) → Φ (fbT t i tk us root hd hinj pl k'))
    (hw : ∀ j pl k', (∀ bl tl, Φ (k' bl tl)) → Φ (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ nc dd bl tl, Φ (k nc dd bl tl)) :
    Φ (fbG gr chal t i tk us root hd hinj emb α k) := by
  cases gr with
  | none => exact h0 _ _ fun bl tl => hk _ _ bl tl
  | some g =>
    show Φ (fbTG g chal t i tk us root hd hinj emb α fun m => k (some m))
    unfold fbTG
    split
    · exact h0 _ _ fun bl tl => hk _ _ bl tl
    · refine h0 _ _ fun bl tl => ?_
      split
      · exact hk _ _ bl tl
      · exact fbW_ind g hw (fun m dd bl tl => hk (some m) dd bl tl) _ _ _

theorem fbW_cost {Φ : ℕ → St lam K L β → Prop} (g : GrW C P)
    {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β} {c n₀ : ℕ}
    (mono : ∀ a b x, a ≤ b → Φ a x → Φ b x)
    (hw : ∀ n j pl k', (∀ bl tl, Φ n (k' bl tl)) → Φ (c + n) (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ m dd bl tl, Φ n₀ (k m dd bl tl)) :
    ∀ n j dd, Φ ((n + 1) * c + n₀) (fbW g chal t i tk us root hd hinj emb α k n j dd)
  | 0, j, dd => by
      have := hw n₀ j (emb (g.put (j + 1) α)) _ fun bl tl => hk (j + 1) dd bl tl
      simpa using this
  | n + 1, j, dd => by
      have e : (n + 1 + 1) * c + n₀ = c + ((n + 1) * c + n₀) := by ring
      rw [e]
      refine hw _ j _ _ fun bl tl => ?_
      split
      · exact mono _ _ _ (Nat.le_add_left _ _) (hk _ _ bl tl)
      · exact fbW_cost g mono hw hk n (j + 1) (tl :: dd)

/-- A number that grows by at most c for each query and may be enlarged (`mono`) grows by at most
`triesOf gr` (the largest number of attempts) * c in fbG. -/
theorem fbG_cost {Φ : ℕ → St lam K L β → Prop} (gr : Option (GrW C P))
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β} {c n₀ : ℕ}
    (mono : ∀ a b x, a ≤ b → Φ a x → Φ b x)
    (h0 : ∀ n pl k', (∀ bl tl, Φ n (k' bl tl)) → Φ (c + n) (fbT t i tk us root hd hinj pl k'))
    (hw : ∀ n j pl k', (∀ bl tl, Φ n (k' bl tl)) → Φ (c + n) (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ nc dd bl tl, Φ n₀ (k nc dd bl tl)) :
    Φ (triesOf gr * c + n₀) (fbG gr chal t i tk us root hd hinj emb α k) := by
  cases gr with
  | none =>
    have := h0 n₀ (emb α) _ fun bl tl => hk none [] bl tl
    simpa [triesOf] using this
  | some g =>
    show Φ ((g.more + 1) * c + n₀) (fbTG g chal t i tk us root hd hinj emb α fun m => k (some m))
    unfold fbTG
    split
    next e =>
      rw [e]
      have := h0 n₀ (emb (g.put 0 α)) _ fun bl tl => hk (some 0) [] bl tl
      simpa using this
    next n e =>
      rw [e]
      have e' : (n + 1 + 1) * c + n₀ = c + ((n + 1) * c + n₀) := by ring
      rw [e']
      refine h0 _ _ _ fun bl tl => ?_
      split
      · exact mono _ _ _ (Nat.le_add_left _ _) (hk _ _ bl tl)
      · exact fbW_cost g mono hw (fun m dd bl tl => hk (some m) dd bl tl) _ _ _

theorem fbW_two {β' : Type} {Ψ : St lam K L β → St lam K L β' → Prop} (g : GrW C P)
    {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    {k' : ℕ → List Tok → Blk lam K → Tok → St lam K L β'}
    (hw : ∀ j pl k₁ k₂, (∀ bl tl, Ψ (k₁ bl tl) (k₂ bl tl)) →
      Ψ (fbTw t j i tk us root hd hinj pl k₁) (fbTw t j i tk us root hd hinj pl k₂))
    (hk : ∀ m dd bl tl, Ψ (k m dd bl tl) (k' m dd bl tl)) :
    ∀ n j dd, Ψ (fbW g chal t i tk us root hd hinj emb α k n j dd)
      (fbW g chal t i tk us root hd hinj emb α k' n j dd)
  | 0, j, dd => hw j _ _ _ fun bl tl => hk _ _ bl tl
  | n + 1, j, dd => hw j _ _ _ fun bl tl => by
      by_cases h : g.ok (chal bl) = true
      · simp only [h, if_true]; exact hk _ _ bl tl
      · simp only [h]; exact fbW_two g hw hk n (j + 1) (tl :: dd)

/-- A relation between two programs that take the same steps, if it carries through fbT and fbTw,
carries through fbG. -/
theorem fbG_two {β' : Type} {Ψ : St lam K L β → St lam K L β' → Prop} (gr : Option (GrW C P))
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    {k' : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β'}
    (h0 : ∀ pl k₁ k₂, (∀ bl tl, Ψ (k₁ bl tl) (k₂ bl tl)) →
      Ψ (fbT t i tk us root hd hinj pl k₁) (fbT t i tk us root hd hinj pl k₂))
    (hw : ∀ j pl k₁ k₂, (∀ bl tl, Ψ (k₁ bl tl) (k₂ bl tl)) →
      Ψ (fbTw t j i tk us root hd hinj pl k₁) (fbTw t j i tk us root hd hinj pl k₂))
    (hk : ∀ nc dd bl tl, Ψ (k nc dd bl tl) (k' nc dd bl tl)) :
    Ψ (fbG gr chal t i tk us root hd hinj emb α k)
      (fbG gr chal t i tk us root hd hinj emb α k') := by
  cases gr with
  | none => exact h0 _ _ _ fun bl tl => hk _ _ bl tl
  | some g =>
    show Ψ (fbTG g chal t i tk us root hd hinj emb α fun m => k (some m))
      (fbTG g chal t i tk us root hd hinj emb α fun m => k' (some m))
    unfold fbTG
    cases g.more with
    | zero => exact h0 _ _ _ fun bl tl => hk _ _ bl tl
    | succ n =>
      refine h0 _ _ _ fun bl tl => ?_
      by_cases h : g.ok (chal bl) = true
      · simp only [h, if_true]; exact hk _ _ bl tl
      · simp only [h]; exact fbW_two g hw (fun m dd bl tl => hk (some m) dd bl tl) _ _ _

end One

/-! ## The query of a slot in a local round -/

section Slot
variable {chal : Blk lam K → C} {t : Tag} {i : ℕ} {cms : List (Dig lam)} {x : Option X} {tk c : Tok}
  {root : Option Tok} {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}

theorem fbSlotG_ind {Φ : St lam K L β → Prop} (gr : Option (GrW C P)) (ph : PhT)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (h0 : ∀ tk us hd hinj pl k', (∀ bl tl, Φ (k' bl tl)) → Φ (fbT t i tk us root hd hinj pl k'))
    (hw : ∀ j tk us hd hinj pl k',
      (∀ bl tl, Φ (k' bl tl)) → Φ (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ nc dd bl tl, Φ (k nc dd bl tl)) :
    Φ (fbSlotG gr chal t i cms x ph tk c root emb α k) := by
  cases ph <;> exact fbG_ind gr (h0 _ _ _ _) (fun j => hw j _ _ _ _) hk

theorem fbSlotG_cost {Φ : ℕ → St lam K L β → Prop} (gr : Option (GrW C P))
    (ph : PhT) {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    {c₀ n₀ : ℕ} (mono : ∀ a b x, a ≤ b → Φ a x → Φ b x)
    (h0 : ∀ n tk us hd hinj pl k',
      (∀ bl tl, Φ n (k' bl tl)) → Φ (c₀ + n) (fbT t i tk us root hd hinj pl k'))
    (hw : ∀ n j tk us hd hinj pl k',
      (∀ bl tl, Φ n (k' bl tl)) → Φ (c₀ + n) (fbTw t j i tk us root hd hinj pl k'))
    (hk : ∀ nc dd bl tl, Φ n₀ (k nc dd bl tl)) :
    Φ (triesOf gr * c₀ + n₀) (fbSlotG gr chal t i cms x ph tk c root emb α k) := by
  cases ph <;> exact fbG_cost gr mono (fun n => h0 n _ _ _ _) (fun n j => hw n j _ _ _ _) hk

end Slot

end Compile.Batch
