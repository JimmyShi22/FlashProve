-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Cell.lean: a cell: all that the proof of the rule
(`row_law_abs`, Honest/Law/Rule/Items.lean) reads of one part with its simulator, as functions on
coins. These are the row of a run's coins that is the part's own (a lens); the blocks that the book
gives it (Honest/Law/Rule/Weave.lean: `runs`); what it says at these, as a function of what has been
produced; and what its simulator outputs. Φ (what has been produced) and V (what is shown) are type
parameters: no description, no prover, no `Part` and no run of a protocol occurs here.

  1  `spentE`, `carryE`, `Cell`, `Cell.spent`, `Cell.carried`, `Cell.out`,
     `Cell.stage`   definitions
  2  `cell_ker`   step L2 of that proof, in the abstract. Three hypotheses. The cell's own coins and
     the blocks that it spends are as drawn afresh beside the pair (what has been produced before,
     the blocks that it carries). Where the cell is called and `On` holds, over fresh ones what it
     says has the distribution of what its simulator outputs. And at all coins at which the cell is
     called its blocks are available, `On` holds and it says something. Then the chain rule's
     hypothesis holds at its stage
  3  `Cell.get_other`, `runs_other`, `runs_known`, `Cell.shows_other`, `Cell.shows_known`   through
     what a cell reads another cell's row

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Owner
import Johnson.Desc.ProofFile.Honest.Law.Rule.LentAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.Ker

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob

/-! ## 1 Definitions -/

/-- The entries by which the part at a spends coins, in the book's order. -/
def spentE (Bk : ProverCoinCounts) (a : Addr) : List Ahead :=
  (Bk.ahead.filter fun e => e.spender == a).filter fun e => e.once

/-- The entries by which it carries coins. -/
def carryE (Bk : ProverCoinCounts) (a : Addr) : List Ahead :=
  (Bk.ahead.filter fun e => e.spender == a).filter fun e => !e.once

/-- **A cell.** Nothing in the structure ties its fields to one another. That `get` and `put` are a
lens on the row at `addr` is a separate hypothesis (`RowAt`, Honest/Law/Rule/LentAt.lean). `live`,
`sub`, `On` and `tell` are free; `tell` is tied to `speaks` by the second hypothesis of `cell_ker`
alone. -/
structure Cell (Bk : ProverCoinCounts) (Φ V : Type) where
  /- the part's address -/
  addr : Addr
  /-- the chain's number, from 0 -/
  chain : Nat
  /- the count of its own coins -/
  takes : Due
  /-- meant as the lens on the part's own row (see above) -/
  get : Coins Bk → Cs takes
  put : Cs takes → Coins Bk → Coins Bk
  /-- what the part says, at its own coins, the blocks that it spends, the blocks that it carries,
  and what has been produced before; or `none` -/
  speaks : Cs takes → CsAll ((spentE Bk addr).map Ahead.named) →
    CsAll ((carryE Bk addr).map Ahead.named) → Φ → Option V
  /-- the part is called -/
  live : Φ → Bool
  /-- what is produced in its place where it is not -/
  sub : V
  /- the count of its simulator's coins -/
  simTakes : Due
  /- what its simulator outputs, at what has been produced before and at the simulator's coins; or
  `none` -/
  tell : Φ → Cs simTakes → Option V
  /- a condition on the blocks that it carries and on what has been produced before -/
  On : CsAll ((carryE Bk addr).map Ahead.named) → Φ → Prop
  /- what has been produced, with what the cell shows added -/
  add : Φ → V → Φ

variable {Bk : ProverCoinCounts} {Φ V : Type}

/- The blocks that it spends, at a run's coins (`runs`, Honest/Law/Rule/Weave.lean); `none` where a
block is not within its owner's count. -/
def Cell.spent (C : Cell Bk Φ V) (k : Coins Bk) :
    Option (CsAll ((spentE Bk C.addr).map Ahead.named)) :=
  runs (k.look C.chain) (spentE Bk C.addr)

/- The blocks that it carries, likewise. -/
def Cell.carried (C : Cell Bk Φ V) (k : Coins Bk) :
    Option (CsAll ((carryE Bk C.addr).map Ahead.named)) :=
  runs (k.look C.chain) (carryE Bk C.addr)

/-- What it says where all three are available; `none` where one is not, or where `speaks` returns
`none`. -/
def Cell.out (C : Cell Bk Φ V) (c : Option (Cs C.takes))
    (sp : Option (CsAll ((spentE Bk C.addr).map Ahead.named)))
    (ca : Option (CsAll ((carryE Bk C.addr).map Ahead.named))) (φ : Φ) : Option V :=
  c.bind fun c => sp.bind fun sp => ca.bind fun ca => C.speaks c sp ca φ

/-- **The cell as a stage.** `shows`: where the cell is called (`live`), what it says at its own
coins and its blocks (`Cell.out`); where that is `none` (a block is not available, or the cell says
nothing) the `Inhabited` instance's value of V takes its place: the third hypothesis of `cell_ker`
keeps that case from being reached; where the cell is not called, `sub`. `tells`: where it is
called, `(unif (Cs C.simTakes)).map (C.tell φ)`; else `PMF.pure (some C.sub)`. `add`: the cell's. -/
noncomputable def Cell.stage [Inhabited V] (C : Cell Bk Φ V) : Kit.Stage (Coins Bk) Φ V :=
  ⟨fun k φ => if C.live φ then (C.out (some (C.get k)) (C.spent k) (C.carried k) φ).getD default
      else C.sub,
    fun φ => if C.live φ then (unif (Cs C.simTakes)).map (C.tell φ) else PMF.pure (some C.sub),
    C.add⟩

/-! ## 2 Step L2, in the abstract -/

/-- **The chain rule's hypothesis at a cell's stage.** -/
theorem cell_ker [Inhabited V] (C : Cell Bk Φ V) (L₀ : Φ)
    (pre : List (Kit.Stage (Coins Bk) Φ V))
    (hind : (unif (Coins Bk)).map (fun k =>
        ((some (C.get k), C.spent k), (Kit.real pre k L₀, C.carried k))) =
      (unif ((Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named)) × Coins Bk)).map fun z =>
        ((some z.1.1, some z.1.2), (Kit.real pre z.2 L₀, C.carried z.2)))
    (hexact : ∀ ca φ, C.live φ = true → C.On ca φ →
      (unif (Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named))).map
        (fun c => C.speaks c.1 c.2 ca φ) = (unif (Cs C.simTakes)).map (C.tell φ))
    (hk : ∀ k, C.live (Kit.real pre k L₀) = true → ∃ sp ca v, C.spent k = some sp ∧
      C.carried k = some ca ∧ C.On ca (Kit.real pre k L₀) ∧
      C.speaks (C.get k) sp ca (Kit.real pre k L₀) = some v) :
    Kit.KerAt L₀ pre C.stage := by
  have h := Kit.kernel_step (fun k => (some (C.get k), C.spent k))
    (fun z : Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named) => (some z.1, some z.2))
    (fun k => (Kit.real pre k L₀, C.carried k)) hind
    (fun a b => if C.live b.1 then C.out a.1 a.2 b.2 b.1 else some C.sub) (fun b => b.1)
    C.stage.tells (by
      intro k
      by_cases hl : C.live (Kit.real pre k L₀) = true
      · obtain ⟨sp, ca, v, -, h2, h3, -⟩ := hk k hl
        show (unif _).map (fun x : Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named) =>
            if C.live (Kit.real pre k L₀) = true then
              C.out (some x.1) (some x.2) (C.carried k) (Kit.real pre k L₀) else some C.sub) =
          if C.live (Kit.real pre k L₀) = true then
            (unif (Cs C.simTakes)).map (C.tell (Kit.real pre k L₀)) else PMF.pure (some C.sub)
        simp only [if_pos hl, h2]
        exact hexact ca _ hl h3
      · show (unif _).map (fun x : Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named) =>
            if C.live (Kit.real pre k L₀) = true then
              C.out (some x.1) (some x.2) (C.carried k) (Kit.real pre k L₀) else some C.sub) =
          if C.live (Kit.real pre k L₀) = true then
            (unif (Cs C.simTakes)).map (C.tell (Kit.real pre k L₀)) else PMF.pure (some C.sub)
        simp only [if_neg hl]
        exact PMF.map_const _ _)
  have e : (fun k => (Kit.real pre k L₀, some (C.stage.shows k (Kit.real pre k L₀)))) =
      fun k => (Kit.real pre k L₀, if C.live (Kit.real pre k L₀) = true then
        C.out (some (C.get k)) (C.spent k) (C.carried k) (Kit.real pre k L₀) else some C.sub) := by
    funext k
    refine congrArg (Prod.mk (Kit.real pre k L₀)) ?_
    show some (if C.live (Kit.real pre k L₀) = true then
      (C.out (some (C.get k)) (C.spent k) (C.carried k) (Kit.real pre k L₀)).getD default
      else C.sub) = _
    by_cases hl : C.live (Kit.real pre k L₀) = true
    · obtain ⟨sp, ca, v, h1, h2, -, h4⟩ := hk k hl
      have ho : C.out (some (C.get k)) (C.spent k) (C.carried k) (Kit.real pre k L₀) = some v := by
        rw [h1, h2]
        exact h4
      rw [if_pos hl, if_pos hl, ho]
      rfl
    · rw [if_neg hl, if_neg hl]
  unfold Kit.KerAt
  rw [e]
  exact h

/-! ## 3 Through what a cell reads another cell's row -/

section
variable {o : Addr} {t : Nat} {d : Due} {get : Coins Bk → Cs d} {put : Cs d → Coins Bk → Coins Bk}

/-- A cell's own coins are not another row's. -/
theorem Cell.get_other (C : Cell Bk Φ V) (hC : RowAt Bk C.addr C.chain C.takes C.get C.put)
    (R : RowAt Bk o t d get put) (hne : C.addr ≠ o) (c : Cs d) (k : Coins Bk) :
    C.get (put c k) = C.get k := by
  have h1 := hC.self C.chain (Or.inl rfl) (put c k)
  have h2 := hC.self C.chain (Or.inl rfl) k
  rw [R.other c k C.chain C.addr hne, h2] at h1
  exact (eq_of_heq (Sigma.mk.inj h1).2).symm

/-- `runs` returns the same, whatever is set in o's row, over entries none of which is cut from it.
-/
theorem runs_other (R : RowAt Bk o t d get put) (ch : Nat) (E : List Ahead)
    (h : ∀ e ∈ E, e.owner ≠ o) (c : Cs d) (k : Coins Bk) :
    runs ((put c k).look ch) E = runs (k.look ch) E :=
  runs_congr _ _ E fun e he => by rw [R.other c k ch e.owner (h e he)]

/-- `runs` returns the same at two settings of o's row that have in common what these entries cut
from it, in a chain that sees o's row. -/
theorem runs_known (R : RowAt Bk o t d get put) (ch : Nat) (E : List Ahead) (c c' : Cs d)
    (h : ∀ e ∈ E, e.owner = o → (ch = t ∨ ch = 2) ∧
      c.cut e.start e.count = c'.cut e.start e.count) (k : Coins Bk) :
    runs ((put c k).look ch) E = runs ((put c' k).look ch) E :=
  runs_congr _ _ E fun e he => by
    by_cases ho : e.owner = o
    · rw [ho, R.set (h e he ho).1 c k, R.set (h e he ho).1 c' k]
      exact (h e he ho).2
    · rw [R.other c k ch e.owner ho, R.other c' k ch e.owner ho]

variable [Inhabited V]

/-- **A cell that is given no block of o's row** shows the same, whatever is in that row. -/
theorem Cell.shows_other (C : Cell Bk Φ V) (hC : RowAt Bk C.addr C.chain C.takes C.get C.put)
    (R : RowAt Bk o t d get put) (hne : C.addr ≠ o)
    (h : ∀ e ∈ Bk.ahead, e.spender = C.addr → e.owner ≠ o) (c : Cs d) (k : Coins Bk) (φ : Φ) :
    C.stage.shows (put c k) φ = C.stage.shows k φ := by
  have hE : ∀ P : Ahead → Bool, ∀ e ∈ (Bk.ahead.filter fun e => e.spender == C.addr).filter P,
      e.owner ≠ o := by
    intro P e he
    have h2 := List.mem_filter.1 (List.mem_filter.1 he).1
    exact h e h2.1 (beq_iff_eq.1 h2.2)
  show (if C.live φ = true then (C.out (some (C.get (put c k))) (C.spent (put c k))
      (C.carried (put c k)) φ).getD default else C.sub) =
    if C.live φ = true then (C.out (some (C.get k)) (C.spent k) (C.carried k) φ).getD default
      else C.sub
  have e1 : C.spent (put c k) = C.spent k := runs_other R C.chain _ (hE _) c k
  have e2 : C.carried (put c k) = C.carried k := runs_other R C.chain _ (hE _) c k
  rw [C.get_other hC R hne, e1, e2]

/-- **A cell that is given blocks of o's row** shows the same at two settings of the row that have
these blocks in common. -/
theorem Cell.shows_known (C : Cell Bk Φ V) (hC : RowAt Bk C.addr C.chain C.takes C.get C.put)
    (R : RowAt Bk o t d get put) (hne : C.addr ≠ o) (c c' : Cs d)
    (h : ∀ e ∈ Bk.ahead, e.spender = C.addr → e.owner = o → (C.chain = t ∨ C.chain = 2) ∧
      c.cut e.start e.count = c'.cut e.start e.count) (k : Coins Bk) (φ : Φ) :
    C.stage.shows (put c k) φ = C.stage.shows (put c' k) φ := by
  have hE : ∀ P : Ahead → Bool, ∀ e ∈ (Bk.ahead.filter fun e => e.spender == C.addr).filter P,
      e.owner = o → (C.chain = t ∨ C.chain = 2) ∧
        c.cut e.start e.count = c'.cut e.start e.count := by
    intro P e he
    have h2 := List.mem_filter.1 (List.mem_filter.1 he).1
    exact h e h2.1 (beq_iff_eq.1 h2.2)
  show (if C.live φ = true then (C.out (some (C.get (put c k))) (C.spent (put c k))
      (C.carried (put c k)) φ).getD default else C.sub) =
    if C.live φ = true then (C.out (some (C.get (put c' k))) (C.spent (put c' k))
      (C.carried (put c' k)) φ).getD default else C.sub
  have e1 : C.spent (put c k) = C.spent (put c' k) := runs_known R C.chain _ c c' (hE _) k
  have e2 : C.carried (put c k) = C.carried (put c' k) := runs_known R C.chain _ c c' (hE _) k
  rw [C.get_other hC R hne, C.get_other hC R hne c' k, e1, e2]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.cell_ker
#print axioms ProofFile.Honest.Cell.get_other
#print axioms ProofFile.Honest.runs_other
#print axioms ProofFile.Honest.runs_known
#print axioms ProofFile.Honest.Cell.shows_other
#print axioms ProofFile.Honest.Cell.shows_known
