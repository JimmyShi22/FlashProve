-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Items.lean: the rule over cells. A list of items, each a cell
(Honest/Law/Rule/Cell.lean) or a stage that draws nothing; what is asked of the list, as one
proposition (`RowOk`); and from it the main lemma, `row_law_abs`: over uniform coins, what the list
produces has the distribution of the kernels' fold. The proof has three steps, called L1, L2 and L3
(items 4 and 5 below). L1 is proved here. L2 is proved in the abstract in Honest/Law/Rule/Cell.lean
(`cell_ker`) and for an item that draws nothing in Honest/Law/Rule/Ker.lean (`kerAt_det`); here the
two are applied at every item. L3 is `real_eq_sim_of` (Honest/Law/Rule/Ker.lean), applied here. Φ
and V are type parameters: no description, no prover, no `Part` and no run of a protocol occurs
here; of the book's fields the statements name `ahead` alone, also through `spentE`, `ProverCoinCounts.spentBy`
and `ProverCoinCounts.knownBy`, which filter it; its three tables occur as the type `Coins Bk` of a run's coins,
and through `Coins.look` in `RowAt` (the field `row`).

  1  `Item`, `Item.stage`, `RowOk`   definitions
  2  `RowOk.before_front`, `RowOk.before_back`, `RowOk.self_free`, `mem_split`, `mem_front`,
     `RowOk.front_blind`   the list's order; the items before a cell do not read its row
  3  `step_nil`, `fresh_map`, `RowOk.owner_fresh`   one owner's condition, at its stage
  4  `RowOk.afresh`   L1: a cell's own coins and the blocks that it spends are as drawn afresh
     beside the pair (what has been produced before it, the blocks that it carries)
  5  `RowOk.ker`, `row_law_abs`   L2: the chain rule's hypothesis, at every item; L3: the main lemma

Limits.
  * `RowOk` is a definition, meant as a hypothesis; it is proved here of nothing.
  * `ord`, `L₀`, and in each cell `live`, `On` and `sub`, are free. At a cell whose `live` is false
    everywhere the fields `exact` and `here` ask nothing.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Cell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (Place)

variable {Bk : ProverCoinCounts} {Φ V : Type} [Inhabited V]

/-! ## 1 Definitions -/

/-- An item of a list: a stage that draws nothing, with the function that it shows; or a cell. -/
inductive Item (Bk : ProverCoinCounts) (Φ V : Type) where
  | det (s : Kit.Stage (Coins Bk) Φ V) (f : Φ → V)
  | cell (C : Cell Bk Φ V)

/- An item's stage: the stage that it holds; a cell's `Cell.stage`. -/
noncomputable def Item.stage : Item Bk Φ V → Kit.Stage (Coins Bk) Φ V
  | .det s _ => s
  | .cell C => C.stage

/-- **What is asked of a list of items.** `ord`: an order of places. `L₀`: what has been produced
before the list. -/
structure RowOk (ord : List Place) (items : List (Item Bk Φ V)) (L₀ : Φ) : Prop where
  /- an item `det`: its stage shows `f` whatever the coins, and its `tells` is
  `PMF.pure (some (f φ))` -/
  det : ∀ s f, Item.det s f ∈ items →
    (∀ k φ, s.shows k φ = f φ) ∧ ∀ φ, s.tells φ = PMF.pure (some (f φ))
  /- `get` and `put` are a lens on the cell's own row (`RowAt`, Honest/Law/Rule/LentAt.lean) -/
  row : ∀ C, Item.cell C ∈ items → RowAt Bk C.addr C.chain C.takes C.get C.put
  /-- the spender's condition -/
  exact : ∀ C, Item.cell C ∈ items → ∀ ca φ, C.live φ = true → C.On ca φ →
    (unif (Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named))).map
      (fun c => C.speaks c.1 c.2 ca φ) = (unif (Cs C.simTakes)).map (C.tell φ)
  /-- the owner's condition -/
  fresh : ∀ C, Item.cell C ∈ items → ∀ (p : Addr) sp ca φ,
    (unif (Cs C.takes)).map (fun c => (cutAll c (Bk.spentBy C.addr p), C.speaks c sp ca φ,
        cutAll c (Bk.knownBy ord C.addr p))) =
      (unif (CsAll ((Bk.spentBy C.addr p).map Ahead.named) × Cs C.takes)).map fun a =>
        (some a.1, C.speaks a.2 sp ca φ, cutAll a.2 (Bk.knownBy ord C.addr p))
  /-- the cells are in the order of their addresses -/
  order : items.Pairwise fun i j => ∀ C C', i = .cell C → j = .cell C' →
    C.addr.before ord C'.addr = true
  /-- the book: an owner is before its spender -/
  behind : ∀ e ∈ Bk.ahead, e.owner.before ord e.spender = true
  /-- the book: a spender's chain sees its owner's row -/
  vis : ∀ e ∈ Bk.ahead, ∀ Co Cb, Item.cell Co ∈ items → Item.cell Cb ∈ items →
    Co.addr = e.owner → Cb.addr = e.spender → Cb.chain = Co.chain ∨ Cb.chain = 2
  /-- the book: a block is within its owner's count -/
  within : ∀ e ∈ Bk.ahead, ∀ Co, Item.cell Co ∈ items → Co.addr = e.owner →
    e.start.f + e.count.f ≤ Co.takes.f ∧ e.start.e + e.count.e ≤ Co.takes.e
  /-- whoever owns a block that a cell spends is a cell -/
  owns : ∀ e ∈ Bk.ahead, e.once = true → ∀ Cb, Item.cell Cb ∈ items → Cb.addr = e.spender →
    ∃ Co, Item.cell Co ∈ items ∧ Co.addr = e.owner
  /-- at all coins at which the cell is called: its blocks are available, `On` holds of the blocks
  that it carries and of what has been produced before it, and it says something -/
  here : ∀ I₁ C I₂, items = I₁ ++ Item.cell C :: I₂ → ∀ k,
    C.live (Kit.real (I₁.map Item.stage) k L₀) = true → ∃ sp ca v, C.spent k = some sp ∧
      C.carried k = some ca ∧ C.On ca (Kit.real (I₁.map Item.stage) k L₀) ∧
      C.speaks (C.get k) sp ca (Kit.real (I₁.map Item.stage) k L₀) = some v

/-! ## 2 The list's order -/

section
variable {ord : List Place} {items : List (Item Bk Φ V)} {L₀ : Φ}

theorem RowOk.before_front (h : RowOk ord items L₀) {I₁ I₂ : List (Item Bk Φ V)}
    {C Cb : Cell Bk Φ V} (hi : items = I₁ ++ Item.cell C :: I₂) (hb : Item.cell Cb ∈ I₁) :
    Cb.addr.before ord C.addr = true := by
  have ho := h.order
  rw [hi] at ho
  exact (List.pairwise_append.1 ho).2.2 _ hb _ (List.mem_cons.2 (Or.inl rfl)) Cb C rfl rfl

theorem RowOk.before_back (h : RowOk ord items L₀) {I₁ I₂ : List (Item Bk Φ V)}
    {C Cb : Cell Bk Φ V} (hi : items = I₁ ++ Item.cell C :: I₂) (hb : Item.cell Cb ∈ I₂) :
    C.addr.before ord Cb.addr = true := by
  have ho := h.order
  rw [hi] at ho
  exact (List.pairwise_cons.1 (List.pairwise_append.1 ho).2.1).1 _ hb C Cb rfl rfl

/-- No entry of the book gives an address a block of its own row. -/
theorem RowOk.self_free (h : RowOk ord items L₀) (a : Addr) :
    ∀ e ∈ Bk.ahead, e.spender = a → e.owner ≠ a := by
  intro e he hs ho
  have hb := h.behind e he
  rw [hs, ho, Addr.before_irrefl] at hb
  cases hb

theorem mem_split {α : Type} {l I₁ I₂ : List α} {x : α} (hi : l = I₁ ++ x :: I₂) : x ∈ l := by
  rw [hi]
  exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))

theorem mem_front {α : Type} {l I₁ I₂ : List α} {x y : α} (hi : l = I₁ ++ x :: I₂) (hy : y ∈ I₁) :
    y ∈ l := by
  rw [hi]
  exact List.mem_append.2 (Or.inl hy)

/-- **The items before a cell do not read its row.** -/
theorem RowOk.front_blind (h : RowOk ord items L₀) {I₁ I₂ : List (Item Bk Φ V)}
    {C : Cell Bk Φ V} (hi : items = I₁ ++ Item.cell C :: I₂) :
    ∀ s ∈ I₁.map Item.stage, ∀ c k φ, s.shows (C.put c k) φ = s.shows k φ := by
  intro s hs c k φ
  obtain ⟨i, hiI, rfl⟩ := List.mem_map.1 hs
  cases i with
  | det s f =>
    have hd := (h.det s f (mem_front hi hiI)).1
    show s.shows (C.put c k) φ = s.shows k φ
    rw [hd, hd]
  | cell Cb =>
    have hbf := h.before_front hi hiI
    refine Cb.shows_other (h.row Cb (mem_front hi hiI)) (h.row C (mem_split hi)) ?_ ?_ c k φ
    · intro e
      rw [e, Addr.before_irrefl] at hbf
      cases hbf
    · intro e he hs' ho
      have hb := h.behind e he
      rw [hs', ho, Addr.before_asymm ord hbf] at hb
      cases hb

/-! ## 3 One owner's condition, at its stage -/

/-- An owner of whom nothing is spent. -/
theorem step_nil {K Ω : Type} [Fintype K] [Nonempty K] (cs : K → (d : Due) × Cs d) (W : K → Ω) :
    ∀ es : List Ahead, es = [] →
    (unif K).map (fun k => (cutAll (cs k).2 es, W k)) =
      (unif (CsAll (es.map Ahead.named) × K)).map fun z => (some z.1, W z.2) := by
  intro es h
  subst h
  exact afresh_sub (U := CsAll (([] : List Ahead).map Ahead.named)) () (fun _ => rfl) W

/-- The owner's condition, carried along a function of what is said. -/
theorem fresh_map {d : Due} {es known : List Ahead} {U U' : Type} {say : Cs d → U}
    (h : (unif (Cs d)).map (fun c => (cutAll c es, say c, cutAll c known)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun a =>
        (some a.1, say a.2, cutAll a.2 known)) (G : U → U') :
    (unif (Cs d)).map (fun c => (cutAll c es, G (say c), cutAll c known)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun a =>
        (some a.1, G (say a.2), cutAll a.2 known) := by
  have h' := congrArg (PMF.map fun y : Option (CsAll (es.map Ahead.named)) × U ×
    Option (CsAll (known.map Ahead.named)) => (y.1, G y.2.1, y.2.2)) h
  rw [PMF.map_comp, PMF.map_comp] at h'
  exact h'

/-- **`RowOk.fresh`, carried from `speaks` to the cell's stage**, at the owner's own row set anew.
-/
theorem RowOk.owner_fresh (h : RowOk ord items L₀) (Co : Cell Bk Φ V)
    (hCo : Item.cell Co ∈ items) (p : Addr) (k : Coins Bk) (φ : Φ) :
    (unif (Cs Co.takes)).map (fun c => (cutAll c (Bk.spentBy Co.addr p),
        Co.stage.shows (Co.put c k) φ, cutAll c (Bk.knownBy ord Co.addr p))) =
      (unif (CsAll ((Bk.spentBy Co.addr p).map Ahead.named) × Cs Co.takes)).map fun z =>
        (some z.1, Co.stage.shows (Co.put z.2 k) φ, cutAll z.2 (Bk.knownBy ord Co.addr p)) := by
  have hR := h.row Co hCo
  have hE : ∀ P : Ahead → Bool, ∀ e ∈ (Bk.ahead.filter fun e => e.spender == Co.addr).filter P,
      e.owner ≠ Co.addr := by
    intro P e he
    have h2 := List.mem_filter.1 (List.mem_filter.1 he).1
    exact h.self_free Co.addr e h2.1 (beq_iff_eq.1 h2.2)
  have hs : ∀ c, Co.stage.shows (Co.put c k) φ = if Co.live φ = true then
      (Co.out (some c) (Co.spent k) (Co.carried k) φ).getD default else Co.sub := by
    intro c
    show (if Co.live φ = true then (Co.out (some (Co.get (Co.put c k))) (Co.spent (Co.put c k))
      (Co.carried (Co.put c k)) φ).getD default else Co.sub) = _
    have e1 : Co.spent (Co.put c k) = Co.spent k := runs_other hR Co.chain _ (hE _) c k
    have e2 : Co.carried (Co.put c k) = Co.carried k := runs_other hR Co.chain _ (hE _) c k
    rw [hR.ok.tst_set, e1, e2]
  obtain ⟨sp, ca, G, hG⟩ : ∃ sp ca, ∃ G : Option V → V, ∀ c,
      Co.stage.shows (Co.put c k) φ = G (Co.speaks c sp ca φ) := by
    by_cases hl : Co.live φ = true
    · cases h1 : Co.spent k with
      | none =>
        exact ⟨Classical.arbitrary _, Classical.arbitrary _, fun _ => default, fun c => by
          rw [hs, if_pos hl, h1]
          rfl⟩
      | some sp =>
        cases h2 : Co.carried k with
        | none =>
          exact ⟨Classical.arbitrary _, Classical.arbitrary _, fun _ => default, fun c => by
            rw [hs, if_pos hl, h1, h2]
            rfl⟩
        | some ca =>
          exact ⟨sp, ca, fun y => y.getD default, fun c => by
            rw [hs, if_pos hl, h1, h2]
            rfl⟩
    · exact ⟨Classical.arbitrary _, Classical.arbitrary _, fun _ => Co.sub, fun c => by
        rw [hs, if_neg hl]⟩
  simp only [hG]
  exact fresh_map (h.fresh Co hCo p sp ca φ) G

/-! ## 4 Step L1 -/

/-- **Step L1.** A cell's own coins and the blocks that it spends are as drawn afresh beside what
has been produced before it and the blocks that it carries. -/
theorem RowOk.afresh (h : RowOk ord items L₀) {I₁ I₂ : List (Item Bk Φ V)} {C : Cell Bk Φ V}
    (hi : items = I₁ ++ Item.cell C :: I₂) :
    (unif (Coins Bk)).map (fun k =>
        ((some (C.get k), C.spent k), (Kit.real (I₁.map Item.stage) k L₀, C.carried k))) =
      (unif ((Cs C.takes × CsAll ((spentE Bk C.addr).map Ahead.named)) × Coins Bk)).map fun z =>
        ((some z.1.1, some z.1.2), (Kit.real (I₁.map Item.stage) z.2 L₀, C.carried z.2)) := by
  have hC := mem_split hi
  have hR := h.row C hC
  have hE : ∀ P : Ahead → Bool, ∀ e ∈ (Bk.ahead.filter fun e => e.spender == C.addr).filter P,
      e.owner ≠ C.addr := by
    intro P e he
    have h2 := List.mem_filter.1 (List.mem_filter.1 he).1
    exact h.self_free C.addr e h2.1 (beq_iff_eq.1 h2.2)
  refine lent_afresh_abs hR.ok (fun k => k.look C.chain) (spentE Bk C.addr)
    (fun o => Bk.spentBy o C.addr) (fun o => Or.inr ?_)
    (fun k => (Kit.real (I₁.map Item.stage) k L₀, C.carried k)) (fun c k => ?_)
    (fun c k => runs_other hR C.chain _ (hE _) c k) (fun o rest hrest => ?_)
  · unfold spentE ProverCoinCounts.spentBy
    rw [List.filter_filter, List.filter_filter]
    refine List.filter_congr fun e _ => ?_
    cases (e.owner == o) <;> cases (e.spender == C.addr) <;> cases e.once <;> rfl
  · exact Prod.ext (Kit.real_congr _ _ _ (fun s hs L => h.front_blind hi s hs c k L) L₀)
      (runs_other hR C.chain _ (hE _) c k)
  · by_cases hsp : Bk.spentBy o C.addr = []
    · exact step_nil (fun k : Coins Bk => k.look C.chain o) _ _ hsp
    · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hsp
      obtain ⟨hea, hec⟩ := List.mem_filter.1 he
      simp only [Bool.and_eq_true, beq_iff_eq] at hec
      obtain ⟨⟨eo, es⟩, eonce⟩ := hec
      obtain ⟨Co, hCo, hoa⟩ := h.owns e hea eonce C hC es.symm
      have hao : Co.addr = o := hoa.trans eo
      subst hao
      have hbef : Co.addr.before ord C.addr = true := by
        have := h.behind e hea
        rw [eo, es] at this
        exact this
      -- the owner comes before
      have hI₁ : Item.cell Co ∈ I₁ := by
        have hm := hCo
        rw [hi] at hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hm
        · rcases List.mem_cons.1 hm with hm | hm
          · have e' : Co = C := Item.cell.inj hm
            rw [e', Addr.before_irrefl] at hbef
            cases hbef
          · have hb := h.before_back hi hm
            rw [Addr.before_asymm ord hbef] at hb
            cases hb
      obtain ⟨J₁, J₂, hJ⟩ := List.append_of_mem hI₁
      have hi' : items = J₁ ++ Item.cell Co :: (J₂ ++ Item.cell C :: I₂) := by
        rw [hi, hJ, List.append_assoc]
        rfl
      have hRo := h.row Co hCo
      have hin : ∀ e' ∈ Bk.knownBy ord Co.addr C.addr,
          e'.start.f + e'.count.f ≤ Co.takes.f ∧ e'.start.e + e'.count.e ≤ Co.takes.e := by
        intro e' he'
        obtain ⟨h1, h2⟩ := List.mem_filter.1 he'
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        exact h.within e' h1 Co hCo h2.1.1.symm
      have hstage : I₁.map Item.stage =
          J₁.map Item.stage ++ Co.stage :: J₂.map Item.stage := by
        rw [hJ, List.map_append]
        rfl
      rw [hstage]
      refine owner_step hRo.ok (fun k => k.look C.chain) Co.addr
        (fun k => hRo.self C.chain (h.vis e hea Co C hCo hC eo.symm es.symm) k)
        (fun x k b hb => hRo.other x k C.chain b hb) (J₁.map Item.stage) (J₂.map Item.stage)
        Co.stage L₀ (Bk.spentBy Co.addr C.addr) (Bk.knownBy ord Co.addr C.addr)
        (h.front_blind hi') ?_ C.carried ?_ (fun k => h.owner_fresh Co hCo C.addr k _) rest hrest
      · -- the items between the owner and the spender
        intro s hs k c c' L hcc
        obtain ⟨i, hiJ, rfl⟩ := List.mem_map.1 hs
        have hiI : i ∈ I₁ := by
          rw [hJ]
          exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ hiJ))
        cases i with
        | det s f =>
          have hd := (h.det s f (mem_front hi hiI)).1
          show s.shows (Co.put c k) L = s.shows (Co.put c' k) L
          rw [hd, hd]
        | cell Cb =>
          have hb1 : Co.addr.before ord Cb.addr = true :=
            h.before_back hi' (List.mem_append.2 (Or.inl hiJ))
          have hb2 : Cb.addr.before ord C.addr = true := h.before_front hi hiI
          have hCb := mem_front hi hiI
          refine Cb.shows_known (h.row Cb hCb) hRo ?_ c c' ?_ k L
          · intro e'
            rw [e', Addr.before_irrefl] at hb1
            cases hb1
          · intro e' he' hs' ho'
            refine ⟨h.vis e' he' Co Cb hCo hCb ho'.symm hs'.symm, ?_⟩
            refine cutAll_cuts c c' _ hin hcc e' (List.mem_filter.2 ⟨he', ?_⟩)
            have hne : (e'.spender == C.addr) = false := by
              rw [hs']
              cases hq : Cb.addr == C.addr with
              | false => rfl
              | true =>
                rw [beq_iff_eq.1 hq, Addr.before_irrefl] at hb2
                cases hb2
            rw [ho', hne, hs', hb2]
            simp
      · -- the blocks that the spender carries
        intro k c c' hcc
        refine runs_known hRo C.chain _ c c' ?_ k
        intro e' he' ho'
        obtain ⟨h1, h2⟩ := List.mem_filter.1 he'
        obtain ⟨h3, h4⟩ := List.mem_filter.1 h1
        have hs' : e'.spender = C.addr := beq_iff_eq.1 h4
        refine ⟨h.vis e' h3 Co C hCo hC ho'.symm hs'.symm, ?_⟩
        refine cutAll_cuts c c' _ hin hcc e' (List.mem_filter.2 ⟨h3, ?_⟩)
        have honce : e'.once = false := by
          cases hq : e'.once with
          | false => rfl
          | true =>
            rw [hq] at h2
            cases h2
        rw [ho', hs', honce]
        simp

/-! ## 5 Step L2 at every item; step L3 -/

theorem RowOk.ker (h : RowOk ord items L₀) : ∀ (I₂ I₁ : List (Item Bk Φ V)), items = I₁ ++ I₂ →
    Kit.Ker L₀ (I₁.map Item.stage) (I₂.map Item.stage)
  | [], _, _ => trivial
  | i :: I₂, I₁, hi => by
    show Kit.KerAt L₀ (I₁.map Item.stage) i.stage ∧
      Kit.Ker L₀ (I₁.map Item.stage ++ [i.stage]) (I₂.map Item.stage)
    refine ⟨?_, ?_⟩
    · cases i with
      | det s f =>
        have hd := h.det s f (mem_split hi)
        exact Kit.kerAt_det L₀ _ s f hd.1 hd.2
      | cell C => exact cell_ker C L₀ _ (h.afresh hi) (h.exact C (mem_split hi)) (h.here I₁ C I₂ hi)
    · have ih := RowOk.ker h I₂ (I₁ ++ [i]) (by rw [hi, List.append_assoc]; rfl)
      rw [List.map_append] at ih
      exact ih

/-- **The rule over cells.** Over uniform coins, what the list produces has the distribution of the
kernels' fold. -/
theorem row_law_abs (h : RowOk ord items L₀) :
    (unif (Coins Bk)).map (fun k => some (Kit.real (items.map Item.stage) k L₀)) =
      Kit.sim (items.map Item.stage) L₀ :=
  Kit.real_eq_sim_of _ _ (h.ker items [] rfl)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.RowOk.before_front
#print axioms ProofFile.Honest.RowOk.before_back
#print axioms ProofFile.Honest.RowOk.self_free
#print axioms ProofFile.Honest.mem_split
#print axioms ProofFile.Honest.mem_front
#print axioms ProofFile.Honest.RowOk.front_blind
#print axioms ProofFile.Honest.step_nil
#print axioms ProofFile.Honest.fresh_map
#print axioms ProofFile.Honest.RowOk.owner_fresh
#print axioms ProofFile.Honest.RowOk.afresh
#print axioms ProofFile.Honest.RowOk.ker
#print axioms ProofFile.Honest.row_law_abs
