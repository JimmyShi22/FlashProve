-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/SizedAtStand.lean: THE OPEN LEDGER FROM THE FRONT OF A SEGMENT's FIRST LOOKUP UP TO THE FRONT OF ITS
BATCHING, AT EVERY STATE THAT THE FIRST CHAIN's OWN SUB-PROTOCOLS REACH: it has its sizes (its three arrays on slots have an
entry a slot: `PscRun.Sized`), and of two states of one run the later one's ledger is a later state of the earlier one's
(`PscRun.Later`: no slot is given back; what is filled stays filled, with its value and factor). So the premise `sized` of
`accepted_bat_at_head` (Honest/K9/BatAtHead.lean) is paid, and no kind walks this stretch a second time.

"TWO STATES OF ONE RUN" is said as the library says it (`Meaning.K2.open_between`, Johnson/IMR/WalkGivesAt.lean): two folds over two
front stretches of the chain's list, from one first state, over the same words.

  `ix_facts`              the three numbers of a segment: where its two lookups stand among its sub-protocols, and how many
                         stand in front of its batching
  `kind_behind`, `block_carries`   from the first lookup on, each sub-protocol in front of the batching carries the ledger on: the
                         library's `hear_steps` (Johnson/Desc/First/Look/K03RowsBare.lean), at all 25 segments
  `fold_front`            a fold over a front stretch holds a fold over each shorter one
  **`carried_between`**   of two states of one run in that stretch: what the first lookup returned stands, and a ledger with its
                         sizes goes on to a later one with its sizes
  `sized_first`           in front of the first lookup a ledger is open, with its sizes
  **`sized_at_fold`**, **`later_between`**   the two facts, at folds
  **`sized_reached`**     under the library's hypothesis, at "reached", at each border of the stretch
  **`sized_at_batching`**, `sized_of_front`, `sized_at_thr`   in front of the batching: at "reached", at `Front` (Honest/K9/ReadyOf.lean), at the
                         thread's invariant
  **`sized_of_stand`**    the premise `sized`, to the letter

Limits. On the sub-protocols' decisions alone: nothing on the runs of claims inside the batching. Laws from a yes: nothing says
that any state is reached. The full size and the hash function `secondHashFunction` alone. This file proves no property of a prover or a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.ReadyOf
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Desc.AtSeats.RowsBareWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open Johnson.Desc.First.Walk.Tied (Reach reach_fold reach_of_fold fold_split)

/-! ## The numbers and the kinds -/

/-- A segment's three numbers. -/
theorem ix_facts (l : ℕ) :
    (l = 24 ∧ IM.k3Ix l false = 2 ∧ IM.k3Ix l true = 7 ∧ IM.nAt l = 9) ∨
      (l ≠ 24 ∧ IM.k3Ix l false = 1 ∧ IM.k3Ix l true = 6 ∧ IM.nAt l = 7) := by
  by_cases h : l = 24
  · subst h
    exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨h, by simp [IM.k3Ix, h], by simp [IM.k3Ix, h], by simp [IM.nAt, h]⟩

/-- From the first lookup on, the kinds in front of a batching are of the seven that carry the ledger on. -/
theorem kind_behind {l i : ℕ} (h1 : IM.k3Ix l false ≤ i) {k : KindName}
    (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some k) : k ∈ Desc.K9.behindKinds := by
  rcases ix_facts l with ⟨rfl, a, -, -⟩ | ⟨h24, a, -, -⟩
  · have e : IM.subAt 24 = .head := by
      unfold IM.subAt
      rw [if_pos rfl]
    rw [e] at hk
    have hall : ((kindsBeforeBatching .head ((24 : ℕ) == 0)).drop 2).all
        (fun k => decide (k ∈ Desc.K9.behindKinds)) = true := by decide
    have hm : k ∈ (kindsBeforeBatching .head ((24 : ℕ) == 0)).drop 2 := by
      refine List.mem_of_getElem? (i := i - 2) ?_
      rw [List.getElem?_drop, show 2 + (i - 2) = i by omega]
      exact hk
    exact of_decide_eq_true (List.all_eq_true.1 hall k hm)
  · have hs : IM.subAt l ≠ .head := by
      unfold IM.subAt
      rw [if_neg h24]
      split <;> simp
    exact OnPublicFiles.kindsBehind1 _ hs _ _ _ (by omega) hk

/-- A fold over a front stretch of a list holds a fold over each shorter front stretch, over the same words. -/
theorem fold_front {Cl : Type} (L : List (Block S Cl)) {k k' : ℕ} (hkk : k ≤ k') {ft : ℕ} {s₀ : S}
    {R : List Fmt.RoundView} {C : List Desc.OpenedColumn} {out : S × List Fmt.RoundView × List Desc.OpenedColumn}
    (h : foldBlocks ft (L.take k') s₀ R C = .ok out) :
    ∃ v R₁ C₁, foldBlocks ft (L.take k) s₀ R C = .ok (v, R₁, C₁) := by
  have e : L.take k ++ (L.take k').drop k = L.take k' := by
    have z := List.take_append_drop k (L.take k')
    rwa [List.take_take, Nat.min_eq_left hkk] at z
  rw [← e] at h
  obtain ⟨t, r, c, h1, -⟩ := fold_split ft _ _ _ _ _ _ h
  exact ⟨t, r, c, h1⟩

/-! ## In the goals' scope, at an opening of the description -/

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Each sub-protocol from the first lookup up to the batching carries the ledger on. -/
theorem block_carries (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l i : ℕ} (hl : l < 25) (h1 : IM.k3Ix l false ≤ i) (h2 : i < IM.nAt l) :
    ∃ b, c.blocksInOrder[14 * l + i + 2]? = some b ∧ b.Steps (Desc.K9.CF S.lookHeard?) := by
  have hlen : i < (kindsBeforeBatching (IM.subAt l) (l == 0)).length := by
    rw [IM.hear_len_at]
    unfold IM.nAt at h2
    exact h2
  have hk := List.getElem?_eq_getElem hlen
  have hi : 1 ≤ i := by
    rcases ix_facts l with ⟨-, a, -, -⟩ | ⟨-, a, -, -⟩ <;> omega
  exact OnPublicFiles.hear_steps hS hR O hOk l hl i _ hk (kind_behind h1 hk) hi

/-- **Of two states of one run, from the front of the first lookup up to the front of the batching.** -/
theorem carried_between (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {s₀ : S} {R : List Fmt.RoundView} {C : List Desc.OpenedColumn} {k : ℕ}
    (h1 : 14 * l + IM.k3Ix l false + 2 ≤ k) {v : S} {R₁ : List Fmt.RoundView} {C₁ : List Desc.OpenedColumn}
    (hv : foldBlocks 0 (c.blocksInOrder.take k) s₀ R C = .ok (v, R₁, C₁)) :
    ∀ (n : ℕ), k + n ≤ 14 * l + IM.nAt l + 2 → ∀ {t : S} {R₂ : List Fmt.RoundView} {C₂ : List Desc.OpenedColumn},
      foldBlocks 0 (c.blocksInOrder.take (k + n)) s₀ R C = .ok (t, R₂, C₂) → Desc.K9.CF S.lookHeard? v t
  | 0, _, t, R₂, C₂, ht => by
    rw [Nat.add_zero, hv] at ht
    obtain rfl : v = t := congrArg Prod.fst (Except.ok.inj ht)
    exact (Desc.K9.preCF _).refl v
  | n + 1, h2, t, R₂, C₂, ht => by
    obtain ⟨i, hi⟩ : ∃ i, k + n = 14 * l + i + 2 := ⟨k + n - (14 * l + 2), by omega⟩
    obtain ⟨b, hb, st⟩ := block_carries hS hR O hOk (i := i) hl (by omega) (by omega)
    rw [← hi] at hb
    obtain ⟨s, R₃, C₃, rs, gs, hf, hd⟩ := OnPublicFiles.foldCut c.blocksInOrder (k + n) b hb ht
    exact (Desc.K9.preCF _).trans _ _ _
      (carried_between hS hR O hOk hl h1 hv n (by omega) hf) (st s rs gs t hd)

/-- In front of the first lookup a ledger is open, with its sizes. -/
theorem sized_first (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take (14 * l + IM.k3Ix l false + 2)) s₀ R C = .ok (t, R', C')) :
    OnPublicFiles.SizedAt t := by
  rcases ix_facts l with ⟨rfl, a, -, -⟩ | ⟨h24, a, -, -⟩
  · rw [a, show 14 * 24 + 2 + 2 = 339 + 1 from rfl] at h
    have hlen : c.blocksInOrder.length = 358 := Meaning.K2.flat_358 hS O
    exact K1.sized_340 hS hR O ((), t)
      (reach_of_fold (start := fun _ : Unit => s₀) (z := ()) (339 + 1) (by omega) t R R' C C' h)
  · rw [a, show 14 * l + 1 + 2 = 14 * l + 2 + 1 by omega] at h
    exact OnPublicFiles.opened_sized hS hR O l (by omega) h

/-- **At each border of the stretch a ledger is open, with its sizes.** -/
theorem sized_at_fold (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {k : ℕ} (h1 : 14 * l + IM.k3Ix l false + 2 ≤ k)
    (h2 : k ≤ 14 * l + IM.nAt l + 2) {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take k) s₀ R C = .ok (t, R', C')) : OnPublicFiles.SizedAt t := by
  obtain ⟨v, R₁, C₁, hv⟩ := fold_front c.blocksInOrder h1 h
  obtain ⟨G, hG, hz⟩ := sized_first hS hR O hl hv
  obtain ⟨n, rfl⟩ : ∃ n, k = 14 * l + IM.k3Ix l false + 2 + n :=
    ⟨k - (14 * l + IM.k3Ix l false + 2), by omega⟩
  obtain ⟨G', h', -, hz'⟩ := (carried_between hS hR O hOk hl (Nat.le_refl _) hv n h2 h).2 G hG hz
  exact ⟨G', h', hz'⟩

/-- **Of two states of one run in the stretch the later one's ledger is a later state of the earlier one's.** -/
theorem later_between (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {k k' : ℕ} (h1 : 14 * l + IM.k3Ix l false + 2 ≤ k) (hkk : k ≤ k')
    (h2 : k' ≤ 14 * l + IM.nAt l + 2) {s₀ v t : S} {R R₁ R₂ : List Fmt.RoundView} {C C₁ C₂ : List Desc.OpenedColumn}
    (hv : foldBlocks 0 (c.blocksInOrder.take k) s₀ R C = .ok (v, R₁, C₁))
    (ht : foldBlocks 0 (c.blocksInOrder.take k') s₀ R C = .ok (t, R₂, C₂)) {G : Fork} (hG : v.fork? = some G) :
    PscRun.Sized G ∧ ∃ G', t.fork? = some G' ∧ PscRun.Later G G' := by
  obtain ⟨G₀, hG₀, hz⟩ := sized_at_fold hS hR O hOk hl h1 (by omega) hv
  obtain rfl : G₀ = G := Option.some.inj (hG₀.symm.trans hG)
  obtain ⟨n, rfl⟩ : ∃ n, k' = k + n := ⟨k' - k, by omega⟩
  obtain ⟨G', h', ⟨a1, a2, a3⟩, hz'⟩ := (carried_between hS hR O hOk hl h1 hv n h2 ht).2 G₀ hG hz
  exact ⟨hz, G', h', ⟨a1, a2, fun _ => hz', a3⟩⟩

end

/-! ## Under the library's hypothesis -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At every reached state, at each border from the front of the first lookup up to the front of the batching.** -/
theorem sized_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {k : ℕ}
    (h1 : 14 * l + IM.k3Ix l false + 2 ≤ k) (h2 : k ≤ 14 * l + IM.nAt l + 2) {z : ProofFile.InstPub} {s : S}
    (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s)) : ∀ F, s.fork? = some F → PscRun.Sized F := by
  intro F hF
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := reach_fold.1 hz
  obtain ⟨G, hG, hs⟩ := sized_at_fold h.scope h.reads O h.laid.planOk hl h1 h2 f
  obtain rfl : G = F := Option.some.inj (hG.symm.trans hF)
  exact hs

/-- **At every state that is reached in front of a batching.** -/
theorem sized_at_batching (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S} (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 2) (z, s)) :
    ∀ F, s.fork? = some F → PscRun.Sized F :=
  sized_reached h hl (by rcases ix_facts l with ⟨-, a, -, b⟩ | ⟨-, a, -, b⟩ <;> omega) (Nat.le_refl _) hz

/-- At a state that stands in front of a batching. -/
theorem sized_of_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {s : S}
    (hS : Front cF Zp l s) : ∀ F, s.fork? = some F → PscRun.Sized F := by
  obtain ⟨z, hz⟩ := hS.reach
  exact sized_at_batching h hl hz

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)

/-- Where the thread's invariant holds in front of a batching. -/
theorem sized_at_thr {l : ℕ} (hl : l < 25) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread
      (14 * l + IM.nAt l + 2) k s μ En) : ∀ F, s.fork? = some F → PscRun.Sized F :=
  sized_of_front h hl (front_of_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ hl hT)

/-- **The premise `sized` of `accepted_bat_at_head`, to the letter.** -/
theorem sized_of_stand {l : ℕ} (hl : l < 25)
    {Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} :
    ∀ s tr a, StandAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said
      (14 * l + IM.nAt l + 2) K8.k8Front s tr a → ∀ F, s.fork? = some F → PscRun.Sized F := by
  rintro s tr a ⟨⟨κ, m, En, hT⟩, -, -⟩
  exact sized_at_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ hl hT.1

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.ix_facts
#print axioms ProofFile.Honest.K9.kind_behind
#print axioms ProofFile.Honest.K9.fold_front
#print axioms ProofFile.Honest.K9.block_carries
#print axioms ProofFile.Honest.K9.carried_between
#print axioms ProofFile.Honest.K9.sized_first
#print axioms ProofFile.Honest.K9.sized_at_fold
#print axioms ProofFile.Honest.K9.later_between
#print axioms ProofFile.Honest.K9.sized_reached
#print axioms ProofFile.Honest.K9.sized_at_batching
#print axioms ProofFile.Honest.K9.sized_of_front
#print axioms ProofFile.Honest.K9.sized_at_thr
#print axioms ProofFile.Honest.K9.sized_of_stand
