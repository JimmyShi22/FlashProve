-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/OneCallCostR.lean: counts for the rounds and the chains of the compiled prover, and
that, for a weight with `TryW` and under `RuleSh`, they bound the weights of its queries on every
path; at ca = 1, bff i = nbf i + 1 they are the counts of Compile/Batch/SpecOneCall.lean. (Words of
this library: lean/GLOSSARY.md.)

It is the counterpart of Part 3 of Compile/Batch/NeedCostP.lean (the rounds; its lemmas on the
chains are not in this library) for `SWV`, for every weight that meets `TryW W nb m wt ca bf`. `SWV`
(Compile/CostV.lean) says: on every path the weights of the queries, each at its own answer, add up
to at most n, and the result has the property P. `TryW` (Compile/Batch/OneCallCostW.lean) asks:
`Std m`; never more than the rule asks for; a failed attempt that is not the last weighs at most ca,
any Fiat-Shamir query of round i at most bf t i (with proof-of-work bits: if the table marks a block
there).

  `cSlotW`, `cSharedW`, `cProve1W`, `cPUW`, `cCBW`
      the counts: "moreOf g · ca + bff i" for a Fiat-Shamir query, where the table's counts (not in
      this library; told in the head of Compile/Batch/NeedCostP.lean, Part 1; one search: `swa_fbG`
      there) have "triesOf g · (nb t i + 1)"; trees, g and the request tree as there
  `swv_of`   under `TryW`: a part that is bounded, in `SWA`, for the table that marks every block is
             bounded here. So the trees and the request trees are taken over as they are
  `RuleSh`   the hypothesis of the lemmas on a chain, for the rounds that are left: their wire
             record is well-formed (`RoundsQueryLayout.OKG`); the embedding embP of their plain parts preserves
             `tryInfo` (so the rule reads each search's own check off its query); in a round with a
             proof-of-work record the table marks a block
  `swv_chainTU`   under `TryW`, `RuleSh`: all chains of a batch with no query for an empty slot:
                  cSharedW + (slots with a request) · cSlotW; and what they return: the slots that
                  hold a request at the end are those of the start
  `swv_chainT`   all chains of a batch in which every slot works

Notation:
  `.sh`, `.lo`: a round is called shared (sh) or local (lo) after its verifier message (`Kind`,
    Iop/Batch.lean)
  `PhK` (`.first`, `.loc`, `.shr`, `.aft`): where the chains are (before the first local round;
    local rounds; shared rounds; local rounds afterwards), without tokens
    (Compile/Batch/NeedCostP.lean)
  `costJ w`, `cost0 w`: what the tree over a slot's component, and over the shared component, of the
    round costs (Compile/Batch/NeedCostP.lean); `tr d`: the leaves and the inner nodes of a tree of
    depth d (Compile/Batch/NeedCostTree.lean)
  `w.grJ`, `w.gr0`: the proof-of-work record (`GrW`), if any, of the Fiat-Shamir query of a slot in
    a local round, and of a shared round (`WireRB`, Iop/BatchWire.lean); `moreOf`: at most this many
    attempts after the first (Compile/Batch/Counts.lean)
  in `cSlotW`, "+ 1 + 1": in the joining round its query to g, its leaf of the request tree; in
    `cSharedW`, "Ns - 1": the Ns − 1 inner nodes of the request tree (the head of
    Compile/Batch/NeedCostP.lean)
  `.test`, `.link`, `.onl`: the `Tag` (Compile/Oracles.lean) of Test, Link and Batch; `L.maxBatchSize`: the
    number of slots (`BatchProtocol`, Iop/Batch.lean); the number of copies is `p.M` + 1 (`Params`,
    Compile/Star.lean)
Limits: what the header of Compile/Batch/NeedCostP.lean lists. Worst case over the oracle.
-/
import Compile.Batch.OneCallCostL

noncomputable section

namespace Compile.Batch
namespace OneCall
open Iop Rom ZKCP
open Compile.CostP (SWV SWA)
open Compile.Batch.Need (Std needOf PhK phK phK_afterLo costJ cost0 tr full full_hear map_full_hear)

/-! ## The counts -/

section Counts
variable {lam K : ℕ}

/-- one slot with a request, from round i on. A Fiat-Shamir query of round i is counted with moreOf
g · a + bff i: with a proof-of-work record, a for each attempt but the one with which the search
ends, and bff i for that one; without one (moreOf = 0) bff i for its one query -/
def cSlotW (a : ℕ) (bff : ℕ → ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → PhK → ℕ
  | [], _, _, _, _ => 0
  | _ :: s, (an, A), (w, W), i, ph =>
      match an.kind, ph with
      | .lo, ph => (costJ w + (moreOf w.grJ * a + bff i)) + cSlotW a bff s A W (i + 1) ph.afterLo
      | .sh, .loc => (costJ w + 1 + 1) + cSlotW a bff s A W (i + 1) .shr
      | .sh, ph => cSlotW a bff s A W (i + 1) ph

/-- the shared part, for Ns slots -/
def cSharedW (a : ℕ) (bff : ℕ → ℕ) (Ns : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → PhK → ℕ
  | [], _, _, _, _ => 0
  | _ :: s, (an, A), (w, W), i, ph =>
      match an.kind, ph with
      | .lo, ph => cSharedW a bff Ns s A W (i + 1) ph.afterLo
      | .sh, .loc => ((Ns - 1) + cost0 w + (moreOf w.gr0 * a + bff i)) + cSharedW a bff Ns s A W (i + 1) .shr
      | .sh, .shr => (cost0 w + (moreOf w.gr0 * a + bff i)) + cSharedW a bff Ns s A W (i + 1) .shr
      | .sh, ph => cSharedW a bff Ns s A W (i + 1) ph

/-- one execution with one slot, which holds a request -/
def cProve1W (a : ℕ) (bff : ℕ → ℕ) {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) : ℕ :=
  cSharedW a bff 1 Q.loc.shape Q.ann wq.sh 0 .first + cSlotW a bff Q.loc.shape Q.ann wq.sh 0 .first

end Counts

/-- the prover with no query for an empty slot, a batch with n requests -/
def cPUW {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (a : ℕ) (bf : Tag → ℕ → ℕ) (n : ℕ) :
    ℕ :=
  cSharedW a (bf .onl) L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first +
    n * cSlotW a (bf .onl) L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first

/-- the committer -/
def cCBW {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params)
    (a : ℕ) (bf : Tag → ℕ → ℕ) : ℕ :=
  tr W.depth + cProve1W a (bf .test) W.T + (p.M + 1) * (tr W.depth + cProve1W a (bf .link) W.Lk)

section Unfold
variable {lam K : ℕ} (c : ℕ) (bff : ℕ → ℕ) (Ns : ℕ) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (i : ℕ)

theorem cSlotW_lo (hk : a.kind = .lo) (ph : PhK) :
    cSlotW c bff (r :: s) (a, A) (w, W) i ph =
      (costJ w + (moreOf w.grJ * c + bff i)) + cSlotW c bff s A W (i + 1) ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem cSlotW_join (hk : a.kind = .sh) :
    cSlotW c bff (r :: s) (a, A) (w, W) i .loc =
      (costJ w + 1 + 1) + cSlotW c bff s A W (i + 1) .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem cSlotW_sh (hk : a.kind = .sh) (ph : PhK) (hph : ph = .first ∨ ph = .shr ∨ ph = .aft) :
    cSlotW c bff (r :: s) (a, A) (w, W) i ph = cSlotW c bff s A W (i + 1) ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl | rfl <;> rfl
theorem cSharedW_lo (hk : a.kind = .lo) (ph : PhK) :
    cSharedW c bff Ns (r :: s) (a, A) (w, W) i ph = cSharedW c bff Ns s A W (i + 1) ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem cSharedW_join (hk : a.kind = .sh) :
    cSharedW c bff Ns (r :: s) (a, A) (w, W) i .loc =
      ((Ns - 1) + cost0 w + (moreOf w.gr0 * c + bff i)) + cSharedW c bff Ns s A W (i + 1) .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem cSharedW_shr (hk : a.kind = .sh) :
    cSharedW c bff Ns (r :: s) (a, A) (w, W) i .shr =
      (cost0 w + (moreOf w.gr0 * c + bff i)) + cSharedW c bff Ns s A W (i + 1) .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem cSharedW_none (hk : a.kind = .sh) (ph : PhK) (hph : ph = .first ∨ ph = .aft) :
    cSharedW c bff Ns (r :: s) (a, A) (w, W) i ph = cSharedW c bff Ns s A W (i + 1) ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl <;> rfl

end Unfold

/-! ## At a = 1, bff i = nbf i + 1 they are the counts of Compile/Batch/SpecOneCall.lean -/

section Unfold
variable {lam K : ℕ} (nbf : ℕ → ℕ) (Ns : ℕ) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (i : ℕ)

theorem cSlotA_lo (hk : a.kind = .lo) (ph : PhK) :
    cSlotA nbf (r :: s) (a, A) (w, W) i ph =
      (costJ w + (moreOf w.grJ + (nbf i + 1))) + cSlotA nbf s A W (i + 1) ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem cSlotA_join (hk : a.kind = .sh) :
    cSlotA nbf (r :: s) (a, A) (w, W) i .loc =
      (costJ w + 1 + 1) + cSlotA nbf s A W (i + 1) .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem cSlotA_sh (hk : a.kind = .sh) (ph : PhK) (hph : ph = .first ∨ ph = .shr ∨ ph = .aft) :
    cSlotA nbf (r :: s) (a, A) (w, W) i ph = cSlotA nbf s A W (i + 1) ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl | rfl <;> rfl
theorem cSharedA_lo (hk : a.kind = .lo) (ph : PhK) :
    cSharedA nbf Ns (r :: s) (a, A) (w, W) i ph = cSharedA nbf Ns s A W (i + 1) ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem cSharedA_join (hk : a.kind = .sh) :
    cSharedA nbf Ns (r :: s) (a, A) (w, W) i .loc =
      ((Ns - 1) + cost0 w + (moreOf w.gr0 + (nbf i + 1))) + cSharedA nbf Ns s A W (i + 1) .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem cSharedA_shr (hk : a.kind = .sh) :
    cSharedA nbf Ns (r :: s) (a, A) (w, W) i .shr =
      (cost0 w + (moreOf w.gr0 + (nbf i + 1))) + cSharedA nbf Ns s A W (i + 1) .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem cSharedA_none (hk : a.kind = .sh) (ph : PhK) (hph : ph = .first ∨ ph = .aft) :
    cSharedA nbf Ns (r :: s) (a, A) (w, W) i ph = cSharedA nbf Ns s A W (i + 1) ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl <;> rfl

end Unfold

theorem cSlotW_one {lam K : ℕ} (nbf : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ph : PhK),
      cSlotW 1 (fun i => nbf i + 1) s A W i ph = cSlotA nbf s A W i ph
  | [], _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), i, ph => by
    by_cases hk : a.kind = .lo
    · rw [cSlotW_lo _ _ a A w W i hk, cSlotA_lo _ a A w W i hk, Nat.mul_one, cSlotW_one nbf s A W]
    · have hk' : a.kind = .sh := by
        cases h : a.kind with
        | lo => exact absurd h hk
        | sh => rfl
      cases ph with
      | loc => rw [cSlotW_join _ _ a A w W i hk', cSlotA_join _ a A w W i hk', cSlotW_one nbf s A W]
      | first =>
        rw [cSlotW_sh _ _ a A w W i hk' _ (.inl rfl),
          cSlotA_sh _ a A w W i hk' _ (.inl rfl), cSlotW_one nbf s A W]
      | shr =>
        rw [cSlotW_sh _ _ a A w W i hk' _ (.inr (.inl rfl)),
          cSlotA_sh _ a A w W i hk' _ (.inr (.inl rfl)), cSlotW_one nbf s A W]
      | aft =>
        rw [cSlotW_sh _ _ a A w W i hk' _ (.inr (.inr rfl)),
          cSlotA_sh _ a A w W i hk' _ (.inr (.inr rfl)), cSlotW_one nbf s A W]

theorem cSharedW_one {lam K : ℕ} (nbf : ℕ → ℕ) (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ph : PhK),
      cSharedW 1 (fun i => nbf i + 1) Ns s A W i ph = cSharedA nbf Ns s A W i ph
  | [], _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), i, ph => by
    by_cases hk : a.kind = .lo
    · rw [cSharedW_lo _ _ _ a A w W i hk, cSharedA_lo _ _ a A w W i hk, cSharedW_one nbf Ns s A W]
    · have hk' : a.kind = .sh := by
        cases h : a.kind with
        | lo => exact absurd h hk
        | sh => rfl
      cases ph with
      | loc =>
        rw [cSharedW_join _ _ _ a A w W i hk', cSharedA_join _ _ a A w W i hk',
          Nat.mul_one, cSharedW_one nbf Ns s A W]
      | shr =>
        rw [cSharedW_shr _ _ _ a A w W i hk', cSharedA_shr _ _ a A w W i hk',
          Nat.mul_one, cSharedW_one nbf Ns s A W]
      | first =>
        rw [cSharedW_none _ _ _ a A w W i hk' _ (.inl rfl),
          cSharedA_none _ _ a A w W i hk' _ (.inl rfl), cSharedW_one nbf Ns s A W]
      | aft =>
        rw [cSharedW_none _ _ _ a A w W i hk' _ (.inr rfl),
          cSharedA_none _ _ a A w W i hk' _ (.inr rfl), cSharedW_one nbf Ns s A W]

theorem cProve1W_one {lam K : ℕ} (nbf : ℕ → ℕ) {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) :
    cProve1W 1 (fun i => nbf i + 1) wq = cProve1A nbf wq := by
  unfold cProve1W cProve1A
  rw [cSharedW_one, cSlotW_one]

theorem cPUW_one {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) (n : ℕ) :
    cPUW W 1 (fun t i => nb t i + 1) n = cPUA W nb n := by
  unfold cPUW cPUA
  rw [cSharedW_one, cSlotW_one]

theorem cCBW_one {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)
    (p : Params) (nb : Tag → ℕ → ℕ) :
    cCBW W p 1 (fun t i => nb t i + 1) = cCBA W p nb := by
  unfold cCBW cCBA
  rw [cProve1W_one, cProve1W_one]

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} {nb : Tag → ℕ → ℕ} {m : OracleCoding (spec lam W.K L) lam} {wt : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ} {ca : ℕ} {bf : Tag → ℕ → ℕ}

local notation "T1" => fun _ => True
local notation "SWr" => SWV (S := spec lam W.K L) (sp := split lam W.K L) (pre wt)

/-- Under `TryW`: a bound in `SWA` at the table that marks every block is a bound here. -/
theorem swv_of (TW : TryW W nb m wt ca bf) {β : Type} {c : St lam W.K L β} {n : ℕ} {P : β → Prop}
    (h : SWA (S := spec lam W.K L) (sp := split lam W.K L)
      (Rom.Need.num (needOf (nbAll W.K) m)) c n P) : SWr c n P :=
  SWV.of_swa (w := pre wt) (fun o q r => (pre_le TW o q r).trans (wR_le_all TW.std o q r)) h

/-! ## The hypothesis of the lemmas on a chain -/

/-- For the rounds that are left. -/
structure RuleSh (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) (t : Tag) (s : Shape) (A : RoundSplits s)
    (Ws : RoundsQueryLayout lam W.K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) : Prop where
  ok : RoundsQueryLayout.OKG s A Ws
  info : ∀ z, tryInfoT W t (embP z) = tryInfo s A Ws z
  pos : NbPosSh (nb t) s A Ws i

section Carried
variable {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam W.K r a} {Ws : RoundsQueryLayout lam W.K s A} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}

theorem RuleSh.tail (H : RuleSh W nb t (r :: s) (a, A) (w, Ws) embP i) :
    RuleSh W nb t s A Ws (fun z => embP (.inr z)) (i + 1) :=
  ⟨H.ok.2, fun z => H.info (.inr z), H.pos.2⟩

theorem RuleSh.loopJ (H : RuleSh W nb t (r :: s) (a, A) (w, Ws) embP i)
    (g : GrW r.Chal a.Pj) (hg : w.grJ = some g) :
    RuleLoop W nb t i w.chal (fun α => embP (.inl (.inr α))) g :=
  ⟨H.ok.1.grJ_ok g hg,
    fun α => (H.info (.inl (.inr α))).trans (by show w.grJ.map _ = _; rw [hg]; rfl),
    H.pos.1 (.inl (by rw [hg]; rfl))⟩

theorem RuleSh.noneJ (H : RuleSh W nb t (r :: s) (a, A) (w, Ws) embP i)
    (α : a.Pj) (hg : w.grJ = none) :
    tryInfoT W t (embP (.inl (.inr α))) = none :=
  (H.info (.inl (.inr α))).trans (by show w.grJ.map _ = _; rw [hg]; rfl)

theorem RuleSh.loop0 (H : RuleSh W nb t (r :: s) (a, A) (w, Ws) embP i)
    (g : GrW r.Chal a.P0) (hg : w.gr0 = some g) :
    RuleLoop W nb t i w.chal (fun α => embP (.inl (.inl α))) g :=
  ⟨H.ok.1.gr0_ok g hg,
    fun α => (H.info (.inl (.inl α))).trans (by show w.gr0.map _ = _; rw [hg]; rfl),
    H.pos.1 (.inr (by rw [hg]; rfl))⟩

theorem RuleSh.none0 (H : RuleSh W nb t (r :: s) (a, A) (w, Ws) embP i)
    (α : a.P0) (hg : w.gr0 = none) :
    tryInfoT W t (embP (.inl (.inl α))) = none :=
  (H.info (.inl (.inl α))).trans (by show w.gr0.map _ = _; rw [hg]; rfl)

end Carried

/-! ## Doing something in each slot -/

theorem swv_eachM {σ τ : Type} {f : σ → St lam W.K L τ} (g : σ → Bool) (g' : τ → Bool) (c : ℕ)
    (hf : ∀ a, SWr (f a) (if g a then c else 0) fun b => g' b = g a) :
    ∀ l : List σ, SWr (eachM f l) ((l.map g).count true * c) fun l' => l'.map g' = l.map g
  | [] => rfl
  | a :: t =>
      SWV.bind' (hf a) (m' := (t.map g).count true * c) (fun b hb => SWV.bind' (swv_eachM g g' c hf t) (m' := 0) (fun r hr => by
        show (b :: r).map g' = (a :: t).map g
        rw [List.map_cons, List.map_cons, hb, hr]) (Nat.le_refl _)) (by
        rw [List.map_cons, List.count_cons]
        cases g a
        · simp
        · simp [Nat.add_mul, Nat.add_comm])

theorem swv_eachM_all {σ τ : Type} {f : σ → St lam W.K L τ} (c : ℕ) (hf : ∀ a, SWr (f a) c T1) :
    ∀ l : List σ, SWr (eachM f l) (l.length * c) fun l' => l'.length = l.length
  | [] => rfl
  | a :: t =>
      SWV.bind' (hf a) (m' := t.length * c) (fun b _ => SWV.bind' (swv_eachM_all c hf t) (m' := 0) (fun r hr => by
        show (b :: r).length = (a :: t).length
        rw [List.length_cons, List.length_cons, hr]) (Nat.le_refl _)) (by rw [List.length_cons, Nat.succ_mul]; omega)

/-! ## The rounds -/

section Rounds
variable (TW : TryW W nb m wt ca bf) {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)
include TW

theorem swv_withTree {β : Type} (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam W.K L β} {n : ℕ} {P : β → Prop} (hk : ∀ tr, SWr (k tr) n P) :
    SWr (withTree sMT has depth leaf k) (tr depth + n) P := by
  cases has with
  | true =>
    exact SWV.bind' (swv_of TW (Need.swa_commitT (nbAll W.K) TW.std sMT depth leaf))
      (fun tr _ => hk (some tr)) (Nat.le_refl _)
  | false => exact (hk none).mono (fun _ h => h) (Nat.le_add_left _ _)

/-- the trees over a component, one after the other, and then what follows. The bound counts `tr d`
for each depth d of the list: so nothing for a component without a tree -/
theorem swv_withTrees {β : Type} {n : ℕ} {P : β → Prop} :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam W.K L β},
      (∀ trs, SWr (k trs) n P) → SWr (withTrees sMT ds leaf k) ((ds.map tr).sum + n) P
  | [], _, _, hk => (hk []).mono (fun _ h => h) (Nat.le_add_left _ _)
  | d :: ds, leaf, _, hk =>
    SWV.bind' (swv_of TW (Need.swa_commitT (nbAll W.K) TW.std sMT d (leaf 0)))
      (m' := (ds.map tr).sum + n)
      (fun x _ => swv_withTrees ds (fun j => leaf (j + 1)) fun trs => hk (x :: trs))
      (le_of_eq (by rw [List.map_cons, List.sum_cons, Nat.add_assoc]))

section One
variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam W.K r a) (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem swv_tree0 {β : Type} (m0 : a.M0) {k : Option TTree → St lam W.K L β} {n : ℕ}
    {P : β → Prop} (hk : ∀ tr, SWr (k tr) n P) :
    SWr (tree0 sMT a w emb m0 k) (cost0 w + n) P :=
  swv_withTree TW sMT _ _ _ hk

/-- the joining round in one slot: its tree, its query to g -/
theorem swv_slotJoin (z : SlotSt lam W.K Y (r :: s)) :
    SWr (slotJoin sMT t a w emb plJ i z) (costJ w + 1) fun z' => full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  exact swv_withTree TW sMT _ _ _ (n := 1 + 0) fun _ => swv_gT TW t i _ _ _ fun _ => rfl

theorem swv_slotJoinU (z : SlotSt lam W.K Y (r :: s)) :
    SWr (slotJoinU sMT t a w emb plJ i z) (if full z then costJ w + 1 else 0) fun z' =>
      full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [Need.slotJoinU_none sMT t a w emb plJ i hx]
    exact rfl
  | some y =>
    have hf : full z = true := by unfold full; rw [hx]; rfl
    rw [Need.slotJoinU_some sMT t a w emb plJ i hx, hf, if_pos rfl]
    exact (swv_slotJoin TW sMT t a w emb plJ i z).mono (fun _ h => h.trans hf) (Nat.le_refl _)

theorem swv_joinM :
    ∀ zs : List (SlotSt lam W.K Y (r :: s)),
      SWr (joinM sMT t a w emb plJ i zs) (zs.length * (costJ w + 1)) fun o =>
        o.1.length = zs.length ∧ o.2.length = zs.length
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWV.bind' (swv_slotJoin TW sMT t a w emb plJ i z) (m' := zs.length * (costJ w + 1)) (fun z' _ => SWV.bind' (swv_joinM zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).length = (z :: zs).length ∧ (z'.2.c :: o.2).length = (z :: zs).length
        rw [List.length_cons, List.length_cons, List.length_cons, ho.1, ho.2]
        exact ⟨rfl, rfl⟩) (Nat.le_refl _)) (by rw [List.length_cons, Nat.succ_mul]; omega)

theorem swv_joinMU :
    ∀ zs : List (SlotSt lam W.K Y (r :: s)),
      SWr (joinMU sMT t a w emb plJ i zs) ((zs.map full).count true * (costJ w + 1))
        fun o => o.1.map full = zs.map full ∧ o.2.map Option.isSome = zs.map full
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWV.bind' (swv_slotJoinU TW sMT t a w emb plJ i z) (m' := (zs.map full).count true * (costJ w + 1)) (fun z' hz' => SWV.bind' (swv_joinMU zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).map full = (z :: zs).map full ∧
          ((z'.2.x.map fun _ => z'.2.c) :: o.2).map Option.isSome = (z :: zs).map full
        rw [List.map_cons, List.map_cons, List.map_cons, ho.1, ho.2, hz', Option.isSome_map]
        exact ⟨rfl, by rw [← hz']; rfl⟩) (Nat.le_refl _)) (by
        rw [List.map_cons, List.count_cons]
        cases full z
        · simp
        · simp [Nat.add_mul, Nat.add_comm])

/-- A local round in one slot: its tree, its Fiat-Shamir query: ca for each attempt but the one with
which the search ends -/
theorem swv_slotLo (hR : ∀ g, w.grJ = some g → RuleLoop W nb t i w.chal plJ g)
    (hN : w.grJ = none → ∀ α, tryInfoT W t (plJ α) = none) (ph : PhT)
    (z : SlotSt lam W.K Y (r :: s)) :
    SWr (slotLo sMT t cms xin a w emb plJ i ph z)
      (costJ w + (moreOf w.grJ * ca + bf t i)) fun z' => full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotLo]
  exact swv_withTree TW sMT _ _ _ (n := moreOf w.grJ * ca + bf t i + 0) fun _ =>
    swv_fbSlotG TW _ hR cms _ ph _ _ _ _ (fun h => hN h _) fun _ _ _ _ => rfl

theorem swv_slotLoU (hR : ∀ g, w.grJ = some g → RuleLoop W nb t i w.chal plJ g)
    (hN : w.grJ = none → ∀ α, tryInfoT W t (plJ α) = none) (ph : PhT)
    (z : SlotSt lam W.K Y (r :: s)) :
    SWr (slotLoU sMT t cms xin a w emb plJ i ph z)
      (if full z then costJ w + (moreOf w.grJ * ca + bf t i) else 0)
      fun z' => full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [Need.slotLoU_none sMT t cms xin a w emb plJ i ph hx]
    exact rfl
  | some y =>
    have hf : full z = true := by unfold full; rw [hx]; rfl
    rw [Need.slotLoU_some sMT t cms xin a w emb plJ i ph hx, hf, if_pos rfl]
    exact (swv_slotLo TW sMT t cms xin a w emb plJ i hR hN ph z).mono
      (fun _ h => h.trans hf) (Nat.le_refl _)

end One

/-! ## The chains -/

variable (depthReq : ℕ)

/-- All chains of a batch with no query for an empty slot, with what they return. fl: which slots
hold a request. -/
theorem swv_chainTU :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam W.K Y s)) (a0 : Acc0) (fl : List Bool),
      RuleSh W nb t s A Ws embP i → zs.map full = fl →
      SWr (chainTU sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
        (cSharedW ca (bf t) fl.length s A Ws i (phK ph) +
          fl.count true * cSlotW ca (bf t) s A Ws i (phK ph))
        fun out => out.1.map (fun a => a.x.isSome) = fl
  | [], _, _, _, _, _, _, _, zs, _, fl, _, hz => by
      show (zs.map Prod.snd).map (fun a => a.x.isSome) = fl
      rw [List.map_map]
      exact hz
  | r :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, fl, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [Need.chainTU_lo sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk ph,
          cSharedW_lo _ _ _ a A w Ws i hk, cSlotW_lo _ _ a A w Ws i hk, ← phK_afterLo]
        refine SWV.bind'
          (swv_eachM full full (costJ w + (moreOf w.grJ * ca + bf t i))
            (fun z => swv_slotLoU TW sMT t cms xin a w _ _ i H.loopJ (fun h α => H.noneJ α h) ph z)
            zs)
          (fun zs' hz' => swv_chainTU s A Ws _ _ (i + 1) _ _ zs' _ fl H.tail (hz'.trans hz))
          (le_of_eq ?_)
        rw [hz]
        ring
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [Need.chainTU_join sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk']
          show SWr _
            (cSharedW ca (bf t) fl.length (r :: s) (a, A) (w, Ws) i .loc +
              fl.count true * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .loc) _
          rw [cSharedW_join _ _ _ a A w Ws i hk', cSlotW_join _ _ a A w Ws i hk']
          refine SWV.bind' (swv_joinMU TW sMT t a w _ _ i zs)
            (m' := (fl.count true + (fl.length - 1)) +
                (cost0 w +
                  (moreOf w.gr0 * ca + bf t i +
                    (cSharedW ca (bf t) fl.length s A Ws (i + 1) .shr +
                      fl.count true * cSlotW ca (bf t) s A Ws (i + 1) .shr))))
            (fun o ho => ?_) (le_of_eq ?_)
          · have e1 : o.2.map Option.isSome = fl := ho.2.trans hz
            have e2 : o.2.length = fl.length := by rw [← e1, List.length_map]
            have hq := Need.swa_reqTU (nbAll W.K) TW.std (K := W.K) (L := L) depthReq o.2
            rw [e1, e2] at hq
            exact SWV.bind' (swv_of TW hq)
              (fun rq _ =>
                swv_tree0 TW sMT a w _ m0 fun tr0 =>
                  swv_fbG TW _ H.loop0 _ _ _ _ _ _ (fun h => H.none0 _ h) fun nc dd bl tl =>
                    swv_chainTU s A Ws _ _ (i + 1) (.shr tl) _ _ _ fl H.tail
                      ((map_full_hear w bl true o.1).trans (ho.1.trans hz))) (Nat.le_refl _)
          · rw [hz]
            generalize fl.length - 1 = q
            ring
        | shr tk0 =>
          rw [Need.chainTU_shr sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk' tk0]
          show SWr _
            (cSharedW ca (bf t) fl.length (r :: s) (a, A) (w, Ws) i .shr +
              fl.count true * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .shr) _
          rw [cSharedW_shr _ _ _ a A w Ws i hk', cSlotW_sh _ _ a A w Ws i hk' _ (.inr (.inl rfl))]
          exact (swv_tree0 TW sMT a w _ m0
              (n := moreOf w.gr0 * ca + bf t i +
                  (cSharedW ca (bf t) fl.length s A Ws (i + 1) .shr +
                    fl.count true * cSlotW ca (bf t) s A Ws (i + 1) .shr)) fun tr0 =>
                      swv_fbG TW _ H.loop0 _ _ _ _ _ _ (fun h => H.none0 _ h) fun nc dd bl tl =>
                        swv_chainTU s A Ws _ _ (i + 1) (.shr tl) _ _ _ fl H.tail
                          ((map_full_hear w bl false zs).trans hz)).mono
            (fun _ h => h) (le_of_eq (by ring))
        | first =>
          rw [Need.chainTU_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inl rfl)]
          show SWr _
            (cSharedW ca (bf t) fl.length (r :: s) (a, A) (w, Ws) i .first +
              fl.count true * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .first) _
          rw [cSharedW_none _ _ _ a A w Ws i hk' _ (.inl rfl),
            cSlotW_sh _ _ a A w Ws i hk' _ (.inl rfl)]
          exact swv_chainTU s A Ws _ _ (i + 1) .first _ _ _ fl
            H.tail ((map_full_hear w _ false zs).trans hz)
        | aft =>
          rw [Need.chainTU_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inr rfl)]
          show SWr _
            (cSharedW ca (bf t) fl.length (r :: s) (a, A) (w, Ws) i .aft +
              fl.count true * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .aft) _
          rw [cSharedW_none _ _ _ a A w Ws i hk' _ (.inr rfl),
            cSlotW_sh _ _ a A w Ws i hk' _ (.inr (.inr rfl))]
          exact swv_chainTU s A Ws _ _ (i + 1) .aft _ _ _ fl
            H.tail ((map_full_hear w _ false zs).trans hz)

/-- All chains of a batch in which every slot works. n: the number of slots. -/
theorem swv_chainT :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam W.K Y s)) (a0 : Acc0) (n : ℕ),
      RuleSh W nb t s A Ws embP i → zs.length = n →
      SWr (chainT sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
        (cSharedW ca (bf t) n s A Ws i (phK ph) + n * cSlotW ca (bf t) s A Ws i (phK ph)) T1
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, n, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [Need.chainT_lo sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk ph,
          cSharedW_lo _ _ _ a A w Ws i hk, cSlotW_lo _ _ a A w Ws i hk, ← phK_afterLo]
        refine SWV.bind'
          (swv_eachM_all (costJ w + (moreOf w.grJ * ca + bf t i))
            (fun z =>
              (swv_slotLo TW sMT t cms xin a w _ _ i H.loopJ (fun h α => H.noneJ α h) ph z).mono
                (fun _ _ => trivial) (Nat.le_refl _)) zs)
          (fun zs' hz' => swv_chainT s A Ws _ _ (i + 1) _ _ zs' _ n H.tail (hz'.trans hz))
          (le_of_eq ?_)
        rw [hz]
        ring
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [Need.chainT_join sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk']
          show SWr _
            (cSharedW ca (bf t) n (r :: s) (a, A) (w, Ws) i .loc +
              n * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .loc) T1
          rw [cSharedW_join _ _ _ a A w Ws i hk', cSlotW_join _ _ a A w Ws i hk']
          refine SWV.bind' (swv_joinM TW sMT t a w _ _ i zs)
            (m' := (n + (n - 1)) +
                (cost0 w +
                  (moreOf w.gr0 * ca + bf t i +
                    (cSharedW ca (bf t) n s A Ws (i + 1) .shr +
                      n * cSlotW ca (bf t) s A Ws (i + 1) .shr))))
            (fun o ho => ?_) (le_of_eq ?_)
          · have e2 : o.2.length = n := ho.2.trans hz
            have hq := Need.swa_reqT (nbAll W.K) TW.std (K := W.K) (L := L) depthReq o.2
            rw [e2] at hq
            exact SWV.bind' (swv_of TW hq)
              (fun rq _ =>
                swv_tree0 TW sMT a w _ m0 fun tr0 =>
                  swv_fbG TW _ H.loop0 _ _ _ _ _ _ (fun h => H.none0 _ h) fun nc dd bl tl =>
                    swv_chainT s A Ws _ _ (i + 1) (.shr tl) _ _ _ n H.tail
                      (by rw [List.length_map]; exact ho.1.trans hz)) (Nat.le_refl _)
          · rw [hz]
            generalize n - 1 = q
            ring
        | shr tk0 =>
          rw [Need.chainT_shr sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk' tk0]
          show SWr _
            (cSharedW ca (bf t) n (r :: s) (a, A) (w, Ws) i .shr +
              n * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .shr) T1
          rw [cSharedW_shr _ _ _ a A w Ws i hk', cSlotW_sh _ _ a A w Ws i hk' _ (.inr (.inl rfl))]
          exact (swv_tree0 TW sMT a w _ m0
              (n := moreOf w.gr0 * ca + bf t i +
                  (cSharedW ca (bf t) n s A Ws (i + 1) .shr +
                    n * cSlotW ca (bf t) s A Ws (i + 1) .shr)) fun tr0 =>
                      swv_fbG TW _ H.loop0 _ _ _ _ _ _ (fun h => H.none0 _ h) fun nc dd bl tl =>
                        swv_chainT s A Ws _ _ (i + 1) (.shr tl) _ _ _ n H.tail
                          (by rw [List.length_map]; exact hz)).mono
            (fun _ h => h) (le_of_eq (by ring))
        | first =>
          rw [Need.chainT_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inl rfl)]
          show SWr _
            (cSharedW ca (bf t) n (r :: s) (a, A) (w, Ws) i .first +
              n * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .first) T1
          rw [cSharedW_none _ _ _ a A w Ws i hk' _ (.inl rfl),
            cSlotW_sh _ _ a A w Ws i hk' _ (.inl rfl)]
          exact swv_chainT s A Ws _ _ (i + 1) .first _ _ _ n
            H.tail (by rw [List.length_map]; exact hz)
        | aft =>
          rw [Need.chainT_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inr rfl)]
          show SWr _
            (cSharedW ca (bf t) n (r :: s) (a, A) (w, Ws) i .aft +
              n * cSlotW ca (bf t) (r :: s) (a, A) (w, Ws) i .aft) T1
          rw [cSharedW_none _ _ _ a A w Ws i hk' _ (.inr rfl),
            cSlotW_sh _ _ a A w Ws i hk' _ (.inr (.inr rfl))]
          exact swv_chainT s A Ws _ _ (i + 1) .aft _ _ _ n
            H.tail (by rw [List.length_map]; exact hz)

end Rounds

end OneCall
end Compile.Batch
