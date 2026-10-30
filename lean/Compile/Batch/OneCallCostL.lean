-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/OneCallCostL.lean: what one search over nonces weighs. Under `RuleLoop`, for every
weight w that meets `TryW W nb m w a bf` (Compile/Batch/OneCallCostW.lean), with its numbers a and
bf: at most a for each attempt but the one with which the search ends, and bf t i for that one. For
the rule's own weight (under `Std m`, `Test0 W`) a is 1 and bf t i is nb t i + 1. (Words of this
library: lean/GLOSSARY.md.)

The bounds are stated with `SWV` of Compile/CostV.lean (the weight of a query may depend on its
answer); the programs are those before `realQ` (Compile/Batch/Oracles.lean: queries to `fbw` become
queries to `fb`), so the weight is `pre w`.

  `RuleLoop`   the hypothesis at a search: the record g is well-formed; the rule reads this search's
               check, and whether an attempt is the last, off the plain part (`tryInfoT` at emb α is
               the check of g, and whether the nonce of α denotes the last number or a later one);
               the table marks a block in this round
  `swv_fbW`, `swv_fbTG`   under `TryW`, `RuleLoop`, the search: g.more · a + bf t i, and what
                          follows
  `swv_fbG`, `swv_fbSlotG`   under the same, with a proof-of-work record or without (then: if the
                             rule sees none at the query): moreOf gr · a + bf t i, and what follows

Notation:
  `w`: (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ, a weight: a number for a query and its
    answer; what a program weighs: the sum over its queries (`SWV`)
  `a`, `bf`: ℕ and Tag → ℕ → ℕ; a: what a failed attempt that is not the last weighs at most; bf t
    i: what any Fiat-Shamir query of round i of protocol t weighs at most (`TryW`,
    Compile/Batch/OneCallCostW.lean): with proof-of-work bits: if the table marks a block there
  `nb`: Tag → ℕ → ℕ, a parameter; nb t i: the number of blocks that round i of protocol t needs (the
    head of Compile/Batch/NeedTable.lean); the table: `needOf nb m`
  `m`: a `Rom.OracleCoding` (Rom/Family.lean), a query encoding (the head of Compile/Batch/NeedTable.lean)
  the rule: `ruleT W nb m` (Compile/Batch/SpecOneCall.lean): at a query to `fb t` with proof-of-work
    bits: block 0 first; the rest only if it passes or the attempt is the last; its own weight:
    `numA`, how many hash blocks the rule queries at (o, q) if the answer is r
    (Rom/SpecOverOneA.lean)
  `SWr c n P`: `SWV` (Compile/CostV.lean) at the weight `pre w`: on every path the weights of the
    queries, each at its own answer, add up to at most n, and the result has the property P
  "and what follows": the bound n₀ of the continuation k (`hk`), which is added
  `g`, `gr`: a `GrW C P`, an Option of one: the proof-of-work record (Iop/BatchWire.lean); `g.more`:
    at most more + 1 tries; `moreOf gr`: at most this many attempts after the first
    (Compile/Batch/Counts.lean)
Limits: nothing about rounds, chains and schemes. The bound is for the worst case over the oracle:
all attempts but one fail.
-/
import Compile.Batch.OneCallCostW

noncomputable section

namespace Compile.Batch
namespace OneCall
open Iop Rom ZKCP
open Compile.CostP (SWV)
open Compile.Batch.Need (Std)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} {nb : Tag → ℕ → ℕ} {m : OracleCoding (spec lam W.K L) lam} {w : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ} {a : ℕ} {bf : Tag → ℕ → ℕ}

local notation "SWr" => SWV (S := spec lam W.K L) (sp := split lam W.K L) (pre w)

/-- The hypothesis at a search. -/
structure RuleLoop (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) (t : Tag) (i : ℕ) {C P : Type}
    (chal : Blk lam W.K → C) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (g : GrW C P) : Prop where
  ok : g.OK
  info : ∀ α, tryInfoT W t (emb α) = some (fun bl => g.ok (chal bl), decide (g.more ≤ g.get α))
  pos : 1 ≤ nb t i

section Evals
variable {β : Type} {P : β → Prop}

/-- one query, for a bound on its weight that holds at all answers -/
theorem swv_fbT (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam W.K → Tok → St lam W.K L β} {c n : ℕ}
    (hc : ∀ (q : FbIn lam L t) r, q.round = i → q.plain = pl → w (.fb t) q r ≤ c)
    (hk : ∀ bl tl, SWr (k bl tl) n P) :
    SWr (fbT t i tk us root hd hinj pl k) (c + n) P :=
  fun v => ⟨c, n, fun _ _ r _ => hc _ r rfl rfl, le_rfl, fun tl => hk v tl⟩

theorem swv_fbTw (t : Tag) (j i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam W.K → Tok → St lam W.K L β} {c n : ℕ}
    (hc : ∀ (q : FbIn lam L t) r, q.round = i → q.plain = pl → w (.fb t) q r ≤ c)
    (hk : ∀ bl tl, SWr (k bl tl) n P) :
    SWr (fbTw t j i tk us root hd hinj pl k) (c + n) P :=
  fun v => ⟨c, n, fun _ _ r _ => hc _ r rfl rfl, le_rfl, fun tl => hk v tl⟩

variable {C P' : Type} {chal : Blk lam W.K → C} {t : Tag} {i : ℕ} {emb : P' → PlainPart (shapeOf L t) (annOf L t)} {g : GrW C P'}

/-- under `TryW`, `RuleLoop`: any attempt of the search weighs at most bf t i -/
theorem try_le (TW : TryW W nb m w a bf) (hR : RuleLoop W nb t i chal emb g) (α : P')
    (q : FbIn lam L t) (r : rngOf lam W.K (.fb t)) (hi : q.round = i) (hq : q.plain = emb α) :
    w (.fb t) q r ≤ bf t i := by
  have h := TW.some t q r _ (hq ▸ hR.info α) (hi ▸ hR.pos)
  rwa [hi] at h

/-- under `TryW`, `RuleLoop`: a failed attempt that is not the last weighs at most a -/
theorem try_fail (TW : TryW W nb m w a bf) (hR : RuleLoop W nb t i chal emb g) (α : P') {n : ℕ}
    (hn : n < g.more) (q : FbIn lam L t) (r : rngOf lam W.K (.fb t))
    (hq : q.plain = emb (g.put n α)) (hf : g.ok (chal r.1) = false) : w (.fb t) q r ≤ a := by
  refine TW.fail t q r ?_
  have hx := hR.info (g.put n α)
  rw [← hq, hR.ok.get_put n α hn.le] at hx
  unfold failsAt
  rw [hx]
  show (!g.ok (chal r.1) && !decide (g.more ≤ n)) = true
  rw [hf, decide_eq_false (by omega)]
  rfl

/-- The attempts after the first: n more attempts after attempt number j + 1; j + 1 + n is the last
number. -/
theorem swv_fbW (TW : TryW W nb m w a bf) (hR : RuleLoop W nb t i chal emb g) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (α : P')
    {k : ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWr (k a dd bl tl) n₀ P) :
    ∀ (n j : ℕ) (dd : List Tok), j + 1 + n = g.more →
      SWr (fbW g chal t i tk us root hd hinj emb α k n j dd) (n * a + bf t i + n₀) P
  | 0, j, dd, _ => by
    have h := swv_fbTw (w := w) (P := P) t j i tk us root hd hinj (emb (g.put (j + 1) α))
      (fun q r hi hq => try_le TW hR _ q r hi hq) fun bl tl => hk (j + 1) dd bl tl
    exact h.mono (fun _ h => h) (by omega)
  | n + 1, j, dd, e => fun v => by
    by_cases hok : g.ok (chal v) = true
    · refine ⟨bf t i, n₀, fun _ _ r _ => try_le TW hR _ _ r rfl rfl,
        by have e : (n + 1) * a = n * a + a := Nat.succ_mul n a; omega, fun tl => ?_⟩
      show SWr (if g.ok (chal v) then _ else _) n₀ P
      rw [if_pos hok]
      exact hk _ _ v tl
    · refine ⟨a, n * a + bf t i + n₀,
        fun _ _ r hr => try_fail TW hR α (n := j + 1) (by omega) _ r rfl ?_,
        by have e : (n + 1) * a = n * a + a := Nat.succ_mul n a; omega,
        fun tl => ?_⟩
      · have hr' : r.1 = v := hr
        rw [hr']
        exact Bool.eq_false_iff.2 hok
      · show SWr (if g.ok (chal v) then _ else _) _ P
        rw [if_neg hok]
        exact swv_fbW TW hR tk us root hd hinj α hk n (j + 1) (tl :: dd) (by omega)

/-- The search. -/
theorem swv_fbTG (TW : TryW W nb m w a bf) (hR : RuleLoop W nb t i chal emb g) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (α : P')
    {k : ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWr (k a dd bl tl) n₀ P) :
    SWr (fbTG g chal t i tk us root hd hinj emb α k) (g.more * a + bf t i + n₀) P := by
  unfold fbTG
  cases hmo : g.more with
  | zero =>
    have h := swv_fbT (w := w) (P := P) t i tk us root hd hinj (emb (g.put 0 α))
      (fun q r hi hq => try_le TW hR _ q r hi hq) fun bl tl => hk 0 [] bl tl
    exact h.mono (fun _ h => h) (by omega)
  | succ n =>
    intro v
    by_cases hok : g.ok (chal v) = true
    · refine ⟨bf t i, n₀, fun _ _ r _ => try_le TW hR _ _ r rfl rfl,
        by have e : (n + 1) * a = n * a + a := Nat.succ_mul n a; omega, fun tl => ?_⟩
      show SWr (if g.ok (chal v) then _ else _) n₀ P
      rw [if_pos hok]
      exact hk _ _ v tl
    · refine ⟨a, n * a + bf t i + n₀,
        fun _ _ r hr => try_fail TW hR α (n := 0) (by omega) _ r rfl ?_,
        by have e : (n + 1) * a = n * a + a := Nat.succ_mul n a; omega,
        fun tl => ?_⟩
      · have hr' : r.1 = v := hr
        rw [hr']
        exact Bool.eq_false_iff.2 hok
      · show SWr (if g.ok (chal v) then _ else _) _ P
        rw [if_neg hok]
        exact swv_fbW TW hR tk us root hd hinj α hk n 0 [tl] (by omega)

/-- A Fiat-Shamir query, with a proof-of-work record or without. hN: without one the rule sees none
at its query. -/
theorem swv_fbG (TW : TryW W nb m w a bf) (gr : Option (GrW C P'))
    (hR : ∀ g, gr = some g → RuleLoop W nb t i chal emb g) (tk : Tok) (us : List Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (α : P')
    (hN : gr = none → tryInfoT W t (emb α) = none)
    {k : Option ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWr (k a dd bl tl) n₀ P) :
    SWr (fbG gr chal t i tk us root hd hinj emb α k) (moreOf gr * a + bf t i + n₀) P := by
  cases gr with
  | none =>
    have h := swv_fbT (w := w) (P := P) t i tk us root hd hinj (emb α) (c := bf t i) (fun q r hi hq => by
      have := TW.none t q r (hq ▸ hN rfl)
      rwa [hi] at this) fun bl tl => hk none [] bl tl
    exact h.mono (fun _ h => h) (by simp [moreOf])
  | some g =>
    exact swv_fbTG TW (hR g rfl) tk us root hd hinj α fun a dd bl tl => hk (some a) dd bl tl

/-- the same in a slot, whatever its phase -/
theorem swv_fbSlotG (TW : TryW W nb m w a bf) (gr : Option (GrW C P'))
    (hR : ∀ g, gr = some g → RuleLoop W nb t i chal emb g) (cms : List (Dig lam)) (x : Option X)
    (ph : PhT) (tk c : Tok) (root : Option Tok) (α : P')
    (hN : gr = none → tryInfoT W t (emb α) = none)
    {k : Option ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWr (k a dd bl tl) n₀ P) :
    SWr (fbSlotG gr chal t i cms x ph tk c root emb α k) (moreOf gr * a + bf t i + n₀) P := by
  cases ph <;> exact swv_fbG TW gr hR _ _ root _ _ α hN hk

/-- under `TryW`: the query to the oracle g weighs at most 1 -/
theorem swv_gT (TW : TryW W nb m w a bf) (t : Tag) (i : ℕ) (tk : Tok)
    (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Tok → St lam W.K L β}
    {n : ℕ} (hk : ∀ c, SWr (k c) n P) :
    SWr (gT t i tk root pl k) (1 + n) P :=
  fun _ =>
    ⟨1, n, fun _ _ r _ => (pre_le TW (.g t) _ r).trans (wR_g TW.std t _ r), le_rfl, fun c => hk c⟩

end Evals

end OneCall
end Compile.Batch
