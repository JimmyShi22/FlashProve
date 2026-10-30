-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/KeptWalk.lean: the bound on the Fiat-Shamir queries, not counting failed attempts
  that are not the last, for the parts of the compiled prover up to all chains of a batch. For
  Compile/Batch/SpecKept.lean, whose header says what is counted and why (words of this library:
  lean/GLOSSARY.md).
  The bounds are stated with `SWV` (Compile/CostV.lean: the weight of a query may depend on its
  answer). The programs are those before `realQ`, so the weight is `pre (wKept W)`
  (Compile/Batch/OneCallCostW.lean): at a ghost name `fbw t j` it is what `wKept W` is at `fb t`.
    `k_zero`             a program without a Fiat-Shamir query (`NoFbS`, Compile/Batch/NoFb.lean)
                         has weight 0
    `k_fbG`              under `RuleLoop`: the search over nonces has weight at most 1, whatever its
                         cap: 0 for each attempt but the one with which the search ends, at most 1
                         for that one.
                         After Compile/Batch/OneCallCostL.lean, whose record `RuleLoop` (what the
                         rule reads off a query of the search) serves here at the function "1
                         everywhere"
    `k_chainTU`, `k_chainT`
                         all chains of a batch, under `RuleSh`: at most kShared + (slots with a
                         request) · kSlot (in `k_chainT`: all slots)

  Notation: `SWk c m P`: `SWV` (Compile/CostV.lean) at the weight `pre (wKept W)`: on every path the
  weights of the queries, each at its own answer, add up to at most m, and the result has the
  property P; `T1`: the property that always holds (`fun _ => True`); `RuleLoop`
  (Compile/Batch/OneCallCostL.lean): the hypothesis at a search; `RuleSh`
  (Compile/Batch/OneCallCostR.lean): the hypothesis of the lemmas on a chain, for the rounds that
  are left; names that begin with nf_: the program has `NoFbS` (Compile/Batch/NoFb.lean): it queries
  neither a Fiat-Shamir oracle nor a ghost name; with k_: a bound in `SWk`; `kSlot`, `kShared`
  (Compile/Batch/SpecKept.lean): the searches of one slot with a request, in the rounds that are
  left: one for each local round; the shared searches: one for the joining round and for each of the
  shared rounds after it up to the next local round.

  Limits: nothing on schemes (Compile/Batch/Kept.lean).
-/
import Compile.Batch.SpecKept
import Compile.Batch.OneCallCostS
import Compile.Batch.NoFb

noncomputable section

namespace Compile.Batch
namespace Kept
open Iop Rom ZKCP
open Compile.CostP (SWV)
open Compile.Batch.Need (PhK phK full phK_afterLo map_full_hear)
open Compile.Batch.OneCall (pre RuleLoop RuleSh swv_fbT swv_fbTw swv_eachM swv_eachM_all)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}

local notation "T1" => fun _ => True
local notation "SWk" => SWV (S := spec lam W.K L) (sp := split lam W.K L) (pre (wKept W))

/-- the function "1 everywhere": it serves only to state the records `RuleLoop`, `RuleSh` -/
abbrev nb1 : Tag → ℕ → ℕ := fun _ _ => 1

/-! ## The weight -/

theorem pre_nf {o : OracleName} (h : NF o) (q : domOf lam L o) (r : rngOf lam W.K o) :
    pre (wKept W) o q r = 0 := by
  cases o <;> first | exact h.elim | rfl

theorem kept_le_one (t : Tag) (q : FbIn lam L t) (r : rngOf lam W.K (.fb t)) :
    wKept W (.fb t) q r ≤ 1 := by
  show (if failsAt W t q r.1 = true then 0 else 1) ≤ 1
  split_ifs <;> omega

theorem kept_fail {t : Tag} {q : FbIn lam L t}
    {r : rngOf lam W.K (.fb t)} (h : failsAt W t q r.1 = true) : wKept W (.fb t) q r = 0 := if_pos h

/-! ## Programs without a Fiat-Shamir query -/

/-- A program without a Fiat-Shamir query (`NoFbS`) has weight 0. -/
theorem k_zero {β : Type} {c : St lam W.K L β} (h : NoFbS c) : SWk c 0 T1 := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r (h r)
  | plain o q k ih => exact fun r => ⟨0, le_of_eq (by rw [pre_nf h.1]), ih r (h.2 r)⟩
  | fresh l k ih => exact fun t => ih t (h t)
  | marked o t us pt inj k ih =>
    exact fun v =>
      ⟨0, 0, fun _ _ _ _ => le_of_eq (pre_nf h.1 _ _), le_rfl, fun t' => ih v t' (h.2 v t')⟩
  | reveal ts k ih => exact fun vs => ih vs (h vs)

section NF
variable {K : ℕ}

theorem nf_nodeT (a b : Tok) : NoFbS (nodeT (lam := lam) (K := K) (L := L) a b) :=
  ⟨trivial, fun _ _ => trivial⟩
theorem nf_rleafT (c : Tok) : NoFbS (rleafT (lam := lam) (K := K) (L := L) c) :=
  ⟨trivial, fun _ _ => trivial⟩
theorem nf_rnodeT (a b : Tok) : NoFbS (rnodeT (lam := lam) (K := K) (L := L) a b) :=
  ⟨trivial, fun _ _ => trivial⟩

theorem nf_leavesT (sMT : ℕ) : ∀ l : List (Body L), NoFbS (leavesT (lam := lam) (K := K) sMT l)
  | [] => trivial
  | b :: t => (nf_leafT sMT b).bind fun _ => (nf_leavesT sMT t).bind fun _ => trivial

theorem nf_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    NoFbS (commitT (lam := lam) (K := K) sMT d leaf) :=
  (nf_leavesT sMT _).bind fun x => (nf_levelsM nf_nodeT d x.1).bind fun _ => trivial

theorem nf_rleavesT : ∀ l : List Tok, NoFbS (rleavesT (lam := lam) (K := K) (L := L) l)
  | [] => trivial
  | c :: t => (nf_rleafT c).bind fun _ => (nf_rleavesT t).bind fun _ => trivial

theorem nf_reqT (depthReq : ℕ) (cs : List Tok) :
    NoFbS (reqT (lam := lam) (K := K) (L := L) depthReq cs) :=
  (nf_rleavesT cs).bind fun ls => (nf_levelsM nf_rnodeT depthReq ls).bind fun _ => trivial

theorem nf_rleavesTU : ∀ l : List (Option Tok), NoFbS (rleavesTU (lam := lam) (K := K) (L := L) l)
  | [] => trivial
  | some c :: t => (nf_rleafT c).bind fun _ => (nf_rleavesTU t).bind fun _ => trivial
  | none :: t => fun _ => (nf_rleavesTU t).bind fun _ => trivial

theorem nf_reqTU (depthReq : ℕ) (cs : List (Option Tok)) :
    NoFbS (reqTU (lam := lam) (K := K) (L := L) depthReq cs) :=
  (nf_rleavesTU cs).bind fun ls => (nf_levelsM nf_rnodeT depthReq ls).bind fun _ => trivial

end NF

section Evals
variable {β : Type} {P : β → Prop}

theorem k_withTree (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam W.K L β} {n : ℕ} (hk : ∀ tr, SWk (k tr) n P) :
    SWk (withTree sMT has depth leaf k) n P := by
  cases has with
  | true =>
    exact SWV.bind' (k_zero (nf_commitT sMT depth leaf))
      (fun tr _ => hk (some tr)) (le_of_eq (Nat.zero_add n))
  | false => exact hk none

/-- The trees over a component, however many, have weight 0: a bound on what follows them is a bound
on the whole. -/
theorem k_withTrees (sMT : ℕ) {n : ℕ} :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam W.K L β},
      (∀ trs, SWk (k trs) n P) → SWk (withTrees sMT ds leaf k) n P
  | [], _, _, hk => hk []
  | d :: ds, leaf, _, hk =>
    SWV.bind' (k_zero (nf_commitT sMT d (leaf 0)))
      (fun tr _ => k_withTrees sMT ds (fun j => leaf (j + 1)) fun trs => hk (tr :: trs))
      (le_of_eq (Nat.zero_add n))

theorem k_gT (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Tok → St lam W.K L β} {n : ℕ} (hk : ∀ c, SWk (k c) n P) : SWk (gT t i tk root pl k) n P :=
  fun _ => ⟨0, n, fun _ _ _ _ => le_rfl, le_of_eq (Nat.zero_add n), fun c => hk c⟩

/-! ## The search over nonces -/

variable {C P' : Type} {chal : Blk lam W.K → C} {t : Tag} {i : ℕ} {emb : P' → PlainPart (shapeOf L t) (annOf L t)} {g : GrW C P'}

/-- Under `RuleLoop`: a failed attempt that is not the last has weight 0. -/
theorem try_zero (hR : RuleLoop W nb1 t i chal emb g) (α : P') {n : ℕ}
    (hn : n < g.more) (q : FbIn lam L t) (r : rngOf lam W.K (.fb t))
    (hq : q.plain = emb (g.put n α)) (hf : g.ok (chal r.1) = false) : wKept W (.fb t) q r ≤ 0 := by
  refine le_of_eq (kept_fail ?_)
  have hx := hR.info (g.put n α)
  rw [← hq, hR.ok.get_put n α hn.le] at hx
  unfold failsAt
  rw [hx]
  show (!g.ok (chal r.1) && !decide (g.more ≤ n)) = true
  rw [hf, decide_eq_false (by omega)]
  rfl

/-- The attempts after the first: at most 1 + n₀, under `RuleLoop`, `hk`, j + 1 + n = `g.more`. -/
theorem k_fbW (hR : RuleLoop W nb1 t i chal emb g) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs)) (α : P')
    {k : ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWk (k a dd bl tl) n₀ P) :
    ∀ (n j : ℕ) (dd : List Tok),
      j + 1 + n = g.more → SWk (fbW g chal t i tk us root hd hinj emb α k n j dd) (1 + n₀) P
  | 0, j, dd, _ =>
    swv_fbTw (w := wKept W) (P := P) t j i tk us root hd hinj (emb (g.put (j + 1) α))
      (fun q r _ _ => kept_le_one t q r) fun bl tl => hk (j + 1) dd bl tl
  | n + 1, j, dd, e => fun v => by
    by_cases hok : g.ok (chal v) = true
    · refine ⟨1, n₀, fun _ _ r _ => kept_le_one t _ r, le_rfl, fun tl => ?_⟩
      show SWk (if g.ok (chal v) then _ else _) n₀ P
      rw [if_pos hok]
      exact hk _ _ v tl
    · refine ⟨0, 1 + n₀, fun _ _ r hr => try_zero hR α (n := j + 1) (by omega) _ r rfl ?_,
        le_of_eq (Nat.zero_add _), fun tl => ?_⟩
      · have hr' : r.1 = v := hr
        rw [hr']
        exact Bool.eq_false_iff.2 hok
      · show SWk (if g.ok (chal v) then _ else _) _ P
        rw [if_neg hok]
        exact k_fbW hR tk us root hd hinj α hk n (j + 1) (tl :: dd) (by omega)

theorem k_fbTG (hR : RuleLoop W nb1 t i chal emb g) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs)) (α : P')
    {k : ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWk (k a dd bl tl) n₀ P) :
    SWk (fbTG g chal t i tk us root hd hinj emb α k) (1 + n₀) P := by
  unfold fbTG
  cases hmo : g.more with
  | zero =>
    exact swv_fbT (w := wKept W) (P := P) t i tk us root hd hinj (emb (g.put 0 α))
      (fun q r _ _ => kept_le_one t q r) fun bl tl => hk 0 [] bl tl
  | succ n =>
    intro v
    by_cases hok : g.ok (chal v) = true
    · refine ⟨1, n₀, fun _ _ r _ => kept_le_one t _ r, le_rfl, fun tl => ?_⟩
      show SWk (if g.ok (chal v) then _ else _) n₀ P
      rw [if_pos hok]
      exact hk _ _ v tl
    · refine ⟨0, 1 + n₀, fun _ _ r hr => try_zero hR α (n := 0) (by omega) _ r rfl ?_,
        le_of_eq (Nat.zero_add _), fun tl => ?_⟩
      · have hr' : r.1 = v := hr
        rw [hr']
        exact Bool.eq_false_iff.2 hok
      · show SWk (if g.ok (chal v) then _ else _) _ P
        rw [if_neg hok]
        exact k_fbW hR tk us root hd hinj α hk n 0 [tl] (by omega)

/-- A Fiat-Shamir query, with proof-of-work bits (under `RuleLoop`) or without: at most 1 + n₀
(`hk`). -/
theorem k_fbG (gr : Option (GrW C P')) (hR : ∀ g, gr = some g → RuleLoop W nb1 t i chal emb g)
    (tk : Tok) (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (α : P')
    {k : Option ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWk (k a dd bl tl) n₀ P) :
    SWk (fbG gr chal t i tk us root hd hinj emb α k) (1 + n₀) P := by
  cases gr with
  | none =>
    exact swv_fbT (w := wKept W) (P := P) t i tk us root hd hinj (emb α)
      (fun q r _ _ => kept_le_one t q r) fun bl tl => hk none [] bl tl
  | some g => exact k_fbTG (hR g rfl) tk us root hd hinj α fun a dd bl tl => hk (some a) dd bl tl

theorem k_fbSlotG (gr : Option (GrW C P')) (hR : ∀ g, gr = some g → RuleLoop W nb1 t i chal emb g)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok) (α : P')
    {k : Option ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} {n₀ : ℕ}
    (hk : ∀ a dd bl tl, SWk (k a dd bl tl) n₀ P) :
    SWk (fbSlotG gr chal t i cms x ph tk c root emb α k) (1 + n₀) P := by
  cases ph <;> exact k_fbG gr hR _ _ root _ _ α hk

end Evals

/-! ## The sums, unfolded -/

section Unfold
variable {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)

theorem kSlot_lo (hk : a.kind = .lo) (ph : PhK) :
    kSlot (r :: s) (a, A) ph = 1 + kSlot s A ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem kSlot_join (hk : a.kind = .sh) : kSlot (r :: s) (a, A) .loc = kSlot s A .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem kSlot_sh (hk : a.kind = .sh) (ph : PhK) (hph : ph = .first ∨ ph = .shr ∨ ph = .aft) :
    kSlot (r :: s) (a, A) ph = kSlot s A ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl | rfl <;> rfl
theorem kShared_lo (hk : a.kind = .lo) (ph : PhK) :
    kShared (r :: s) (a, A) ph = kShared s A ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem kShared_join (hk : a.kind = .sh) : kShared (r :: s) (a, A) .loc = 1 + kShared s A .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem kShared_shr (hk : a.kind = .sh) : kShared (r :: s) (a, A) .shr = 1 + kShared s A .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem kShared_none (hk : a.kind = .sh) (ph : PhK) (hph : ph = .first ∨ ph = .aft) :
    kShared (r :: s) (a, A) ph = kShared s A ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl <;> rfl

end Unfold

/-! ## The rounds -/

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

section One
variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam W.K r a) (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem k_tree0 {β : Type} (m0 : a.M0) {k : Option TTree → St lam W.K L β} {n : ℕ}
    {P : β → Prop} (hk : ∀ tr, SWk (k tr) n P) :
    SWk (tree0 sMT a w emb m0 k) n P :=
  k_withTree sMT _ _ _ hk

theorem k_slotJoin (z : SlotSt lam W.K Y (r :: s)) :
    SWk (slotJoin sMT t a w emb plJ i z) 0 fun z' => full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  exact k_withTree sMT _ _ _ fun _ => k_gT t i _ _ _ fun _ => rfl

theorem k_slotJoinU (z : SlotSt lam W.K Y (r :: s)) :
    SWk (slotJoinU sMT t a w emb plJ i z) 0 fun z' => full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [Need.slotJoinU_none sMT t a w emb plJ i hx]
    exact rfl
  | some y =>
    rw [Need.slotJoinU_some sMT t a w emb plJ i hx]
    exact k_slotJoin sMT t a w emb plJ i z

theorem k_joinM :
    ∀ zs : List (SlotSt lam W.K Y (r :: s)),
      SWk (joinM sMT t a w emb plJ i zs) 0 fun o => o.1.length = zs.length ∧ o.2.length = zs.length
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWV.bind' (k_slotJoin sMT t a w emb plJ i z) (m' := 0) (fun z' _ => SWV.bind' (k_joinM zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).length = (z :: zs).length ∧ (z'.2.c :: o.2).length = (z :: zs).length
        rw [List.length_cons, List.length_cons, List.length_cons, ho.1, ho.2]
        exact ⟨rfl, rfl⟩) (Nat.le_refl _)) (Nat.le_refl _)

theorem k_joinMU :
    ∀ zs : List (SlotSt lam W.K Y (r :: s)), SWk (joinMU sMT t a w emb plJ i zs) 0
      fun o => o.1.map full = zs.map full ∧ o.2.map Option.isSome = zs.map full
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWV.bind' (k_slotJoinU sMT t a w emb plJ i z) (m' := 0) (fun z' hz' => SWV.bind' (k_joinMU zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).map full = (z :: zs).map full ∧
          ((z'.2.x.map fun _ => z'.2.c) :: o.2).map Option.isSome = (z :: zs).map full
        rw [List.map_cons, List.map_cons, List.map_cons, ho.1, ho.2, hz', Option.isSome_map]
        exact ⟨rfl, by rw [← hz']; rfl⟩) (Nat.le_refl _)) (Nat.le_refl _)

/-- A local round in one slot: at most 1 (under `RuleLoop` if it has proof-of-work bits). -/
theorem k_slotLo (hR : ∀ g, w.grJ = some g → RuleLoop W nb1 t i w.chal plJ g)
    (ph : PhT) (z : SlotSt lam W.K Y (r :: s)) :
    SWk (slotLo sMT t cms xin a w emb plJ i ph z) 1 fun z' => full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotLo]
  exact k_withTree sMT _ _ _ (n := 1 + 0) fun _ =>
    k_fbSlotG _ hR cms _ ph _ _ _ _ fun _ _ _ _ => rfl

theorem k_slotLoU (hR : ∀ g, w.grJ = some g → RuleLoop W nb1 t i w.chal plJ g)
    (ph : PhT) (z : SlotSt lam W.K Y (r :: s)) :
    SWk (slotLoU sMT t cms xin a w emb plJ i ph z) (if full z then 1 else 0) fun z' =>
      full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [Need.slotLoU_none sMT t cms xin a w emb plJ i ph hx]
    exact rfl
  | some y =>
    have hf : full z = true := by unfold full; rw [hx]; rfl
    rw [Need.slotLoU_some sMT t cms xin a w emb plJ i ph hx, hf, if_pos rfl]
    exact (k_slotLo sMT t cms xin a w emb plJ i hR ph z).mono
      (fun _ h => h.trans hf) (Nat.le_refl _)

end One

/-! ## The chains -/

variable (depthReq : ℕ)

/-- All chains of a batch in `chainTU` (no query for an empty slot), under `RuleSh`. fl: which slots
hold a request. -/
theorem k_chainTU :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam W.K Y s)) (a0 : Acc0) (fl : List Bool),
      RuleSh W nb1 t s A Ws embP i → zs.map full = fl →
      SWk (chainTU sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
        (kShared s A (phK ph) + fl.count true * kSlot s A (phK ph)) T1
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, fl, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [Need.chainTU_lo sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk ph,
          kShared_lo a A hk, kSlot_lo a A hk, ← phK_afterLo]
        refine SWV.bind'
          (swv_eachM full full 1 (fun z => k_slotLoU sMT t cms xin a w _ _ i H.loopJ ph z) zs)
          (fun zs' hz' => k_chainTU s A Ws _ _ (i + 1) _ _ zs' _ fl H.tail (hz'.trans hz))
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
          show SWk _ (kShared (r :: s) (a, A) .loc + fl.count true * kSlot (r :: s) (a, A) .loc) _
          rw [kShared_join a A hk', kSlot_join a A hk']
          refine SWV.bind' (k_joinMU sMT t a w _ _ i zs)
            (m' := 1 + (kShared s A .shr + fl.count true * kSlot s A .shr))
            (fun o ho => ?_) (le_of_eq (by ring))
          exact SWV.bind' (k_zero (nf_reqTU depthReq o.2))
            (fun rq _ =>
              k_tree0 sMT a w _ m0 fun tr0 =>
                k_fbG _ H.loop0 _ _ _ _ _ _ fun nc dd bl tl =>
                  k_chainTU s A Ws _ _ (i + 1) (.shr tl) _ _ _ fl H.tail
                    ((map_full_hear w bl true o.1).trans (ho.1.trans hz)))
            (le_of_eq (Nat.zero_add _))
        | shr tk0 =>
          rw [Need.chainTU_shr sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk' tk0]
          show SWk _ (kShared (r :: s) (a, A) .shr + fl.count true * kSlot (r :: s) (a, A) .shr) _
          rw [kShared_shr a A hk', kSlot_sh a A hk' _ (.inr (.inl rfl))]
          exact (k_tree0 sMT a w _ m0
              (n := 1 + (kShared s A .shr + fl.count true * kSlot s A .shr)) fun tr0 =>
                k_fbG _ H.loop0 _ _ _ _ _ _ fun nc dd bl tl =>
                  k_chainTU s A Ws _ _ (i + 1) (.shr tl) _ _ _ fl H.tail
                    ((map_full_hear w bl false zs).trans hz)).mono
            (fun _ h => h) (le_of_eq (by ring))
        | first =>
          rw [Need.chainTU_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inl rfl)]
          show SWk _
            (kShared (r :: s) (a, A) .first + fl.count true * kSlot (r :: s) (a, A) .first) _
          rw [kShared_none a A hk' _ (.inl rfl), kSlot_sh a A hk' _ (.inl rfl)]
          exact k_chainTU s A Ws _ _ (i + 1) .first _ _ _ fl
            H.tail ((map_full_hear w _ false zs).trans hz)
        | aft =>
          rw [Need.chainTU_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inr rfl)]
          show SWk _ (kShared (r :: s) (a, A) .aft + fl.count true * kSlot (r :: s) (a, A) .aft) _
          rw [kShared_none a A hk' _ (.inr rfl), kSlot_sh a A hk' _ (.inr (.inr rfl))]
          exact k_chainTU s A Ws _ _ (i + 1) .aft _ _ _ fl
            H.tail ((map_full_hear w _ false zs).trans hz)

/-- All chains of a batch in `chainT` (an empty slot is hashed like any other), under `RuleSh`. n:
the number of slots. -/
theorem k_chainT :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam W.K Y s)) (a0 : Acc0) (n : ℕ),
      RuleSh W nb1 t s A Ws embP i → zs.length = n →
      SWk (chainT sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
        (kShared s A (phK ph) + n * kSlot s A (phK ph)) T1
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, n, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [Need.chainT_lo sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk ph,
          kShared_lo a A hk, kSlot_lo a A hk, ← phK_afterLo]
        refine SWV.bind'
          (swv_eachM_all 1
            (fun z =>
              (k_slotLo sMT t cms xin a w _ _ i H.loopJ ph z).mono
                (fun _ _ => trivial) (Nat.le_refl _)) zs)
          (fun zs' hz' => k_chainT s A Ws _ _ (i + 1) _ _ zs' _ n H.tail (hz'.trans hz))
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
          show SWk _ (kShared (r :: s) (a, A) .loc + n * kSlot (r :: s) (a, A) .loc) T1
          rw [kShared_join a A hk', kSlot_join a A hk']
          refine SWV.bind' (k_joinM sMT t a w _ _ i zs)
            (m' := 1 + (kShared s A .shr + n * kSlot s A .shr))
            (fun o ho => ?_) (le_of_eq (by ring))
          exact SWV.bind' (k_zero (nf_reqT depthReq o.2))
            (fun rq _ =>
              k_tree0 sMT a w _ m0 fun tr0 =>
                k_fbG _ H.loop0 _ _ _ _ _ _ fun nc dd bl tl =>
                  k_chainT s A Ws _ _ (i + 1) (.shr tl) _ _ _ n H.tail
                    (by rw [List.length_map]; exact ho.1.trans hz))
            (le_of_eq (Nat.zero_add _))
        | shr tk0 =>
          rw [Need.chainT_shr sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk' tk0]
          show SWk _ (kShared (r :: s) (a, A) .shr + n * kSlot (r :: s) (a, A) .shr) T1
          rw [kShared_shr a A hk', kSlot_sh a A hk' _ (.inr (.inl rfl))]
          exact (k_tree0 sMT a w _ m0 (n := 1 + (kShared s A .shr + n * kSlot s A .shr)) fun tr0 =>
              k_fbG _ H.loop0 _ _ _ _ _ _ fun nc dd bl tl =>
                k_chainT s A Ws _ _ (i + 1) (.shr tl) _ _ _ n H.tail
                  (by rw [List.length_map]; exact hz)).mono
            (fun _ h => h) (le_of_eq (by ring))
        | first =>
          rw [Need.chainT_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inl rfl)]
          show SWk _ (kShared (r :: s) (a, A) .first + n * kSlot (r :: s) (a, A) .first) T1
          rw [kShared_none a A hk' _ (.inl rfl), kSlot_sh a A hk' _ (.inl rfl)]
          exact k_chainT s A Ws _ _ (i + 1) .first _ _ _ n
            H.tail (by rw [List.length_map]; exact hz)
        | aft =>
          rw [Need.chainT_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inr rfl)]
          show SWk _ (kShared (r :: s) (a, A) .aft + n * kSlot (r :: s) (a, A) .aft) T1
          rw [kShared_none a A hk' _ (.inr rfl), kSlot_sh a A hk' _ (.inr (.inr rfl))]
          exact k_chainT s A Ws _ _ (i + 1) .aft _ _ _ n H.tail (by rw [List.length_map]; exact hz)

end Rounds

end Kept
end Compile.Batch
