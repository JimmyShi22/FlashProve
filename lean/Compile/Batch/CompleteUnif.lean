-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUnif.lean: under lazily sampled oracles, the distribution of the hash blocks
that any one slot sees, and the probability that its proof string is `none`. Towards completeness of
the compiled scheme.

For the algorithms without tokens of Compile/Batch/CompleteRefDefs.lean (a token is a position in a
store: the head there). The verifier randomness of a slot is made from the hash blocks of its
Fiat-Shamir answers. (words of this library: lean/GLOSSARY.md)

  1  `OnlyQ`: all queries of an algorithm have a property; then so have all new entries of the
     table. `FbLt t i`: every entry of the Fiat-Shamir oracle of t has a round below i.
  2  `eachO`: one entry of the result has, for fixed oracles, the distribution of its own program
     (`eager_eachO_entry`), so under lazy sampling too (`Rom.map_runLazy_congr`). This is needed
     because in a local round the query of slot n may be that of an earlier slot; only the marginal
     distribution of its hash block matters.
  3  `chainO_blocks`: the hash blocks that slot n gathers are independent, each with the
     distribution of its round (`ublkG`): uniform without proof-of-work bits; with them that of the
     final attempt, `retry` (Prob/Retry.lean: sample until the check is passed, at most `more` + 1
     times; the last sample is kept whatever it is). Among the hypotheses: `FbLt t i` of the table,
     `RoundsQueryLayout.OKG`, and no proof-of-work bits or `embP` injective (the attempts of a search must be
     different queries; they differ in the nonce, in the plain part).
  4  `zero_ublkG`: under `RoundsQueryLayout.OKG`, the verifier randomness with all proof-of-work bits set to 0
     has the distribution that it has under uniform verifier randomness (`Prob.map_retry`,
     `ok_indep`).
  5  `pr_noneAtG`: under the hypotheses of item 3, the proof string of a slot is `none` with exactly
     the probability of the withheld set, if the withheld set does not depend on the proof-of-work
     bits (`GrFitP.wh`, Compile/Batch/SpecFit.lean). `pr_noneAt`: the same without such bits
     (`RoundsQueryLayout.OK`).
  6  Test and Link on given nodes (`testO`, `linkO`: `pr_testO`, `pr_linkO`), for `W.OK`: see their
     statements. `badAt_of_ok`: there `badAt` (`none`, or a failed search) is `noneAt` (`none`).

Limits: not here: the probability that a search fails.
-/
import Compile.Batch.LoopLazy
import Compile.Batch.LoopLaw
import Rom.Forget
import Iop.BatchOne
import Compile.Batch.Spec

noncomputable section

open scoped ENNReal

namespace Compile.Batch.CompleteUnif
open Iop Rom Prob Compile.Batch.Ref

/-! ## 1. Algorithms all of whose queries have a property -/

section OnlyQ
variable {S : OSpec} {α β : Type}

/-- all queries of the algorithm, on all paths, have the property P -/
def OnlyQ (P : (o : S.ι) → S.Dom o → Prop) : OComp S α → Prop
  | .pure _ => True
  | .query o q k => P o q ∧ ∀ r, OnlyQ P (k r)
  | .sample _ k => ∀ r, OnlyQ P (k r)

variable {P P' : (o : S.ι) → S.Dom o → Prop}

theorem OnlyQ.bind {c : OComp S α} {g : α → OComp S β} (hc : OnlyQ P c) (hg : ∀ a, OnlyQ P (g a)) :
    OnlyQ P (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | query o q k ih => exact ⟨hc.1, fun r => ih r (hc.2 r)⟩
  | sample n k ih => exact fun r => ih r (hc r)

theorem OnlyQ.mono (h : ∀ o q, P o q → P' o q) {c : OComp S α} (hc : OnlyQ P c) : OnlyQ P' c := by
  induction c with
  | pure a => trivial
  | query o q k ih => exact ⟨h o q hc.1, fun r => ih r (hc.2 r)⟩
  | sample n k ih => exact fun r => ih r (hc r)

/-- for an algorithm with `OnlyQ P`: every entry of the table after the run was there before, or has
P -/
theorem OnlyQ.table {c : OComp S α} (hc : OnlyQ P c) :
    ∀ (T : Table S), ∀ x ∈ (c.runLazy T).support, ∀ o q, x.2 o q ≠ none → T o q ≠ none ∨ P o q := by
  induction c with
  | pure a =>
    intro T x hx o q h
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx] at h
    exact Or.inl h
  | query o₀ q₀ k ih =>
    intro T x hx o q h
    simp only [OComp.runLazy] at hx
    cases hT : T o₀ q₀ with
    | some r =>
      rw [hT] at hx
      exact ih r (hc.2 r) T x hx o q h
    | none =>
      rw [hT] at hx
      obtain ⟨r, -, hx'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
      rcases ih r (hc.2 r) _ x hx' o q h with h1 | h1
      · by_cases ho : o = o₀
        · subst ho
          by_cases hq : q = q₀
          · subst hq; exact Or.inr hc.1
          · rw [Table.set, Function.update_self, Function.update_of_ne hq] at h1
            exact Or.inl h1
        · rw [Table.set, Function.update_of_ne ho] at h1
          exact Or.inl h1
      · exact Or.inr h1
  | sample n k ih =>
    intro T x hx o q h
    simp only [OComp.runLazy] at hx
    obtain ⟨r, -, hx'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    exact ih r (hc r) T x hx' o q h

theorem bind_const_supp {γ τ : Type} {p : PMF γ} {g : γ → PMF τ}
    {q : PMF τ} (h : ∀ a ∈ p.support, g a = q) : p.bind g = q :=
  (Rom.bind_congr_support p (g := fun _ => q) h).trans (PMF.bind_const _ _)

end OnlyQ

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- the query does not go to the Fiat-Shamir oracle of t -/
def NotFb (t : Tag) : (o : OracleName) → domOf lam L o → Prop := fun o _ => o ≠ OracleName.fb t

/-- if the query goes to the Fiat-Shamir oracle of t, its round is i -/
def FbAt (t : Tag) (i : ℕ) : (o : OracleName) → domOf lam L o → Prop
  | .fb t', q => t' = t → q.round = i
  | _, _ => True

theorem NotFb.fbAt {t : Tag} (i : ℕ) : ∀ (o : OracleName) (q : domOf lam L o), NotFb t o q → FbAt t i o q
  | .fb _, _, h => fun e => absurd (congrArg OracleName.fb e) h
  | .leaf, _, _ => trivial
  | .node, _, _ => trivial
  | .rleaf, _, _ => trivial
  | .rnode, _, _ => trivial
  | .g _, _, _ => trivial
  | .ann, _, _ => trivial
  | .other, _, _ => trivial
  | .fbw _ _, _, _ => trivial

/-- every entry of the Fiat-Shamir oracle of t has a round below i -/
def FbLt (t : Tag) (i : ℕ) (T : Table (spec lam K L)) : Prop :=
  ∀ q : FbIn lam L t, T (OracleName.fb t) q ≠ none → q.round < i

theorem FbLt.of_notFb {α : Type} {t : Tag} {i : ℕ} {c : TypedOracleComputation lam K L α}
    (hc : OnlyQ (S := spec lam K L) (NotFb t) c) {T : Table (spec lam K L)} (hT : FbLt t i T) :
    ∀ x ∈ (c.runLazy T).support, FbLt t i x.2 := fun x hx q hq => by
  rcases hc.table T x hx (OracleName.fb t) q hq with h | h
  · exact hT q h
  · exact absurd rfl h

theorem FbLt.of_fbAt {α : Type} {t : Tag} {i : ℕ} {c : TypedOracleComputation lam K L α}
    (hc : OnlyQ (S := spec lam K L) (FbAt t i) c) {T : Table (spec lam K L)} (hT : FbLt t i T) :
    ∀ x ∈ (c.runLazy T).support, FbLt t (i + 1) x.2 := fun x hx q hq => by
  rcases hc.table T x hx (OracleName.fb t) q hq with h | h
  · exact Nat.lt_succ_of_lt (hT q h)
  · have h' : q.round = i := h rfl
    rw [h']; exact Nat.lt_succ_self i

/-- from `FbLt t i` to `FbLt t (i + 1)`: an entry set at a query of round i -/
theorem FbLt.set {t : Tag} {i : ℕ} {T : Table (spec lam K L)} (hT : FbLt t i T) (q₀ : FbIn lam L t)
    (h₀ : q₀.round = i) (r : (spec lam K L).Rng (OracleName.fb t)) :
    FbLt t (i + 1) (T.set (OracleName.fb t) q₀ r) := fun q hq => by
  by_cases hqq : q = q₀
  · rw [hqq, h₀]; exact Nat.lt_succ_self i
  · rw [Table.set, Function.update_self,
      @Function.update_of_ne _ _ ((spec lam K L).decDom (OracleName.fb t)) _ _ hqq] at hq
    exact Nat.lt_succ_of_lt (hT q hq)

theorem FbLt.new {t : Tag} {i : ℕ} {T : Table (spec lam K L)} (hT : FbLt t i T)
    (q₀ : FbIn lam L t) (h₀ : q₀.round = i) : T (OracleName.fb t) q₀ = none := by
  by_contra h
  exact absurd (hT q₀ h) (by rw [h₀]; exact lt_irrefl i)

/-! ### The algorithms that do not query the Fiat-Shamir oracle -/

section Progs
variable (t : Tag)

theorem onlyQ_eachO {σ τ : Type} {P : (o : OracleName) → domOf lam L o → Prop} {g : σ → TypedOracleComputation lam K L τ}
    (hg : ∀ a, OnlyQ (S := spec lam K L) P (g a)) :
    ∀ l : List σ, OnlyQ (S := spec lam K L) P (eachO g l)
  | [] => trivial
  | a :: l => OnlyQ.bind (hg a) fun _ => OnlyQ.bind (onlyQ_eachO hg l) fun _ => trivial

theorem onlyQ_askV (o : OracleName) (ho : o ≠ OracleName.fb t) (q : domOf lam L o) :
    OnlyQ (S := spec lam K L) (NotFb t) (askTypedOracle (L := L) (K := K) o q) :=
  ⟨ho, fun _ => trivial⟩

theorem onlyQ_pairUp {hN : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)}
    (h : ∀ a b, OnlyQ (S := spec lam K L) (NotFb t) (hN a b)) :
    ∀ l : List (Dig lam), OnlyQ (S := spec lam K L) (NotFb t) (pairUp hN l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: l => OnlyQ.bind (h a b) fun _ => OnlyQ.bind (onlyQ_pairUp h l) fun _ => trivial

theorem onlyQ_levelsM {hN : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)}
    (h : ∀ a b, OnlyQ (S := spec lam K L) (NotFb t) (hN a b)) :
    ∀ (d : ℕ) (l : List (Dig lam)), OnlyQ (S := spec lam K L) (NotFb t) (levelsM hN d l)
  | 0, _ => trivial
  | d + 1, l =>
    OnlyQ.bind (onlyQ_pairUp t h l) fun _ => OnlyQ.bind (onlyQ_levelsM h d _) fun _ => trivial

theorem onlyQ_freshO (l : ℕ) :
    OnlyQ (S := spec lam K L) (NotFb t) (freshO (lam := lam) (K := K) (L := L) l) :=
  fun _ => trivial
theorem onlyQ_drawO {β : Type} (e : Enum β) :
    OnlyQ (S := spec lam K L) (NotFb t) (drawO (lam := lam) (K := K) (L := L) e) := fun _ => trivial

theorem onlyQ_leafO (sMT : ℕ) (b : Body L) :
    OnlyQ (S := spec lam K L) (NotFb t) (leafO (lam := lam) (K := K) sMT b) :=
  OnlyQ.bind (onlyQ_freshO t sMT) fun _ => onlyQ_askV t OracleName.leaf (by simp) _

theorem onlyQ_rootO (sMT d : ℕ) (leaf : ℕ → Body L) :
    OnlyQ (S := spec lam K L) (NotFb t) (rootO (lam := lam) (K := K) sMT d leaf) :=
  OnlyQ.bind (onlyQ_eachO (onlyQ_leafO t sMT) _) fun _ =>
    OnlyQ.bind (onlyQ_levelsM t (fun _ _ => onlyQ_askV t OracleName.node (by simp) _) d _) fun _ => trivial

theorem onlyQ_rootOO (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → Body L) :
    OnlyQ (S := spec lam K L) (NotFb t) (rootOO (lam := lam) (K := K) sMT has d leaf) := by
  cases has with
  | true => exact OnlyQ.bind (onlyQ_rootO t sMT d leaf) fun _ => trivial
  | false => exact trivial

theorem onlyQ_rootsOO (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L),
      OnlyQ (S := spec lam K L) (NotFb t) (rootsOO (lam := lam) (K := K) sMT ds leaf)
  | [], _ => trivial
  | d :: ds, leaf =>
    OnlyQ.bind (onlyQ_rootO t sMT d (leaf 0)) fun _ =>
      OnlyQ.bind (onlyQ_rootsOO sMT ds fun n => leaf (n + 1)) fun _ => trivial

theorem onlyQ_leafEO (sMT : ℕ) (x : Body L × Bool) :
    OnlyQ (S := spec lam K L) (NotFb t) (leafEO (lam := lam) (K := K) sMT x) := by
  unfold leafEO
  split
  · exact onlyQ_leafO t sMT _
  · exact onlyQ_askV t OracleName.leaf (by simp) _

theorem onlyQ_rootEO (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    OnlyQ (S := spec lam K L) (NotFb t) (rootEO (lam := lam) (K := K) sMT d leaf) :=
  OnlyQ.bind (onlyQ_eachO (onlyQ_leafEO t sMT) _) fun _ =>
    OnlyQ.bind (onlyQ_levelsM t (fun _ _ => onlyQ_askV t OracleName.node (by simp) _) d _) fun _ => trivial

theorem onlyQ_reqRootO (dR : ℕ) (cs : List Bits) :
    OnlyQ (S := spec lam K L) (NotFb t) (reqRootO (lam := lam) (K := K) (L := L) dR cs) :=
  OnlyQ.bind (onlyQ_eachO (fun _ => onlyQ_askV t OracleName.rleaf (by simp) _) _) fun _ =>
    OnlyQ.bind (onlyQ_levelsM t (fun _ _ => onlyQ_askV t OracleName.rnode (by simp) _) dR _)
      fun _ => trivial

end Progs

/-! ## 2. One entry of eachO -/

section Each
variable {σ τ γ : Type}

/-- a function of entry number n of a list; d if there is no such entry -/
def atN (h : τ → γ) (d : γ) (n : ℕ) (l : List τ) : γ := ((l[n]?).map h).getD d

theorem atN_cons_zero (h : τ → γ) (d : γ) (b : τ) (l : List τ) : atN h d 0 (b :: l) = h b := rfl
theorem atN_cons_succ (h : τ → γ) (d : γ) (n : ℕ) (b : τ) (l : List τ) :
    atN h d (n + 1) (b :: l) = atN h d n l := by
  simp [atN]

/-- With the oracles fixed, one entry of the result has the distribution of its own program. -/
theorem eager_eachO_entry (g : σ → TypedOracleComputation lam K L τ) (h : τ → γ) (d : γ) (f : Fam (spec lam K L)) :
    ∀ (n : ℕ) (l : List σ) (v : σ),
      l[n]? = some v → ((eachO g l).runEager f).map (atN h d n) = ((g v).runEager f).map h
  | _, [], _, hl => by simp at hl
  | 0, a :: l, v, hl => by
    obtain rfl : a = v := by simpa using hl
    show (((g a).bind fun b => (eachO g l).bind fun r => OComp.pure (b :: r)).runEager f).map _ = _
    simp only [OComp.runEager_bind, PMF.map_bind, OComp.runEager, PMF.pure_map,
      atN_cons_zero, PMF.bind_const]
    rfl
  | n + 1, a :: l, v, hl => by
    have hl' : l[n]? = some v := by simpa using hl
    show (((g a).bind fun b => (eachO g l).bind fun r => OComp.pure (b :: r)).runEager f).map _ = _
    simp only [OComp.runEager_bind, PMF.map_bind, OComp.runEager, PMF.pure_map, atN_cons_succ]
    rw [PMF.bind_const, ← eager_eachO_entry g h d f n l v hl']
    rfl

/-- the same (`eager_eachO_entry`) under lazy sampling, from any table -/
theorem lazy_eachO_entry (g : σ → TypedOracleComputation lam K L τ) (h : τ → γ) (d : γ) (n : ℕ) (l : List σ) (v : σ)
    (hl : l[n]? = some v) (T : Table (spec lam K L)) :
    ((eachO g l).runLazy T).map (fun x => atN h d n x.1) = ((g v).runLazy T).map fun x => h x.1 :=
  Rom.map_runLazy_congr (atN h d n) h (fun f => eager_eachO_entry g h d f n l v hl) T

/-- in every run, entry number n of the result comes from a run of the program of entry number n -/
theorem supp_eachO_entry (g : σ → TypedOracleComputation lam K L τ) (R : σ → τ → Prop)
    (hg : ∀ a T, ∀ y ∈ ((g a).runLazy T).support, R a y.1) :
    ∀ (n : ℕ) (l : List σ) (v : σ),
      l[n]? = some v → ∀ T, ∀ y ∈ ((eachO g l).runLazy T).support, ∃ v', y.1[n]? = some v' ∧ R v v'
  | _, [], _, hl, _, _, _ => by simp at hl
  | n, a :: l, v, hl, T, y, hy => by
    have hy' : y ∈
        (((g a).bind fun b => (eachO g l).bind fun r => OComp.pure (b :: r)).runLazy T).support :=
      hy
    rw [OComp.runLazy_bind] at hy'
    obtain ⟨y1, h1, hy'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
    rw [OComp.runLazy_bind] at hy'
    obtain ⟨y2, h2, hy'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hy'
    rw [hy']
    cases n with
    | zero =>
      obtain rfl : a = v := by simpa using hl
      exact ⟨y1.1, rfl, hg a T y1 h1⟩
    | succ n =>
      obtain ⟨v', e, r⟩ := supp_eachO_entry g R hg n l v (by simpa using hl) y1.2 y2 h2
      exact ⟨v', by simpa using e, r⟩

end Each

/-! ## 3. The hash blocks of one slot -/


theorem map_fst_unif_ans : (unif ((Fin K → Dig lam) × Dig lam)).map Prod.fst = unif (Blk lam K) :=
  map_fst_unif

/-! ### With proof-of-work bits -/

/-- the distribution of the answer that a Fiat-Shamir query ends with: uniform; with proof-of-work
bits: sample until the check is passed, at most `more` + 1 times (`retry`, Prob/Retry.lean) -/
def gAns {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) :
    PMF ((Fin K → Dig lam) × Dig lam) :=
  match gr with
  | none => unif _
  | some g => retry (fun x : (Fin K → Dig lam) × Dig lam => g.ok (chal x.1)) g.more

/-- the distribution of the hash blocks of that answer -/
def gblk {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) : PMF (Blk lam K) :=
  (gAns gr chal).map Prod.fst

/-- the distribution of the hash blocks that a slot sees in one round -/
def rblk {r : Round} (a : RAnn r) (w : WireRB lam K r a) : PMF (Blk lam K) :=
  match a.kind with
  | .lo => gblk w.grJ w.chal
  | .sh => gblk w.gr0 w.chal

/-- independent hash blocks, one for each round, each with the distribution of its round -/
def ublkG : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PMF (List (Blk lam K))
  | [], _, _ => PMF.pure []
  | _ :: s, (a, A), (w, W) => (rblk a w).bind fun bl => (ublkG s A W).map fun l => bl :: l

theorem ublkG_step {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (b : List (Blk lam K)) :
    ((rblk a w).bind fun bl => (ublkG s A W).map fun l => (b ++ [bl]) ++ l) =
      (ublkG (r :: s) (a, A) (w, W)).map fun l => b ++ l := by
  show _ = ((rblk a w).bind fun bl => (ublkG s A W).map fun l => bl :: l).map _
  rw [PMF.map_bind]
  refine congrArg _ (funext fun bl => ?_)
  rw [PMF.map_comp]
  refine congrArg (fun f => PMF.map f (ublkG s A W)) (funext fun l => ?_)
  simp

theorem gblk_none {C P : Type} (chal : Blk lam K → C) :
    gblk (none : Option (GrW C P)) chal = unif (Blk lam K) := map_fst_unif_ans

def toFO : PhO → FPhase
  | .first => .first
  | .loc => .loc
  | .shr _ => .shr
  | .aft => .aft

theorem toFO_afterLo (ph : PhO) : toFO ph.afterLo = (toFO ph).afterLo := by cases ph <;> rfl

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (dR : ℕ)

theorem onlyQ_askW {C P : Type} (g : GrW C P) (chal : Blk lam K → C) (q : ℕ → FbIn lam L t)
    (i : ℕ) (hr : ∀ m, (q m).round = i) :
    ∀ n j : ℕ, OnlyQ (S := spec lam K L) (FbAt t i) (askW g chal t q n j)
  | 0, j => ⟨fun _ => hr j, fun _ => trivial⟩
  | n + 1, j =>
      OnlyQ.bind (c := askTypedOracle (L := L) (K := K) (OracleName.fb t) (q j))
          ⟨fun _ => hr j, fun _ => trivial⟩ fun ans => by
      by_cases ho : g.ok (chal ans.1) = true
      · rw [if_pos ho]; trivial
      · rw [if_neg ho]; exact onlyQ_askW g chal q i hr n (j + 1)

theorem onlyQ_askG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C)
    (q : P → FbIn lam L t) (i : ℕ) (hr : ∀ β, (q β).round = i) (α : P) :
    OnlyQ (S := spec lam K L) (FbAt t i) (askG gr chal t q α) := by
  cases gr with
  | none => exact ⟨fun _ => hr α, fun _ => trivial⟩
  | some g => exact onlyQ_askW t g chal _ i (fun _ => hr _) _ _

theorem onlyQ_slotLoO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhO) (v : VSlot lam K X (r :: s)) :
    OnlyQ (S := spec lam K L) (FbAt t i) (slotLoO sMT t cms a w emb plJ i ph v) :=
  OnlyQ.bind ((onlyQ_rootOO t sMT _ _ _).mono (NotFb.fbAt i)) fun _ =>
    OnlyQ.bind (onlyQ_askG t _ _ _ i (fun _ => rfl) _) fun _ => trivial

/-- T' is T except at queries q β to the Fiat-Shamir oracle of t -/
def LeftQ {P : Type} (q : P → FbIn lam L t) (T T' : Table (spec lam K L)) : Prop :=
  ∀ (o : OracleName) (x : (spec lam K L).Dom o),
    T' o x ≠ T o x → ∃ β, (⟨o, x⟩ : Σ o : OracleName, (spec lam K L).Dom o) = ⟨OracleName.fb t, q β⟩

theorem FbLt.left {P : Type} {q : P → FbIn lam L t} {i : ℕ} {T T' : Table (spec lam K L)}
    (hT : FbLt t i T) (hr : ∀ β, (q β).round = i) (hL : LeftQ t q T T') :
    FbLt t (i + 1) T' := fun x hx => by
  by_cases e : T' (OracleName.fb t) x = T (OracleName.fb t) x
  · exact Nat.lt_succ_of_lt (hT x (by rw [← e]; exact hx))
  · obtain ⟨β, hβ⟩ := hL (OracleName.fb t) x e
    have : x = q β := eq_of_heq (Sigma.mk.inj hβ).2
    rw [this, hr β]
    exact Nat.lt_succ_self i

/-- A Fiat-Shamir query, with or without proof-of-work bits, at new inputs, with what follows it. -/
theorem askG_then {C P γ τ : Type} (gr : Option (GrW C P)) (hgr : ∀ g, gr = some g → g.OK)
    (chal : Blk lam K → C) (q : P → FbIn lam L t) (hq : ∀ g, gr = some g → Function.Injective q)
    (α : P) (k : (Fin K → Dig lam) × Dig lam → TypedOracleComputation lam K L γ) (h : γ × Table (spec lam K L) → τ)
    (F : (Fin K → Dig lam) × Dig lam → PMF τ) (T : Table (spec lam K L))
    (hnew : ∀ β, T (OracleName.fb t) (q β) = none)
    (hk : ∀ ans T', LeftQ t q T T' → ((k ans).runLazy T').map h = F ans) :
    (((askG gr chal t q α).bind k).runLazy T).map h = (gAns gr chal).bind F := by
  cases gr with
  | none =>
    refine (congrArg (PMF.map h) (LoopLazy.run_ask_new t (q α) k T (hnew α))).trans ?_
    rw [PMF.map_bind]
    refine congrArg _ (funext fun ans => hk ans _ fun o x hx => ?_)
    obtain ⟨m, -, -, c⟩ := LoopLazy.leftBy_set t (fun _ => q α) T 0 0 ans o x hx
    exact ⟨α, c⟩
  | some g =>
    refine LoopLazy.askW_then g chal t (fun j => q (g.put j α)) k h F g.more 0 T
      (fun m _ _ => hnew _) (fun m m' _ hm _ hm' e => ?_)
      fun ans T' hT' => hk ans T' fun o x hx => ?_
    · have e2 := congrArg g.get (hq g rfl e)
      rwa [(hgr g rfl).get_put m α (by omega), (hgr g rfl).get_put m' α (by omega)] at e2
    · obtain ⟨m, -, -, c⟩ := hT' o x hx
      exact ⟨_, c⟩

theorem onlyQ_slotJoinO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (v : VSlot lam K X (r :: s)) :
    OnlyQ (S := spec lam K L) (NotFb t) (slotJoinO sMT t a w emb plJ i v) :=
  OnlyQ.bind (onlyQ_rootOO t sMT _ _ _) fun _ => ⟨by simp [NotFb], fun _ => trivial⟩

/-- A local round in one slot, under the hypotheses below: one more hash block, with the
distribution of the round. -/
theorem blocks_slotLoO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhO) (v : VSlot lam K X (r :: s)) (T : Table (spec lam K L)) (hT : FbLt t i T)
    (hgr : ∀ g, w.grJ = some g → g.OK) (hq : ∀ g, w.grJ = some g → Function.Injective plJ) :
    ((slotLoO sMT t cms a w emb plJ i ph v).runLazy T).map (fun x => x.1.blocks) =
      (gblk w.grJ w.chal).map fun bl => v.blocks ++ [bl] := by
  unfold slotLoO
  rw [OComp.runLazy_bind, PMF.map_bind]
  refine bind_const_supp fun out hout => ?_
  have hT' := FbLt.of_notFb (onlyQ_rootOO t sMT _ _ _) hT out hout
  refine (askG_then t w.grJ hgr w.chal
    (fun α => (⟨i, headO L cms i ph v, out.1, plJ α⟩ : FbIn lam L t))
    (fun g hg x y e => hq g hg (congrArg FbIn.plain e)) _ _
    (fun x : VSlot lam K X s × Table (spec lam K L) => x.1.blocks)
    (fun ans => PMF.pure (v.blocks ++ [ans.1])) out.2 (fun β => hT'.new _ rfl)
    fun ans T' _ => PMF.pure_map _ _).trans ?_
  unfold gblk
  rw [PMF.map_comp]
  rfl

theorem supp_slotJoinO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (v : VSlot lam K X (r :: s)) (T : Table (spec lam K L)) :
    ∀ y ∈ ((slotJoinO sMT t a w emb plJ i v).runLazy T).support, y.1.blocks = v.blocks := by
  intro y hy
  unfold slotJoinO at hy
  rw [OComp.runLazy_bind] at hy
  obtain ⟨y1, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  rw [OComp.runLazy_bind] at hy
  obtain ⟨y2, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hy
  rw [hy]

section Unfold
variable {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} (w : WireRB lam K r a)
  (W : RoundsQueryLayout lam K s A) (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
  (σ0 : SStrat (r :: s) (a, A)) (vs : List (VSlot lam K X (r :: s)))

theorem chainO_lo (hk : a.kind = .lo) (ph : PhO) :
    chainO sMT t cms dR (r :: s) (a, A) (w, W) embS embP i ph σ0 vs =
      (eachO (slotLoO sMT t cms a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
        vs).bind fun vs' =>
          chainO sMT t cms dR s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              ph.afterLo (σ0.2 (a.kind.shOf (w.chal (blk0 lam K)))) vs' := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

theorem chainO_join (hk : a.kind = .sh) :
    chainO sMT t cms dR (r :: s) (a, A) (w, W) embS embP i .loc σ0 vs =
      (eachO (slotJoinO sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i)
        vs).bind fun vs1 =>
          (reqRootO dR (vs1.map fun v => v.c)).bind fun rq =>
          (root0O sMT a w (fun p => embS (.inl p)) σ0.1).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f4 cms (List.ofFn rq), rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 σ0.1)).bind fun ans =>
          chainO sMT t cms dR s A W (fun p => embS (.inr p))
              (fun z => embP (.inr z)) (i + 1) (.shr (List.ofFn ans.2))
              (σ0.2 (a.kind.shOf (w.chal ans.1))) (vs1.map (hearO w ans.1)) := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

theorem chainO_shr (hk : a.kind = .sh) (ρ0 : Bits) :
    chainO sMT t cms dR (r :: s) (a, A) (w, W) embS embP i (.shr ρ0) σ0 vs
      = (root0O sMT a w (fun p => embS (.inl p)) σ0.1).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f5 ρ0, rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 σ0.1)).bind fun ans =>
          chainO sMT t cms dR s A W (fun p => embS (.inr p))
              (fun z => embP (.inr z)) (i + 1) (.shr (List.ofFn ans.2))
              (σ0.2 (a.kind.shOf (w.chal ans.1))) (vs.map (hearO w ans.1)) := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

end Unfold

/-- a new Fiat-Shamir query whose answer enters what follows only through a distribution that
depends on its hash blocks -/
theorem ask_new {γ τ : Type} (q : FbIn lam L t) (k : (Fin K → Dig lam) × Dig lam → TypedOracleComputation lam K L γ)
    (h : γ × Table (spec lam K L) → τ) (T : Table (spec lam K L)) (hnew : T (OracleName.fb t) q = none)
    (F : Blk lam K → PMF τ)
    (hk : ∀ ans, ((k ans).runLazy (T.set (OracleName.fb t) q ans)).map h = F ans.1) :
    (((askTypedOracle (L := L) (K := K) (OracleName.fb t) q).bind k).runLazy T).map h =
      (unif (Blk lam K)).bind F := by
  show (OComp.runLazy (OComp.query (S := spec lam K L) (OracleName.fb t) q k) T).map h = _
  simp only [OComp.runLazy]
  rw [hnew]
  show ((unif ((Fin K → Dig lam) × Dig lam)).bind fun ans =>
      (k ans).runLazy (T.set (OracleName.fb t) q ans)).map h = _
  rw [PMF.map_bind]
  simp only [hk]
  rw [← map_fst_unif_ans, PMF.bind_map]
  rfl

/-- The hash blocks that one slot gathers are independent, each with the distribution of its round,
from every state of the execution: whatever the other slots, the strategies and the shared chain
are, if the table holds no Fiat-Shamir query of a round that is still to come. Further hypotheses
are below. -/
theorem chainO_blocks (n : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhO) (σ0 : SStrat s A)
        (vs : List (VSlot lam K X s)) (v : VSlot lam K X s) (T : Table (spec lam K L)),
      RoundsQueryLayout.OKG s A W → (RoundsQueryLayout.OK s A W ∨ Function.Injective embP) →
      RoundSplits.FmtFrom s A (toFO ph) → vs[n]? = some v → FbLt t i T →
      ((chainO sMT t cms dR s A W embS embP i ph σ0 vs).runLazy T).map (fun x => x.1.getD n []) =
        (ublkG s A W).map fun l => v.blocks ++ l
  | [], _, _, _, _, _, _, _, vs, v, T, _, _, _, hv, _ => by
    show ((OComp.pure (vs.map fun v => v.blocks) : TypedOracleComputation lam K L _).runLazy T).map _ =
      (PMF.pure []).map _
    simp only [OComp.runLazy, PMF.pure_map, List.append_nil]
    congr 1
    simp [List.getD, hv]
  | r :: s, (a, A), (w, W), embS, embP, i, ph, σ0, vs, v, T, hW, hE, hF, hv, hT => by
    have hE' : RoundsQueryLayout.OK s A W ∨ Function.Injective fun z => embP (.inr z) :=
      hE.imp (fun h => h.2) fun h x y e => Sum.inr.inj (h e)
    have hqJ : ∀ g,
        w.grJ = some g → Function.Injective fun α => embP (.inl (.inr α)) := fun g hg => by
      rcases hE with h | h
      · rw [h.1.grJ_none] at hg; cases hg
      · exact fun x y e => Sum.inr.inj (Sum.inl.inj (h e))
    have hq0 : ∀ g,
        w.gr0 = some g → Function.Injective fun α => embP (.inl (.inl α)) := fun g hg => by
      rcases hE with h | h
      · rw [h.1.gr0_none] at hg; cases hg
      · exact fun x y e => Sum.inl.inj (Sum.inl.inj (h e))
    have hsh : ∀ b : List (Blk lam K), a.kind = .sh →
        ((gAns w.gr0 w.chal).bind fun ans => (ublkG s A W).map fun l => (b ++ [ans.1]) ++ l) =
          (ublkG (r :: s) (a, A) (w, W)).map fun l => b ++ l := fun b hk => by
      rw [← ublkG_step a A w W b]
      have e : rblk a w = gblk w.gr0 w.chal := by unfold rblk; rw [hk]
      rw [e]
      unfold gblk
      rw [PMF.bind_map]
      rfl
    cases hk : a.kind with
    | lo =>
      have hF' : RoundSplits.FmtFrom s A (toFO ph.afterLo) := by
        rw [toFO_afterLo]
        have : a.NoShared ∧ RoundSplits.FmtFrom s A (toFO ph).afterLo := by
          simpa only [RoundSplits.FmtFrom, hk] using hF
        exact this.2
      rw [chainO_lo sMT t cms dR w W embS embP i σ0 vs hk ph, OComp.runLazy_bind, PMF.map_bind]
      have step : ∀ y ∈
              ((eachO (slotLoO sMT t cms a w (fun p => embS (.inl p))
                    (fun α => embP (.inl (.inr α))) i ph) vs).runLazy T).support,
            ((chainO sMT t cms dR s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
                  ph.afterLo (σ0.2 (a.kind.shOf (w.chal (blk0 lam K)))) y.1).runLazy y.2).map
                (fun x => x.1.getD n []) =
              (fun b : List (Blk lam K) => (ublkG s A W).map fun l => b ++ l)
                (atN VSlot.blocks [] n y.1) := by
        intro y hy
        obtain ⟨v', e, -⟩ :=
          supp_eachO_entry _ (fun _ _ => True) (fun _ _ _ _ => trivial) n vs v hv T y hy
        rw [chainO_blocks n s A W _ _ (i + 1) _ _ y.1 v' y.2 hW.2 hE' hF' e
          (FbLt.of_fbAt (onlyQ_eachO (onlyQ_slotLoO sMT t cms a w _ _ i ph) vs) hT y hy)]
        simp [atN, e]
      have e : ∀ p : PMF (List (VSlot lam K X s) × Table (spec lam K L)),
          (p.bind fun y =>
              (fun b : List (Blk lam K) => (ublkG s A W).map fun l => b ++ l)
                (atN VSlot.blocks [] n y.1)) =
            (p.map fun y => atN VSlot.blocks [] n y.1).bind fun b =>
              (ublkG s A W).map fun l => b ++ l := fun p => by
        rw [PMF.bind_map]; rfl
      rw [Rom.bind_congr_support _ step, e, lazy_eachO_entry _ VSlot.blocks [] n vs v hv T,
        blocks_slotLoO sMT t cms a w _ _ i ph v T hT hW.1.grJ_ok hqJ, PMF.bind_map]
      have er : rblk a w = gblk w.grJ w.chal := by unfold rblk; rw [hk]
      rw [← er]
      exact ublkG_step a A w W v.blocks
    | sh =>
      cases ph with
      | first => simp only [RoundSplits.FmtFrom, hk, toFO] at hF
      | aft => simp only [RoundSplits.FmtFrom, hk, toFO] at hF
      | loc =>
        have hF' : RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toFO] using hF
        rw [chainO_join sMT t cms dR w W embS embP i σ0 vs hk, OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y1 h1 => ?_
        have t1 := FbLt.of_notFb (onlyQ_eachO (onlyQ_slotJoinO sMT t a w _ _ i) vs) hT y1 h1
        obtain ⟨v1, e1, b1⟩ := supp_eachO_entry _
          (fun v v' : VSlot lam K X (r :: s) => v'.blocks = v.blocks)
          (fun a' T' => supp_slotJoinO sMT t a w _ _ i a' T') n vs v hv T y1 h1
        rw [OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y2 h2 => ?_
        have t2 := FbLt.of_notFb (onlyQ_reqRootO t dR _) t1 y2 h2
        rw [OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y3 h3 => ?_
        have t3 := FbLt.of_notFb (onlyQ_rootOO t sMT _ _ _) t2 y3 h3
        refine (askG_then t w.gr0 hW.1.gr0_ok w.chal
            (fun α => (⟨i, .f4 cms (List.ofFn y2.1), y3.1, embP (.inl (.inl α))⟩ : FbIn lam L t))
            (fun g hg x y e => hq0 g hg (congrArg FbIn.plain e)) _ _ _
            (fun ans => (ublkG s A W).map fun l => (v.blocks ++ [ans.1]) ++ l) y3.2
            (fun β => t3.new _ rfl) fun ans T' hT' => ?_).trans
          (hsh v.blocks hk)
        have ih := chainO_blocks n s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          (.shr (List.ofFn ans.2)) (σ0.2 (a.kind.shOf (w.chal ans.1))) (y1.1.map (hearO w ans.1))
          (hearO w ans.1 v1) T' hW.2 hE' hF' (by simp [e1]) (t3.left t (fun _ => rfl) hT')
        refine ih.trans ?_
        show (ublkG s A W).map (fun l => (v1.blocks ++ [ans.1]) ++ l) = _
        rw [b1]
      | shr ρ0 =>
        have hF' : RoundSplits.FmtFrom s A .shr := by
          have : a.NoSlot ∧ RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toFO] using hF
          exact this.2
        rw [chainO_shr sMT t cms dR w W embS embP i σ0 vs hk ρ0, OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y3 h3 => ?_
        have t3 := FbLt.of_notFb (onlyQ_rootOO t sMT _ _ _) hT y3 h3
        refine (askG_then t w.gr0 hW.1.gr0_ok w.chal
            (fun α => (⟨i, .f5 ρ0, y3.1, embP (.inl (.inl α))⟩ : FbIn lam L t))
            (fun g hg x y e => hq0 g hg (congrArg FbIn.plain e)) _ _ _
            (fun ans => (ublkG s A W).map fun l => (v.blocks ++ [ans.1]) ++ l) y3.2
            (fun β => t3.new _ rfl) fun ans T' hT' => ?_).trans
          (hsh v.blocks hk)
        exact chainO_blocks n s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          (.shr (List.ofFn ans.2)) (σ0.2 (a.kind.shOf (w.chal ans.1))) (vs.map (hearO w ans.1))
          (hearO w ans.1 v) T' hW.2 hE' hF' (by simp [hv]) (t3.left t (fun _ => rfl) hT')

end Rounds

/-! ## 4. From the hash blocks to the verifier randomness -/

theorem pmf_unit_eq (μ ν : PMF Unit) : μ = ν := by
  have h : ∀ p : PMF Unit, p = PMF.pure () := fun p => by
    refine PMF.ext fun u => ?_
    have h := p.tsum_coe
    rw [tsum_fintype] at h
    simpa using h
  rw [h μ, h ν]

/-! ### With proof-of-work bits, under `RoundsQueryLayout.OKG`: the verifier randomness, with these bits set to
0, has the distribution that it has under uniform verifier randomness -/

theorem zeroG_gblk {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hw : w.OKG)
    {P : Type} (gr : Option (GrW r.Chal P)) (hgr : ∀ g, gr = some g → g.OK)
    (z : r.Chal → r.Chal) (hz : ∀ c, z c = zeroG gr c) :
    (gblk gr w.chal).map (fun bl => z (w.chal bl)) = (unif r.Chal).map z := by
  have hu : (unif ((Fin K → Dig lam) × Dig lam)).map (fun x => z (w.chal x.1)) =
      (unif r.Chal).map z := by
    rw [← LoopLaw.chalU w hw, PMF.map_comp]
    rfl
  unfold gblk
  rw [PMF.map_comp]
  cases gr with
  | none => exact hu
  | some g =>
    have h1 := map_retry (fun x : (Fin K → Dig lam) × Dig lam => g.ok (w.chal x.1))
      (fun x => (g.set (fun _ => false) (w.chal x.1), x.2))
      (ok_indep lam K r a w P g hw (hgr g rfl)) g.more
    have h2 := congrArg (PMF.map Prod.fst) h1
    rw [PMF.map_comp, PMF.map_comp] at h2
    have ez : (fun x : (Fin K → Dig lam) × Dig lam => z (w.chal x.1)) =
        Prod.fst ∘
          fun x : (Fin K → Dig lam) × Dig lam => (g.set (fun _ => false) (w.chal x.1), x.2) :=
      funext fun x => hz _
    rw [← hu]
    show (retry _ g.more).map (fun x : (Fin K → Dig lam) × Dig lam => z (w.chal x.1)) = _
    rw [ez]
    exact h2

theorem zero_rblk {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hw : w.OKG) :
    (rblk a w).map (fun bl => w.zero (w.chal bl)) = (unif r.Chal).map w.zero := by
  unfold rblk
  cases hk : a.kind with
  | lo =>
    exact zeroG_gblk w hw w.grJ hw.grJ_ok w.zero fun c => by
      unfold WireRB.zero; rw [hk]; cases w.grJ <;> rfl
  | sh =>
    exact zeroG_gblk w hw w.gr0 hw.gr0_ok w.zero fun c => by
      unfold WireRB.zero; rw [hk]; cases w.gr0 <;> rfl

/-- Under `RoundsQueryLayout.OKG`, the verifier randomness of a slot, with all proof-of-work bits set to 0, has
the distribution that it has under uniform verifier randomness. -/
theorem zero_ublkG :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      (ublkG s A W).map (fun l => RoundsQueryLayout.zero s A W (rhoOf s A W l)) =
        (unif (Rho s)).map (RoundsQueryLayout.zero s A W)
  | [], _, _, _ => pmf_unit_eq _ _
  | r :: s, (a, A), (w, W), hW => by
    have h2 : unif (Rho (r :: s)) = Prob.prod (unif r.Chal) (unif (Rho s)) := unif_prod
    have e1 : (ublkG (r :: s) (a, A) (w, W)).map
          (fun l => RoundsQueryLayout.zero (r :: s) (a, A) (w, W) (rhoOf (r :: s) (a, A) (w, W) l)) =
        ((rblk a w).map fun bl => w.zero (w.chal bl)).bind fun c =>
          ((ublkG s A W).map fun l => RoundsQueryLayout.zero s A W (rhoOf s A W l)).map fun ρ =>
              ((c, ρ) : Rho (r :: s)) := by
      show ((rblk a w).bind fun bl => (ublkG s A W).map fun l => bl :: l).map _ = _
      rw [PMF.map_bind, PMF.bind_map]
      refine congrArg _ (funext fun bl => ?_)
      rw [PMF.map_comp, Function.comp_apply, PMF.map_comp]
      rfl
    have e2 : (unif (Rho (r :: s))).map (RoundsQueryLayout.zero (r :: s) (a, A) (w, W)) =
        ((unif r.Chal).map w.zero).bind fun c =>
          ((unif (Rho s)).map (RoundsQueryLayout.zero s A W)).map fun ρ => ((c, ρ) : Rho (r :: s)) := by
      rw [h2, Prob.prod]
      refine (PMF.map_bind _ _ _).trans ?_
      rw [PMF.bind_map]
      refine congrArg _ (funext fun c => ?_)
      rw [Function.comp_apply, PMF.map_comp]
      exact PMF.map_comp _ _ _
    rw [e1, e2, zero_rblk w hW.1, zero_ublkG s A W hW.2]

/-- without proof-of-work bits (`RoundsQueryLayout.OK`) nothing is set -/
theorem zero_of_ok :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      RoundsQueryLayout.OK s A W → ∀ ρ, RoundsQueryLayout.zero s A W ρ = ρ
  | [], _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), hW, (c, ρ) => by
    have e : w.zero c = c := by
      unfold WireRB.zero
      rw [hW.1.grJ_none, hW.1.gr0_none]
      cases a.kind <;> rfl
    show (w.zero c, RoundsQueryLayout.zero s A W ρ) = (c, ρ)
    rw [e, zero_of_ok s A W hW.2 ρ]

/-- without proof-of-work bits (`RoundsQueryLayout.OK`) every verifier randomness passes -/
theorem pass_of_ok :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      RoundsQueryLayout.OK s A W → ∀ ρ, RoundsQueryLayout.pass s A W ρ = true
  | [], _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), hW, (c, ρ) => by
    have e : w.pass c = true := by
      unfold WireRB.pass
      rw [hW.1.grJ_none, hW.1.gr0_none]
      cases a.kind <;> rfl
    show (w.pass c && RoundsQueryLayout.pass s A W ρ) = true
    rw [e, pass_of_ok s A W hW.2 ρ]
    rfl

/-! ## 5. One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

theorem onlyQ_initO (c0 : H.Coin0) (x : Option Y) :
    OnlyQ (S := spec lam K L) (NotFb t)
      (initO (lam := lam) (K := K) (L := L) sFS Q H wp xin w c0 x) :=
  OnlyQ.bind (onlyQ_drawO t _) fun _ => OnlyQ.bind (onlyQ_freshO t _) fun _ => trivial

theorem supp_initO (c0 : H.Coin0) (x : Option Y) (T : Table (spec lam K L)) :
    ∀ y ∈ ((initO (lam := lam) (K := K) (L := L) sFS Q H wp xin w c0 x).runLazy T).support,
      y.1.blocks = [] := by
  intro y hy
  unfold initO at hy
  rw [OComp.runLazy_bind] at hy
  obtain ⟨y1, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  rw [OComp.runLazy_bind] at hy
  obtain ⟨y2, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hy
  rw [hy]

/-- under the hypotheses below, the hash blocks that slot number n sees in one execution are
independent, each with the distribution of its round -/
theorem blocks_proveOG (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh)
    (hE : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh ∨ Function.Injective embP)
    (hF : Q.ann.Fmt) (xs : List (Option Y)) (n : ℕ) (hn : n < xs.length)
    (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    ((proveO sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map
        (fun x => x.1.getD n []) =
      ublkG Q.loc.shape Q.ann wq.sh := by
  unfold proveO
  rw [OComp.runLazy_bind, PMF.map_bind]
  refine bind_const_supp fun y0 h0 => ?_
  have t0 := FbLt.of_notFb (onlyQ_drawO t wp.coin0) hT y0 h0
  rw [OComp.runLazy_bind, PMF.map_bind]
  refine bind_const_supp fun y1 h1 => ?_
  have t1 := FbLt.of_notFb (onlyQ_eachO (onlyQ_initO sFS t Q H wp xin w y0.1) xs) t0 y1 h1
  obtain ⟨v, e, b⟩ := supp_eachO_entry _ (fun _ (v' : VSlot lam K X Q.loc.shape) => v'.blocks = [])
    (fun a' T' => supp_initO sFS Q H wp xin w y0.1 a' T') n xs xs[n] (List.getElem?_eq_getElem hn)
    y0.2 y1 h1
  rw [chainO_blocks sMT t cms depthReq n Q.loc.shape Q.ann wq.sh embS embP 0 .first _
        y1.1 v y1.2 hW hE hF e t1, b]
  exact PMF.map_id _

/-- Under the hypotheses below, the proof string of a slot is `none` with exactly the probability of
the withheld set, if the withheld set does not depend on the proof-of-work bits. -/
theorem pr_noneAtG (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh)
    (hE : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh ∨ Function.Injective embP) (hF : Q.ann.Fmt)
    (xs : List (Option Y)) (n : ℕ) (hn : n < xs.length) (x : Y)
    (hwh : ∀ ρ, ρ ∈ H.one.withheld w x ↔ RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ H.one.withheld w x)
    (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    pr (((proveO sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
        {bss | noneAt Q H wq wp w x n bss = true} =
      prRho (H.one.withheld w x) := by
  have h := blocks_proveOG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW hE hF xs n hn T hT
  have e : {bss : List (List (Blk lam K)) | noneAt Q H wq wp w x n bss = true} =
      (fun bss : List (List (Blk lam K)) =>
          RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n [])))
        ⁻¹' (H.one.withheld w x) := by
    ext bss
    simp only [noneAt, Set.mem_setOf_eq, decide_eq_true_eq, Set.mem_preimage]
    exact hwh _
  have e2 : prRho (H.one.withheld w x) =
      pr ((unif (Rho Q.loc.shape)).map (RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh))
        (H.one.withheld w x) := by
    rw [pr_map]
    exact congrArg _ (Set.ext fun ρ => hwh ρ)
  rw [e, ← pr_map, PMF.map_comp, e2, ← zero_ublkG Q.loc.shape Q.ann wq.sh hW, ← h, PMF.map_comp]
  rfl

theorem pr_noneAt (hW : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh) (hF : Q.ann.Fmt) (xs : List (Option Y))
    (n : ℕ) (hn : n < xs.length) (x : Y) (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    pr (((proveO sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
        {bss | noneAt Q H wq wp w x n bss = true} =
      prRho (H.one.withheld w x) :=
  pr_noneAtG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW.toG (Or.inl hW) hF xs n hn x
    (fun ρ => by rw [zero_of_ok _ _ _ hW]) T hT

/-- without proof-of-work bits `badAt` (`none`, or a failed search) is `noneAt` (`none`) -/
theorem badAt_of_ok (hW : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh) (x : Y)
    (n : ℕ) (bss : List (List (Blk lam K))) :
    badAt Q H wq wp w x n bss = noneAt Q H wq wp w x n bss := by
  unfold badAt
  rw [pass_of_ok _ _ _ hW]
  simp

end Prove

/-! ## 6. Test and Link on given nodes -/

theorem pr_bind_le {α β : Type} (c : TypedOracleComputation lam K L α) (g : α → TypedOracleComputation lam K L β) (T : Table (spec lam K L))
    (Ev : Set β) (ε : ℝ≥0∞)
    (hg : ∀ x ∈ (c.runLazy T).support, pr (((g x.1).runLazy x.2).map Prod.fst) Ev ≤ ε) :
    pr (((c.bind g).runLazy T).map Prod.fst) Ev ≤ ε := by
  rw [OComp.runLazy_bind, PMF.map_bind]
  exact pr_bind_le_of_forall _ _ _ hg

theorem pr_bind_pure {α β : Type} (c : TypedOracleComputation lam K L α) (h : α → β)
    (T : Table (spec lam K L)) (Ev : Set β) :
    pr (((c.bind fun a => OComp.pure (h a)).runLazy T).map Prod.fst) Ev =
      pr ((c.runLazy T).map Prod.fst) (h ⁻¹' Ev) := by
  rw [OComp.runLazy_bind, PMF.map_bind, ← pr_map, PMF.map_comp]
  simp only [OComp.runLazy, PMF.pure_map]
  rfl

theorem fbLt_empty (t : Tag) : FbLt t 0 (Table.empty (spec lam K L)) := fun _ h => absurd rfl h

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

theorem onlyQ_nodeO (t : Tag) : OnlyQ (S := spec lam W.K L) (NotFb t) (nodeO W WP p i) :=
  OnlyQ.bind (onlyQ_drawO t _) fun _ => OnlyQ.bind (onlyQ_rootEO t _ _ _) fun _ => trivial

theorem pr_testO (hW : W.OK) (nd : L.EncodingRandomness × Dig lam)
    (T : Table (spec lam W.K L)) (hT : FbLt Tag.test 0 T) :
    pr (((testO W WP p i nd).runLazy T).map Prod.fst) {b | b = true} =
      prRho (L.honestOfflineProver.withheld (i, nd.1) ()) := by
  unfold testO
  rw [pr_bind_pure, ← BatchOne.ofHonest_withheld]
  refine Eq.trans (congrArg (pr _) (Set.ext fun bss => ?_))
    (pr_noneAt p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T _
      id _ W.depthReq [nd.2] (i, nd.1) hW.T.sh (RoundSplits.fmt_allLocal _) [some ()] 0 (by simp) () T hT)
  show badAt _ _ _ _ _ _ _ bss = true ↔ noneAt _ _ _ _ _ _ _ bss = true
  rw [badAt_of_ok _ _ _ _ _ hW.T.sh]

theorem pr_linkO (hW : W.OK) (nd0 nd : L.EncodingRandomness × Dig lam)
    (T : Table (spec lam W.K L)) (hT : FbLt Tag.link 0 T) :
    pr (((linkO W WP p i nd0 nd).runLazy T).map Prod.fst) {b | b = true} =
      prRho (L.honestLinkProver.withheld (i, nd0.1, nd.1) ()) := by
  unfold linkO
  rw [pr_bind_pure, ← BatchOne.ofHonest_withheld]
  refine Eq.trans (congrArg (pr _) (Set.ext fun bss => ?_))
    (pr_noneAt p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver)
      W.Lk WP.Lk _ id _ W.depthReq [nd0.2, nd.2] (i, nd0.1, nd.1) hW.Lk.sh
      (RoundSplits.fmt_allLocal _) [some ()] 0 (by simp) () T hT)
  show badAt _ _ _ _ _ _ _ bss = true ↔ noneAt _ _ _ _ _ _ _ bss = true
  rw [badAt_of_ok _ _ _ _ _ hW.Lk.sh]

end Scheme

end Compile.Batch.CompleteUnif
