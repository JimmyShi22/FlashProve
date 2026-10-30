-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Extraction.lean: general tools on the runs of an algorithm within a trace, on the queries of
a Merkle tree in a trace, and on the number of a program's queries. No scheme occurs in this file;
Compile/Batch/Extraction.lean applies the tools to the honest committer.
  `OutsIn f tr c`      the values that the algorithm c can return under the oracle functions f on
                       paths all of whose queries, with their answers, are entries of the trace tr
                       (`outsIn_of_withTrace`: the trace that an algorithm returns beside its output
                       holds all its queries)
  `TriI f tr c vs Q`   the postcondition `Tri` (Compile/EraseKit.lean) for the runs of an erased
                       program (`erase`, Compile/Star.lean) all of whose queries are entries of tr,
                       with a rule for `bind` and for five constructors of `Step` (Rom/Defer.lean)
  `climbsIn_pathOf`    if the trace holds all node queries of a tree over 2^d digests (`PairsIn`,
                       `LevelsIn`), the path of every leaf leads to the root within the trace
                       (`ClimbsIn`, Compile/MerkleList.lean)
  `SQ c m P`           on every path, whatever the answers, the program c makes at most m queries,
                       and its result has the property P (`SQ.erase`: the erased program makes at
                       most m queries)
-/
import Compile.CompleteAcc
import Compile.HashEvents
import Rom.Prefix

noncomputable section

namespace Compile.Extr
open Iop Rom Prob Merkle Compile.Cmpl
open scoped ENNReal

/-! ## Part 1. Runs within a trace -/

section OutsIn

variable {S : OSpec} {α β : Type}

/-- The values that the algorithm can return under the oracle functions f on paths all of whose
queries, with their answers, are entries of the trace tr. -/
def OutsIn (f : Fam S) (tr : Trace S) : OComp S α → Set α
  | .pure a => {a}
  | .query o q k => {b | (⟨o, q, f o q⟩ : QA S) ∈ tr ∧ b ∈ OutsIn f tr (k (f o q))}
  | .sample _ k => {b | ∃ r, b ∈ OutsIn f tr (k r)}

variable {f : Fam S} {tr tr' : Trace S}

theorem OutsIn.mono (hs : tr ⊆ tr') {c : OComp S α} {b : α} (h : b ∈ OutsIn f tr c) :
    b ∈ OutsIn f tr' c := by
  induction c with
  | pure a => exact h
  | query o q k ih => exact ⟨hs h.1, ih _ h.2⟩
  | sample n k ih => obtain ⟨r, hr⟩ := h; exact ⟨r, ih r hr⟩

theorem outs_of_outsIn {c : OComp S α} {b : α} (h : b ∈ OutsIn f tr c) : b ∈ Outs f c := by
  induction c with
  | pure a => exact mem_outs_pure.2 h
  | query o q k ih => exact mem_outs_query.2 (ih _ h.2)
  | sample n k ih => obtain ⟨r, hr⟩ := h; exact mem_outs_sample.2 ⟨r, ih r hr⟩

theorem mem_outsIn_bind {c : OComp S α} {g : α → OComp S β} {b : β} :
    b ∈ OutsIn f tr (c.bind g) ↔ ∃ a ∈ OutsIn f tr c, b ∈ OutsIn f tr (g a) := by
  induction c with
  | pure a =>
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨a', rfl, h⟩; exact h
  | query o q k ih =>
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a, ha, hb⟩ := (ih _).1 h2
      exact ⟨a, ⟨h1, ha⟩, hb⟩
    · rintro ⟨a, ⟨h1, ha⟩, hb⟩
      exact ⟨h1, (ih _).2 ⟨a, ha, hb⟩⟩
  | sample n k ih =>
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨a, ha, hb⟩ := (ih r).1 hr
      exact ⟨a, ⟨r, ha⟩, hb⟩
    · rintro ⟨a, ⟨r, ha⟩, hb⟩
      exact ⟨r, (ih r).2 ⟨a, ha, hb⟩⟩

/-- The trace that an algorithm returns beside its output holds all its queries. -/
theorem outsIn_of_withTrace {c : OComp S α} :
    ∀ {o : α × Trace S}, o ∈ Outs f c.withTrace → o.1 ∈ OutsIn f o.2 c := by
  induction c with
  | pure a =>
    intro o ho
    rw [mem_outs_pure.1 (show o ∈ Outs f (OComp.pure (a, [])) from ho)]
    rfl
  | query o q k ih =>
    intro x hx
    have hx' : x ∈
        Outs f ((k (f o q)).withTrace.bind fun out =>
            OComp.pure (out.1, (⟨o, q, f o q⟩ : QA S) :: out.2)) := hx
    obtain ⟨out, hout, hx''⟩ := mem_outs_bind.1 hx'
    rw [mem_outs_pure.1 hx'']
    exact ⟨List.mem_cons_self, OutsIn.mono (List.subset_cons_self _ _) (ih _ hout)⟩
  | sample n k ih =>
    intro x hx
    obtain ⟨r, hr⟩ :=
      mem_outs_sample.1 (show x ∈ Outs f (OComp.sample n fun r => (k r).withTrace) from hx)
    exact ⟨r, ih r hr⟩

end OutsIn

section TriI

variable {S : OSpec} {sp : Split S} {α β : Type} {f : Fam S} {tr : Trace S}

/-- Postcondition for the runs of an erased program all of whose queries are entries of tr. -/
def TriI (f : Fam S) (tr : Trace S) (c : Step S sp α) (vs : List Bits) (Q : α → List Bits → Prop) :
    Prop :=
  ∀ o ∈ OutsIn f tr (erase c vs), Q o.1 o.2

theorem TriI.of_tri {c : Step S sp α} {vs : List Bits}
    {Q : α → List Bits → Prop} (h : Tri f c vs Q) : TriI f tr c vs Q :=
  fun o ho => h o (outs_of_outsIn ho)

theorem TriI.and {c : Step S sp α} {vs : List Bits} {Q R : α → List Bits → Prop}
    (h : TriI f tr c vs Q) (h' : TriI f tr c vs R) :
    TriI f tr c vs fun a vs' => Q a vs' ∧ R a vs' :=
  fun o ho => ⟨h o ho, h' o ho⟩

theorem TriI.mono {c : Step S sp α} {vs : List Bits} {Q R : α → List Bits → Prop}
    (h : TriI f tr c vs Q) (hQR : ∀ a vs', Q a vs' → R a vs') : TriI f tr c vs R :=
  fun o ho => hQR _ _ (h o ho)

theorem triI_pure_iff {a : α} {vs : List Bits} {Q : α → List Bits → Prop} :
    TriI f tr (Step.pure a : Step S sp α) vs Q ↔ Q a vs := by
  constructor
  · intro h; exact h (a, vs) rfl
  · rintro h o rfl; exact h

theorem TriI.bind {c : Step S sp α} {g : α → Step S sp β} {vs : List Bits}
    {Q : α → List Bits → Prop} {R : β → List Bits → Prop} (h : TriI f tr c vs Q)
    (hg : ∀ a vs', Q a vs' → TriI f tr (g a) vs' R) : TriI f tr (c.bind g) vs R := by
  intro o ho
  rw [erase_bind] at ho
  obtain ⟨x, hx, hox⟩ := mem_outsIn_bind.1 ho
  exact hg x.1 x.2 (h x hx) o hox

theorem triI_sample {n : ℕ} {k : Fin (n + 1) → Step S sp α} {vs : List Bits}
    {Q : α → List Bits → Prop} (h : ∀ r, TriI f tr (k r) vs Q) :
    TriI f tr (Step.sample n k) vs Q := by
  rintro o ⟨r, ho⟩; exact h r o ho

theorem triI_plain {o : S.ι} {q : S.Dom o} {k : S.Rng o → Step S sp α} {vs : List Bits}
    {Q : α → List Bits → Prop} (h : (⟨o, q, f o q⟩ : QA S) ∈ tr → TriI f tr (k (f o q)) vs Q) :
    TriI f tr (Step.plain o q k) vs Q := by
  rintro x ⟨h1, hx⟩; exact h h1 x hx

theorem triI_fresh {l : ℕ} {k : Tok → Step S sp α} {vs : List Bits} {Q : α → List Bits → Prop}
    (h : ∀ r : Fin (2 ^ l - 1 + 1),
      TriI f tr (k vs.length) (vs ++ [List.ofFn fun i : Fin l => r.val.testBit i]) Q) :
    TriI f tr (Step.fresh l k) vs Q := by
  rintro o ⟨r, ho⟩; exact h r o ho

theorem triI_marked {o : S.ι} {t : Tok} {us : List Tok} {pt : Bits → List Bits → S.Dom o}
    {inj : ∀ vs, Function.Injective fun v => pt v vs} {k : sp.Vis o → Tok → Step S sp α}
    {vs : List Bits} {Q : α → List Bits → Prop}
    (h : (⟨o, pt (vs.getD t []) (us.map fun u => vs.getD u []),
          f o (pt (vs.getD t []) (us.map fun u => vs.getD u []))⟩ : QA S) ∈ tr →
      TriI f tr
        (k (sp.split o (f o (pt (vs.getD t []) (us.map fun u => vs.getD u [])))).1 vs.length)
        (vs ++ [List.ofFn (sp.split o (f o (pt (vs.getD t []) (us.map fun u => vs.getD u [])))).2])
        Q) :
    TriI f tr (Step.marked o t us pt inj k) vs Q := by
  rintro x ⟨h1, hx⟩; exact h h1 x hx

theorem triI_true (c : Step S sp α) (vs : List Bits) : TriI f tr c vs fun _ _ => True := fun _ _ =>
  trivial

end TriI

/-! ## Part 2. The trace holds the queries of a tree -/

section Levels

variable {E D X : Type} {Ev : Events E D} (V : OraclePair Ev X) (hN : D → D → D) [Inhabited D]

/-- All node queries of one step from a level to the next are entries of the trace. -/
def PairsIn (tr : List E) (l : List D) : Prop :=
  ∀ i, 2 * i + 1 < l.length →
    ∃ e ∈ tr, V.node e =
      some ((l.getD (2 * i) default, l.getD (2 * i + 1) default),
          hN (l.getD (2 * i) default) (l.getD (2 * i + 1) default))

/-- All node queries of d steps are entries of the trace. -/
def LevelsIn (tr : List E) : ℕ → List D → Prop
  | 0, _ => True
  | d + 1, l => PairsIn V hN tr l ∧ LevelsIn tr d (pairUpF hN l)

/-- If the trace holds all node queries of a tree over 2^d digests (`l.length = 2 ^ d`), the path of
every leaf j < 2^d leads to the root within the trace (`ClimbsIn`). -/
theorem climbsIn_pathOf {tr : List E} :
    ∀ (d : ℕ) (l : List D) (j : ℕ), LevelsIn V hN tr d l → l.length = 2 ^ d → j < 2 ^ d →
      ClimbsIn V tr (pathOf (levelsF hN d l) j) j (l.getD j default) (rootOf (levelsF hN d l))
  | 0, l, j, _, hl, hj => by
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      match l, hl with
      | [a], _ => rfl
  | d + 1, l, j, hin, hl, hj => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      have hl2 : l.length = 2 * 2 ^ d := by rw [hl, pow_succ, Nat.mul_comm]
      have hj2 : j / 2 < 2 ^ d :=
        Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at hj; exact hj)
      have ih := climbsIn_pathOf d (pairUpF hN l) (j / 2) hin.2 (length_pairUpF hN _ l hl2) hj2
      have hg := getD_pairUpF hN l (j / 2) (by omega)
      obtain ⟨e, he, hev⟩ := hin.1 (j / 2) (by omega)
      rw [levelsF_succ, hls, pathOf_cons₂, rootOf_cons₂, ← hls]
      refine ⟨(pairUpF hN l).getD (j / 2) default, ⟨e, he, ?_⟩, ih⟩
      rw [hev, hg]
      by_cases hb : j % 2 = 0
      · have e1 : 2 * (j / 2) = j := by omega
        simp only [if_pos hb, e1]
      · have e1 : 2 * (j / 2) + 1 = j := by omega
        have e2 : 2 * (j / 2) = j - 1 := by omega
        rw [if_neg hb, if_neg hb, e1, e2]

end Levels

variable {I X : Type} {lam K : ℕ}

/-! ## Part 3. The number of a program's queries -/

section SQ

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- On every path, whatever the answers, the program makes at most m queries, and its result has the
property P. -/
def SQ : Step S sp α → ℕ → (α → Prop) → Prop
  | .pure a, _, P => P a
  | .sample _ k, m, P => ∀ r, SQ (k r) m P
  | .plain _ _ k, m, P => ∃ m', m = m' + 1 ∧ ∀ r, SQ (k r) m' P
  | .fresh _ k, m, P => ∀ t, SQ (k t) m P
  | .marked _ _ _ _ _ k, m, P => ∃ m', m = m' + 1 ∧ ∀ v t, SQ (k v t) m' P
  | .reveal _ k, m, P => ∀ vs, SQ (k vs) m P

theorem SQ.mono {c : Step S sp α} {P P' : α → Prop} (hP : ∀ a, P a → P' a) :
    ∀ {m m' : ℕ}, m ≤ m' → SQ c m P → SQ c m' P' := by
  induction c with
  | pure a => exact fun _ h => hP a h
  | sample n k ih => exact fun hm h r => ih r hm (h r)
  | plain o q k ih =>
    rintro m m' hm ⟨m0, rfl, h⟩
    exact ⟨m' - 1, by omega, fun r => ih r (by omega) (h r)⟩
  | fresh l k ih => exact fun hm h t => ih t hm (h t)
  | marked o t us pt inj k ih =>
    rintro m m' hm ⟨m0, rfl, h⟩
    exact ⟨m' - 1, by omega, fun v t => ih v t (by omega) (h v t)⟩
  | reveal ts k ih => exact fun hm h vs => ih vs hm (h vs)

theorem SQ.bind {c : Step S sp α} {g : α → Step S sp β} {P : α → Prop} {Q : β → Prop} {m' : ℕ}
    (hg : ∀ a, P a → SQ (g a) m' Q) : ∀ {m : ℕ}, SQ c m P → SQ (c.bind g) (m + m') Q := by
  induction c with
  | pure a => exact fun h => (hg a h).mono (fun _ h => h) (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | plain o q k ih =>
    rintro m ⟨m0, rfl, h⟩
    exact ⟨m0 + m', by omega, fun r => ih r (h r)⟩
  | fresh l k ih => exact fun h t => ih t (h t)
  | marked o t us pt inj k ih =>
    rintro m ⟨m0, rfl, h⟩
    exact ⟨m0 + m', by omega, fun v t => ih v t (h v t)⟩
  | reveal ts k ih => exact fun h vs => ih vs (h vs)

theorem SQ.erase {c : Step S sp α} {P : α → Prop} :
    ∀ {m : ℕ}, SQ c m P → ∀ vs, (erase c vs).QueryBound m := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun h vs r => ih r (h r) vs
  | plain o q k ih =>
    rintro m ⟨m0, rfl, h⟩ vs
    exact fun r => ih r (h r) vs
  | fresh l k ih => exact fun h vs r => ih _ (h _) _
  | marked o t us pt inj k ih =>
    rintro m ⟨m0, rfl, h⟩ vs
    exact fun r => ih _ _ (h _ _) _
  | reveal ts k ih => exact fun h vs => ih _ (h _) vs

theorem SQ.bind' {c : Step S sp α} {g : α → Step S sp β} {P : α → Prop} {Q : β → Prop} {m m' n : ℕ}
    (hc : SQ c m P) (hg : ∀ a, P a → SQ (g a) m' Q) (hn : m + m' ≤ n) : SQ (c.bind g) n Q :=
  (SQ.bind hg hc).mono (fun _ h => h) hn

end SQ

local notation "T1" => fun _ => True

end Compile.Extr

