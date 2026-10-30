-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/OverOneN.lean: the step to one hash function in which only marked hash blocks of an answer are
queried (other files call this step the second exit).

Rom/Family.lean implements a family S of oracles, whose answers are tuples of hash blocks of lam
bits, by one hash function f: hash block j of the answer of o at q is f (code o q j), and
`OComp.overOne` queries f for all hash blocks of every query. Here a function `need` of the oracle,
the query and j marks hash blocks, and `OComp.overOneN` queries f for the marked ones only; an
unmarked one is the all-zero block `dig0`. The file is generic in S and in the query encoding m
(`OracleCoding`). Nothing of Rom/Family.lean changes: an answer is split by `m.rng o` and joined by
`(m.rng o).symm`, as there.

What is proved and what is not. With all hash blocks marked, `overOneN` is `overOne`, as a program
(Section 5). That the two have the same output distribution if the program reads no unmarked hash
block is not proved in this library. For the number of queries to f there is an upper bound (Section
6). No theorem compares the numbers of queries of the two, and none says that the marked hash blocks
are those that a program needs: that is the condition `FactorsBy (Agree m need)`; Section 5 has
lemmas that give it (for bind, query, pure and sample, for a relation contained in ag, for
equality). Section 7 has lemmas on traces (`singleTr`, Rom/ExitDown.lean: the entries at one-block
oracles).

Limits: the all-zero block can appear in the output: a program that returns an unmarked hash block
returns `dig0` whatever the hash function f is. The theorems `overOneN_all`, `overOneN_bind`
(`overOneN` commutes with bind) and `queryBound_overOneN` are about the program and its queries, not
about what it returns.
-/
import Rom.Cost
import Rom.ExitDown

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {lam : ℕ} {α β : Type}

/-! ## 1. The step -/

/-- Which hash blocks of the answer to a query are marked: these are queried. -/
abbrev Need (m : OracleCoding S lam) : Type := (o : S.ι) → S.Dom o → Fin (m.blocks o) → Bool

/-- the all-zero block, which replaces a hash block that is not queried -/
def dig0 (lam : ℕ) : Fin lam → Bool := fun _ => false

/-- query f at those of n strings that are flagged, one after the other, in the order of `askAll`
(Rom/Family.lean); the all-zero block at the others -/
def askSome (lam : ℕ) :
    (n : ℕ) → (Fin n → Bool) → (Fin n → List Bool) → OComp (rom lam) (Fin n → Fin lam → Bool)
  | 0, _, _ => .pure fun i => i.elim0
  | n + 1, nd, g =>
      match nd 0 with
      | true => .query (S := rom lam) () (g 0) fun r =>
          (askSome lam n (fun i => nd i.succ) fun i => g i.succ).bind fun rest =>
            .pure (Fin.cons (α := fun _ => Fin lam → Bool) r rest)
      | false =>
        (askSome lam n (fun i => nd i.succ) fun i => g i.succ).bind fun rest =>
          .pure (Fin.cons (α := fun _ => Fin lam → Bool) (dig0 lam) rest)

/-- The same algorithm over the hash function, querying only the marked hash blocks. The hash blocks
are joined as in `OComp.overOne`: by `(m.rng o).symm`. -/
def OComp.overOneN (m : OracleCoding S lam) (need : Need m) : OComp S α → OComp (rom lam) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).overOneN m need
  | .query o q k =>
    (askSome lam (m.blocks o) (need o q) (m.code o q)).bind fun bs =>
      (k ((m.rng o).symm bs)).overOneN m need

/-! ## 2. The condition -/

/-- The program reads an answer only up to a relation ag on answers: at every query node, answers in
the relation have the same continuation program; and so on in every continuation. (The relation is a
parameter, and m does not occur: so the condition can be proved for a relation that is stated on the
answers of a particular family, and carried to `Agree m need` afterwards by `FactorsBy.mono`.) -/
def OComp.FactorsBy (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop) : OComp S α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, (k r).FactorsBy ag
  | .query o q k => (∀ r r', ag o q r r' → k r = k r') ∧ ∀ r, (k r).FactorsBy ag

/-- two answers to the query (o, q) agree on the marked hash blocks; the hash blocks of an answer
are what m's own splitting gives: `m.rng o` -/
def Agree (m : OracleCoding S lam) (need : Need m) (o : S.ι) (q : S.Dom o) (r r' : S.Rng o) : Prop :=
  ∀ j, need o q j = true → m.rng o r j = m.rng o r' j

/-! ## 3. Costs -/

/-- the number of flagged indices among n -/
def cnt : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, nd => (if nd 0 then 1 else 0) + cnt n fun i => nd i.succ

/-- the number of marked hash blocks of a query -/
def Need.num {m : OracleCoding S lam} (need : Need m) (o : S.ι) (q : S.Dom o) : ℕ :=
  cnt (m.blocks o) (need o q)

/-- On every path, whatever the answers and the coins, the weights w o q of the queries add up to at
most t. (`OComp.CostBound` of Rom/Cost.lean with a weight that may depend on the query.) -/
def OComp.CostBoundAt (w : (o : S.ι) → S.Dom o → ℕ) : OComp S α → ℕ → Prop
  | .pure _, _ => True
  | .sample _ k, t => ∀ r, (k r).CostBoundAt w t
  | .query o q k, t => ∃ t', t = w o q + t' ∧ ∀ r, (k r).CostBoundAt w t'

/-! ## 4. The run under a fixed hash function -/

/-- the hash blocks that `askSome` returns: the true answer at a flagged index, the all-zero block
at the others -/
def valSome (g : Fam (rom lam)) {n : ℕ} (nd : Fin n → Bool) (pts : Fin n → List Bool) :
    Fin n → Fin lam → Bool :=
  fun j => if nd j then g () (pts j) else dig0 lam

/-- Under a fixed hash function g the run of `askSome` returns `valSome g nd pts`. -/
theorem runEager_askSome (g : Fam (rom lam)) :
    ∀ (n : ℕ) (nd : Fin n → Bool) (pts : Fin n → List Bool),
      (askSome lam n nd pts).runEager g = PMF.pure (valSome g nd pts)
  | 0, _, _ => by
    simp only [askSome, OComp.runEager]
    congr 1; funext j; exact j.elim0
  | n + 1, nd, pts => by
    have ih := runEager_askSome g n (fun i => nd i.succ) fun i => pts i.succ
    unfold askSome
    cases h : nd 0
    · simp only [OComp.runEager_bind, ih]
      refine (PMF.pure_bind _ _).trans ?_
      try simp only [OComp.runEager]
      congr 1; funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [valSome, h]
      · rfl
    · simp only [OComp.runEager, OComp.runEager_bind, ih]
      refine (PMF.pure_bind _ _).trans ?_
      try simp only [OComp.runEager]
      congr 1; funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [valSome, h]
      · rfl

/-- the hash blocks that `overOneN` joins at the query (o, q) agree with the true answer on the
marked hash blocks -/
theorem agree_some (m : OracleCoding S lam) (need : Need m) (g : Fam (rom lam)) (o : S.ι) (q : S.Dom o) :
    Agree m need o q ((m.rng o).symm (valSome g (need o q) (m.code o q))) (readBlocks m g o q) := by
  intro j hj
  unfold readBlocks valSome
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, if_pos hj]
  rfl


/-! ## 5. Programs -/

theorem askSome_all :
    ∀ (n : ℕ) (pts : Fin n → List Bool), askSome lam n (fun _ => true) pts = askAll lam n pts
  | 0, _ => rfl
  | n + 1, pts => by
    unfold askSome askAll
    simp only [askSome_all n]

/-- With all hash blocks marked, `overOneN` is `overOne`, as a program. -/
theorem overOneN_all (m : OracleCoding S lam) (c : OComp S α) :
    c.overOneN m (fun _ _ _ => true) = c.overOne m := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.overOneN, OComp.overOne, ih]
  | query o q k ih => simp only [OComp.overOneN, OComp.overOne, ih, askSome_all]

theorem overOneN_bind (m : OracleCoding S lam) (need : Need m) (c : OComp S α) (g : α → OComp S β) :
    (c.bind g).overOneN m need = (c.overOneN m need).bind fun a => (g a).overOneN m need := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, OComp.overOneN, ih]
  | query o q k ih => simp only [OComp.bind, OComp.overOneN, ih, OComp.bind_assoc]

namespace OComp.FactorsBy

variable {ag ag' : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}

theorem bind {c : OComp S α} {g : α → OComp S β}
    (h : c.FactorsBy ag) (hg : ∀ a, (g a).FactorsBy ag) : (c.bind g).FactorsBy ag := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact fun r => ih r (h r)
  | query o q k ih =>
    exact ⟨fun r r' hr => congrArg (fun c => c.bind g) (h.1 r r' hr), fun r => ih r (h.2 r)⟩

/-- If every pair of answers that ag' relates is related by ag, the condition for ag gives the
condition for ag'. -/
theorem mono {c : OComp S α} (hag : ∀ o q r r', ag' o q r r' → ag o q r r') (h : c.FactorsBy ag) :
    c.FactorsBy ag' := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r (h r)
  | query o q k ih => exact ⟨fun r r' hr => h.1 r r' (hag o q r r' hr), fun r => ih r (h.2 r)⟩

/-- a query whose continuation goes through a function of the answer that respects the relation
(not all hypotheses are named here: see the statement below) -/
theorem query {γ : Type} (o : S.ι) (q : S.Dom o) {rd : S.Rng o → γ} {k : γ → OComp S α}
    (hrd : ∀ r r', ag o q r r' → rd r = rd r') (hk : ∀ x, (k x).FactorsBy ag) :
    (OComp.query o q fun r => k (rd r)).FactorsBy ag :=
  ⟨fun r r' hr => congrArg k (hrd r r' hr), fun r => hk (rd r)⟩

theorem pure (a : α) : (OComp.pure a : OComp S α).FactorsBy ag := trivial

theorem sample (n : ℕ) {k : Fin (n + 1) → OComp S α} (hk : ∀ r, (k r).FactorsBy ag) :
    (OComp.sample n k).FactorsBy ag := hk

/-- every program factors by equality -/
theorem eq (c : OComp S α) : c.FactorsBy fun _ _ r r' => r = r' := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact ih
  | query o q k ih => exact ⟨fun r r' hr => by rw [hr], ih⟩

end OComp.FactorsBy

/-- agreement of two joined answers on the marked hash blocks is agreement, on the marked ones, of
the hash blocks before they are joined -/
theorem agree_symm (m : OracleCoding S lam) (need : Need m) (o : S.ι) (q : S.Dom o)
    (b b' : Fin (m.blocks o) → Fin lam → Bool) :
    Agree m need o q ((m.rng o).symm b) ((m.rng o).symm b') ↔
    ∀ j, need o q j = true → b j = b' j := by
  unfold Agree
  simp only [Equiv.apply_symm_apply]


/-! ## 6. Queries to f -/

theorem cnt_le : ∀ (n : ℕ) (nd : Fin n → Bool), cnt n nd ≤ n
  | 0, _ => le_rfl
  | n + 1, nd => by
    have := cnt_le n fun i => nd i.succ
    unfold cnt
    split_ifs <;> omega

theorem cnt_eq :
    ∀ (n : ℕ) (nd : Fin n → Bool), cnt n nd = (Finset.univ.filter fun j => nd j = true).card
  | 0, _ => rfl
  | n + 1, nd => by
    rw [Fin.card_filter_univ_succ, ← cnt_eq n fun i => nd i.succ]
    show (if nd 0 then 1 else 0) + cnt n (fun i => nd i.succ) = _
    split_ifs <;> omega

theorem cnt_all (n : ℕ) : cnt n (fun _ => true) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if true = true then 1 else 0) + cnt n (fun _ => true) = n + 1
    rw [ih, if_pos rfl, Nat.add_comm]

theorem queryBound_askSome :
    ∀ (n : ℕ) (nd : Fin n → Bool) (pts : Fin n → List Bool),
      (askSome lam n nd pts).QueryBound (cnt n nd)
  | 0, _, _ => trivial
  | n + 1, nd, pts => by
    have ih := queryBound_askSome n (fun i => nd i.succ) fun i => pts i.succ
    unfold askSome cnt
    cases h : nd 0
    · have := ih.bind (t := 0)
        (g := fun rest =>
            (OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) (dig0 lam) rest) :
              OComp (rom lam) (Fin (n + 1) → Fin lam → Bool))) fun _ => trivial
      simpa using this
    · have e : (if (true : Bool) = true then 1 else 0) + cnt n (fun i => nd i.succ) =
          cnt n (fun i => nd i.succ) + 1 := by
        rw [if_pos rfl, Nat.add_comm]
      rw [e]
      intro r
      have := ih.bind (t := 0)
        (g := fun rest =>
            (OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) r rest) :
              OComp (rom lam) (Fin (n + 1) → Fin lam → Bool))) fun _ => trivial
      simpa using this

namespace OComp.CostBoundAt

variable {w : (o : S.ι) → S.Dom o → ℕ}

theorem mono {c : OComp S α} : ∀ {s t : ℕ}, c.CostBoundAt w s → s ≤ t → c.CostBoundAt w t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun h hst r => ih r (h r) hst
  | query o q k ih =>
    rintro s t ⟨s', rfl, h⟩ hst
    exact ⟨t - w o q, by omega, fun r => ih r (h r) (by omega)⟩

theorem bind {c : OComp S α} {g : α → OComp S β} {t : ℕ} (hg : ∀ a, (g a).CostBoundAt w t) :
    ∀ {s : ℕ}, c.CostBoundAt w s → (c.bind g).CostBoundAt w (s + t) := by
  induction c with
  | pure a => exact fun _ => (hg a).mono (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro s ⟨s', rfl, h⟩
    exact ⟨s' + t, by omega, fun r => ih r (h r)⟩

theorem pure (a : α) (t : ℕ) : (OComp.pure a : OComp S α).CostBoundAt w t := trivial

theorem ask (o : S.ι) (q : S.Dom o) : (OComp.ask o q).CostBoundAt w (w o q) :=
  ⟨0, rfl, fun _ => trivial⟩

/-- A bound for a weight that does not depend on the query (`OComp.CostBound`, Rom/Cost.lean) gives
`CostBoundAt`. -/
theorem of_costBound {v : S.ι → ℕ} {c : OComp S α} :
    ∀ {t : ℕ}, c.CostBound v t → c.CostBoundAt (fun o _ => v o) t := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro t ⟨t', rfl, h⟩
    exact ⟨t', rfl, fun r => ih r (h r)⟩

end OComp.CostBoundAt

/-- The queries to the hash function: if on every path of c the numbers of marked hash blocks of its
queries add up to at most t (`CostBoundAt need.num`), then `c.overOneN m need` makes at most t
queries. -/
theorem queryBound_overOneN (m : OracleCoding S lam) (need : Need m) (c : OComp S α)
    (t : ℕ) (h : c.CostBoundAt need.num t) :
    (c.overOneN m need).QueryBound t := by
  induction c generalizing t with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r t (h r)
  | query o q k ih =>
    obtain ⟨t', rfl, h⟩ := h
    exact (queryBound_askSome (lam := lam) (m.blocks o) (need o q) (m.code o q)).bind
      (g := fun bs => (k ((m.rng o).symm bs)).overOneN m need) fun bs => ih _ t' (h _)

/-! ## 7. Traces -/

private theorem bind_pure' (c : OComp S α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, ih]
  | query o q k ih => simp only [OComp.bind, ih]

theorem withTrace_bind (c : OComp S α) (k : α → OComp S β) :
    (c.bind k).withTrace =
      c.withTrace.bind fun out =>
        (k out.1).withTrace.bind fun out' => .pure (out'.1, out.2 ++ out'.2) := by
  induction c with
  | pure a => exact (bind_pure' (k a).withTrace).symm
  | sample n f ih => simp only [OComp.bind, OComp.withTrace, ih]
  | query o q f ih =>
    simp only [OComp.bind, OComp.withTrace, ih, OComp.bind_assoc]
    rfl


theorem singleTr_append (m : OracleCoding S lam) (a b : Trace (rom lam)) :
    singleTr m (a ++ b) = singleTr m a ++ singleTr m b :=
  List.filterMap_append


theorem singleTr_one (m : OracleCoding S lam) (s : List Bool) (r : Fin lam → Bool) :
    singleTr m [⟨(), s, r⟩] =
      if m.blocks (m.dec s).1 = 1 then
        [⟨(m.dec s).1, (m.dec s).2.1, (m.rng (m.dec s).1).symm fun _ => r⟩]
      else [] := by
  simp only [singleTr, List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> rfl


end Rom

