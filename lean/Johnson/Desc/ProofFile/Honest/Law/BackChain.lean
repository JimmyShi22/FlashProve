-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/BackChain.lean: one chain's typed transcript (the library's
`Iop.Tr`), computed from the rounds as produced, and compared with the transcript that is computed
from what the rounds show. Where the walk (`walk`, Honest/Walk.lean) over a chain's `Step`s returns,
the transcript that the strategies' chain writes (`trOfC`, Honest/Law/StratChainC.lean) is, message
by message, the typed message of the round as produced (`trLaid`): this is `trOfC_laid`. That
transcript and the one computed from what the rounds show (`trOff`, Honest/Law/Rule/Back.lean) have
the same plain parts (`laid_plains`), and the same symbol at every position of a tree that is listed
among the positions shown (`laid_read`). Both take as a hypothesis that at least as many rounds were
produced as are declared; `laid_read` also that each round produced has as many tables as its
declared round has trees.

What this is. Lemmas about this folder's own strategies and about a function of Honest/Law/Rule/
(`trOff`): equations between typed transcripts. They are none of the library's goals.

  1  `trLaid`, `trOfC_laid`   the chain's transcript, from the rounds as produced
  2  `laid_plains`   the plain parts
  3  `lookup_cols`, `orc_eq`, `laid_read`   a symbol at a listed position

Limits.
  * At a position that is not listed the two transcripts may differ.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratWalk
import Johnson.Desc.ProofFile.Honest.Law.Rule.Back
import Johnson.Desc.ProofFile.Honest.Law.Rule.Shown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT roundT drawnT posAtT posAtST posAtST_cons PosT SymT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-! ## 1 The chain's transcript, from the rounds as produced -/

/-- A chain's typed transcript, computed from rounds as produced and the typed challenges: each
message is the typed message of the round's items and tables. Where fewer rounds were produced than
are declared, the message is the round's fixed substitute (`msgOf C d none`, Honest/Strat.lean);
rounds produced beyond the declared ones are not read. -/
def trLaid (C : CK) : (ds : List RDT) → List Played → Iop.Rho (uLT C ds) → Iop.Tr (uLT C ds)
  | [], _, _ => ()
  | d :: ds, ps, (c, ρ) =>
    (msgOf C d (ps.head?.map fun p => ⟨p.vals, p.tables, p.told⟩), c, trLaid C ds ps.tail ρ)

/-- **The strategies' chain writes the rounds as the walk produces them.** -/
theorem trOfC_laid (C : CK) (L : Lay) (left : List (Step W Y)) : ∀ (ds : List RDT)
    (ss : List (Step W Y)) (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds)) (z' : ChainProgress S Cl W Y),
    walk L ss (drawnT C ds ρ) z = .ok z' →
    ∃ ps, z'.laid = z.laid ++ ps ∧ ps.length = ds.length ∧
      trOfC C L ds (ss ++ left) z ρ = trLaid C ds ps ρ
  | [], [], z, ρ, z', hw => by
    have hw' : walk L ([] : List (Step W Y)) [] z = .ok z' := hw
    rw [walk_nil_ok hw']
    exact ⟨[], (List.append_nil _).symm, rfl, rfl⟩
  | [], _ :: _, _, _, _, hw => by
    have hw' : walk L (_ :: _) [] _ = .ok _ := hw
    simp [walk] at hw'
  | d :: ds, [], _, (c, ρ), _, hw => by
    have hw' : walk L ([] : List (Step W Y)) (drOf C d c :: drawnT C ds ρ) _ = .ok _ := hw
    simp [walk] at hw'
  | d :: ds, s :: ss, z, (c, ρ), z', hw => by
    have hw' : walk L (s :: ss) (drOf C d c :: drawnT C ds ρ) z = .ok z' := hw
    obtain ⟨x, z₁, hx, hz₁, hw₁⟩ := walk_cons_ok hw'
    obtain ⟨ps, ih0, ih1, ih2⟩ := trOfC_laid C L left ds ss z₁ ρ z' hw₁
    refine ⟨⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, drOf C d c⟩ :: ps, ?_,
      by rw [List.length_cons, List.length_cons, ih1], ?_⟩
    · rw [ih0, heard_laid hz₁, List.append_assoc]
      rfl
    · show ((msgOf C d (tellC z (some s)), c, trOfC C L ds (ss ++ left)
        (progressAfterChallenge L z (some s) (drOf C d c)) ρ) : Iop.Tr (uLT C (d :: ds))) =
        ((msgOf C d (some ⟨x.vals, x.tables, x.told⟩), c, trLaid C ds ps ρ) :
          Iop.Tr (uLT C (d :: ds)))
      rw [tellC_ok hx, hearC_ok hx hz₁, ih2]

/-! ## 2 The plain parts -/

/-- **The same plain parts.** `tree`, `n`: as `shownBy` takes them. -/
theorem laid_plains (C : CK) (ch : Nat) (tree : Nat → List Nat) : ∀ (ds : List RDT)
    (ps : List Played) (n : Nat) (ρ : Iop.Rho (uLT C ds)), ds.length ≤ ps.length →
    (trLaid C ds ps ρ).plains = (trOff C ds ((shownBy ch tree ps n).map (·.2.1)) ρ).plains
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, h => by simp at h
  | d :: ds, p :: ps, n, (c, ρ), h => by
    have ih := laid_plains C ch tree ds ps (n + p.tables.length) ρ (Nat.le_of_succ_le_succ h)
    show ((Iop.GPlain.mk d.entry.work (plainOf d.items p.vals) (0 : ℕ),
        (trLaid C ds ps ρ).plains) : Iop.Plains (uLT C (d :: ds))) =
      (Iop.GPlain.mk d.entry.work (plainOf d.items p.vals) (0 : ℕ),
        (trOff C ds ((shownBy ch tree ps (n + p.tables.length)).map (·.2.1)) ρ).plains)
    rw [ih]

/-! ## 3 A symbol at a listed position -/

theorem lookup_cols (T : Table) : ∀ (xs : List Nat) (x : Nat), x ∈ xs →
    (xs.map fun y => (y, T.col y)).lookup x = some (T.col x)
  | [], _, h => by cases h
  | y :: xs, x, h => by
    show ((y, T.col y) :: xs.map fun y => (y, T.col y)).lookup x = _
    by_cases e : x = y
    · subst e
      rw [List.lookup_cons_self]
    · have hb : (x == y) = false := beq_eq_false_iff_ne.2 e
      rw [List.lookup_cons, hb]
      exact lookup_cols T xs x ((List.mem_cons.1 h).resolve_left e)

/-- One round's oracle part, at the position of tree number k and leaf x, where x is listed for that
tree. `l`: the round's tables; `a`: for each of them the positions shown. -/
theorem orc_eq : ∀ (ts : List Fmt.Shape) (l : List (Option Table)) (a : Nat → List Nat) (k x : Nat)
    (q : PosT ts), posAtT ts k x = some q → x ∈ a k →
    orcOf ts l q =
      orcOff ts ((List.range l.length).map fun i => colsOfT (l[i]?).join (a i)) q
  | [], _, _, _, _, q, _, _ => q.elim
  | s :: ts, l, a, 0, x, q, hq, hx => by
    have hq' : (if h : x < 2 ^ s.a then some (Sum.inl ⟨x, h⟩) else none) = some q := hq
    by_cases hlt : x < 2 ^ s.a
    · rw [dif_pos hlt] at hq'
      cases hq'
      funext i
      show (((l.head?.join.map fun t => t.col x).getD [])[i.val]?).getD 0 =
        ((((((List.range l.length).map fun i => colsOfT (l[i]?).join (a i)).head?.getD []).lookup
          x).getD [])[i.val]?).getD 0
      cases l with
      | nil => rfl
      | cons o l' =>
        have e : ((List.range (o :: l').length).map fun i =>
            colsOfT ((o :: l')[i]?).join (a i)).head? = some (colsOfT o (a 0)) := by
          rw [List.length_cons, List.range_succ_eq_map, List.map_cons]
          rfl
        rw [e]
        cases o with
        | none => rfl
        | some T =>
          show (((some (T.col x)).getD [])[i.val]?).getD 0 =
            (((((a 0).map fun y => (y, T.col y)).lookup x).getD [])[i.val]?).getD 0
          rw [lookup_cols T (a 0) x hx]
    · rw [dif_neg hlt] at hq'
      cases hq'
  | s :: ts, l, a, k + 1, x, q, hq, hx => by
    have hq' : (posAtT ts k x).map Sum.inr = some q := hq
    obtain ⟨q', hq1, rfl⟩ := Option.map_eq_some_iff.1 hq'
    have ih := orc_eq ts l.tail (fun i => a (i + 1)) k x q' hq1 hx
    show orcOf ts l.tail q' =
      orcOff ts ((List.range l.length).map fun i => colsOfT (l[i]?).join (a i)).tail q'
    rw [ih]
    congr 1
    cases l with
    | nil => rfl
    | cons o l' =>
      show ((List.range l'.length).map fun i => colsOfT (l'[i]?).join (a (i + 1))) =
        ((List.range (l'.length + 1)).map fun i => colsOfT ((o :: l')[i]?).join (a i)).tail
      rw [List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
      rfl

/-- **The same symbol at a listed position.** `k`: a tree of the chain, counted from the first of
these rounds; `x`: a leaf that is listed for it. -/
theorem laid_read (C : CK) (ch : Nat) (tree : Nat → List Nat) : ∀ (ds : List RDT)
    (ps : List Played) (n : Nat) (ρ : Iop.Rho (uLT C ds)), ds.length ≤ ps.length →
    (∀ z ∈ ds.zip ps, z.2.tables.length = z.1.trees.length) →
    ∀ (k x : Nat) (q : Iop.OPos (uLT C ds)), posAtST C ds k x = some q → x ∈ tree (n + k) →
    (trLaid C ds ps ρ).read q = (trOff C ds ((shownBy ch tree ps n).map (·.2.1)) ρ).read q
  | [], _, _, _, _, _, _, _, q, _, _ => q.elim
  | _ :: _, [], _, _, h, _, _, _, _, _, _ => by simp at h
  | d :: ds, p :: ps, n, (c, ρ), h, ht, k, x, q, hq, hx => by
    rw [posAtST_cons] at hq
    have hl : p.tables.length = d.trees.length := ht (d, p) List.mem_cons_self
    by_cases hlt : k < d.trees.length
    · rw [if_pos hlt] at hq
      obtain ⟨q', hq1, rfl⟩ := Option.map_eq_some_iff.1 hq
      show orcOf d.trees p.tables q' = orcOff d.trees (p.shownBy tree n).cols q'
      exact orc_eq d.trees p.tables (fun i => tree (n + i)) k x q' hq1 hx
    · rw [if_neg hlt] at hq
      obtain ⟨q', hq1, rfl⟩ := Option.map_eq_some_iff.1 hq
      show (trLaid C ds ps ρ).read q' =
        (trOff C ds ((shownBy ch tree ps (n + p.tables.length)).map (·.2.1)) ρ).read q'
      refine laid_read C ch tree ds ps (n + p.tables.length) ρ (Nat.le_of_succ_le_succ h)
        (fun z hz => ht z (List.mem_cons_of_mem _ hz)) (k - d.trees.length) x q' hq1 ?_
      rw [hl, Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)]
      exact hx

end ProofFile.Honest

#print axioms ProofFile.Honest.trOfC_laid
#print axioms ProofFile.Honest.laid_plains
#print axioms ProofFile.Honest.lookup_cols
#print axioms ProofFile.Honest.orc_eq
#print axioms ProofFile.Honest.laid_read
