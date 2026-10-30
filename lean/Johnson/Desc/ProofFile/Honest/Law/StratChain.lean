-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratChain.lean: what the strategies of Honest/Strat.lean write in
one chain. Theorems on `plainOf`, `orcOf` and the six recursions over a chain's rounds; no
description and no prover is named.

  1  `gots_plainOf`, `colT_orcOf`, `map_itemOf_cons`, `ofFn_getD`   a round's typed message is read
     back, by the library's own `PlainOf.gots` and `colT`, as what was put into it, if the shapes
     agree
  2  `trOf`, `endOf`   a chain's transcript as a speaker writes it; the state of the chain after it
  3  `zip_speakL`, `zip_speakS`, `zip_speakLEnd`   a speaker, zipped with the other strategy's
     silence, writes `trOf` and passes on `endOf`, or the challenges that were heard

Limits.
  * Nothing is said here of `play`, of a view or of a whole file.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Strat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT roundT drawnT PosT posAtT colT)
open _root_.Run.PQ (CK PlainOf)

variable {W Y : Type}

/-! ## 1 A message, read back -/

theorem map_itemOf_cons {i : Fmt.Item} {l : List Fmt.Item} {g : List Fmt.ItemValue}
    (h : g.map itemOf = i :: l) : ∃ a g', g = a :: g' ∧ itemOf a = i ∧ g'.map itemOf = l := by
  cases g with
  | nil => cases h
  | cons a g' => exact ⟨a, g', rfl, (List.cons.inj h).1, (List.cons.inj h).2⟩

theorem gots_plainOf : ∀ (l : List Fmt.Item) (g : List Fmt.ItemValue),
    g.map itemOf = l.filter (· != .root) → PlainOf.gots l (plainOf l g) = g
  | [], g, h => by
    cases g with
    | nil => rfl
    | cons a g => cases h
  | .root :: l, g, h => gots_plainOf l g h
  | .f :: l, g, h => by
    obtain ⟨a, g', rfl, ha, hg⟩ :=
      map_itemOf_cons (show g.map itemOf = .f :: l.filter (· != .root) from h)
    cases a with
    | f x => exact congrArg (Fmt.ItemValue.f x :: ·) (gots_plainOf l g' hg)
    | e x => simp [itemOf] at ha
    | word x => simp [itemOf] at ha
    | root d => simp [itemOf] at ha
    | answer x => simp [itemOf] at ha
  | .e :: l, g, h => by
    obtain ⟨a, g', rfl, ha, hg⟩ :=
      map_itemOf_cons (show g.map itemOf = .e :: l.filter (· != .root) from h)
    cases a with
    | f x => simp [itemOf] at ha
    | e x => exact congrArg (Fmt.ItemValue.e x :: ·) (gots_plainOf l g' hg)
    | word x => simp [itemOf] at ha
    | root d => simp [itemOf] at ha
    | answer x => simp [itemOf] at ha
  | .word :: l, g, h => by
    obtain ⟨a, g', rfl, ha, hg⟩ :=
      map_itemOf_cons (show g.map itemOf = .word :: l.filter (· != .root) from h)
    cases a with
    | f x => simp [itemOf] at ha
    | e x => simp [itemOf] at ha
    | word x => exact congrArg (Fmt.ItemValue.word x :: ·) (gots_plainOf l g' hg)
    | root d => simp [itemOf] at ha
    | answer x => simp [itemOf] at ha
  | .answer :: l, g, h => by
    obtain ⟨a, g', rfl, ha, hg⟩ :=
      map_itemOf_cons (show g.map itemOf = .answer :: l.filter (· != .root) from h)
    cases a with
    | f x => simp [itemOf] at ha
    | e x => simp [itemOf] at ha
    | word x => simp [itemOf] at ha
    | root d => simp [itemOf] at ha
    | answer x => exact congrArg (Fmt.ItemValue.answer x :: ·) (gots_plainOf l g' hg)

theorem ofFn_getD {n : Nat} (L : List UInt64) (h : L.length = n) :
    List.ofFn (fun i : Fin n => (L[i.val]?).getD 0) = L := by
  apply List.ext_getElem
  · rw [List.length_ofFn, h]
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem?_eq_getElem h2]
    rfl

theorem colT_orcOf : ∀ (ts : List Fmt.Shape) (l : List (Option Table)) (n x : Nat) (p : PosT ts)
    (t : Table) (s : Fmt.Shape), posAtT ts n x = some p → l[n]? = some (some t) → ts[n]? = some s →
    t.words = s.W → colT ts p (orcOf ts l p) = t.col x
  | [], _, _, _, p, _, _, _, _, _, _ => p.elim
  | s₀ :: ts, l, 0, x, p, t, s, hp, hl, hs, hw => by
    have hs' : s₀ = s := by simpa using hs
    subst hs'
    cases l with
    | nil => simp at hl
    | cons a l' =>
      have ha : a = some t := by simpa using hl
      subst ha
      have hp' : (if h : x < 2 ^ s₀.a then some (Sum.inl ⟨x, h⟩) else none :
          Option (Fin (2 ^ s₀.a) ⊕ PosT ts)) = some p := hp
      by_cases hx : x < 2 ^ s₀.a
      · rw [dif_pos hx] at hp'
        cases hp'
        have hlen : (t.col x).length = s₀.W := by
          unfold Table.col
          rw [List.length_ofFn, hw]
        exact ofFn_getD (t.col x) hlen
      · rw [dif_neg hx] at hp'
        cases hp'
  | s₀ :: ts, l, n + 1, x, p, t, s, hp, hl, hs, hw => by
    have hp' : (posAtT ts n x).map Sum.inr = some p := hp
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hp'
    have hl' : l.tail[n]? = some (some t) := by
      cases l with
      | nil => simp at hl
      | cons a l' => simpa using hl
    have hs' : ts[n]? = some s := by simpa using hs
    exact colT_orcOf ts l.tail n x q t s hq hl' hs' hw

/-! ## 2 A chain's transcript -/

/-- A chain's transcript as a speaker of Honest/Strat.lean writes it. -/
def trOf (C : CK) : (ds : List RDT) → List (Step W Y) → Option (Mid W Y) → Iop.Rho (uLT C ds) →
    Iop.Tr (uLT C ds)
  | [], _, _, _ => ()
  | d :: ds, ss, m, (c, ρ) =>
    (msgOf C d (tellAt ss.head? m), c,
      trOf C ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) ρ)

/-- The state of the chain after it. -/
def endOf (C : CK) : (ds : List RDT) → List (Step W Y) → Option (Mid W Y) → Iop.Rho (uLT C ds) →
    Option (Mid W Y)
  | [], _, m, _ => m
  | d :: ds, ss, m, (c, ρ) =>
    endOf C ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) ρ

/-! ## 3 A speaker, while the other strategy is silent -/

section
variable (C : CK) {rest : Iop.Shape} {A : Iop.RoundSplits rest}

theorem zip_speakL : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (k : Option (Mid W Y) → Iop.LStrat rest A) (k₀ : Iop.SStrat rest A)
    (ρ : Iop.Rho (uLT C ds ++ rest)),
    ((Iop.SStrat.zip (hushS C ds k₀) (speakL C ds ss m k)).run ρ).1 =
      Iop.Tr.app (trOf C ds ss m (Iop.Rho.fst ρ))
        ((Iop.SStrat.zip k₀ (k (endOf C ds ss m (Iop.Rho.fst ρ)))).run
          (Iop.Rho.snd (s := uLT C ds) ρ)).1
  | [], _, _, _, _, _ => rfl
  | d :: ds, ss, m, k, k₀, (c, ρ) =>
    congrArg (fun (τ : Iop.Tr (uLT C ds ++ rest)) =>
        ((msgOf C d (tellAt ss.head? m), c, τ) : Iop.Tr (uLT C (d :: ds) ++ rest)))
      (zip_speakL ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) k k₀ ρ)

theorem zip_speakS : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (k₀ : Iop.SStrat rest A) (acc : List Fmt.Drawn) (k : List Fmt.Drawn → Iop.LStrat rest A)
    (ρ : Iop.Rho (uLT C ds ++ rest)),
    ((Iop.SStrat.zip (speakS C ds ss m k₀) (hushL C ds acc k)).run ρ).1 =
      Iop.Tr.app (trOf C ds ss m (Iop.Rho.fst ρ))
        ((Iop.SStrat.zip k₀ (k (acc ++ drawnT C ds (Iop.Rho.fst ρ)))).run
          (Iop.Rho.snd (s := uLT C ds) ρ)).1
  | [], _, _, k₀, acc, k, ρ => by
    show ((Iop.SStrat.zip k₀ (k acc)).run ρ).1 = ((Iop.SStrat.zip k₀ (k (acc ++ []))).run ρ).1
    rw [List.append_nil]
  | d :: ds, ss, m, k₀, acc, k, (c, ρ) => by
    have ih := zip_speakS ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) k₀
      (acc ++ [drOf C d c]) k ρ
    rw [List.append_assoc] at ih
    exact congrArg (fun (τ : Iop.Tr (uLT C ds ++ rest)) =>
      ((msgOf C d (tellAt ss.head? m), c, τ) : Iop.Tr (uLT C (d :: ds) ++ rest))) ih

end

theorem zip_speakLEnd (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (ρ : Iop.Rho (uLT C ds)),
    ((Iop.SStrat.zip (hushSEnd C ds) (speakLEnd C ds ss m)).run ρ).1 = trOf C ds ss m ρ
  | [], _, _, _ => rfl
  | d :: ds, ss, m, (c, ρ) =>
    congrArg (fun (τ : Iop.Tr (uLT C ds)) =>
        ((msgOf C d (tellAt ss.head? m), c, τ) : Iop.Tr (uLT C (d :: ds))))
      (zip_speakLEnd C ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) ρ)

end ProofFile.Honest

#print axioms ProofFile.Honest.map_itemOf_cons
#print axioms ProofFile.Honest.gots_plainOf
#print axioms ProofFile.Honest.ofFn_getD
#print axioms ProofFile.Honest.colT_orcOf
#print axioms ProofFile.Honest.zip_speakL
#print axioms ProofFile.Honest.zip_speakS
#print axioms ProofFile.Honest.zip_speakLEnd
