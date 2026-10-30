-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Coins.lean: the coins that a row of parts spends, in one list
(spentOf, Honest/K5/Law/Script.lean), cut part by part: the coins that the book of coins lends the
part number q are the stretch of that list behind the coins of the parts in front. Definitions with
code, and statements with their proofs: first general in the row, then at the row of an attention
segment's own rounds, where the stretch begins at the number of scalars that the parts in front send
(slotsTo, Johnson/Desc/K5/Honest/Law/SlotsTo.lean).

  runsNo, spentNo, runsE_length, spentOf_length   how many coins a list of runs, a row, has
  spent_at       GENERAL in the row, CONDITIONAL: what lendPart lends part q is the stretch of what
                 lendRow lends the row
  spends_scalars, spentNo_take, part_at   at the kind's row: a part spends as many coins as it sends
                 scalars
  k5_spent       CONDITIONAL: **at the kind's row: coin number slotsTo x q + i of the row is coin
                 number i of part q**, and it lies within the list
  sum_runs       a masked sumcheck's coins are its first run, then its end values' run

Limits. On coins as data alone: nothing is said of what a coin is laid over.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Script
import Johnson.Desc.ProofFile.Honest.K5.Law.Plays
import Johnson.Desc.K5.Honest.Law.SlotsTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots)
open H2K5.Honest (PartShape shapes Chal slotsTo)
open ProofFile.Honest.SumLaw

/-! ## 1 General in the row -/

section
variable {V W X : Type}

/-- How many coins of the extension field a list of runs has. -/
def runsNo (ds : List (String × Due)) : Nat := (ds.map (·.2.e)).sum

/-- How many such coins the parts of a row spend. -/
def spentNo (ps : List (Part V W X)) : Nat := (ps.map fun p => runsNo p.spends).sum

theorem sum_take_le : ∀ (l : List Nat) (n : Nat), (l.take n).sum ≤ l.sum
  | [], n => by rw [List.take_nil]
  | _ :: _, 0 => Nat.zero_le _
  | a :: l, n + 1 => by
    rw [List.take_succ_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add_left (sum_take_le l n) a

theorem coinsE_length {d : Due} (c : Cs d) : (coinsE c).length = d.e := List.length_ofFn

theorem runsE_length : ∀ (ds : List (String × Due)) (c : CsAll ds), (runsE ds c).length = runsNo ds
  | [], _ => rfl
  | d :: ds, c => by
    show (coinsE (d := d.2) c.1 ++ runsE ds c.2).length = d.2.e + runsNo ds
    rw [List.length_append, coinsE_length, runsE_length ds]

theorem spentOf_length : ∀ (ps : List (Part V W X)) (c : RowCoins ps),
    (spentOf ps c).length = spentNo ps
  | [], _ => rfl
  | p :: ps, c => by
    show (runsE p.spends c.1.2.1 ++ spentOf ps c.2).length = runsNo p.spends + spentNo ps
    rw [List.length_append, runsE_length, spentOf_length ps]

/-- **What the book lends part number q is the stretch of what it lends the row.** CONDITIONAL: c is
what `lendRow` lends the row from the number j on; p is the part number q of the row; cq is what
`lendPart` lends p at its address. -/
theorem spent_at {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Place} : ∀ (ps : List (Part V W X)) (j : Nat) (c : RowCoins ps),
    lendRow B rows look a ps j = .ok c → ∀ (q : Nat) (p : Part V W X) (cq : p.Coins),
    ps[q]? = some p → lendPart B rows look ⟨a, j + q⟩ p = .ok cq → ∀ i, i < runsNo p.spends →
    (spentOf ps c).getD (spentNo (ps.take q) + i) zeroE = (runsE p.spends cq.2.1).getD i zeroE
  | [], _, _, _, _, _, _, h, _, _, _ => by cases h
  | p' :: ps, j, c, hc, 0, p, cq, hq, hl, i, hi => by
    obtain rfl : p' = p := Option.some.inj hq
    obtain ⟨c1, hc1, hc⟩ := exBind_ok hc
    obtain ⟨c2, _, hcc⟩ := exMap_ok hc
    rw [show lendPart B rows look ⟨a, j⟩ p' = .ok cq from hl] at hc1
    obtain rfl : cq = c1 := Except.ok.inj hc1
    have e1 : c.1 = cq := (congrArg (·.1) hcc).symm
    show (runsE p'.spends c.1.2.1 ++ spentOf ps c.2).getD (0 + i) zeroE = _
    rw [Nat.zero_add, List.getD_append _ _ _ _ (by rw [runsE_length]; exact hi), e1]
  | p' :: ps, j, c, hc, q + 1, p, cq, hq, hl, i, hi => by
    obtain ⟨c1, _, hc⟩ := exBind_ok hc
    obtain ⟨c2, hc2, hcc⟩ := exMap_ok hc
    have e2 : c.2 = c2 := (congrArg (·.2) hcc).symm
    have ih := spent_at ps (j + 1) c.2 (by rw [e2]; exact hc2) q p cq hq
      (by rw [show j + 1 + q = j + (q + 1) by omega]; exact hl) i hi
    show (runsE p'.spends c.1.2.1 ++ spentOf ps c.2).getD
      (runsNo p'.spends + spentNo (ps.take q) + i) zeroE = _
    rw [List.getD_append_right _ _ _ _ (by rw [runsE_length]; omega), runsE_length,
      show runsNo p'.spends + spentNo (ps.take q) + i - runsNo p'.spends =
        spentNo (ps.take q) + i by omega]
    exact ih

end

/-! ## 2 At the row of an attention segment's own rounds -/

section
variable {V W W' X : Type} (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W')
  (wit : W → W')

/-- A part spends as many coins as it sends scalars. -/
theorem spends_scalars : ∀ s : PartShape × Nat, runsNo (partAt a chalOf J s).spends = s.1.scalars
  | (.sum ⟨lead, vs, none⟩, _) => by
    show lead + ownSlots vs + 0 = lead + ownSlots vs + 0
    rfl
  | (.sum ⟨lead, vs, some e⟩, _) => by
    show lead + ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + (e.n + 0) = _
    rfl
  | (.one 0, _) => rfl
  | (.one (_ + 1), _) => rfl

theorem spentNo_take : ∀ (sh : List PartShape) (j q : Nat),
    spentNo ((rowParts (V := V) (X := X) a chalOf J wit sh j).take q) =
      ((sh.take q).map (·.scalars)).sum
  | [], _, q => by
    show spentNo (List.take q []) = ((List.take q []).map _).sum
    rw [List.take_nil, List.take_nil]
    rfl
  | _ :: _, _, 0 => rfl
  | s :: sh, j, q + 1 => by
    show runsNo (partAt a chalOf J (s, j)).spends +
      spentNo ((rowParts (V := V) (X := X) a chalOf J wit sh (j + 1)).take q) =
        s.scalars + ((sh.take q).map (·.scalars)).sum
    rw [spends_scalars a chalOf J (s, j), spentNo_take sh (j + 1) q]

theorem part_at : ∀ (sh : List PartShape) (j q : Nat) (s : PartShape), sh[q]? = some s →
    (rowParts (V := V) (X := X) a chalOf J wit sh j)[q]? =
      some ((partAt a chalOf J (s, j + q)).lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)
  | [], _, _, _, h => by cases h
  | _ :: _, _, 0, _, h => by
    cases h
    rfl
  | _ :: sh, j, q + 1, s, h => by
    show (rowParts (V := V) (X := X) a chalOf J wit sh (j + 1))[q]? = _
    rw [part_at sh (j + 1) q s h, show j + 1 + q = j + (q + 1) by omega]

end

section
variable {W₀ Rc Xi Tr X : Type}

/-- **At the kind's row: coin number slotsTo x q + i of the row is coin number i of part q.**
CONDITIONAL: c is what `lendRow` lends the row; s is part number q; cq is what `lendPart` lends it
at the address (the place, q). -/
theorem k5_spent {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    (cells : Tr → Cells) (Z : Seat5)
    {c : RowCoins (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts}
    (hc : lendRow B rows look Z.place
      (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts 0 = .ok c)
    {q : Nat} {s : PartShape} (hq : (shapes Z.P.x)[q]? = some s)
    {cq : (partAt Z.place (chalOf Z) (jobs Z.P) (s, q)).Coins}
    (hl : lendPart B rows look ⟨Z.place, q⟩
      ((partAt Z.place (chalOf Z) (jobs Z.P) (s, q)).lift (V := Local W₀ Rc Xi Tr) (X := X)
        (fun _ => ()) (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
        (fun _ => ()) fun x _ => x) = .ok cq) {i : Nat} (hi : i < s.scalars) :
    slotsTo Z.P.x q + i < (spentOf _ c).length ∧
      (spentOf _ c).getD (slotsTo Z.P.x q + i) zeroE =
        (runsE (partAt Z.place (chalOf Z) (jobs Z.P) (s, q)).spends cq.2.1).getD i zeroE := by
  have hp := part_at (V := Local W₀ Rc Xi Tr) (X := X) Z.place (chalOf Z) (jobs Z.P)
    (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace)) (shapes Z.P.x) 0 q s hq
  rw [Nat.zero_add] at hp
  have hn := spentNo_take (V := Local W₀ Rc Xi Tr) (X := X) Z.place (chalOf Z) (jobs Z.P)
    (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace)) (shapes Z.P.x) 0
  have hs := spends_scalars Z.place (chalOf Z) (jobs Z.P) (s, q)
  have h := spent_at _ 0 c hc q _ cq hp (by rw [Nat.zero_add]; exact hl) i (by
    show i < runsNo (partAt Z.place (chalOf Z) (jobs Z.P) (s, q)).spends
    rw [hs]
    exact hi)
  refine ⟨?_, ?_⟩
  · have h1 := hn (q + 1)
    have h2 := hn (shapes Z.P.x).length
    rw [spentOf_length]
    have h3 : spentNo ((k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.take
        (q + 1)) ≤ spentNo (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts := by
      unfold spentNo
      rw [List.map_take]
      exact sum_take_le _ _
    have h4 : spentNo ((k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.take
        (q + 1)) = slotsTo Z.P.x (q + 1) := h1
    rw [h4, H2K5.Honest.slotsTo_next Z.P.x hq] at h3
    omega
  · have h5 : spentNo ((k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.take q) =
        slotsTo Z.P.x q := hn q
    rw [h5] at h
    exact h

end

/-- A masked sumcheck's coins are its first run, then its end values' run. No premise. -/
theorem sum_runs {W X : Type} {name endName : String} {lead : Nat} {vs : List Var} {e : Ends}
    {J : SumJob W X} (hJ : J.shape = ⟨lead, vs, some e⟩) (c : SumCoins name endName J) :
    runsE ((name, ⟨0, ownRun J.shape⟩) :: endRuns endName J.shape.ends) c.2.1 =
      firstRun c ++ endRun c := by
  obtain ⟨sh, a1, a2, a3, a4, a5⟩ := J
  have hJ' : sh = ⟨lead, vs, some e⟩ := hJ
  subst hJ'
  show coinsE _ ++ (coinsE _ ++ []) = _
  rw [List.append_nil]
  rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sum_take_le
#print axioms ProofFile.Honest.K5.coinsE_length
#print axioms ProofFile.Honest.K5.runsE_length
#print axioms ProofFile.Honest.K5.spentOf_length
#print axioms ProofFile.Honest.K5.spent_at
#print axioms ProofFile.Honest.K5.spends_scalars
#print axioms ProofFile.Honest.K5.spentNo_take
#print axioms ProofFile.Honest.K5.part_at
#print axioms ProofFile.Honest.K5.k5_spent
#print axioms ProofFile.Honest.K5.sum_runs
