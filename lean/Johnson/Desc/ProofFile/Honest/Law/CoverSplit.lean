-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverSplit.lean: THE EVENT AT A MEMBER, TAKEN APART; AND THE
DEBTS, ONE MEMBER AT A TIME. `LocalDebts` (Honest/Law/CoverHeld.lean) asks one bound a member on all
the list's falls and marks there together, and goes down the list by recursion. Here: (1) a fall of
a list fs₁ ++ fs₂ is a fall of fs₁ or of fs₂; (2) a fall that the members b :: t meet from a state
is a fall SEATED AT b, at that state and b's own challenges, or: b's own step returns a state, and
the members t meet a fall from there; (3) where no fall of the list sits at any member of a list of
members, these meet none; (4) the debts in one sentence for each member (as `gatesHeld_of`,
Honest/Law/SharesAt.lean (not in the sealed library), for `GatesHeld`).

WHAT THIS IS. Lemmas on the frame's own `fallOf` (Honest/Side.lean), `frontsOf`, `chainFall`
(Honest/Fall.lean) and on definitions of ours. No measure is in 1 to 3. None of the library's goals.

  1  `fallOf_append`, `findSome_isSome`, `chainFall_iff`, `chainFall_append`, `runFall_append`,
     `localFall_append`   by falls
  2  `chainFall_cons`   by the seat
  3  `fallOf_none`, `fronts_places`, `chainFall_none`   nothing sits here
  4  `DebtAt`, `localDebts_of`   one member at a time

Limits. 3 asks that no fall sits at ANY member of the list that is still to do: more than is needed
(only the member and those without a round behind it are reached). This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-! ## 1 By falls -/

theorem fallOf_append (fs₁ fs₂ : List (Fall S)) (a : Place) (s : S) (ds : List Fmt.Drawn) :
    fallOf (fs₁ ++ fs₂) a s ds = (fallOf fs₁ a s ds).or (fallOf fs₂ a s ds) := by
  unfold fallOf
  rw [List.filter_append, List.findSome?_append]

/-- A list's `findSome?` says something just where some entry's value does. -/
theorem findSome_isSome {α β : Type} (f : α → Option β) : ∀ l : List α,
    (l.findSome? f).isSome = true ↔ ∃ x ∈ l, (f x).isSome = true
  | [] => by simp
  | x :: l => by
    rw [List.findSome?_cons]
    cases h : f x with
    | some y => simp [h]
    | none =>
      simp only [List.mem_cons, exists_eq_or_imp, h]
      rw [findSome_isSome f l]
      simp

theorem chainFall_iff (fs : List (Fall S)) (ft : Nat) (bs : List (Block S Cl)) (s : S)
    (v : Fmt.View) : (chainFall fs ft bs s v).isSome = true ↔
      ∃ e ∈ frontsOf ft bs s v.rounds v.opened, (fallOf fs e.1 e.2.1 e.2.2).isSome = true := by
  unfold chainFall
  rw [findSome_isSome]
  constructor
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    cases hf : fallOf fs e.1 e.2.1 e.2.2 with
    | none =>
      rw [hf] at h
      cases h
    | some _ => rfl
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    cases hf : fallOf fs e.1 e.2.1 e.2.2 with
    | none =>
      rw [hf] at h
      cases h
    | some _ => rfl

/-- **A fall of fs₁ ++ fs₂ is a fall of fs₁ or of fs₂.** -/
theorem chainFall_append (fs₁ fs₂ : List (Fall S)) (ft : Nat) (bs : List (Block S Cl)) (s : S)
    (v : Fmt.View) (h : (chainFall (fs₁ ++ fs₂) ft bs s v).isSome = true) :
    (chainFall fs₁ ft bs s v).isSome = true ∨ (chainFall fs₂ ft bs s v).isSome = true := by
  obtain ⟨e, he, hf⟩ := (chainFall_iff _ ft bs s v).1 h
  rw [fallOf_append] at hf
  cases h1 : fallOf fs₁ e.1 e.2.1 e.2.2 with
  | some _ => exact Or.inl ((chainFall_iff _ ft bs s v).2 ⟨e, he, by rw [h1]; rfl⟩)
  | none =>
    rw [h1] at hf
    exact Or.inr ((chainFall_iff _ ft bs s v).2 ⟨e, he, hf⟩)

theorem runFall_append {fs₁ fs₂ : List (Fall S)} {L : Lay} {ss' : List (Step W Y)}
    {z : ChainProgress S Cl W Y} {s' : S} {ext : List Fmt.Drawn}
    (h : runFall (fs₁ ++ fs₂) L ss' z s' ext) :
    runFall fs₁ L ss' z s' ext ∨ runFall fs₂ L ss' z s' ext := by
  obtain ⟨z', ps, cs, h1, h2, h3, h4⟩ := h
  rcases chainFall_append _ _ _ _ _ _ h4 with g | g
  · exact Or.inl ⟨z', ps, cs, h1, h2, h3, g⟩
  · exact Or.inr ⟨z', ps, cs, h1, h2, h3, g⟩

theorem localFall_append {fs₁ fs₂ : List (Fall S)} {ft : Nat} {todo : List (Block S Cl)} {s' : S}
    {own : List Fmt.Drawn} (h : localFall (fs₁ ++ fs₂) ft todo s' own) :
    localFall fs₁ ft todo s' own ∨ localFall fs₂ ft todo s' own := by
  obtain ⟨rs, cols, h1, h2⟩ := h
  rcases chainFall_append _ _ _ _ _ _ h2 with g | g
  · exact Or.inl ⟨rs, cols, h1, g⟩
  · exact Or.inr ⟨rs, cols, h1, g⟩

/-! ## 2 By the seat -/

/-- **A fall that b :: t meet from s: seated at b; or b's own step returns, and t meet one from
there.** -/
theorem chainFall_cons (fs : List (Fall S)) (ft : Nat) (b : Block S Cl) (t : List (Block S Cl))
    (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : (chainFall fs ft (b :: t) s ⟨rs, cols⟩).isSome = true) :
    (fallOf fs b.place s ((rs.take b.rounds.length).map (·.drawn))).isSome = true ∨
      ∃ s' k, b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
        (chainFall fs ft t s' ⟨rs.drop b.rounds.length, cols.drop k⟩).isSome = true := by
  obtain ⟨e, he, hf⟩ := (chainFall_iff _ ft _ s _).1 h
  have he' : e ∈ frontsOf ft (b :: t) s rs cols := he
  by_cases hm : (rs.take b.rounds.length).length = b.rounds.length
  · cases hs : b.step ft s (rs.take b.rounds.length) cols with
    | error w =>
      rw [frontsOf_err ft b t s rs cols w hm hs] at he'
      obtain rfl := List.mem_singleton.1 he'
      exact Or.inl hf
    | ok y =>
      obtain ⟨s', k⟩ := y
      rw [frontsOf_ok ft b t s s' k rs cols hm hs] at he'
      rcases List.mem_cons.1 he' with rfl | he''
      · exact Or.inl hf
      · exact Or.inr ⟨s', k, rfl, (chainFall_iff _ ft t s' _).2 ⟨e, he'', hf⟩⟩
  · exfalso
    rw [frontsOf_cons, if_pos (bne_iff_ne.2 hm)] at he'
    cases he'

/-! ## 3 Nothing sits here -/

theorem fallOf_none (fs : List (Fall S)) (a : Place) (h : ∀ f ∈ fs, f.place ≠ a) (s : S)
    (ds : List Fmt.Drawn) : fallOf fs a s ds = none := by
  unfold fallOf
  have e : (fs.filter fun f => f.place == a) = [] :=
    List.filter_eq_nil_iff.2 fun f hf => by
      have := h f hf
      simpa using this
  rw [e]
  rfl

/-- The places that `frontsOf` lists are the members'. -/
theorem fronts_places (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn), ∀ e ∈ frontsOf ft bs s rs cols, ∃ c ∈ bs, c.place = e.1
  | [], _, _, _, e, he => by simp [frontsOf] at he
  | b :: t, s, rs, cols, e, he => by
    by_cases hm : (rs.take b.rounds.length).length = b.rounds.length
    · cases hs : b.step ft s (rs.take b.rounds.length) cols with
      | error w =>
        rw [frontsOf_err ft b t s rs cols w hm hs] at he
        obtain rfl := List.mem_singleton.1 he
        exact ⟨b, List.mem_cons_self, rfl⟩
      | ok y =>
        obtain ⟨s', k⟩ := y
        rw [frontsOf_ok ft b t s s' k rs cols hm hs] at he
        rcases List.mem_cons.1 he with rfl | he'
        · exact ⟨b, List.mem_cons_self, rfl⟩
        · obtain ⟨c, hc, hp⟩ := fronts_places ft t s' _ _ e he'
          exact ⟨c, List.mem_cons_of_mem _ hc, hp⟩
    · exfalso
      rw [frontsOf_cons, if_pos (bne_iff_ne.2 hm)] at he
      cases he

/-- **Where no fall of the list sits at any of these members, they meet none.** -/
theorem chainFall_none (fs : List (Fall S)) (ft : Nat) (bs : List (Block S Cl))
    (h : ∀ c ∈ bs, ∀ f ∈ fs, f.place ≠ c.place) (s : S) (v : Fmt.View) :
    chainFall fs ft bs s v = none := by
  cases hc : chainFall fs ft bs s v with
  | none => rfl
  | some _ =>
    exfalso
    obtain ⟨e, he, hf⟩ := (chainFall_iff fs ft bs s v).1 (by rw [hc]; rfl)
    obtain ⟨c, hcb, hp⟩ := fronts_places ft bs s _ _ e he
    rw [fallOf_none fs e.1 (fun f hf' => by rw [← hp]; exact h c hcb f hf')] at hf
    cases hf

/-! ## 4 One member at a time -/

section
variable (C : CK) (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark) (skip : Nat)
  (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞) (tail : List Fmt.Drawn)
  (Q : Nat → List Fmt.Drawn → Prop)

/-- **One member's debt.** b: the member; j: its number; n: the chain's rounds in front of it; dsb:
its own rounds' data; tl: behind the last member the fixed challenges, else none; last: it is the
last. -/
def DebtAt (b : Block S Cl) (j n : Nat) (dsb : List RDT) (tl : List Fmt.Drawn) (last : Bool) :
    Prop :=
  ∀ fr, skip ≤ fr.length → (fr.drop skip).length = n →
    fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false → Q j fr →
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) |
      localAt fs ms skip X b fr n (drawnT C dsb ρ) (drawnT C dsb ρ ++ tl)} ≤ p j ∧
    (last = false → ∀ ρ : Iop.Rho (uLT C dsb),
      (markOf ms b.place fr (drawnT C dsb ρ)).isSome = false →
      fellBy all fs (X (fr.take skip)) (n + b.rounds.length)
        (fr.drop skip ++ drawnT C dsb ρ) = false → Q (j + 1) (fr ++ drawnT C dsb ρ))

/-- **The debts, from one sentence for each member.** A: the members in front of b; B: those
behind. -/
theorem localDebts_of : ∀ (bs : List (Block S Cl)) (j n : Nat) (ds : List RDT),
    (∀ (A : List (Block S Cl)) (b : Block S Cl) (B : List (Block S Cl)), bs = A ++ b :: B →
      DebtAt C all fs ms skip X p Q b (j + A.length) (n + (A.flatMap (·.rounds)).length)
        ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
        (if B.isEmpty then tail else []) B.isEmpty) →
    LocalDebts C all fs ms skip X p tail Q bs j n ds
  | [], _, _, _, _ => trivial
  | [b], j, n, ds, h => by
    intro fr h1 h2 h3 h4
    exact (h [] b [] rfl fr h1 h2 h3 h4).1
  | b :: b' :: bs, j, n, ds, h => by
    refine ⟨fun fr h1 h2 h3 h4 => ?_, localDebts_of (b' :: bs) (j + 1) (n + b.rounds.length)
      (ds.drop b.rounds.length) fun A c B e => ?_⟩
    · obtain ⟨g1, g2⟩ := h [] b (b' :: bs) rfl fr h1 h2 h3 h4
      have g1' : Iop.prRho {ρ : Iop.Rho (uLT C (ds.take b.rounds.length)) |
          localAt fs ms skip X b fr n (drawnT C _ ρ) (drawnT C _ ρ ++ [])} ≤ p j := g1
      simp only [List.append_nil] at g1'
      exact ⟨g1', g2 rfl⟩
    · have g := h (b :: A) c B (by rw [e]; rfl)
      have e1 : j + (b :: A).length = j + 1 + A.length := by
        rw [List.length_cons]
        omega
      have e2 : n + ((b :: A).flatMap (·.rounds)).length =
          n + b.rounds.length + (A.flatMap (·.rounds)).length := by
        rw [List.flatMap_cons, List.length_append]
        omega
      have e3 : ds.drop ((b :: A).flatMap (·.rounds)).length =
          (ds.drop b.rounds.length).drop (A.flatMap (·.rounds)).length := by
        rw [List.flatMap_cons, List.length_append, List.drop_drop]
      rw [e1, e2, e3] at g
      exact g

end

end ProofFile.Honest

#print axioms ProofFile.Honest.fallOf_append
#print axioms ProofFile.Honest.findSome_isSome
#print axioms ProofFile.Honest.chainFall_iff
#print axioms ProofFile.Honest.chainFall_append
#print axioms ProofFile.Honest.runFall_append
#print axioms ProofFile.Honest.localFall_append
#print axioms ProofFile.Honest.chainFall_cons
#print axioms ProofFile.Honest.fallOf_none
#print axioms ProofFile.Honest.fronts_places
#print axioms ProofFile.Honest.chainFall_none
#print axioms ProofFile.Honest.localDebts_of
