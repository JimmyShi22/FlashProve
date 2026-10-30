-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/ScriptLendRow.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: ONE RUN's COINS UNDER TWO NAMES ARE ONE: WHAT THE FRAME's lendRow HANDS A ROW's
FIRST PART IS lentCut (Honest/K1/ScriptAt.lean) AT THAT PART's ADDRESS. Statements and proofs; no
definition.

  ok_bind_map   tool: where a bind over a map returns, both halves returned, and with what
  ok_mapError   tool: where a mapError returns, so did what it wraps
  cut_of_lendRow   lendRow ... a (p :: ps) j = .ok c gives lentCut k ch (a, j) p.takes = some c.1.1
  cut_of_lendHalf   the same at a half of one part, from part number 0: the form in which a
                sending's half (proverSideOfSending, placeHalf) is lent its coins
  cut_of_lendPlace   AT placeHalf (Honest/K1/PlaceJob.lean): its one part takes the job's own count
                dueR J.P J.ride (Part.lift keeps "takes"): so what lendRow hands it is lentCut at
                the place's part 0 and that count: the very cut of msgTxt, padTxt and treeTbl

ok_bind_map says more than ok_of_bind_map (Honest/K1/ScriptAtLaw.lean): that one follows from it.

Why. The laws on the part's moves speak at the coins that the frame lends; the terms for the Script
speak at lentCut k. The three laws here say that they are the same coins, by name.

Limits. Wherever lendRow returns: where it refuses nothing is said; whether it returns is public
(the book's counts and entries). An equation at each run. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc

variable {Bk : ProverCoinCounts} {V W X Xi : Type}

theorem ok_bind_map {ε α β γ : Type} (x : Except ε α) (y : Except ε β) (f : α → β → γ) (c : γ)
    (h : (x.bind fun a => y.map fun b => f a b) = .ok c) :
    ∃ a b, x = .ok a ∧ y = .ok b ∧ c = f a b := by
  cases x with
  | error _ => simp [Except.bind] at h
  | ok a =>
    cases y with
    | error _ => simp [Except.bind, Except.map] at h
    | ok b =>
      simp only [Except.bind, Except.map, Except.ok.injEq] at h
      exact ⟨a, b, rfl, rfl, h.symm⟩

theorem ok_mapError {ε ε' α : Type} (x : Except ε α) (g : ε → ε') (a : α)
    (h : x.mapError g = .ok a) : x = .ok a := by
  cases x with
  | error _ => simp [Except.mapError] at h
  | ok b =>
    simp only [Except.mapError, Except.ok.injEq] at h
    rw [h]

/-- **What lendRow hands a row's first part is lentCut at that part's address.** -/
theorem cut_of_lendRow (rows : List (Addr × Due)) (k : Coins Bk) (ch : Nat) (a : Place)
    (p : Part V W X) (ps : List (Part V W X)) (j : Nat) (c : RowCoins (p :: ps))
    (h : lendRow Bk rows (k.look ch) a (p :: ps) j = .ok c) :
    lentCut k ch ⟨a, j⟩ p.takes = some c.1.1 := by
  unfold lendRow at h
  obtain ⟨c₀, r, h1, _, hc⟩ := ok_bind_map _ _ (fun (u : p.Coins) (v : RowCoins ps) => (u, v)) c h
  have h2 := ok_mapError _ _ _ h1
  rw [hc]
  exact cut_of_lend rows k ch ⟨a, j⟩ p c₀ h2

/-- The same at a half of one part. -/
theorem cut_of_lendHalf (rows : List (Addr × Due)) (k : Coins Bk) (ch : Nat) (a : Place)
    (p : Part V W X) (c : RowCoins [p]) (h : lendRow Bk rows (k.look ch) a [p] 0 = .ok c) :
    lentCut k ch ⟨a, 0⟩ p.takes = some c.1.1 :=
  cut_of_lendRow rows k ch a p [] 0 c h

/-- **At placeHalf**: the very cut of the lots' texts. -/
theorem cut_of_lendPlace (rows : List (Addr × Due)) (k : Coins Bk) (ch : Nat)
    (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X)
    (c : RowCoins (placeHalf (V := V) wit J).parts)
    (h : lendRow Bk rows (k.look ch) J.P.place (placeHalf (V := V) wit J).parts 0 = .ok c) :
    lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c.1.1 :=
  cut_of_lendHalf rows k ch J.P.place ((sendPart (V := V) J).lift id wit id fun _ y => y) c h

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ok_bind_map
#print axioms ProofFile.Honest.K1.ok_mapError
#print axioms ProofFile.Honest.K1.cut_of_lendRow
#print axioms ProofFile.Honest.K1.cut_of_lendHalf
#print axioms ProofFile.Honest.K1.cut_of_lendPlace
