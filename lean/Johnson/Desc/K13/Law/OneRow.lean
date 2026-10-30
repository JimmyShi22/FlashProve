-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OneRow.lean: where the pile has one row there is no batching: kind K13's block
for that case (Johnson/Desc/K13/Kind.lean: `oneRowB`) takes the one row as the claim. Its law.
Statements with their proofs.
Main names:
  `enter_eq`: what the chain's coming to its end leaves, at the first chain's state.
  `oneRowB_ok`: where the block says yes: the rows on the table stay; the claim behind is made of a
    row; W's vector fits its table.
  `oneRowB_goodIn`: the piece without a round that holds the block has what it owes, from all rows
    true behind to all rows true in front, with `FrontOk P` promised behind; no error.
Used of `verify-on-bytes`: `memberClaim`, `linOk`, as pure functions.

What is not claimed. The premise: the pin is carried back over the piece. That the block says yes
anywhere: by the head of Johnson/Desc/K13/Kind.lean it has run at a made-up state alone, and no
stored proof has a plan with a pile of one row; neither was tried for this file. Nothing on
soundness beyond the form. The number nR of the matrix's rows is a free letter.

-/
import Johnson.Desc.K13.Law.M3Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- one proof serves the lens with and without the arm "between": one alternative stays unused
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- What the chain's coming to its end leaves. -/
theorem enter_eq {s s₁ : S} (he : atS.enter s = some s₁) :
    s₁ = { s with here := .mem { msg := #[], ids := #[], lin := none } } ∧
      s.rows = s.out.pending := by
  cases hs : s.here with
  | fin a =>
    have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
    rw [e1] at he
    refine ⟨?_, by simp only [S.rows, hs]⟩
    rw [← Option.some.inj he]
    simp only [S.enterMem, hs]
  | between =>
    first
      | (have e1 : atS.enter s = none := by simp only [atS, hs]
         rw [e1] at he
         cases he)
      | (have e1 : atS.enter s = some s.enterMem := by simp only [atS, hs]
         rw [e1] at he
         refine ⟨?_, by simp only [S.rows, hs]⟩
         rw [← Option.some.inj he]
         simp only [S.enterMem, hs])
  | lay a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he
  | att a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he
  | head a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he
  | mem a =>
    have e1 : atS.enter s = none := by simp only [atS, hs]
    rw [e1] at he
    cases he

/-- **Where the block says yes**: the rows on the table stay; the claim behind is made of a row; W's
vector fits its table. -/
theorem oneRowB_ok {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (oneRowB (Cl := Cl) atS P).decide s rs gs = .ok s') :
    s'.rows = s.rows ∧ (∀ l, linAt s' = some l → ∃ row, l.claim = memberClaim row) ∧
      P.lin.kCol ≤ (linLayW s'.st.codes P.lin).bits := by
  simp only [oneRowB, still, bind_ok, there_ok, Lens.part] at h
  obtain ⟨t₁, h1, p, hp, one, hone, h3⟩ := h
  obtain ⟨rfl, hrows⟩ := enter_eq (frontB_ok atS P h1)
  obtain rfl := Option.some.inj hp
  have hpile : s.out.pending = [one] := by
    have hone' : (match s.out.pending with | [r] => some r | _ => none) = some one := hone
    split at hone'
    · next r hr => rw [hr, Option.some.inj hone']
    · cases hone'
  obtain ⟨p', msg, hp', hl, rfl⟩ := quietB_lin atS P h3
  obtain rfl := Option.some.inj hp'
  refine ⟨?_, fun l hl' => ⟨one, ?_⟩, fits_of_linOk hl⟩
  · rw [hrows, hpile]
    show [rowOfClaim (memberClaim one)] = [one]
    rw [rowOfClaim_member]
  · have e : some ({ claim := memberClaim one } : LinFirst) = some l := hl'
    rw [← Option.some.inj e]

/-- **The law of the block for a pile of one row.** -/
theorem oneRowB_goodIn (F : Frame) (P : Where) (base : ℕ) {k : ℕ} (rw : W → Wit GE nR k)
    (Pin : F.E.Str → W → Prop)
    (hback : ∀ a τ b w, (pieceQuiet (Cl := Cl) (W := W) F (oneRowB atS P) base).ior.red.out a τ =
      some b → Pin b.2 w → Pin a.2 w) :
    (pieceQuiet (Cl := Cl) (W := W) F (oneRowB atS P) base).GoodIn (fun _ => True) (FrontOk P)
      (RowsHold rw Pin) (RowsHold rw Pin) := by
  intro a _
  show ∀ b, _ = some b → _
  intro b hb
  obtain ⟨gs, hdec⟩ := quiet_ok hb
  obtain ⟨hr, hc, hf⟩ := oneRowB_ok hdec
  exact ⟨fun l hl => ⟨hc l hl, hf⟩, fun w hw => ⟨hback a () b w hb hw.1, by rw [← hr]; exact hw.2⟩⟩

end VerifiableInference.Desc.K13.Law
