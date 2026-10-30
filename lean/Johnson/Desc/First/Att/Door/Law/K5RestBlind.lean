-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5RestBlind.lean: kind K5: WHAT THE COMPOSED MEANING's LETTERS (P5J.At, Johnson/P5J/LettersAt.lean) DO NOT READ: SMALL LAWS ON TERMS OF OTHER FILES (the table saysNone · smpNamed · rwBook · digitsPartK3 · headPartK6 with tokHOf · K3Lot.ofForm), FROM WHICH
THE FIELDS "BY THE MAKE" OF K5Rest (K5AtMgPaid.lean) FALL AT THE CLOSED CONSTANT (K5RestMake.lean). NO COMPOSED MEANING IS IMPORTED HERE: so the file compiles over few files.

Main names:
  `said_touched`: at each item that the kind's law touches (one of the twenty that may be open in front; three that the row makes), the wider filling's five names and the item left apart, the table saysNone
    (Johnson/Desc/First/AllSaid.lean) has an answer. The premise hQ is K5Table.openQ's own text: no list is unfolded.
  `smpROf`, `smpIs_named`: THE CHOICE of the filled pin's reader of samples: smp1At at the statement that holds the given oracle messages and nothing else; it is smpNamed at every state with these oracle messages.
  `smpq_named`, `rwq_book`: the kind's lay (behind) leaves the statement and the book: so smpNamed and rwBook.
  `digits_blind`: digitsPartK3 reads neither the state nor the strings. `head_behind`: headPartK6 with tokHOf rides over the lay, where H.req does (headPartK6_blind, Johnson/Desc/Kinds/Law/HeadCutsK6.lean).
  `clForm_lot`: the field clForm at the seated maker of claims K3Lot.ofForm.
Is it empty here? Laws at every state; said_touched's premise is decided at the written lists elsewhere (K5ListsFull.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.AllSaid
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.First.Look.K3FillDigits
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.P5J.TokTerms
import Johnson.Desc.ProofFile.Lot.K3
import Johnson.Desc.First.Att.Door.Law.K5AtMgPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (behind)

/-- **At each item that the kind's law touches the table saysNone has an answer.** -/
theorem said_touched (m : ℕ) (Q : List Pub)
    (hQ : ∀ q ∈ Q, q ∈ ten m ∨ q ∈ quiet9 m ∨ q = .more (some m) "ledger.treesAre" ∨ q = .more (some m) "K5.lookLeft") (q : Pub)
    (hq : q ∈ Q ∨ q ∈ made3 m) (hw : isWideQ q = false) (hl : ∀ m', q ≠ .left m') : (saysNone q).isSome = true := by
  rcases hq with hq | hq
  · rcases hQ q hq with h | h | rfl | rfl
    · simp only [ten, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact absurd rfl (hl _)
    · simp only [quiet9, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact absurd hw (by simp [isWideQ, isWide, isThree, isOurs])
    · rfl
    · exact absurd hw (by simp [isWideQ, isWide, isThree, isOurs])
  · simp only [made3, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> rfl

section
variable {P : Type} (cs : Codes) (seats : List (ℕ × ℕ))

/-- **The choice of the filled pin's reader of samples**: off the oracle messages alone. -/
noncomputable def smpROf (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (ob : Array OnBytes.Oracle × OnBytes.TreeBook)
    (i : Fin l.length) : Option ((sigOf cs l).om i).Smp :=
  smp1At cs seats { oracles := ob.1 } (l.get i) (seat i)

/-- It is smpNamed at every state with these oracle messages. -/
theorem smpIs_named (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (π : P) (s : S) (i : Fin l.length) :
    smpROf cs seats l seat (s.st.oracles, s.book) i = smpNamed cs seats (π, s) ⟨l, seat⟩ i := by
  show smp1At cs seats { oracles := s.st.oracles } (l.get i) (seat i) = smp1At cs seats s.st (l.get i) (seat i)
  unfold smp1At
  split
  · exact smpAt_stays cs _ _ s.st _ _ rfl rfl
  · rfl

/-- The kind's lay leaves the statement: so smpNamed. -/
theorem smpq_named (π : P) (s : S) (a : AttOwn) (h : _) (G : Fork) :
    smpNamed cs seats (π, behind s a h G) = smpNamed cs seats (π, s) := rfl

end

/-- The kind's lay leaves the statement and the book: so rwBook. -/
theorem rwq_book {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin k → Bool) → OnBytes.Slice.GE) (π : Pp) (s : S)
    (a : AttOwn) (h : _) (G : Fork) :
    K13.Law.rwBook (Tok := Tok) arr mat (π, behind s a h G) = K13.Law.rwBook arr mat (π, s) := rfl

/-- digitsPartK3 reads neither the state nor the strings. -/
theorem digits_blind {P Cells Tok : Type} (X : Verify.Public) (D : Look.Sent) (L : VerifiableInference.OnPublicFiles.K3Letters Cells Tok) (m : ℕ)
    (a a' : P × S) (y y' : Strs) (w : Wit Cells Tok MsgT) :
    VerifiableInference.OnPublicFiles.digitsPartK3 X D L m a y w = VerifiableInference.OnPublicFiles.digitsPartK3 X D L m a' y' w := rfl

/-- The heard token rides over the kind's lay. -/
theorem tokH_behind {P : Type} (π : P) (s : S) (a : AttOwn) (h : _) (G : Fork) :
    P5J.tokHOf (π, behind s a h G) = P5J.tokHOf (π, s) := rfl

/-- **The field clForm at the seated maker of claims.** -/
theorem clForm_lot : ∀ f, (K3Lot.ofForm f).form = f ∧ (K3Lot.ofForm f).runs.isEmpty = true ∧ (K3Lot.ofForm f).eqFirst.isNone = true :=
  fun _ => ⟨rfl, rfl, rfl⟩

end H2K5.Door

#print axioms H2K5.Door.said_touched
#print axioms H2K5.Door.smpIs_named
#print axioms H2K5.Door.smpq_named
#print axioms H2K5.Door.rwq_book
#print axioms H2K5.Door.digits_blind
#print axioms H2K5.Door.tokH_behind
#print axioms H2K5.Door.clForm_lot
