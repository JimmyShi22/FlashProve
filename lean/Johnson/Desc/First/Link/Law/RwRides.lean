-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RwRides.lean: THE THREE PREMISES hR1, hR2, hR3 OF THE LINK's LAW
(link_table | link_table_more | link_table_worth) AT THE PUBLIC SENTENCE THAT THE COMPOSED MEANING
ITSELF CARRIES BESIDE "total" AND "totalB": Rw := `rwAt 𝔇 m` (TieThreeFour.lean: 𝔇.rw m a.1 = true),
WHERE 𝔇.rw m IS THE TEST WITH CODE `K9.rowsFit rows` (Johnson/Desc/First/Batch/OwedLaid.lean: "the
plan's claims and the ties' and reads' indices are at most the batching round's rows"), as it is at
the closed constant (P5T.rwAt, where the plan has such a round). Theorems.

THE THREE LAY ALREADY, AT ANOTHER WORD FOR THE SAME SENTENCE: rows_hR1 | rows_hR2 |
rows_hR3 (Johnson/Desc/First/Batch/Law/RowsRide.lean) at `rowsAt rows u s`, a Prop over the record
with its written fields blanked. WHAT IS NEW HERE IS THE BRIDGE, which OwedLaid.lean's head says
was "held by reading, not by Lean".

What is said.
  `rowsFit_iff`: **K9.rowsFit rows s = true ↔ rowsAt rows u s**, at every u (by
    top8_topOf's and topOf_blank's rfl).
  `hon2_of_tests`: the two public things that rows_hR3 asks of a state in front of the one
    equation's piece are what the tests with code `K9.owedIs rows` and `K9.laidIs` say.
  `rw_hR3`, `rw_hR2`, `rw_hR1`: the three at Rw := fun a => K9.rowsFit p.rows a.1 = true.
  `rwAt_hR3`, `rwAt_hR2`, `rwAt_hR1`: the same at Rw := rwAt 𝔇 m, under hrw (𝔇.rw m is that
    test).

Limits. PREMISES: hrw (a closed fact at the constant) · the law's own hpb hpq hpe hb₁ hb₂ hb₃ hπ ·
`MoveNum u` of every move of the link (shown in NumRuns.lean: `moveNum_layers`,
`moveNum_attention`, `moveNum_head`: at every move of `moves₁ L rl ++ moves₂ L`, under `SegAt`, the
sort's Take and k3f: each of the lookup's runs at the link leaves `numOf v`: IMPLICATIONS: no Take
is shown of a link there; nothing here ties the letter ms of `rw_hR1` | `rw_hR2` to
these moves) ·
**AT hR3: `K9.owedIs p.rows` AND `K9.laidIs` AT EVERY STATE IN FRONT OF THE ONE EQUATION's
PIECE THAT MEETS on2: SHOWN AT NO STATE HERE; NO ITEM OF THE PROMISE SAYS THEM** (by
report): they must come along the run. Nothing on soundness.

-/
import Johnson.K9R.OwedLaid
import Johnson.Desc.First.Batch.Law.RowsRide
import Johnson.Desc.First.Link.Law.TieThreeFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open _root_.Run (ckP)

/-- **THE BRIDGE: the test with code says the law's sentence.** -/
theorem rowsFit_iff (rows : ℕ) (u : HTailF2) (s : S) :
    K9.rowsFit rows s = true ↔ rowsAt rows u s := by
  unfold K9.rowsFit rowsAt K9L.numOf
  rcases s.tl? with _ | tl
  · exact ⟨fun _ tlb f n e => by simp at e, fun _ => by cases s.funs? <;> cases s.fork? <;> rfl⟩
  · rcases s.funs? with _ | funs
    · exact ⟨fun _ tlb f n e => by simp at e, fun _ => by cases s.fork? <;> rfl⟩
    · rcases s.fork? with _ | G
      · exact ⟨fun _ tlb f n e => by simp at e, fun _ => rfl⟩
      · constructor
        · intro h tlb f n e
          simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          exact of_decide_eq_true h
        · intro h
          have h' := h (blank u tl) funs G.planClaimsF rfl
          exact decide_eq_true h'

/-- **The two public things in front of the one equation's piece, from the tests with code.** -/
theorem hon2_of_tests (rows : ℕ) (u : HTailF2) (s : S) (h1 : K9.owedIs rows s = true)
    (h2 : K9.laidIs s = true) : ∀ x tl funs, atS.get? s = some x → s.tl? = some tl →
      s.funs? = some funs → x.owed = some rows ∧ x.laid = some (top8 (blank u tl) funs) := by
  intro x tl funs hx ht hf
  unfold K9.owedIs at h1
  unfold K9.laidIs at h2
  rw [hx] at h1
  rw [hx, ht, hf] at h2
  exact ⟨by simpa using h1, by simpa using h2⟩

section
variable {α Cl W : Type} {F : Frame}

/-- **hR3.** -/
theorem rw_hR3 (u : HTailF2) (p pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (pe : Piece (ckP .two) F S Cl W) (hpe : pe.b = below b₃) (on2 : S × F.E.Str → Prop)
    (hon2 : ∀ a, on2 a → K9.owedIs p.rows a.1 = true ∧ K9.laidIs a.1 = true) :
    ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → K9.rowsFit p.rows a.1 = true :=
  fun a τ b' ha hout => (rowsFit_iff p.rows u a.1).2
    (rows_hR3 u p pw b₃ hb₃ pe hpe on2
      (fun a ha => hon2_of_tests p.rows u a.1 (hon2 a ha).1 (hon2 a ha).2) a τ b' ha hout)

/-- **hR2.** -/
theorem rw_hR2 (u : HTailF2) (rows : ℕ) (ms : List (Move S)) (b₂ : Block S Cl)
    (hb₂ : IsMoves atS ms b₂) (hms : ∀ m ∈ ms, MoveNum u m)
    (pq : Piece (ckP .two) F S Cl W) (hpq : pq.b = below b₂) :
    ∀ a τ b', pq.ior.red.out a τ = some b' → K9.rowsFit rows b'.1 = true →
      K9.rowsFit rows a.1 = true :=
  fun a τ b' hout h => (rowsFit_iff rows u a.1).2
    (rows_hR2 u rows ms b₂ hb₂ hms pq hpq a b' τ hout ((rowsFit_iff rows u b'.1).1 h))

/-- **hR1.** -/
theorem rw_hR1 (u : HTailF2) (φ : S → α) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (p : Where) (ms : List (Move S))
    (b₁ : Block S Cl) (hb₁ : DrawMoves atS p ms b₁) (hms : ∀ m ∈ ms, MoveNum u m)
    (pb : Piece (ckP .two) F S Cl W) (hpb : pb.b = below b₁) :
    ∀ a τ b', pb.ior.red.out a τ = some b' → K9.rowsFit p.rows b'.1 = true →
      rowsFit p.rows π (fixed9 φ a.1) :=
  fun a τ b' hout h =>
    rows_hR1 u φ π hπ p ms b₁ hb₁ hms pb hpb a b' τ hout ((rowsFit_iff p.rows u b'.1).1 h)

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {α Cl W : Type} {F : Frame} (m : ℕ)

/-- **hR3 AT THE COMPOSED MEANING's OWN SENTENCE.** -/
theorem rwAt_hR3 (u : HTailF2) (p pw : Where) (hrw : ∀ s, 𝔇.rw m s = K9.rowsFit p.rows s)
    (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (pe : Piece (ckP .two) F S Cl W) (hpe : pe.b = below b₃) (on2 : S × F.E.Str → Prop)
    (hon2 : ∀ a, on2 a → K9.owedIs p.rows a.1 = true ∧ K9.laidIs a.1 = true) :
    ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → rwAt 𝔇 m a := by
  intro a τ b' ha hout
  show 𝔇.rw m a.1 = true
  rw [hrw]
  exact rw_hR3 u p pw b₃ hb₃ pe hpe on2 hon2 a τ b' ha hout

/-- **hR2 there.** -/
theorem rwAt_hR2 (u : HTailF2) (r : ℕ) (hrw : ∀ s, 𝔇.rw m s = K9.rowsFit r s)
    (ms : List (Move S)) (b₂ : Block S Cl) (hb₂ : IsMoves atS ms b₂)
    (hms : ∀ m ∈ ms, MoveNum u m) (pq : Piece (ckP .two) F S Cl W) (hpq : pq.b = below b₂) :
    ∀ a τ b', pq.ior.red.out a τ = some b' → rwAt 𝔇 m b' → rwAt 𝔇 m a := by
  intro a τ b' hout h
  have h' : 𝔇.rw m b'.1 = true := h
  show 𝔇.rw m a.1 = true
  rw [hrw] at h' ⊢
  exact rw_hR2 u r ms b₂ hb₂ hms pq hpq a τ b' hout h'

/-- **hR1 there.** -/
theorem rwAt_hR1 (u : HTailF2) (φ : S → α) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (p : Where)
    (hrw : ∀ s, 𝔇.rw m s = K9.rowsFit p.rows s) (ms : List (Move S)) (b₁ : Block S Cl)
    (hb₁ : DrawMoves atS p ms b₁) (hms : ∀ m ∈ ms, MoveNum u m)
    (pb : Piece (ckP .two) F S Cl W) (hpb : pb.b = below b₁) :
    ∀ a τ b', pb.ior.red.out a τ = some b' → rwAt 𝔇 m b' → rowsFit p.rows π (fixed9 φ a.1) := by
  intro a τ b' hout h
  have h' : 𝔇.rw m b'.1 = true := h
  rw [hrw] at h'
  exact rw_hR1 u φ π hπ p ms b₁ hb₁ hms pb hpb a τ b' hout h'

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsFit_iff
#print axioms VerifiableInference.Desc.LinkJoin.hon2_of_tests
#print axioms VerifiableInference.Desc.LinkJoin.rwAt_hR3
#print axioms VerifiableInference.Desc.LinkJoin.rwAt_hR2
#print axioms VerifiableInference.Desc.LinkJoin.rwAt_hR1
