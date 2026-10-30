-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Lays.lean: THE TABLE's EXTRACTOR AT A CODE SWITCH, WRITTEN OUT. Four theorems.
    A law file: no sub-protocol imports it.

Why. The structure of ties (`TiesAtR`, Johnson/Top/H0/Tw/K2C/TiedFormR.lean) has a field lays: at
    every accept the piece's own extractor is the table's. The fourth tie takes the piece's
    extractor written out (`extAt` at no member whose message is laid, the members whose pads are
    laid, no cells, no token). Here the table's extractor at a place of the kind K2 is shown to be
    that term.

What is said.
  `mineAt_switch`: at a place of the kind K2 no member's message is laid. `laysTok_switch`: nor the
      token.
  `extQAt_switch`: so `extQAt … k a b w` = `extAt cs G arr smp decT c₀ [] (minePadAt ms N links p)
      false none (get a.1) (strsOf Fr a.2) w`: it does not read the statement behind.
  `lays_of_ext`: THE FIELD lays, in its own form, for any piece: from "the extractor is that term,
      read at the state alone with the public part z beside it".

Limits. That a description's piece bears that extractor is a premise. OTHER FILES HAVE
    mineAt_K2 · laysTok_K2 · minePadAt_K2 (Johnson/Desc/Sound/MembersAtB.lean):
    the first two here may be their twins. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.TiedLays
import Johnson.Top.H0.K2Ties.PadsTurn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Place Wit FileDescription KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers laysSeats laysTok rowOf)

theorem mineAt_switch (ms : List Mem) (N : Numbers) (links : List ModelPart) (p : Place) (hk : p.kind =
          KindName.K2) : mineAt ms N links p = [] := by
  have h1 : laysSeats N links p = [] := by
    unfold laysSeats
    rw [hk]
    split <;> rfl
  unfold mineAt
  rw [h1]
  exact List.filter_eq_nil_iff.2 fun _ _ h => by cases h

theorem laysTok_switch (links : List ModelPart) (p : Place) (hk : p.kind = KindName.K2) : laysTok links p
    = false := by
  unfold laysTok
  rw [hk]
  cases (rowOf links p).lays <;> rfl

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (smp : P ×
           First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List
           Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells) (c₀ : Cells) (tokOf :
           P × First.S → Tok)

/-- **The table's extractor at a code switch, written out.** -/
theorem extQAt_switch {A : Type} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (p : Place) (hp : ps[k]? = some p) (hk : p.kind = KindName.K2)
    (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w = extAt cs G arr smp decT c₀ []
        (minePadAt ms N links p) false none (get a.1) (strsOf Fr a.2) w := by
  unfold extQAt
  rw [hp]
  show extQ cs G arr smp ms decT c₀ tokOf N links p (get a.1) (strsOf Fr a.2) (some (get b.1)) w = _
  unfold extQ
  rw [mineAt_switch ms N links p hk, laysTok_switch links p hk]
  rfl

/-- **The field lays**, for any piece over the state alone. -/
theorem lays_of_ext {Fr : Frame} {C : CK} {Cl : Type} (N : Numbers) (links : List ModelPart) (ps : List
          Place) (k : ℕ) (p : Place) (hp : ps[k]? = some p) (hk : p.kind = KindName.K2) (q : P → Piece C
          Fr First.S Cl (Wit Cells Tok MsgT)) (hext : ∀ z a τ w, (q z).ext a τ w = extAt cs G arr smp decT
          c₀ [] (minePadAt ms N links p) false none (z, a.1) (strsOf Fr a.2) w) :
    ∀ z a τ b w, (q z).ior.red.out a τ = some b → (q z).ext a τ w = atPub (extQAt cs G arr smp ms
        decT c₀ tokOf N links ps (fun x => x) k) z a b w := by
  intro z a τ b w _
  rw [hext]
  exact (extQAt_switch cs G arr smp ms decT c₀ tokOf N links ps (fun x => x) k p hp hk ((z, a.1),
      a.2) ((z, b.1), b.2) w).symm

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.mineAt_switch
#print axioms VerifiableInference.Desc.First.K2Ties.laysTok_switch
#print axioms VerifiableInference.Desc.First.K2Ties.extQAt_switch
#print axioms VerifiableInference.Desc.First.K2Ties.lays_of_ext
