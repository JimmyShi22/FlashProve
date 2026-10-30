-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/ReadersSayAt.lean: the honest side of the kind "lookup" (K3).
The seated text's fold over the planes' columns (`planesAtF`,
Johnson/Desc/First/Look/LookPlanes.lean), at readers that answer or reject and change nothing, is
the plain form `planesAff` (OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean). So, conditional on the
caller's columns' law (`ColsSay`, Honest/K3/Law/ReadersSayOf.lean), what it yields is worth the
planes' value under the equality pairs of the point: the clauses at0 and at1 of `ReadersSay`
(Honest/K3/Law/SeatedWorth.lean). Theorems.

Terms. Honest/K3/GLOSSARY.md ("count, bits, planes", "form", "reader, readers", "world, worth"). The
flat monad is `Fl` (OnBytes/K/Kc/Flat.lean): a function from a ledger and a tape to a value with a
ledger and a tape, or nothing.

What is shown.
  `fl_bind_none`, `fl_need_none`: in the flat monad, a bind behind a step that rejected rejects.
  `fl_fold_need`: a fold whose step asks a reader and goes on plainly is a plain fold.
  `planesAtF_is`: the seated fold is `planesAff` at the readers' forms; ledger and tape are as they
    were.
  `at_of_cols`: the clause of `ReadersSay`, at either point.

Hypotheses that remain, in `at_of_cols`.
  `hB`: `ColsSay`. Shown at the constant forms `readersAt` alone (Thread/ExchangePlanes.lean).
  `ha`: the seated fold returns.
  The others are those of `planes_of_cols` (ReadersSayOf.lean): `h0`, `hbit`, `hNC`, `h5`, `hlm`,
    `hsh`, `hz`, `hD`.
In the steps: `h`: the step in front rejected (in `fl_bind_none`); the seated fold returns (in
`planesAtF_is`). `fl_fold_need` has a hypothesis without a name: the fold returns.

Users. Honest/K3/Law/ReadersSayCount.lean imports this file.

Limits. No instance of these hypotheses is exhibited in this file. The count's clause is not
reached.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.ReadersSayOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.Model.Forest (Shape)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.HonestTrace.Look (Data)
open VerifiableInference.Desc.K3 (eqPairs)
open VerifiableInference.Desc.First.Look (planesAtF)
open ProofFile.Honest.K3.Law (fl_bind_some fl_need_some)

variable {α β : Type}

theorem fl_bind_none {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} (h : x F t = none) :
    (x >>= f) F t = none := by
  show Fl.andThen x f F t = _
  unfold Fl.andThen
  rw [h]

theorem fl_need_none (F : Fork) (t : Tape) : Fl.need (none : Option α) F t = none := by
  unfold Fl.need
  rfl

/-- A fold whose step asks a reader and goes on plainly is a plain fold, and changes neither ledger
nor tape. -/
theorem fl_fold_need (x : Nat → Option Aff) (step : Aff → Nat → Aff → Aff) (F : Fork) (t : Tape) :
    ∀ (l : List Nat) (s a : Aff) (G : Fork) (u : Tape),
    l.foldlM (fun (f : Aff) col => Fl.need (x col) >>= fun y => (pure (step f col y) : Fl Aff)) s F
      t =
      some (a, G, u) →
    a = l.foldl (fun f col => step f col ((x col).getD {})) s ∧ G = F ∧ u = t
  | [], s, a, G, u, h => by
    have h' : some (s, F, t) = some (a, G, u) := h
    cases h'
    exact ⟨rfl, rfl, rfl⟩
  | col :: l, s, a, G, u, h => by
    rw [List.foldlM_cons] at h
    cases hx : x col with
    | none =>
      rw [hx, fl_bind_none (fl_bind_none (fl_need_none F t))] at h
      cases h
    | some y =>
      have h1 : (Fl.need (x col) >>= fun y => (pure (step s col y) : Fl Aff)) F t =
          some (step s col y, F, t) := by
        rw [fl_bind_some (fl_need_some hx F t)]
        rfl
      rw [fl_bind_some h1] at h
      have := fl_fold_need x step F t l _ a G u h
      rw [List.foldl_cons, hx]
      exact this

/-- **The seated fold over the planes' columns is the plain form**, at the readers' forms. -/
theorem planesAtF_is (g' : OnBytes.Model.Forest.Heard) (lm e : Nat) (b : Nat → Nat → Option Aff)
    {F G : Fork} {t u : Tape} {a : Aff}
    (h : planesAtF g' lm e (fun e col => Fl.need (b e col)) F t = some (a, G, u)) :
    a = Cb.Fo.PlaneClaims.planesAff g' lm e (fun col => (b e col).getD {}) ∧ G = F ∧ u = t := by
  have h' : (List.range (g'.shape.NC * 2 ^ (g'.shape.kT + 5 - lm))).foldlM
      (fun (f : Aff) col => Fl.need (b e col) >>= fun y => (pure (Aff.addMul f y
        (OnBytes.mulE
          ((OnBytes.Model.eqTab ((g'.zb e).extract g'.shape.kT (g'.shape.kT + g'.shape.cK))).getD
            (col / 2 ^ (g'.shape.kT + 5 - lm)) zeroE)
          ((OnBytes.Model.eqTab ((g'.zb e).extract 0 (g'.shape.kT + 5 - lm))).getD
            (col % 2 ^ (g'.shape.kT + 5 - lm)) zeroE))) : Fl Aff))
      (Aff.ofConst zeroE) F t = some (a, G, u) := h
  have k := fl_fold_need (b e) (fun f col y => Aff.addMul f y
    (OnBytes.mulE
      ((OnBytes.Model.eqTab ((g'.zb e).extract g'.shape.kT (g'.shape.kT + g'.shape.cK))).getD
        (col / 2 ^ (g'.shape.kT + 5 - lm)) zeroE)
      ((OnBytes.Model.eqTab ((g'.zb e).extract 0 (g'.shape.kT + 5 - lm))).getD
        (col % 2 ^ (g'.shape.kT + 5 - lm)) zeroE))) F t _ _ a G u h'
  unfold Cb.Fo.PlaneClaims.planesAff
  exact k

/-- **Conditional on the caller's columns' law (`ColsSay`): what the seated fold yields is worth the
planes' value under the equality pairs of the point.** No instance of these hypotheses is exhibited
in this file. -/
theorem at_of_cols (h : Shape) (lm jLK : Nat) (θ : KE) (μ : _root_.Fo.Pl → KE)
    (h0 : μ .zero = 0) (hNC : h.NC ≤ 2 ^ h.cK) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5)
    (g' : OnBytes.Model.Forest.Heard) (hsh : g'.shape = h) (e : Nat)
    (hz : (g'.zb e).size = 5 + h.d) (b : Nat → Nat → Option Aff) (Wd : World KE)
    (hB : ColsSay h lm (_root_.Fo.rdL Reading.gl (g'.zb e)) μ (fun col => (b e col).getD {}) Wd)
    (D : Data _root_.Fo.Pl KE) (hD : D.N = _root_.Fo.numsF h lm jLK θ)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = μ (D.N.bAt u j))
    {F G : Fork} {t u : Tape} {a : Aff}
    (ha : planesAtF g' lm e (fun e col => Fl.need (b e col)) F t = some (a, G, u)) :
    a.value Reading.gl Wd = planesOf D (eqPairs (5 + h.d) (g'.zb e)) := by
  rw [(planesAtF_is g' lm e b ha).1]
  exact planes_of_cols h lm jLK θ μ h0 hNC h5 hlm g' hsh e hz _ Wd hB D hD hbit

#print axioms ProofFile.Honest.K3.Law.Spec.fl_bind_none
#print axioms ProofFile.Honest.K3.Law.Spec.fl_need_none
#print axioms ProofFile.Honest.K3.Law.Spec.fl_fold_need
#print axioms ProofFile.Honest.K3.Law.Spec.planesAtF_is
#print axioms ProofFile.Honest.K3.Law.Spec.at_of_cols

end ProofFile.Honest.K3.Law.Spec
