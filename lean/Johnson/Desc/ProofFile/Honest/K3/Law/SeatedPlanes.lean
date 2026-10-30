-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SeatedPlanes.lean: the seated run of claims on the planes
returns: `planesRun` (Johnson/Desc/First/Look/K3Runs.lean), through `planeClaimsOwn` and
`leavesRowOwn` (Johnson/Desc/First/Look/LookPlanesOwn.lean). Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("claim", "count, bits, planes", "reader, readers", "run (of claims)",
"seat"). The flat monad is `Fl` (OnBytes/K/Kc/Flat.lean).

What is shown.
  `fl_bind_some`, `fl_foldlM_same`: in the flat monad: a bind behind a step that returned; a fold of
    steps that leave ledger and tape as they are.
  `planesAtF_returns`: the planes' value as a form, where the caller's reader answers.
  `planeClaimsOwn_returns`: three claims, where the packing's test holds, the caller's two readers
    answer and the leaves' late claim returns.
  `planesRun_returns`: the run: besides, a ledger is open at the seat, what was heard is stored
    there, and the debt is not yet marked as paid.

Hypotheses that remain.
  The caller's readers are letters: that they answer at every column is a hypothesis (`hr`, `hb`,
    `hpn`).
  The seat's three in front (`hF`, `hg`, `hu`): a ledger is open; what was heard is stored; the debt
    is not yet marked.
  The packing's test (`hpo`; public).
  `hrow`: the leaves' late claim returns at the ledger of the run. (Honest/K3/Law/SeatedAll.lean has
    it from "the leaves' own slots are still owed" there.)
  `h`: (in `fl_bind_some`, `fl_need_some`) the step in front returned.
  `fl_foldlM_same` has a hypothesis without a name: every step returns and leaves ledger and tape.

Users. This file is imported by Honest/K3/Law/PlanesG.lean, Honest/K3/Law/SeatedAll.lean,
Honest/K3/Law/SeatedWorth.lean, Honest/K3/Law/Thread/Group11.lean [not in this library] and
Honest/K3/Shape/ClaimPlanes.lean.

Limits. At a layers' link the planes' claims are made in another kind's runs: not reached here.
Shown in part: Honest/K3/Law/Thread/Group11.lean [not in this library; so here read: not proved in
this library]. `planes_twin`: where the other kind's text of these claims returns, and its text of
the leaves' late claim returns at what the first keeps, the seated text `planeClaimsOwn` returns at
the other kind's readers, with the same three forms and the same ledger behind. `rowL_returns` and
`group11_returns`: behind the lookup's hearing, the other kind's hearing and the late claim that its
run makes first, the leaves' late claim returns, and so do the three; conditional on these returns,
on the leaves' own slots being still owed at the ledger from which the other kind hears, on the
other kind's text of these claims returning, and on the other kind holding the structure of the
leaves' sumcheck that the lookup heard. What the three are worth there: `group11_zero`
(Honest/K3/Law/Thread/Group11Worth.lean [not in this library; so here read: not proved in this
library]), conditional on `Left`, on the other kind's readers' law and on what that file's head
lists. By the head of Group11.lean [not in this library], that the other kind's readers answer is
for the files of the other kind to show. Nothing is said on what the claims are worth.
Instances: Honest/K3/Law/SeatedGuards.lean [not in this library; so here read: not tested in this
library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Seated
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG toPsc Seat planesRun unpaid
  Readers)
open VerifiableInference.Desc.First.Look
  (leavesRowOwn planeClaimsOwn planesAtF planesOk planesAddedF)

variable {α β γ : Type}

/-! ## The flat monad -/

theorem fl_bind_some {x : Fl α} {f : α → Fl β} {F G : Fork} {t u : Tape} {a : α}
    (h : x F t = some (a, G, u)) : (x >>= f) F t = f a G u := by
  show Fl.andThen x f F t = _
  unfold Fl.andThen
  rw [h]

theorem fl_need_some {x : Option α} {a : α} (h : x = some a) (F : Fork) (t : Tape) :
    Fl.need x F t = some (a, F, t) := by
  unfold Fl.need
  rw [h]
  rfl

theorem fl_foldlM_same (f : β → γ → Fl β) (F : Fork) (t : Tape) : ∀ (l : List γ) (s : β),
    (∀ s, ∀ a ∈ l, ∃ s', f s a F t = some (s', F, t)) → ∃ s', l.foldlM f s F t = some (s', F, t)
  | [], s, _ => ⟨s, rfl⟩
  | a :: l, s, h => by
    obtain ⟨s1, h1⟩ := h s a (List.mem_cons_self ..)
    obtain ⟨s2, h2⟩ := fl_foldlM_same f F t l s1 fun s b hb => h s b (List.mem_cons_of_mem _ hb)
    refine ⟨s2, ?_⟩
    rw [List.foldlM_cons, fl_bind_some h1]
    exact h2

/-! ## The three claims -/

/-- How many columns the planes' matrix has. (This text stands as `planeCount` in
Johnson/Desc/First/Look/PlaneWeights.lean [not in this library]; the tie:
`planeColsOf_eq_planeCount`, Honest/K3/Law/TiesSealedForms.lean [not in this library].) -/
def planeColsOf (h : Shape) (lm : Nat) : Nat := h.NC * 2 ^ (h.kT + 5 - lm)

/-- The planes' value at one of the two points, as a form: it returns, and leaves ledger and tape as
they are, where the caller's reader answers at every column.
Conditional on the reader's answers. -/
theorem planesAtF_returns (g : OnBytes.Model.Forest.Heard) (lm e : Nat) (b : Nat → Nat → Option Aff)
    (hb : ∀ col, col < planeColsOf g.shape lm → (b e col).isSome = true) (F : Fork) (t : Tape) :
    ∃ a, planesAtF g lm e (fun e col => Fl.need (b e col)) F t = some (a, F, t) := by
  unfold planesAtF
  refine fl_foldlM_same _ F t _ _ fun s col hcol => ?_
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hb col (List.mem_range.1 hcol))
  exact ⟨_, by rw [fl_bind_some (fl_need_some hx F t)]; rfl⟩

/-- **The three claims that read the planes are made.**
Conditional on the packing's test, the caller's two readers' answers at every column, and the return
of the leaves' late claim. -/
theorem planeClaimsOwn_returns (g : OnBytes.Model.Forest.Heard) (lm : Nat)
    (b : Nat → Nat → Option Aff) (pn : Nat → Option Aff) (hpo : planesOk g.shape lm = true)
    (hb : ∀ e col, col < planeColsOf g.shape lm → (b e col).isSome = true)
    (hpn : ∀ col, col < planeColsOf g.shape lm → (pn col).isSome = true) {F G : Fork} (t : Tape)
    (hrow : ∀ kept, leavesRowOwn g.leaves oneE kept F t = some (g.leaves.rowForm oneE kept, G, t)) :
    ∃ fs, planeClaimsOwn g lm (fun e col => Fl.need (b e col)) (fun col => Fl.need (pn col)) F t =
      some (fs, G, t) ∧ fs.size = 3 := by
  obtain ⟨a0, h0⟩ := planesAtF_returns g lm 0 b (hb 0) F t
  obtain ⟨a1, h1⟩ := planesAtF_returns g lm 1 b (hb 1) F t
  obtain ⟨c, hc⟩ := fl_foldlM_same
    (fun (f : Aff) col => do pure (f + (← (fun col => Fl.need (pn col)) col))) F t
    (List.range (g.shape.NC * 2 ^ (g.shape.kT + 5 - lm)))
    (Aff.ofConst (OnBytes.negE (OnBytes.ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)))
    (fun s col hcol => by
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hpn col (List.mem_range.1 hcol))
      refine ⟨s + x, ?_⟩
      show (Fl.need (pn col) >>= fun y => (pure (s + y) : Fl Aff)) F t = _
      rw [fl_bind_some (fl_need_some hx F t)]
      rfl)
  have hm : Fl.must (planesOk g.shape lm) F t = some ((), F, t) := by
    unfold Fl.must
    rw [hpo]
    rfl
  refine ⟨#[g.leaves.rowForm oneE (Aff.scale a0 g.leavesA), Aff.slot g.sBit - a1, c], ?_, rfl⟩
  unfold planeClaimsOwn
  dsimp only
  rw [fl_bind_some hm, fl_bind_some h0, fl_bind_some h1, fl_bind_some hc, fl_bind_some (hrow _)]
  rfl

/-- **The seated run of claims on the planes returns**, with three claims; behind it the seat's
ledger is the one behind the leaves' late claim, with the debt marked as paid.
Conditional on: a ledger is open at the seat; what was heard is stored there; the debt is not yet
marked; the caller's readers are there and answer at every column; the packing's test; the return of
the leaves' late claim. Instances and alterations: Honest/K3/Law/SeatedGuards.lean
[not in this library] (by evaluation). -/
theorem planesRun_returns {S Cl : Type} (seat : Seat S Cl) (lm : Nat) (readers : Readers S)
    (n : Nat)
    (s : S) {F G : Fork} {g : OnBytes.Model.Forest.Heard}
    {r : (Nat → Nat → Option Aff) × (Nat → Option Aff)} (hF : seat.fork s = some F)
    (hg : seat.heard s = some g) (hu : unpaid F g.owedPlanes = true) (hr : readers s = some r)
    (hpo : planesOk g.shape lm = true)
    (hb : ∀ e col, col < planeColsOf g.shape lm → (r.1 e col).isSome = true)
    (hpn : ∀ col, col < planeColsOf g.shape lm → (r.2 col).isSome = true)
    (hrow : ∀ kept, leavesRowOwn g.leaves oneE kept F [] = some (g.leaves.rowForm oneE kept, G, []))
      :
    ∃ fs : Array Aff, planesRun seat lm readers n s =
      .ok (fs.toList.map seat.claim, seat.mark s (G.paid g.owedPlanes)) ∧ fs.size = 3 := by
  obtain ⟨fs, hfs, h3⟩ := planeClaimsOwn_returns g lm r.1 r.2 hpo hb hpn [] hrow
  refine ⟨fs, ?_, h3⟩
  have hall : (do
      let fs ← planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col)) fun col => Fl.need (r.2 col)
      planesAddedF g
      pure fs : Fl (Array Aff)) F [] = some (fs, G.paid g.owedPlanes, []) := by
    rw [fl_bind_some hfs]
    rfl
  unfold planesRun
  simp only [hF, hg, hu, hr, named, need, bind, Except.bind, if_true, pure, Except.pure]
  have hall' := hall
  simp only [bind, pure] at hall'
  rw [hall']

#print axioms ProofFile.Honest.K3.Law.fl_bind_some
#print axioms ProofFile.Honest.K3.Law.fl_need_some
#print axioms ProofFile.Honest.K3.Law.fl_foldlM_same
#print axioms ProofFile.Honest.K3.Law.planesAtF_returns
#print axioms ProofFile.Honest.K3.Law.planeClaimsOwn_returns
#print axioms ProofFile.Honest.K3.Law.planesRun_returns

end ProofFile.Honest.K3.Law
