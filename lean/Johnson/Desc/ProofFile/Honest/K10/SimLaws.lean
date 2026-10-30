-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimLaws.lean: the closing of a segment (K10): of Honest/K10/Sim.lean's statements:
(5) proved; (3c) proved from (3b); (2) proved from (3c). So all that is left between the definitions and (2) is (3b),
`CloseSentIs`, which is not proved here. What would follow from these sentences is not said
here.

    `close_fresh`     `CloseFresh`, at every job (general in tot): a call of the frame's `fresh_of_nil`
                   (Honest/Law/ToyLaw.lean). It is the frame's sentence for an owner, at a part that owns no coin:
                   both sides are drawn over one point: without content: it says nothing of the run, and it is not the
                   `fresh` that the run's owners owe. It reads nothing of the kind: it spends the premise on the book
                   alone
  `csFn`, `runFn`   the simulator's coins, and the coins on the part's side, each as an equivalence with the functions
                   from the 2 k + 1 numbers to the field
  `sentFn`          `runSent` with `runBack` as an equivalence of these functions, from `RunOneToOne`
  `oneToOne_of`     `RunOneToOne` and `CloseSentIs` give `CloseOneToOne`: the run; then `runSent`; then a shift by
                   what does not hang on the run
  `exact_of`        `CloseOneToOne` gives `CloseExact`: the frame's `map_unif_by_equiv` (Honest/Law/ToyLaw.lean)
  `exact_of_sentIs` so `CloseSentIs` gives `CloseExact` (with `run_one_to_one`, Honest/K10/SimMap.lean)

Limits. `CloseExact` is not proved here: it stands here under `CloseSentIs`, a premise ((3b) at tot = true:
Honest/K10/SimSent.lean). By type the total form's default can hang on more than what is public, shown or heard.
`CloseAskPublic` (and, at the seated job, `SeatedAskPublic`) says that it does not: a definition: no statement of this
library concludes it, and none takes it as a premise. What this part sends has the simulator's law either way
(`close_exact`, `close_fresh`). The theorems are general in tot; the row's form is tot = true (Sim.lean's head).
`close_fresh`'s premise on the book is shown met here at no policy file. `oneToOne_of` spends neither "the first value
is 0" nor h ≤ k; `exact_of` spends none of the four premises of (2) that it drops. The spender's half alone: Sim.lean's
head. At a job typed at no face's input the four sentences that bind a face have no face to bind. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimMap
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- **`CloseFresh`.** -/
theorem close_fresh (tot : Bool) (J : CloseJob W) : CloseFresh S Cl V X Pb tot J := by
  intro σ φ Bk ord hown p sp ca m ds asks _ _ _
  exact fresh_of_nil _ (hown p) _ _

noncomputable section

/-- Coins of the extension field alone, as a function of their numbers. -/
def csFn (n : Nat) : Cs ⟨0, n⟩ ≃ (Fin n → Cb.Gl.E) where
  toFun c := c.e
  invFun g := ⟨fun i => i.elim0, g⟩
  left_inv c := by
    obtain ⟨f, e⟩ := c
    have hf : f = fun i => i.elim0 := funext fun i => i.elim0
    subst hf
    rfl
  right_inv _ := rfl

/-- The coins over which the part's side of the sentence is drawn, as the run. -/
def runFn (tot : Bool) (J : CloseJob W) :
    (Cs (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.takes ×
      CsAll (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.spends) ≃
      (Fin (2 * J.pub.par.k + 1) → Cb.Gl.E) where
  toFun c := runE (V := V) (X := X) (Pb := Pb) tot J c
  invFun g := (⟨fun i => i.elim0, fun i => i.elim0⟩, ((⟨fun i => i.elim0, g⟩ : Cs ⟨0, 2 * J.pub.par.k + 1⟩), ()))
  left_inv c := by
    obtain ⟨⟨f0, e0⟩, c1⟩ := c
    obtain ⟨⟨f1, e1⟩, ⟨⟩⟩ := c1
    have h0 : f0 = fun i => i.elim0 := funext fun i => i.elim0
    have h1 : e0 = fun i => i.elim0 := funext fun i => i.elim0
    have h2 : f1 = fun i => i.elim0 := funext fun i => i.elim0
    subst h0 h1 h2
    rfl
  right_inv _ := rfl

/-- The map and the way back, as an equivalence. -/
def sentFn (h : RunOneToOne) (k : Nat) (hk : 1 ≤ k) :
    (Fin (2 * k + 1) → Cb.Gl.E) ≃ (Fin (2 * k + 1) → Cb.Gl.E) where
  toFun := runSent k
  invFun := runBack k
  left_inv := (h Cb.Gl.E k hk).1
  right_inv := (h Cb.Gl.E k hk).2

end

/-- **(3a) and (3b) give (3c).** -/
theorem oneToOne_of (h1 : RunOneToOne) {tot : Bool} {J : CloseJob W}
    (h2 : CloseSentIs S Cl V X Pb tot J) : CloseOneToOne S Cl V X Pb tot J := by
  intro hp σ φ ca m front ds asks hOn hd
  obtain ⟨q, _, hq⟩ := h2 hp σ φ ca m front ds asks hOn hd
  refine ⟨(runFn (V := V) (X := X) (Pb := Pb) tot J).trans ((sentFn h1 J.pub.par.k hp.1).trans
    ((Equiv.addRight fun i => epsOf ds * q i).trans (csFn (2 * J.pub.par.k + 1)).symm)),
    fun c => ?_⟩
  rw [hq c]
  exact congrArg (fun g => some (layF J.pub.par.k g)) (funext fun i => rfl)

/-- **(3c) gives (2).** -/
theorem exact_of {tot : Bool} {J : CloseJob W} (h : CloseOneToOne S Cl V X Pb tot J) :
    CloseExact S Cl V X Pb tot J := by
  intro hp σ φ chain firstTree ca m front ds asks hOn _ hd _ _ _
  obtain ⟨e, he⟩ := h hp σ φ ca m front ds asks hOn hd
  exact map_unif_by_equiv e
    (fun c => (closeAt (V := V) (X := X) (Pb := Pb) tot J).tells φ c m.st.input front ds asks) _ he

/-- **So (3b) gives (2).** -/
theorem exact_of_sentIs {tot : Bool} {J : CloseJob W} (h : CloseSentIs S Cl V X Pb tot J) :
    CloseExact S Cl V X Pb tot J :=
  exact_of (oneToOne_of run_one_to_one h)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.close_fresh
#print axioms ProofFile.Honest.K10.csFn
#print axioms ProofFile.Honest.K10.runFn
#print axioms ProofFile.Honest.K10.sentFn
#print axioms ProofFile.Honest.K10.oneToOne_of
#print axioms ProofFile.Honest.K10.exact_of
#print axioms ProofFile.Honest.K10.exact_of_sentIs
