-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/FixedMessages.lean: a prover that sends messages which hang on nothing but the verifier's
randomness, and never aborts, is replayed exactly by whoever knows these messages. Book-keeping, for
one protocol and for a batch; then at the library's placeholder provers (`Files.fixedMessageProvers`,
OnBytes/Flat/Silent.lean).

Why. E2E/WholeView.lean states a theorem for all provers that meet a list of premises. A list of
premises that nothing meets compiles in silence. Here is a member: the placeholder provers. THEY ARE
NOT THE PROTOCOL's PROVER: they send each round's fixed message, whatever the index, the request and
the challenges are. So nothing that is shown of them says anything about the protocol's messages.

Definitions.
  `viewWith Q x y₀ τ a`: the disclosed view of the transcript τ, with a in the place of the
    committed tables' symbols. The table y₀ is named because the library's `InteractiveOracleProof.dview` takes one;
    nothing of it is read (`viewWith_any`).
  `simFixed Q σ y₀`: the function of the simulators' type that plays the strategy σ against the
    given randomness and lays the handed symbols into the view.
  `restrictTo S a`: a, at the positions of S alone.
  `simFixedB Q N σ y₀`: the same for a set of requests of a batch: each request's view gets, of the
    handed symbols, those at its own verifier's positions.
  `silentSims F y₀`: these three at the three protocols F and the fixed messages.
What is shown.
  `output_fixed`, `outputB_fixed`: if an honest prover's strategy is σ at every private input,
    instance and coin, and its abort sets are empty, its output at every randomness IS the
    function's.
  `silent_good`: the three functions are good simulators (`SimsR.Good`, Hiop/RecWhole.lean) of
    `F.withProvers F.fixedMessageProvers`, for every three protocols F over every configuration, every relation and all
    numbers, 0 among them.
  `silent_hiding`: hence `HidingR` there. `silent_withheld`: the abort sets there have measure 0.

Limits. All of this holds because the messages are fixed. No statement here is about a prover that
is ever accepted. By the library's own word (OnBytes/Flat/Silent.lean) `CompleteR` is not to be
asked at these provers.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import Hiop.RecWhole
import OnBytes.Flat.Silent

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Fixed
open Iop Prob Hiop
open Compile.Lifetime (SimOf)
open Compile.BatchLife (BSimOf)
open OnBytes.Flat (Files)
open scoped ENNReal

variable {X : Type} {E : ExtSpec}

/-! ## 1. Small tools -/

/-- A law pushed along a function that is constant is the point law. -/
theorem map_eq_pure {α β : Type} (p : PMF α) (F : α → β) (v : β) (h : ∀ a, F a = v) :
    p.map F = PMF.pure v := by
  have e : F = Function.const α v := funext h
  rw [e, PMF.map_const]

/-- Where two functions agree everywhere, the event "they differ" has probability at most any z. -/
theorem pr_ne_le {α β : Type} (p : PMF α) (A B : α → β) (h : ∀ a, A a = B a) (z : ℝ≥0∞) :
    pr p {a | A a ≠ B a} ≤ z :=
  (pr_mono p (E := {a | A a ≠ B a}) (F := ∅) fun a ha => absurd (h a) ha).trans
    ((pr_empty p).le.trans (zero_le z))

/-- An event that never happens has probability at most any z. -/
theorem pr_never_le {α : Type} (p : PMF α) (S : Set α) (h : ∀ a, a ∉ S) (z : ℝ≥0∞) :
    pr p S ≤ z :=
  (pr_mono p (E := S) (F := ∅) fun a ha => absurd ha (h a)).trans
    ((pr_empty p).le.trans (zero_le z))

/-! ## 2. One protocol -/

/-- The disclosed view of τ with a in the place of the committed tables' symbols. -/
def viewWith (Q : InteractiveOracleProof X E) (x : X) (y₀ : E.Str) (τ : Tr Q.shape) (a : E.Pos → Option E.Sym) :
    DView Q :=
  ⟨(Q.dview x y₀ τ).plains, a, (Q.dview x y₀ τ).orc⟩

/-- It does not hang on y₀. -/
theorem viewWith_any (Q : InteractiveOracleProof X E) (x : X) (y₀ y₁ : E.Str) (τ : Tr Q.shape)
    (a : E.Pos → Option E.Sym) : viewWith Q x y₀ τ a = viewWith Q x y₁ τ a := rfl

/-- The library's disclosed view is that, at the symbols where the verifier reads. -/
theorem dview_eq (Q : InteractiveOracleProof X E) (x : X) (y y₀ : E.Str) (τ : Tr Q.shape) :
    Q.dview x y τ = viewWith Q x y₀ τ (Q.extAns x τ.rho y) := rfl

/-- Play σ against ρ; lay the handed symbols into the view. -/
def simFixed (Q : InteractiveOracleProof X E) (σ : Strat Q.shape Unit) (y₀ : E.Str) : SimOf Q :=
  fun x ρ a => PMF.pure (some (viewWith Q x y₀ (σ.run ρ).1 a))

/-- **A prover with the fixed strategy σ and empty abort sets: its output is that function's**, at
every private input, instance and randomness. -/
theorem output_fixed {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt) (σ : Strat Q.shape Unit)
    (hs : ∀ w x c, H.strat w x c = σ) (hw : ∀ w x ρ, ρ ∉ H.withheld w x) (y₀ : E.Str) (w : Wt)
    (x : X) (ρ : Rho Q.shape) :
    H.output w x ρ = simFixed Q σ y₀ x ρ (Q.extAns x ρ (H.ext w)) := by
  have e1 : H.output w x ρ =
      (unif H.Coin).map fun c => some (Q.dview x (H.ext w) ((H.strat w x c).run ρ).1) :=
    if_neg (hw w x ρ)
  rw [e1]
  refine map_eq_pure _ _ _ fun c => ?_
  show some (Q.dview x (H.ext w) ((H.strat w x c).run ρ).1) =
    some (viewWith Q x y₀ (σ.run ρ).1 (Q.extAns x ρ (H.ext w)))
  rw [hs w x c, dview_eq Q x (H.ext w) y₀ (σ.run ρ).1, Strat.rho_run]

/-! ## 3. A batch -/

open Classical in
/-- a, at the positions of S alone. -/
def restrictTo {Pos Sym : Type} (S : Finset Pos) (a : Pos → Option Sym) : Pos → Option Sym :=
  fun p => if p ∈ S then a p else none

/-- What one request's verifier reads of the committed table, out of what the verifiers of all
requests of J read. -/
theorem extAns_restrict (Q : BatchInteractiveOracleProof X E) {N : ℕ} (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho Q.loc.shape) (y : E.Str) (j : J) :
    Q.loc.extAns (xs j) (ρs j) y =
      restrictTo (Q.loc.extReads (xs j) (ρs j)) (Q.extAnsJ J xs ρs y) := by
  funext p
  unfold InteractiveOracleProof.extAns restrictTo BatchInteractiveOracleProof.extAnsJ
  by_cases hp : p ∈ Q.loc.extReads (xs j) (ρs j)
  · rw [if_pos hp, if_pos hp, if_pos (⟨j, hp⟩ : ∃ j, p ∈ Q.loc.extReads (xs j) (ρs j))]
  · rw [if_neg hp, if_neg hp]

/-- For each request of J: play σ against its randomness; lay into its view those of the handed
symbols that stand where its own verifier reads. -/
def simFixedB (Q : BatchInteractiveOracleProof X E) (N : ℕ) (σ : Strat Q.loc.shape Unit) (y₀ : E.Str) :
    BSimOf Q N :=
  fun _ xs ρs a => PMF.pure fun j =>
    some (viewWith Q.loc (xs j) y₀ (σ.run (ρs j)).1
      (restrictTo (Q.loc.extReads (xs j) (ρs j)) a))

open Classical in
/-- **The same for a batch**: if every request's strategy is σ and no request is ever withheld, the
output for a set J of requests is that function's. -/
theorem outputB_fixed {Q : BatchInteractiveOracleProof X E} {Wt : Type} (H : BatchHonestProver Q Wt)
    (σ : Strat Q.loc.shape Unit) (hs : ∀ w x c, H.one.strat w x c = σ)
    (hw : ∀ w x ρ, ρ ∉ H.one.withheld w x) (y₀ : E.Str) {N : ℕ} (w : Wt)
    (x : Fin N → Option X) (ρ : BRho N Q.loc.shape Q.ann) (J : Finset (Fin N)) (xs : J → X)
    (hxs : ∀ j : J, x j = some (xs j)) :
    H.output w x ρ J =
      simFixedB Q N σ y₀ J xs (fun j => ρ.slot j.1)
        (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w)) := by
  unfold BatchHonestProver.output
  refine map_eq_pure _ _ _ fun c => ?_
  funext j
  beta_reduce
  rw [hxs j]
  show (if ρ.slot j.1 ∈ H.one.withheld w (xs j) then none else some _) = some _
  rw [if_neg (hw w (xs j) (ρ.slot j.1)), hs w (xs j) _,
    dview_eq Q.loc (xs j) (H.ext w) y₀ (σ.run (ρ.slot j.1)).1, Strat.rho_run,
    extAns_restrict Q J xs (fun j => ρ.slot j.1) (H.ext w) j]

/-! ## 4. The library's placeholder provers -/

section Silent
variable {C : ConfigurationWithOutOfDomainSample} (F : Files C)

/-- The fixed messages of a request in a batch, as one strategy. -/
def sigmaB : Strat F.batch.loc.shape Unit :=
  (OnBytes.Flat.silent0 F.batch.loc.shape F.batch.ann).zip
    (OnBytes.Flat.silentJ F.batch.loc.shape F.batch.ann)

/-- The three functions at the fixed messages. y₀: any table; nothing of it is read. -/
def silentSims (y₀ : Fin C.n → C.Sg) : SimsR (F.withProvers F.fixedMessageProvers) where
  T := simFixed F.key (OnBytes.Flat.silent F.key.shape ()) y₀
  Lk := simFixed F.entry (OnBytes.Flat.silent F.entry.shape ()) (y₀, y₀)
  B := simFixedB F.batch F.N (sigmaB F) y₀

theorem silent_freeT (w) (x) (ρ) : ρ ∉ F.fixedMessageProvers.hT.withheld w x := by
  intro h
  rcases h with h | h <;> exact Set.notMem_empty _ h

theorem silent_freeL (w) (x) (ρ) : ρ ∉ F.fixedMessageProvers.hL.withheld w x := by
  intro h
  rcases h with h | h <;> exact Set.notMem_empty _ h

theorem silent_freeB (w) (x) (ρ) : ρ ∉ F.fixedMessageProvers.hB.one.withheld w x := by
  intro h
  rcases h with (h | h) | h
  · exact Set.notMem_empty _ h
  · exact Bool.false_ne_true h
  · exact Set.notMem_empty _ h

/-- **At the placeholder provers the three functions are good simulators**, for every relation and
all numbers. It holds because the messages are fixed. -/
theorem silent_good (y₀ : Fin C.n → C.Sg) (Ryes : C.I → C.X → Prop) (zT zL zO : ℝ≥0∞) :
    (silentSims F y₀).Good Ryes zT zL zO where
  goodT := fun w x _ =>
    pr_ne_le _ _ _ (fun ρ => output_fixed F.fixedMessageProvers.hT (OnBytes.Flat.silent F.key.shape ())
      (fun _ _ _ => rfl) (silent_freeT F) y₀ w x ρ) zT
  goodL := fun w x _ =>
    pr_ne_le _ _ _ (fun ρ => output_fixed F.fixedMessageProvers.hL (OnBytes.Flat.silent F.entry.shape ())
      (fun _ _ _ => rfl) (silent_freeL F) (y₀, y₀) w x ρ) zL
  goodB := fun w x _ J xs hxs =>
    pr_ne_le _ _ _ (fun ρ => outputB_fixed F.fixedMessageProvers.hB (sigmaB F) (fun _ _ _ => rfl)
      (silent_freeB F) y₀ w x ρ J xs hxs) _

/-- Hence `HidingR` there, at all numbers. -/
theorem silent_hiding (y₀ : Fin C.n → C.Sg) (Ryes : C.I → C.X → Prop) (zT zL zO : ℝ≥0∞) :
    (F.withProvers F.fixedMessageProvers).HidingR Ryes zT zL zO :=
  ⟨⟨(silentSims F y₀).T, (silent_good F y₀ Ryes zT zL zO).goodT⟩,
    ⟨(silentSims F y₀).Lk, (silent_good F y₀ Ryes zT zL zO).goodL⟩,
    ⟨(silentSims F y₀).B, (silent_good F y₀ Ryes zT zL zO).goodB⟩⟩

/-- The abort sets there are empty: their measure is at most any number. -/
theorem silent_withheld (pT pL pO : ℝ≥0∞) :
    (∀ w x, prRho (F.fixedMessageProvers.hT.withheld w x) ≤ pT) ∧
    (∀ w x, prRho (F.fixedMessageProvers.hL.withheld w x) ≤ pL) ∧
    (∀ w x, prRho (F.fixedMessageProvers.hB.one.withheld w x) ≤ pO) :=
  ⟨fun w x => pr_never_le _ _ (silent_freeT F w x) pT,
    fun w x => pr_never_le _ _ (silent_freeL F w x) pL,
    fun w x => pr_never_le _ _ (silent_freeB F w x) pO⟩

end Silent

end AtPublicFiles.Fixed

#print axioms AtPublicFiles.Fixed.viewWith_any
#print axioms AtPublicFiles.Fixed.dview_eq
#print axioms AtPublicFiles.Fixed.output_fixed
#print axioms AtPublicFiles.Fixed.extAns_restrict
#print axioms AtPublicFiles.Fixed.outputB_fixed
#print axioms AtPublicFiles.Fixed.silent_good
#print axioms AtPublicFiles.Fixed.silent_hiding
#print axioms AtPublicFiles.Fixed.silent_withheld
