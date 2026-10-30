-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/View.lean: TWO REPLAYS OF ONE LIST OF RECORDED ANSWERS, AGAINST ONE TABLE, OF THE
PROVER's CHAIN AT TWO STRATEGIES: the same hash work, for any two strategies; and, for two
strategies with one view, the same string and the same table handed out. It proves Spec.sameWork and
Spec.ofView (OnBytes/Dry/SpecView.lean).

General lemmas. This file states no goal of the release.

How. The walk (tied_chainO, OnBytes/Dry/Walk.lean) says that the two chains go side by side and in
which relation they end; the law of two replays side by side (TiedL.map_replay, Rom/Dry/Tied.lean)
turns that into an equality of laws, for every function of a run's end that takes one value at ends
which are so related.
  For Spec.sameWork the set G of the walk is empty, and the function reads the verifier messages,
  the
table, what is left of the recorded answers and the flag.
  For Spec.ofView G = {ρ₀}, and the function is what is handed out, on the runs with the verifier
messages ρ₀. There the walk gives: the same entries of the logs but for leaves; the same kept, as
far as it shows at the positions read AT THE STRATEGY's OWN PLAIN PARTS; the same request root; and
that the transcript as it was hashed is the strategy's run but for nonces. The premise that the
verifier reads the same positions whatever the nonces are turns "read at the plain parts as they
were hashed", which is what the string's maker asks (finish, OnBytes/Prover/Defs.lean), into that.
The external strings and their kept trees enter what is handed out at the positions that are read,
and there alone (extK_same, extLaid_same).

Main names.
  rdOfE, extK_same, extLaid_same   the external strings.
  finish_same    the proof string.
  atRho_pos, atRho_neg, of_dec   small tools.
  sameWork, ofView   THE STATEMENTS.

Limits. One slot, one chain.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Dry.Walk
import Iop.ShapeKit

set_option autoImplicit false

noncomputable section

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- from "decide p = true", at whatever instance, to p -/
theorem of_dec {p : Prop} {i : Decidable p} (h : @decide p i = true) : p := @of_decide_eq_true p i h

/-! ## The same hash work -/

/-- **THE STATEMENT.** -/
theorem sameWork : Spec.sameWork := by
  intro I X lam K L m t hm cms x co co' cap hco s A W embS embP i ph σ σ' T lg lg' Rc
  exact TiedL.map_replay (S := typedOracleFamily lam K L) Handler.lazy (H := work) (H' := work)
    (fun a l b l' hR s₀ Rc₀ ms => by
      show (a.map (fun z => z.1), s₀, Rc₀, ms) = (b.map (fun z => z.1), s₀, Rc₀, ms)
      rw [SameC.rho a b hR.1])
    (tied_chainO m t hm (fun _ => false) (fun _ _ => rfl) cms x co co' cap hco s A W embS embP i ph
      σ σ' (fun _ => False) (fun _ => false) (fun _ h => h.elim) (fun ⟨_, h⟩ => h.elim) lg lg'
      (fun ⟨_, h⟩ => h.elim)) T Rc false

/-! ## The external strings -/

section
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q)

/-- "The external position lies in the finite set S", as a test, with the wire's own test of
equality. -/
def rdOfE (S : Finset E.Pos) : E.Pos → Bool := fun p =>
  haveI := wq.ext.dec
  decide (p ∈ S)

variable {y y' : E.Str} {xt xt' : ℕ → TreeK lam L} {S : Finset E.Pos}
  (h : ∀ p ∈ S, E.rd y p = E.rd y' p ∧
    (xt (wq.ext.which p)).inp (wq.ext.leaf p) = (xt' (wq.ext.which p)).inp (wq.ext.leaf p) ∧
    (xt (wq.ext.which p)).lv = (xt' (wq.ext.which p)).lv)
include h

/-- the openings of the external strings -/
theorem extK_same : extK wq.ext y xt (rdOfE wq S) = extK wq.ext y' xt' (rdOfE wq S) := by
  funext p
  unfold extK
  by_cases hr : rdOfE wq S p = true
  · obtain ⟨h1, h2, h3⟩ := h p (of_dec hr)
    rw [if_pos hr, if_pos hr]
    unfold TreeK.opening
    rw [h1, h2, h3]
  · rw [if_neg hr, if_neg hr]

end

/-- the tables' leaves that are written -/
theorem extLaid_same {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y)
    {xt xt' : ℕ → TreeK lam L} (ρ : Rho Q.loc.shape)
    (h : ∀ p ∈ Q.loc.extReads x ρ,
      (xt (wq.ext.which p)).inp (wq.ext.leaf p) = (xt' (wq.ext.which p)).inp (wq.ext.leaf p) ∧
      (xt (wq.ext.which p)).lv = (xt' (wq.ext.which p)).lv) :
    extLaid Q wq x xt ρ = extLaid Q wq x xt' ρ := by
  unfold extLaid
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨h1, h2⟩ := h p (of_dec (List.mem_filter.1 hp).2)
  rw [h1, h2]

/-! ## The proof string -/

section
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y)
  (y y' : E.Str) (xt xt' : ℕ → TreeK lam L) (co : Coins lam L)

theorem finish_same (ρ : Rho Q.loc.shape) (ks ks' : Kept lam L Q.loc.shape) (ph : Phase lam)
    (rq : Option (Dig lam)) (S₀ : Finset (OPos Q.loc.shape))
    (hr : Q.loc.reads x ρ (trK Q.loc.shape ks ρ).plains = S₀)
    (hk : KeptSame Q.loc.shape Q.ann wq.sh (rdOf wq S₀) ks ks')
    (hx : ∀ p ∈ Q.loc.extReads x ρ, E.rd y p = E.rd y' p ∧
      (xt (wq.ext.which p)).inp (wq.ext.leaf p) = (xt' (wq.ext.which p)).inp (wq.ext.leaf p) ∧
      (xt (wq.ext.which p)).lv = (xt' (wq.ext.which p)).lv) :
    finish Q wq x y xt co (ρ, ks, ph, rq) = finish Q wq x y' xt' co (ρ, ks', ph, rq) := by
  have hpk := KeptSame.plains _ _ _ _ _ _ hk ρ
  have hF : ∀ (yy : E.Str) (xx : ℕ → TreeK lam L) (kk : Kept lam L Q.loc.shape),
      finish Q wq x yy xx co (ρ, kk, ph, rq) =
        { salt := co.salt
          roots := rootsK Q.loc.shape kk
          plains := (trK Q.loc.shape kk ρ).plains
          opens := OnBytes.Prover.opensK Q.loc.shape Q.ann wq.sh kk
            (rdOf wq (Q.loc.reads x ρ (trK Q.loc.shape kk ρ).plains))
          ext := extK wq.ext yy xx (rdOfE wq (Q.loc.extReads x ρ))
          rtreq := rq.getD (fun _ => false)
          slot := co.slot
          path := if ph.slotVal.isSome then co.path else []
          rsalt := if ph.slotVal.isSome then co.rsalt else [] } := fun _ _ _ => rfl
  have hop : OnBytes.Prover.opensK Q.loc.shape Q.ann wq.sh ks (rdOf wq S₀) =
      OnBytes.Prover.opensK Q.loc.shape Q.ann wq.sh ks' (rdOf wq S₀) :=
    funext fun p => KeptSame.opens _ _ _ _ _ _ hk p
  rw [hF y xt ks, hF y' xt' ks', ← hpk, hr, KeptSame.roots _ _ _ _ _ _ hk, hop,
    extK_same wq hx]

end

/-! ## On the runs with the verifier messages ρ₀ -/

theorem atRho_pos {s : Shape} {St γ : Type} {ρ₀ : Rho s} (H : Res (OutP lam L s) × St → γ)
    (z : OutP lam L s) (st : St) (h : z.1 = ρ₀) :
    atRho ρ₀ H (.ok z, st) = some (H (.ok z, st)) := if_pos h

theorem atRho_neg {s : Shape} {St γ : Type} {ρ₀ : Rho s} (H : Res (OutP lam L s) × St → γ)
    (z : OutP lam L s) (st : St) (h : ¬ z.1 = ρ₀) : atRho ρ₀ H (.ok z, st) = none := if_neg h

/-- **THE STATEMENT.** -/
theorem ofView : Spec.ofView := by
  intro I X lam K L t Y E Q wq embS embP xin cms x y y' xt xt' cap σ σ' co ρ₀ hfree hpl hrd hx T lg
    Rc
  have hA : AgreeAt Q.loc.shape (rdOf wq (Q.loc.reads x ρ₀ (σ.run ρ₀).1.plains)) ρ₀ σ σ' :=
    agreeAt_of_run _ _ ρ₀ σ σ' hpl fun p hp =>
      hrd p (of_dec hp)
  refine TiedL.map_replay (S := typedOracleFamily lam K L) Handler.lazy (fun a l b l' hR s₀ Rc₀ ms => ?_)
    (tied_chainO lateRun t (runMarks_lateRun t) notLeaf (fun _ _ => rfl) cms (xin x) co co cap
      (Alike.refl co) Q.loc.shape Q.ann wq.sh embS embP 0 .first σ σ' (fun ρ => ρ = ρ₀)
      (rdOf wq (Q.loc.reads x ρ₀ (σ.run ρ₀).1.plains)) (fun ρ h => by rw [h]; exact hA)
      (fun _ => rfl) lg lg (fun _ => rfl)) T Rc false
  obtain ⟨hS, hZ⟩ := hR
  cases a with
  | ok z =>
    cases b with
    | ok z' =>
      have hS' : z.1 = z'.1 ∧ z.2.2.1 = z'.2.2.1 := hS
      obtain ⟨hP, hG⟩ := hZ z z' rfl rfl
      by_cases hz : z.1 = ρ₀
      · have hz' : z'.1 = ρ₀ := hS'.1 ▸ hz
        obtain ⟨e1, e2, e3⟩ := hG hz
        rw [atRho_pos _ _ _ hz, atRho_pos _ _ _ hz']
        refine congrArg some ?_
        obtain ⟨ρ, ks, ph₁, rq⟩ := z
        obtain ⟨ρ', ks', ph₂, rq'⟩ := z'
        obtain rfl : ρ = ρ₀ := hz
        obtain rfl : ρ' = ρ := hz'
        obtain rfl : ph₁ = ph₂ := hS'.2
        obtain rfl : rq = rq' := e3
        have e2' : KeptSame Q.loc.shape Q.ann wq.sh
          (rdOf wq (Q.loc.reads x ρ' (σ.run ρ').1.plains)) ks ks' := e2
        have hP' : Puts Q.loc.shape Q.ann wq.sh (σ.run ρ').1 (trK Q.loc.shape ks ρ') := hP
        have hr1 : Q.loc.reads x ρ' (trK Q.loc.shape ks ρ').plains =
            Q.loc.reads x ρ' (σ.run ρ').1.plains := by
          have := hfree _ _ hP'
          rwa [Strat.rho_run] at this
        have hpk := KeptSame.plains _ _ _ _ _ _ e2' ρ'
        show (some (finish Q wq x y xt co (ρ', ks, ph₁, rq)),
            ((s₀.lay (l.filter notLeaf)).lay (laidK Q.loc.shape Q.ann wq.sh ks
              (rdOf wq (Q.loc.reads x ρ' (trK Q.loc.shape ks ρ').plains)))).lay
              (extLaid Q wq x xt ρ')) =
          (some (finish Q wq x y' xt' co (ρ', ks', ph₁, rq)),
            ((s₀.lay (l'.filter notLeaf)).lay (laidK Q.loc.shape Q.ann wq.sh ks'
              (rdOf wq (Q.loc.reads x ρ' (trK Q.loc.shape ks' ρ').plains)))).lay
              (extLaid Q wq x xt' ρ'))
        rw [finish_same Q wq x y y' xt xt' co ρ' ks ks' ph₁ rq _ hr1 e2' hx, ← hpk, hr1, e1,
          KeptSame.laid _ _ _ _ _ _ e2',
          extLaid_same Q wq x ρ' fun p hp => (hx p hp).2]
      · have hz' : ¬ z'.1 = ρ₀ := fun h => hz (hS'.1.trans h)
        rw [atRho_neg _ _ _ hz, atRho_neg _ _ _ hz']
    | noFormat => exact False.elim hS
    | ranOut j => exact False.elim hS
  | noFormat =>
    cases b with
    | ok _ => exact False.elim hS
    | noFormat => rfl
    | ranOut _ => exact False.elim hS
  | ranOut j =>
    cases b with
    | ok _ => exact False.elim hS
    | noFormat => exact False.elim hS
    | ranOut _ => rfl

end OnBytes.Dry

#print axioms OnBytes.Dry.sameWork
#print axioms OnBytes.Dry.ofView
