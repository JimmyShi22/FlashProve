-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/SpecSession.lean: ONE COMPILED RUN OF THE HONEST SIDE, LAID LATE, IS A RUN OF THE
GAME FOLLOWED BY THE REDUCTION's SECOND PASS. DEFINITIONS AND THE STATEMENT, at letters; the proof
is in Johnson/LateWorld/Session.lean.

General statement, for any protocol, wire and honest side. This file states no goal of the
release.

The two sides.
  LEFT (lateProof, Johnson/LateWorld/Defs.lean): draw the strategy's coins κ; run the prover's chain
      at the honest strategy, at the coins coK κ, with fresh answers at the deferred queries; hand
      out the string unless the chain has not ended or the honest side withholds its messages.
  RIGHT: a run of the game's real side (runAt, Hiop/Seeded/Game.lean): draw (outcome, recorded
      answers) by a first, dry pass at other letters (pass1, Johnson/WholeKey/Wrap.lean); if that
      pass has verifier messages, the honest side's output there: the disclosed view, or nothing.
      Then the reduction's second pass (pass2): replay the recorded answers at the strategy made
      from the view, at coins made from the view's plain parts, and hand out a string if there was a
      view; the external strings and the bodies of the tables' opened leaves are made from the view.

Main names (namespace OnBytes.LateWorld).
  pass2        the second pass as a law. (pass2A, Johnson/WholeKey/Wrap.lean, is the same as a
               program against a challenger: interact_pass2A, Johnson/LateWorld/Session.lean.)
  TabAgree     the honest side's kept trees over the external strings against the reduction's: the
               same levels and salts; the honest side's leaves hold the external strings' symbols.
  Spec.session   THE STATEMENT.
  tabAgree_member   TabAgree can be met.

Its premises: the wire of the external strings keeps its laws; the verifier reads the same positions
whatever the nonces are; "stop" decides the honest side's abort set; the coins made from the plain
parts of an honest run are that run's coins, AT VERIFIER MESSAGES OUTSIDE THE ABORT SET (nothing is
asked where the honest side withholds its messages); the coins of a run without a view are alike to
them;
the first pass's coins have as many sibling digests; TabAgree.

Limits. One run. Nothing on how the coins are drawn, nor on bounds of a game.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Defs
import Johnson.WholeKey.Wrap
import OnBytes.Dry.SpecView

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
  (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (xt : ℕ → TreeK lam L) (cap : ℕ → ℕ)

/-- **The reduction's second pass**, as a law: the chain at the strategy made from the view, the
deferred queries answered by the recorded answers; then what is handed out, and the table. -/
def pass2 (embE : E.Sym → Body L) (v : Option (DView Q.loc)) (co : Coins lam L)
    (Rc : Record (typedOracleFamily lam K L)) (T : Table (typedOracleFamily lam K L)) :
    PMF (Option (OneProtocolProof lam Q) × Table (typedOracleFamily lam K L)) :=
  ((chainX t Q wq embS embP xin cms x cap (stratFor Q wq v) co).runReplay mkRun T [] Rc).map
    (handOut Q wq x (wq.ext.build (ansOf Q v)) (namedAt Q wq xt embE (ansOf Q v)) v.isSome co)

/-- The honest side's kept trees xtR over the external strings y against the reduction's xtW: the
same levels, the same salts; and the honest side's leaf at an external position holds that
position's symbol, as the wire writes it. -/
structure TabAgree (embE : E.Sym → Body L) (y : E.Str) (xtR xtW : ℕ → TreeK lam L) : Prop where
  lv : ∀ k, (xtR k).lv = (xtW k).lv
  salt : ∀ k j, ((xtR k).inp j).salt = ((xtW k).inp j).salt
  body : ∀ p, ((xtR (wq.ext.which p)).inp (wq.ext.leaf p)).body = embE (E.rd y p)

end

/-- **THE STATEMENT.** -/
def Spec.session : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms₁ cms : List (Dig lam)) (x : Y) (xtR xtW : ℕ → TreeK lam L) (cap : ℕ → ℕ)
    (embE : E.Sym → Body L) {Wt : Type} (H : Honest Q.loc Wt) (w : Wt)
    (stop : Rho Q.loc.shape → Bool) (co₁ : Coins lam L) (coK : H.Coin → Coins lam L)
    (coV : Option (Plains Q.loc.shape) → Coins lam L),
    wq.ext.OK →
    (∀ τ τ' : Tr Q.loc.shape, Puts Q.loc.shape Q.ann wq.sh τ τ' →
      Q.loc.reads x τ.rho τ'.plains = Q.loc.reads x τ.rho τ.plains) →
    (∀ ρ, stop ρ = true ↔ ρ ∈ H.withheld w x) →
    (∀ κ ρ, ρ ∉ H.withheld w x → coV (some ((H.strat w x κ).run ρ).1.plains) = coK κ) →
    (∀ κ, Alike (coK κ) (coV none)) →
    (∀ κ, co₁.path.length = (coK κ).path.length) →
    TabAgree Q wq embE (H.ext w) xtR xtW →
    ∀ T : Table (typedOracleFamily lam K L),
      ((unif H.Coin).bind fun κ =>
          lateProof t Q wq embS embP xin cms x (H.ext w) xtR cap stop (H.strat w x κ) (coK κ) T) =
        (Hiop.Seeded.runAt H (pass1 t Q wq embS embP xin cms₁ x cap co₁) (fun a => a.1.toOption) w
          x).bind fun u =>
          pass2 t Q wq embS embP xin cms x xtW cap embE u.2 (coV (u.2.map DView.plains)) u.1.2 T

/-- TabAgree can be met: the reduction's trees made from the honest side's by any change of bodies.
-/
theorem tabAgree_member {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) (embE : E.Sym → Body L) (y : E.Str)
    (xtR : ℕ → TreeK lam L)
    (hb : ∀ p, ((xtR (wq.ext.which p)).inp (wq.ext.leaf p)).body = embE (E.rd y p)) (b₀ : Body L) :
    TabAgree Q wq embE y xtR fun k => { xtR k with inp := fun j => ⟨b₀, ((xtR k).inp j).salt⟩ } :=
  ⟨fun _ => rfl, fun _ _ => rfl, hb⟩

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.tabAgree_member
