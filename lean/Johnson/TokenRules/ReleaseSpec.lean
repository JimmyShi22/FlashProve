-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/ReleaseSpec.lean: THE RULE OF RELEASE. What the end of a compiled run as a token
program does to the table in the mode in which marked evaluations are deferred, said in plain terms.
DEFINITIONS AND STATEMENTS; small members at the end.

General statements. This file states no goal of the release.

The end of a run (endC, Johnson/TokenRules/Chunks.lean) asks no oracle and draws no coin, so its run
is one outcome. In mode I of Rom/Defer.lean its reveals write the answers of the evaluations that
they release into the table, where the table has no entry. Spec.release says which entries these are
WITHOUT A WORD ON TOKENS: they are what the plain rule handOut (Johnson/WholeKey/Sim.lean) writes,
in its order:
  the entries of the run's own log that are no leaves (the log: the evaluations that the hashing has
  added, as entries);
  the leaves of the run's own trees at the positions that are read, by place (laidK), out of what
  the chain has kept, with the salts read off the store (keptK);
  the leaves of the external strings' trees at the positions that are read (extLaid).

What is asked of the state before the hashing.
  Laid d          The point of each released evaluation has an entry in the table. So writing such
                  an evaluation a second time is no move, and the plain rule need not know what was
                  released before.
  LeafAt d T pre  The tree's list of tokens is as long as its lowest level; and for each leaf j:
                  exactly one evaluation is charged to the token of the leaf's salt, and as an entry
                  it is (leaf oracle, the leaf's input, the j-th digest of the lowest level), the
                  input as the compiled prover keeps it (TreeT.toK at the store's values); no
                  evaluation is charged to the token of the empty tail.
  the rules' invariants of Johnson/TokenRules/Spec.lean (TidyO, TreeOKT).
  A premise on the wire: a position of the external strings stands at a leaf that its tree has.

  Spec.release      the case in which a string is handed out: the outcome, the table, and what stays
                    (the store; the evaluations as entries; Laid; LeafAt of every tree).
  Spec.releaseNone  all other cases: "none", and the state is untouched.
Spec.release is proved in Johnson/TokenRel/Release.lean, Spec.releaseNone here. That what is asked
of the state is kept along the experiment is shown in Johnson/TokenRel/Holds.lean. A member for the
case in which a string is handed out: Johnson/TokenRel/ReleaseMember.lean (a protocol without
rounds).

Limits. Statements on token programs in mode I, a device of one step of a proof: by themselves they
say nothing on the scheme. One slot.

-/
import Johnson.TokenRules.Chunks
import Johnson.TokenRules.Spec
import Johnson.WholeKey.Sim

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

/-! ## What is asked of a state -/

/-- The point of each released evaluation has an entry in the table. -/
def Laid {S : OSpec} (d : DSt S) : Prop :=
  ∀ e ∈ d.evs, e.released = true → d.table e.o e.pt ≠ none

section Generic
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- Leaf j of a tree as an entry of a log: the term of laidTree and extLaid
(Johnson/WholeKey/Sim.lean). -/
def entryK (T : TreeK lam L) (j : ℕ) : QA (typedOracleFamily lam K L) :=
  ⟨OracleName.leaf, T.inp j, (T.lv.headD []).getD j default⟩

/-- See the head. -/
def LeafAt (d : DSt (typedOracleFamily lam K L)) (T : TreeT lam L) (pre : Bits) : Prop :=
  T.tok.length = (T.lv.headD []).length ∧
  ∀ j a, T.tok[j]? = some a →
    (d.evs.filter fun e => e.charged == a.1).map qa = [entryK (T.toK d.val pre) j] ∧
    (d.evs.filter fun e => e.charged == a.2) = []

end Generic

namespace Spec

/-- **The rule of release.** D: the state before the hashing; (a, D₁): an outcome of the hashing in
mode I. -/
def release : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop)
      (t : Tag) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits)
      (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits)
      (cap : ℕ → ℕ) (stop : Rho Q.loc.shape → Bool) (D D₁ : DSt (typedOracleFamily lam K L))
      (a : Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) (z : OutT lam L Q.loc.shape),
    bl ≤ ln.fr → bf ≤ ln.sFS → bf ≤ lam →
    (∀ p, wq.ext.leaf p < (xt (wq.ext.which p)).tok.length) →
    TidyO (rulesT K L lam bl bf sd) D → Laid D →
    (∀ k, TreeOKT D [] (xt k)) → (∀ k, LeafAt D (xt k) preX) →
    (a, D₁) ∈ ((hashT t Q wq embS embP xin cms x σ ln pre cap).run true D).support →
    a.2.2 = Res.ok z → stop z.rho = false →
    ∃ D₂ : DSt (typedOracleFamily lam K L),
      (endC Q wq x y xt preX pre stop a).run true D₁ =
        PMF.pure (some (finish Q wq x y
          (fun k => (xt k).toK (valOf (showC Q wq x xt a.1 z) ((showC Q wq x xt a.1 z).map D₁.val))
            preX)
          (coinsK (valOf (showC Q wq x xt a.1 z) ((showC Q wq x xt a.1 z).map D₁.val) a.1) a.2.1)
          (outK (valOf (showC Q wq x xt a.1 z) ((showC Q wq x xt a.1 z).map D₁.val))
            (fun i b => pre i b
              (valOf (showC Q wq x xt a.1 z) ((showC Q wq x xt a.1 z).map D₁.val) a.1)) z)), D₂) ∧
      D₂.table =
        ((D₁.table.lay (((D₁.evs.drop D.evs.length).map qa).filter notLeaf)).lay
          (laidK Q.loc.shape Q.ann wq.sh
            (keptK D₁.val (fun i b => pre i b (D₁.val a.1)) Q.loc.shape 0 z.kept) fun p =>
            haveI := wq.decO
            decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains))).lay
          (extLaid Q wq x (fun k => (xt k).toK D₁.val preX) z.rho) ∧
      D₂.vals = D₁.vals ∧ D₂.evs.map qa = D₁.evs.map qa ∧ D₂.nPlain = D₁.nPlain ∧ Laid D₂ ∧
      ∀ (T : TreeT lam L) (pr : Bits), LeafAt D₁ T pr → LeafAt D₂ T pr

/-- Where no string is handed out the state is untouched. -/
def releaseNone : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X)
      (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits) (pre : ℕ → Bool → Bits → Bits)
      (stop : Rho Q.loc.shape → Bool) (m : Bool) (D₁ : DSt (typedOracleFamily lam K L))
      (a : Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)),
    (∀ z, a.2.2 = Res.ok z → stop z.rho = true) →
    (endC Q wq x y xt preX pre stop a).run m D₁ = PMF.pure (none, D₁)

end Spec

/-! ## Members -/

theorem laid_init (S : OSpec) : Laid (DSt.init S) := fun _ h => absurd h List.not_mem_nil

/-- Laid can fail: a released evaluation over an empty table. -/
theorem not_laid {S : OSpec} (e : Ev S) (he : e.released = true) :
    ¬ Laid (⟨Table.empty S, [], [], [e], fun _ => 0, false⟩ : DSt S) :=
  fun h => h e (List.mem_singleton.mpr rfl) he rfl

section Members
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A tree without leaves has LeafAt in every state. -/
theorem leafAt_nil (d : DSt (typedOracleFamily lam K L)) (body : ℕ → Body L) (pre : Bits) :
    LeafAt d ⟨body, [], []⟩ pre := ⟨rfl, fun _ _ h => nomatch h⟩

/-- LeafAt can fail: a leaf's token to which no evaluation is charged. -/
theorem not_leafAt_init (body : ℕ → Body L) (a : Tok × Tok) (dg : Dig lam) (pre : Bits) :
    ¬ LeafAt (DSt.init (typedOracleFamily lam K L)) ⟨body, [a], [[dg]]⟩ pre :=
  fun h => nomatch (h.2 0 a rfl).1

/-- **Where no string is handed out the state is untouched.** -/
theorem releaseNone : Spec.releaseNone := by
  intro I X lam K L Y E Q wq x y xt preX pre stop m D₁ a h
  obtain ⟨salt, cd, r⟩ := a
  cases r with
  | ok z =>
      have hs : stop z.rho = true := h z rfl
      show (if stop z.rho then Step.pure none
        else _ : StT lam K L (Option (OneProtocolProof lam Q))).run m D₁ = _
      rw [if_pos hs]
      rfl
  | noFormat => rfl
  | ranOut _ => rfl

end Members

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.releaseNone
