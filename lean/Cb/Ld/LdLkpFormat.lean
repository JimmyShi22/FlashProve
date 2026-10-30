-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpFormat.lean: the formats of a base chain that sends no oracle, block by block, and of its
lift over oracle messages.

Definitions, statements and proofs. Glue; no protocol of its own.

This file is book-keeping for the composition of reductions: for each kind of block of a chain it
records which oracles the block reads and copies and that the honest prover ends with its witness,
and it carries these facts through composition; for the sumcheck it also records that the verifier
hands the state on.
At the base means between joints (`IOR.Rels`, Ior/Chain.lean) in which the tuple of messages is a
part of the witness: a block at the base (`BkA`, Cb/Ld/LdLkpTreeP.lean) has witnesses of the type
`M × Wp`, M the tuples of messages. It comes before the lift over a signature
(Cb/Ld/LdSigLift.lean), after which the messages are those of the oracle messages of a statement.

Why: whoever calls a lookup (the preamble of weights-formedness, a segment of a request) asks of it,
beside completeness, knowledge soundness and the masked item (`Honest.MM`, Ior/Masked.lean),
formats: the further oracles (an encoded index) are not read, nothing is tied to them, they are
copied; state and samples are handed on; the honest prover ends with the witness with which it
began; what later blocks read of the oracles is within the budgets.
The assembled lookup is a chain at the base whose blocks are: the verifier draws a value
(`IOR.draw`); the sumcheck for a polynomial summand (`PscPar.psc`, or its part `PscPar.core`); a map
on the explicit part before or after a block (no round); two blocks in a row. Here the format
`b.Plain` is proved for each kind of block and carried through these four ways of building, whatever
the bracketing.

Main names:
  `b.Plain`: the format at the base: the block only copies its oracles: it reads none, ties nothing
    (`OnlyCopies`, Cb/Ld/LdWfPre.lean); the honest prover ends with the witness with which it began;
    every budget is borne (`budAll : ∀ ρ T, b.P.bud ρ T`); nothing is withheld.
  `plain_draw`, `plain_psc`, `plain_core`, `plain_seq`, `plain_chain`, `plain_preM`, `plain_postM`:
  `Plain` for the blocks and the ways of building.
  `psc_passes`, `core_passes`: the sumcheck hands its state on.
The lift of a plain block over a signature S (`R.keep S.Smp S.ext`, `S.liftH H`, `P.keep`):
  `lift_idxStep`: the further oracles E₀ are not read, not tied, copied.
  `lift_passes`: under `b.R.Passes r r'`, what is read off the explicit part is handed on, and so
    are the samples.
  `lift_keepsW`: the honest prover ends with the witness with which it began; `lift_hands`: so it
    hands on whatever is read off the witness.
  `lift_free`: nothing is withheld.
  `lift_need`, `lift_bud`, `lift_bears`: what is needed of the old oracles is what is needed of the
    new ones; every budget is borne.

Limits: this file says nothing on relations. It says nothing on blindness to the masks of later
blocks: Cb/Ld/LdLkpFormatBlind.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpTreeP
import Cb.Ld.LdPscProofsIor
import Cb.Ld.LdWfSide
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

namespace BkA
variable {K M X₁ X₂ X₃ : Type} {Ex : ExtSpec} {Wp : Type}

/-- The format at the base. -/
structure Plain (b : BkA K M X₁ X₂ Ex Wp) : Prop where
  copies : b.R.OnlyCopies
  keepsW : ∀ w x c ρ, ((b.H.strat w x c).run ρ).2.2 = w
  budAll : ∀ ρ T, b.P.bud ρ T
  free   : ∀ w x, b.H.withheld w x = ∅

/-- a map on the explicit part, before and after a block: no round -/
def preM (b : BkA K M X₂ X₃ Ex Wp) (φ : X₁ → X₂) : BkA K M X₁ X₃ Ex Wp :=
  ⟨b.R.pre (fun x => some (φ x)) (ExtMap.id Ex),
    b.H.pre (fun x => some (φ x)) (ExtMap.id Ex) fun o => (φ o.1, o.2),
    b.P.pre (fun x => some (φ x)) (ExtMap.id Ex)⟩
def postM (b : BkA K M X₁ X₂ Ex Wp) (φ : X₂ → X₃) : BkA K M X₁ X₃ Ex Wp :=
  ⟨b.R.post (fun x => some (φ x)) (ExtMap.id Ex),
    b.H.post (fun x => some (φ x)) (ExtMap.id Ex) fun o => (φ o.1, o.2),
    b.P.post (fun x => some (φ x)) (ExtMap.id Ex)⟩

end BkA

section Rules
variable {K M X₁ X₂ X₃ : Type} {Ex : ExtSpec} {Wp : Type}

theorem onlyCopies_post {R : IOR X₁ Ex X₂ Ex} (h : R.OnlyCopies) (f : X₂ → Option X₃) :
    (R.post f (ExtMap.id Ex)).OnlyCopies :=
  ⟨h.noReads, h.noTie, h.copy,
    fun ρ p =>
      ⟨(post_id_srcE R f ρ p).trans (h.src ρ p).1, (post_id_srcO R f ρ p).trans (h.src ρ p).2⟩⟩

theorem onlyCopies_pre {R : IOR X₂ Ex X₃ Ex} (h : R.OnlyCopies) (f : X₁ → Option X₂) :
    (R.pre f (ExtMap.id Ex)).OnlyCopies :=
  ⟨fun ρ => (wfPre_id_set _).trans (h.noReads ρ),
    fun ρ p => (wfPre_id_tie R f ρ p).trans (h.noTie ρ p),
    h.copy,
    fun ρ p => ⟨(wfPre_id_set _).trans (h.src ρ p).1, (h.src ρ p).2⟩⟩

theorem plain_draw (D : Type) [Fintype D] [Nonempty D] (nx : X₁ → D → X₂) (err : ℕ) :
    (⟨IOR.draw D nx Ex,
    Honest.draw D nx Ex (M × Wp),
    Nums.draw K D nx Ex err⟩ : BkA K M X₁ X₂ Ex Wp).Plain :=
  ⟨OnlyCopies.draw D nx Ex, fun _ _ _ _ => rfl, fun _ _ => trivial, fun _ _ => Set.union_self _⟩

theorem plain_seq {a : BkA K M X₁ X₂ Ex Wp} {b : BkA K M X₂ X₃ Ex Wp}
    (ha : a.Plain) (hb : b.Plain) : (a.seq b).Plain where
  copies := ha.copies.seq hb.copies
  keepsW := fun w x c ρ => by
    show (((a.H.seq b.H).strat w x c).run ρ).2.2 = w
    rw [Honest.run_seq]
    exact (hb.keepsW _ _ _ _).trans (ha.keepsW _ _ _ _)
  budAll := fun _ _ _ _ _ _ => ⟨hb.budAll _ _, ha.budAll _ _⟩
  free := fun w x =>
    Set.eq_empty_of_forall_notMem fun ρ =>
      (Honest.not_mem_withheld_seq a.H b.H w x ρ).2
        ⟨by rw [ha.free]; exact Set.notMem_empty _,
          fun c => by rw [hb.free]; exact Set.notMem_empty _⟩

theorem plain_chain (X : ℕ → Type)
    (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (h : ∀ l, (b l).Plain) : ∀ n, (BkA.chain X b n).Plain
  | 0 => h 0
  | n + 1 => plain_seq (plain_chain X b h n) (h (n + 1))

theorem plain_preM {b : BkA K M X₂ X₃ Ex Wp} (h : b.Plain) (φ : X₁ → X₂) : (b.preM φ).Plain :=
  ⟨onlyCopies_pre h.copies _, fun w x c ρ => h.keepsW w (φ x) c ρ,
    h.budAll, fun w x => h.free w (φ x)⟩

theorem plain_postM {b : BkA K M X₁ X₂ Ex Wp} (h : b.Plain) (φ : X₂ → X₃) : (b.postM φ).Plain :=
  ⟨onlyCopies_post h.copies _, fun w x c ρ => by
    show ((Strat.map (fun o : X₂ × (M × Wp) => (φ o.1, o.2)) (b.H.strat w x c)).run ρ).2.2 = w
    rw [Strat.run_map]
    exact h.keepsW w x c ρ, h.budAll, h.free⟩

end Rules

section Psc
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec)

theorem core_onlyCopies : (Y.core Ex).OnlyCopies :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
omit [Fintype E] in
theorem ends_onlyCopies : (Y.ends Ex).OnlyCopies :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
theorem psc_onlyCopies : (Y.psc Ex).OnlyCopies := (core_onlyCopies Y Ex).seq (ends_onlyCopies Y Ex)

theorem core_passes : (Y.core Ex).Passes Prod.snd PscPar.Mid.st := fun x _ τ z h =>
  Y.outC_st x τ z h

theorem psc_passes : (Y.psc Ex).Passes Prod.snd PscPar.Out.st := fun x y τ o h => by
  have h' : (Y.psc Ex).out x y (Tr.app (Tr.fst τ) (Tr.snd (s := (Y.core Ex).shape) τ)) =
      some o := by
    rw [Tr.app_fst_snd]; exact h
  exact Y.outC_st x _ _ (Y.psc_out_some Ex x y _ _ o h')

theorem plain_psc (K M Wp : Type) (msg : M × Wp → Y.J → E) :
    (⟨Y.psc Ex, Y.hon Ex msg, Y.nums Ex K⟩ : BkA K M (E × Y.St) Y.Out Ex Wp).Plain :=
  ⟨psc_onlyCopies Y Ex,
    psc_keeps E Y Ex (M × Wp) msg,
    fun _ _ => trivial,
    fun w x =>
      Set.eq_empty_of_forall_notMem fun ρ =>
        (Honest.not_mem_withheld_seq (Y.honC Ex msg) (Y.honE Ex msg) w x ρ).2
          ⟨fun h => h.elim id id, fun _ h => h.elim id id⟩⟩

theorem plain_core (K M Wp : Type) (msg : M × Wp → Y.J → E) :
    (⟨Y.core Ex, Y.honC Ex msg, Y.numsC Ex K⟩ : BkA K M (E × Y.St) Y.Mid Ex Wp).Plain :=
  ⟨core_onlyCopies Y Ex,
    fun w x _ ρ => congrArg Prod.snd (psc_run E Y Ex (M × Wp) msg w x ρ).2.2.2,
    fun _ _ => trivial,
    fun _ _ => Set.union_self _⟩

end Psc

/-! ## The lift over a signature -/

section Lift
variable {E : Type} (S : Sig E) {K St X' Wp : Type} {E₀ : ExtSpec} {b : BkA K S.Msg St X' E₀ Wp}

theorem lift_idxStep (h : b.Plain) : (b.R.keep S.Smp S.ext).IdxStep :=
  IdxStep.keep h.copies.noReads h.copies.noTie h.copies.copy h.copies.src S.Smp S.ext

theorem lift_passes {Rc : Type} {r : St → Rc} {r' : X' → Rc} (hp : b.R.Passes r r') :
    (b.R.keep S.Smp S.ext).Passes (fun x => (r x.1, x.2)) fun x =>
      (r' x.1, x.2) := fun x y τ x' hx =>
  Prod.ext (((hp.keepX S.Smp).keepE S.ext) x y τ x' hx)
    (((Passes.keepX_snd b.R (fun z : S.Smp => z)).keepE S.ext) x y τ x' hx)

theorem lift_keepsW (h : b.Plain) (w : S.Wit × Wp) (x : St × S.Smp) (c : (S.liftH b.H).Coin)
    (ρ : Rho (b.R.keep S.Smp S.ext).shape) :
    (((S.liftH b.H).strat w x c).run ρ).2.2 = w := by
  show ((((b.H.keep S.Smp S.ext).mapW
        (fun w : S.Wit × Wp => (S.msgs w.1, w.2)) fun w o => (w.1, o.2)).strat
      w x c).run ρ).2.2 = w
  rw [Honest.mapW_run]
  show (w.1, ((((b.H.keepX S.Smp).strat (S.msgs w.1, w.2) x c).run ρ).2.2).2) = w
  rw [Honest.keepX_run]
  show (w.1, (((b.H.strat (S.msgs w.1, w.2) x.1 c).run ρ).2.2).2) = w
  rw [h.keepsW]

theorem lift_hands (h : b.Plain) {Pw : Type}
    (Ri : St × S.Smp → (E₀.prod S.ext).Str → S.Wit × Wp → Prop) (px : S.Wit × Wp → Pw) :
    (S.liftH b.H).Hands Ri px px :=
  fun x _ w c ρ _ _ => congrArg px (lift_keepsW S h w x c ρ)

theorem lift_free (h : b.Plain) (w : S.Wit × Wp) (x : St × S.Smp) :
    (S.liftH b.H).withheld w x = ∅ :=
  h.free (S.msgs w.1, w.2) x.1

theorem lift_need (h : b.Plain) (ρ : Rho b.R.shape) (U : Finset (E₀.prod S.ext).Pos) :
    (b.R.keep S.Smp S.ext).need ρ U = U :=
  need_keep h.copies ρ U

theorem lift_bud (h : b.Plain) (ρ : Rho b.R.shape) (T : Finset (OPos b.R.shape)) :
    (b.P.keep S.Smp S.ext).bud ρ T := h.budAll ρ T

theorem lift_bears (h : b.Plain) (q : Finset (E₀.prod S.ext).Pos → Prop) :
    (b.R.keep S.Smp S.ext).Bears (b.P.keep S.Smp S.ext).bud q q :=
  fun ρ U hU => ⟨h.budAll ρ _, by rw [lift_need S h]; exact hU⟩

end Lift
end Cb
