-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/Fold.lean: the kind of block FOLD (in a plan of rounds: "FOLD epsilon", then "FOLD
round", once for each variable), general in its sizes: the library's fold (the sumcheck that folds,
Cb/Ld/LdSum.lean) as the prover sends it; the statement that it is round-by-round knowledge sound,
proved under conditions on codes and numbers that no file here shows of any setting.

Two forms, by where the fold's fresh mask is sent.
  `foldOwn Y fx`: the mask is the oracle of the fold's first round (in a plan: one root at "FOLD
    epsilon"). It is `Y.iorS fx` of Cb/Ent/FoldShort.lean.
  `foldRide Y fx`: the mask was sent earlier (no root at "FOLD epsilon"). It stands among the
    oracles of the input statement, beside the fold's input word, read natively, and the input joint
    asks nothing of it (`IOR.Rels.keepE`, Ior/Frame.lean). The first round sends the sum alone.
In both forms a later round sends its round polynomial without one coefficient
(Cb/Ent/FoldShort.lean): n scalars.

Two words. An oracle that was sent earlier for a later block is called a rider here: it has no
sample; Cb/Ld/LdGroupNewRide.lean uses the word for sampled oracle messages of a next part. The kind
FOLD is the sumcheck alone.

Main names (Y : `SumPar E P`, the library's parameters of a fold; fx: which coefficient is left out,
and a scalar):
  `inOwn Y e`, `inRide Y e`, `outJ Y e`: the joints: the library's, at the radius e.
  `extOwn`, `extRide`, `errOwn`, `errRide`: the library's extractor on the image of the transcript;
    the library's errors, round for round.
  `FoldOwnKnow`, `FoldRideKnow`: the statements: round-by-round knowledge soundness between the two
    joints' relaxed relations, and nothing else.
  `foldOwn_know`, `foldRide_know`: they hold under `SumPar.HypK` (Cb/Ent/TowerKnow.lean): the
    premises of the library's theorem on the fold.
  `FoldSize E`, `s.HOwn`, `s.HRide`, `s.OK`, `s.hOwn`, `s.hRide`: what is public of a fold as one
    record; the two statements at a size; the conditions; the statements hold under them.
  `s.Pick`, `s.totalOwn`, `s.totalRide`: the condition on fx under which no check is left: `fx.2` is
    an inverse of the "sum" of the power that is left out; then the verifier never rejects. It holds
    where the linear coefficient is left out, at the scalar 1 (`ldEnt_foldS_lin`,
    Cb/Ent/FoldShortProofs.lean).
  Beside the statements: `foldOwn_point`, `foldRide_point` (the oracles are strings);
  `foldOwn_local`, `foldRide_local` (verifier and new oracles read what the term declares, under
  the three codes' laws); `foldOwn_onOut`, `foldRide_onOut` (the joints ask nothing of a statement);
  `foldRide_out` (the verifier in closed form), `foldOwn_total`, `foldRide_total`: these three under
  the condition on fx; `foldOwn_passes`, `foldRide_passes` (the states of the two forms are handed
  on); `foldOwn_shape`, `foldRide_shape`, `foldOwn_rounds`, `foldRide_rounds` (k + 1 rounds);
  `errOwn_toList`, `errRide_toList`, `fold_errList` (the errors as a list, written out);
  `foldOwn_vals`, `foldRide_vals` (the numbers of values of the verifier's messages).
  How the joints meet the neighbours': Cb/Pv/Tower/Stage.lean.

Limits: `SumPar.HypK` holds conditions with any numbers: on the three codes (laws, distance d, a
radius e below d, list sizes, counts of mutual correlated agreement), on the challenges (an
injective map to the field), on the degree (2 ≤ n) and on the degrees of the public weights: that a
given Y meets them, and that the errors are small, is not said here. Who has the counts of agreement
beyond a third of the distance is an instance's matter; the theorem on codes that is taken as given
elsewhere (`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean) does not occur in this file. The errors are
bare counts for one instance: nothing on proof of work, nothing on several instances. That the mask
among the input's oracles is what an earlier block sent is that block's output joint's matter; the
code switch bears a rider (Cb/Pv/Tower/Cs.lean), and so does a sending (Cb/Pv/SendRide.lean
[not in this library]). The statements hold for any fx; without the condition on fx the verifier may
reject what an honest prover sends. Nothing on an honest prover.


Terms: lean/GLOSSARY.md.
-/
import Cb.Ent.FoldRideProofs
import Cb.Ent.FoldShortProofs
import Cb.Ent.TowerKnowProofs
import Ior.PullCProofs
import Cb.Ld.LdSumAcc
import Cb.Ld.LdWfPre
import Mathlib.Data.FinEnum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

variable {E P : Type} [Field E]

/-! ## The typed reductions -/

section Terms
variable (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

/-- FOLD, its mask in its own first round. -/
noncomputable abbrev foldOwn : IOR Y.Xi Y.Cin.ext Y.Xo Y.Cout.ext := Y.iorS fx

/-- the oracles of the input statement where the mask was sent earlier: the fold's input word; the
mask, read natively -/
abbrev EiRide : ExtSpec := Y.Cin.ext.prod Y.Cw.nat

/-- the fold's input word among them -/
def wordOf : ExtMap (EiRide Y) Y.Cin.ext := ExtMap.fst Y.Cin.ext Y.Cw.nat

/-- The declarations on positions: those of the library's block, the mask's positions now in the
input. -/
def declRide : IOR.Decl Y.shapeR (EiRide Y) Y.Cout.ext where
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  srcE := fun _ x => ({x} : Finset P).disjSum (Y.srcW x)
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- the library's block, reading its input word beside a mask that it does not read -/
noncomputable abbrev foldBeside : IOR Y.Xi (EiRide Y) Y.Xo Y.Cout.ext := Y.ior.pre some (wordOf Y)

/-- FOLD, its mask sent earlier. -/
noncomputable def foldRide : IOR Y.Xi (EiRide Y) Y.Xo Y.Cout.ext :=
  (foldBeside Y).pullC Y.shapeR (fun a => Y.carR fx a.1.1 a.2.2) (fun y τ => Y.impR y.2 y.1 τ)
    (declRide Y)

/-- the rounds: the mask's oracle and the sum | the coefficient; then n scalars | a challenge, once
for each variable -/
theorem foldOwn_shape :
    (foldOwn Y fx).shape = Y.round0 :: List.replicate Y.k (sRoundS E Y.Ch Y.n) :=
  rfl

/-- the rounds: the sum | the coefficient; then n scalars | a challenge, once for each variable -/
theorem foldRide_shape :
    (foldRide Y fx).shape = Blocks.plainRound E Y.Ch 0 :: List.replicate Y.k (sRoundS E Y.Ch Y.n) :=
  rfl

end Terms

/-! ## Joints, extractors, errors -/

section Joints
variable [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

/-- the input joint of `foldOwn`: the library's, at the radius e -/
noncomputable abbrev inOwn (e : ℕ) : IOR.Rels Unit Y.Xi Y.Cin.ext Y.Cin.N.Wit := (Y.jIn e).rels

/-- the input joint of `foldRide`: the same, read on the input word; nothing is asked of the mask -/
noncomputable abbrev inRide (e : ℕ) : IOR.Rels Unit Y.Xi (EiRide Y) Y.Cin.N.Wit :=
  (Y.jIn e).rels.keepE Y.Cw.nat

/-- the output joint of both: the library's, at the radius e -/
noncomputable abbrev outJ (e : ℕ) : IOR.Rels Unit Y.Xo Y.Cout.ext Y.Cout.N.Wit := (Y.jOut e).rels

/-- The extractor of `foldOwn`: the library's on the image of the transcript. d: the corrector's
threshold; d₀: the value where there is no image (nowhere). -/
noncomputable def extOwn (d : ℕ) (d₀ : Y.Cin.N.Wit) :
    Y.Xi × Y.Cin.ext.Str → Tr (foldOwn Y fx).shape → Y.Cout.N.Wit → Y.Cin.N.Wit :=
  Y.ior.red.extC Y.shapeS (fun a => Y.carS fx a.1.1) (Y.ext d) d₀

/-- The extractor of `foldRide`: the library's on the image, the mask taken from the input. -/
noncomputable def extRide (d : ℕ) (d₀ : Y.Cin.N.Wit) :
    Y.Xi × (EiRide Y).Str → Tr (foldRide Y fx).shape → Y.Cout.N.Wit → Y.Cin.N.Wit :=
  (foldBeside Y).red.extC Y.shapeR (fun a => Y.carR fx a.1.1 a.2.2)
    (fun a τ w => Y.ext d (a.1, a.2.1) τ w) d₀

/-- the errors, as counts of verifier's messages: the library's block's, round for round -/
noncomputable def errOwn (Lst mC mS mW : ℕ → ℕ) : Err (foldOwn Y fx).shape :=
  mulErr Y.shapeS Y.shape (Err.ones Y.shapeS) (Y.err Lst mC mS mW)

noncomputable def errRide (Lst mC mS mW : ℕ → ℕ) : Err (foldRide Y fx).shape :=
  mulErr Y.shapeR Y.shape (Err.ones Y.shapeR) (Y.err Lst mC mS mW)

/-! ## The statement, and nothing else in it -/

/-- Round-by-round knowledge soundness of `foldOwn`, between its two joints. -/
def FoldOwnKnow (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) (d₀ : Y.Cin.N.Wit) : Prop :=
  (foldOwn Y fx).red.Know (inOwn Y e).on (inOwn Y e).relR (outJ Y e).relR (extOwn Y fx d d₀)
    (errOwn Y fx Lst mC mS mW)

/-- Round-by-round knowledge soundness of `foldRide`, between its two joints. -/
def FoldRideKnow (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) (d₀ : Y.Cin.N.Wit) : Prop :=
  (foldRide Y fx).red.Know (inRide Y e).on (inRide Y e).relR (outJ Y e).relR (extRide Y fx d d₀)
    (errRide Y fx Lst mC mS mW)

/-! ## It holds under the premises of the library's theorem on the fold -/

theorem foldOwn_know (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) (d₀ : Y.Cin.N.Wit)
    (h : Y.HypK d e Lst mC mS mW) : FoldOwnKnow Y fx d e Lst mC mS mW d₀ :=
  ldEnt_foldS_know E P Y fx d e Lst mC mS mW d₀ h.codes h.errs h.inj h.deg h.qw

/-- the library's block beside a mask that it does not read -/
theorem foldBeside_know (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) (h : Y.HypK d e Lst mC mS mW) :
    (foldBeside Y).red.Know (inRide Y e).on (inRide Y e).relR (outJ Y e).relR
      (fun a τ w => Y.ext d (a.1, a.2.1) τ w) (Y.err Lst mC mS mW) := fun a _ =>
  ld_sum_know E P Y d e Lst mC mS mW h.codes h.errs h.inj h.deg h.qw (a.1, a.2.1) trivial

theorem foldRide_know (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) (d₀ : Y.Cin.N.Wit)
    (h : Y.HypK d e Lst mC mS mW) : FoldRideKnow Y fx d e Lst mC mS mW d₀ := by
  refine know_pullC_ior _ _ _ _ (foldBeside Y) Y.shapeR (fun a => Y.carR fx a.1.1 a.2.2)
    (fun y τ => Y.impR y.2 y.1 τ) (declRide Y) (Err.ones Y.shapeR) _ _ _ _ _
    (fun a τ w => Y.ext d (a.1, a.2.1) τ w) (Y.err Lst mC mS mW) d₀ ?_
    (foldBeside_know Y d e Lst mC mS mW h) fun a _ => ldEnt_ride_fib.1 E P Y fx a.1.1 a.2.2
  intro a τ τ' hτ
  have hτ' : some (Y.upR fx a.1.1 a.2.2 τ) = some τ' :=
    (ldEnt_ride_tr.1 E P Y fx a.1.1 a.2.2 τ).symm.trans hτ
  rw [← Option.some.inj hτ']
  exact ldEnt_ride_imp E P Y fx a.1.1 a.2.2 a.2.1 τ

/-! ## The errors as lists; the numbers of verifier's messages -/

omit [Fintype E] [Fintype P] [Nonempty P] in
theorem errOwn_toList (Lst mC mS mW : ℕ → ℕ) :
    (errOwn Y fx Lst mC mS mW).toList = (Y.err Lst mC mS mW).toList :=
  mulErr_ones_toList _ _ (Y.carS fx 0) _

omit [Fintype E] [Fintype P] [Nonempty P] in
theorem errRide_toList (Lst mC mS mW : ℕ → ℕ) :
    (errRide Y fx Lst mC mS mW).toList = (Y.err Lst mC mS mW).toList :=
  mulErr_ones_toList _ _ (Y.carR fx 0 fun _ _ => 0) _

end Joints

/-! ## Beside the statement: strings; locality -/

section Form

/-- a short round's oracle part is the empty string -/
def shortPoint (Ch : Type) [Fintype Ch] [Nonempty Ch] (n : ℕ) : (sRoundS E Ch n).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

def shortPoints (Ch : Type) [Fintype Ch] [Nonempty Ch] (n : ℕ) :
    (k : ℕ) → Shape.IsPoint (List.replicate k (sRoundS E Ch n))
  | 0 => ()
  | k + 1 => (shortPoint Ch n, shortPoints Ch n k)

variable (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

theorem foldOwn_point : Nonempty (foldOwn Y fx).shape.IsPoint :=
  ⟨((⟨inferInstanceAs (Fintype Y.Cw.NP), inferInstanceAs (DecidableEq Y.Cw.NP), fun f => f,
      fun _ _ => rfl, fun _ => rfl, fun _ _ => 0⟩, shortPoints Y.Ch Y.n Y.k) :
    Y.round0.IsPoint × Shape.IsPoint Y.roundsS)⟩

theorem foldRide_point : Nonempty (foldRide Y fx).shape.IsPoint :=
  ⟨((Blocks.plainPoint E Y.Ch 0, shortPoints Y.Ch Y.n Y.k) :
    Y.round0N.IsPoint × Shape.IsPoint Y.roundsS)⟩

theorem roundsS_noOrc : Blocks.NoOrc Y.roundsS :=
  Blocks.NoOrc.replicate (inferInstanceAs (Subsingleton Unit)) Y.k

variable [Fintype E]

theorem foldRide_local (hC : Y.C.Laws) (hZ : Y.Z.Laws) (hW : Y.Zw.Laws) :
    (foldRide Y fx).IsLocal := by
  have L := ld_sum_local E P Y hC hZ hW
  have no : Blocks.NoOrc Y.shapeR := ⟨inferInstanceAs (Subsingleton Unit), roundsS_noOrc Y⟩
  refine ⟨?_, ?_⟩
  · intro x y y' τ τ' hρ hpl _ _
    obtain rfl : τ = τ' := Blocks.Tr.eq_of_noOrc no hρ hpl
    show ((Y.carR fx x.1 y.2).tr τ).bind ((foldBeside Y).out x y) =
      ((Y.carR fx x.1 y'.2).tr τ).bind ((foldBeside Y).out x y')
    rw [ldEnt_ride_tr.1 E P Y fx x.1 y.2 τ, ldEnt_ride_tr.1 E P Y fx x.1 y'.2 τ]
    exact L.out x y.1 y'.1 (Y.upR fx x.1 y.2 τ) (Y.upR fx x.1 y'.2 τ) rfl rfl
      (fun p hp => absurd hp (Finset.notMem_empty p))
      (fun p hp => absurd hp (Finset.notMem_empty p))
  · intro y y' τ τ' q hρ hpl hE _
    obtain rfl : τ = τ' := Blocks.Tr.eq_of_noOrc no hρ hpl
    show Y.Cout.ext.rd (Y.impR y.2 y.1 τ) q = Y.Cout.ext.rd (Y.impR y'.2 y'.1 τ) q
    rw [ldEnt_ride_imp E P Y fx 0 y.2 y.1 τ, ldEnt_ride_imp E P Y fx 0 y'.2 y'.1 τ]
    refine L.imp y.1 y'.1 (Y.upR fx 0 y.2 τ) (Y.upR fx 0 y'.2 τ) q rfl rfl ?_ ?_
    · intro p hp
      obtain rfl : p = q := Finset.mem_singleton.1 hp
      exact Sum.inl.inj (hE (Sum.inl p) (Finset.inl_mem_disjSum.2 (Finset.mem_singleton_self p)))
    · intro p hp
      obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_map.1 hp
      have h := Sum.inr.inj (hE (Sum.inr p₀) (Finset.inr_mem_disjSum.2 hp₀))
      exact eq_of_heq (Sigma.mk.inj h).2

theorem foldOwn_local (hC : Y.C.Laws) (hZ : Y.Z.Laws) (hW : Y.Zw.Laws) :
    (foldOwn Y fx).IsLocal := by
  have L := ld_sum_local E P Y hC hZ hW
  have key : ∀ (t₀ : E) (τ τ' : Tr Y.shapeS), τ.rho = τ'.rho → τ.plains = τ'.plains →
      (Y.upS fx t₀ τ).rho = (Y.upS fx t₀ τ').rho ∧
        (Y.upS fx t₀ τ).plains = (Y.upS fx t₀ τ').plains := by
    rintro t₀ ⟨⟨o, u⟩, c, τ⟩ ⟨⟨o', u'⟩, c', τ'⟩ hρ hpl
    obtain rfl : c = c' := congrArg Prod.fst hρ
    obtain rfl : u = u' := congrArg Prod.fst hpl
    obtain rfl : τ = τ' :=
      Blocks.Tr.eq_of_noOrc (roundsS_noOrc Y) (congrArg Prod.snd hρ) (congrArg Prod.snd hpl)
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · intro x y y' τ τ' hρ hpl _ _
    show ((Y.carS fx x.1).tr τ).bind (Y.ior.out x y) = ((Y.carS fx x.1).tr τ').bind (Y.ior.out x y')
    rw [ldEnt_foldS_tr E P Y fx x.1 τ, ldEnt_foldS_tr E P Y fx x.1 τ']
    exact L.out x y y' _ _ (key x.1 τ τ' hρ hpl).1 (key x.1 τ τ' hρ hpl).2
      (fun p hp => absurd hp (Finset.notMem_empty p))
      (fun p hp => absurd hp (Finset.notMem_empty p))
  · intro y y' τ τ' q hρ hpl hE hO
    show Y.Cout.ext.rd (Y.impS y τ) q = Y.Cout.ext.rd (Y.impS y' τ') q
    rw [ldEnt_foldS_imp E P Y fx 0 y τ, ldEnt_foldS_imp E P Y fx 0 y' τ']
    refine L.imp y y' _ _ q (key 0 τ τ' hρ hpl).1 (key 0 τ τ' hρ hpl).2 hE ?_
    intro p hp
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_map.1 hp
    exact hO (Sum.inl p₀) (Finset.mem_map.2 ⟨p₀, hp₀, rfl⟩)

end Form

/-! ## Beside the statement: outputs; what is handed on -/

section More
variable (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

/-- The verifier of `foldRide` in closed form, if `fx.2` is an inverse of the "sum" of the power
that is left out: no check is left. (For `foldOwn`: `ldEnt_foldS_out`,
Cb/Ent/FoldShortProofs.lean.) -/
theorem foldRide_out (h : fx.2 * (HVar.plain E Y.n).mon fx.1 = 1) (x : Y.Xi) (y : (EiRide Y).Str)
    (τ : Tr Y.shapeR) :
    (foldRide Y fx).out x y τ =
      some (Y.newX x (Y.upRhoR τ.rho)
        (sClaim Y.val Y.n fx Y.k (τ.1.2 + x.1 * Y.val τ.2.1) τ.2.2)) := by
  show ((Y.carR fx x.1 y.2).tr τ).bind ((foldBeside Y).out x y) = _
  rw [ldEnt_ride_tr.1 E P Y fx x.1 y.2 τ]
  exact Y.out_upR fx h x y.2 τ

/-- Under that premise on fx the verifier never rejects. -/
theorem foldOwn_total (h : fx.2 * (HVar.plain E Y.n).mon fx.1 = 1) (x : Y.Xi) (y : Y.Cin.Word)
    (τ : Tr Y.shapeS) : ((foldOwn Y fx).out x y τ).isSome := by
  rw [ldEnt_foldS_out E P Y fx h x y τ]
  rfl

theorem foldRide_total (h : fx.2 * (HVar.plain E Y.n).mon fx.1 = 1) (x : Y.Xi)
    (y : (EiRide Y).Str) (τ : Tr Y.shapeR) : ((foldRide Y fx).out x y τ).isSome := by
  rw [foldRide_out Y fx h x y τ]
  rfl

/-- the two states of the input statement, read in an output statement -/
def statesOf (x' : Y.Xo) : Y.St × Y.StS := (x'.2.1.1.1, x'.2.2.1.1.1)

theorem out_states (x : Y.Xi) (τ : Tr Y.shape) (x' : Y.Xo) (h : Y.out x τ = some x') :
    statesOf Y x' = x.2 := by
  unfold SumPar.out at h
  split at h
  · rw [← Option.some.inj h]
    rfl
  · cases h

/-- The states of the forms are handed on, whatever fx. -/
theorem foldOwn_passes : (foldOwn Y fx).Passes (fun x => x.2) (statesOf Y) := by
  intro x y τ x' h
  have h' : ((Y.carS fx x.1).tr τ).bind (Y.ior.out x y) = some x' := h
  rw [ldEnt_foldS_tr E P Y fx x.1 τ] at h'
  exact out_states Y x _ x' h'

theorem foldRide_passes : (foldRide Y fx).Passes (fun x => x.2) (statesOf Y) := by
  intro x y τ x' h
  have h' : ((Y.carR fx x.1 y.2).tr τ).bind ((foldBeside Y).out x y) = some x' := h
  rw [ldEnt_ride_tr.1 E P Y fx x.1 y.2 τ] at h'
  exact out_states Y x _ x' h'

/-! ## Rounds, errors and numbers of verifier's messages, as lists -/

theorem foldOwn_rounds : (foldOwn Y fx).shape.length = Y.k + 1 := by
  rw [foldOwn_shape, List.length_cons, List.length_replicate]

theorem foldRide_rounds : (foldRide Y fx).shape.length = Y.k + 1 := by
  rw [foldRide_shape, List.length_cons, List.length_replicate]

theorem short_vals (Ch : Type) [Fintype Ch] [Nonempty Ch] (n : ℕ) : ∀ k : ℕ,
    Shape.chalList (List.replicate k (sRoundS E Ch n)) = List.replicate k (Fintype.card Ch)
  | 0 => rfl
  | k + 1 => congrArg (List.cons (Fintype.card Ch)) (short_vals Ch n k)

theorem foldOwn_vals :
    (foldOwn Y fx).shape.chalList = List.replicate (Y.k + 1) (Fintype.card Y.Ch) :=
  congrArg (List.cons (Fintype.card Y.Ch)) (short_vals Y.Ch Y.n Y.k)

theorem foldRide_vals :
    (foldRide Y fx).shape.chalList = List.replicate (Y.k + 1) (Fintype.card Y.Ch) :=
  congrArg (List.cons (Fintype.card Y.Ch)) (short_vals Y.Ch Y.n Y.k)

theorem sErr_toList (Ch : Type) [Fintype Ch] [Nonempty Ch] (n : ℕ) : ∀ (k : ℕ) (f : ℕ → ℕ),
    (sErr (E := E) (Ch := Ch) n k f).toList = (List.range k).map f
  | 0, _ => rfl
  | k + 1, f => by
      show f 0 :: (sErr (E := E) (Ch := Ch) n k fun j => f (j + 1)).toList = _
      rw [sErr_toList Ch n k, List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl

/-- The library's errors of a fold, written out: the first round's; then round i + 1's, i < k. -/
theorem fold_errList (Lst mC mS mW : ℕ → ℕ) :
    (Y.err Lst mC mS mW).toList = Lst 0 :: (List.range Y.k).map fun i =>
      mC (i + 1) + (if i + 1 ≤ Y.h then mS (i + 1) + mW (i + 1) else 0) + Lst i * Y.n :=
  congrArg (List.cons (Lst 0)) (sErr_toList Y.Ch Y.n Y.k _)

end More

/-! ## The statement at a size -/

/-- What is public of a fold: the long positions, the library's parameters, which coefficient is
left out, and the numbers of the statement: the corrector's threshold d, the radius e, list sizes
and counts of agreement round by round. -/
structure FoldSize (E : Type) [Field E] where
  P : Type
  [finP : Fintype P]
  [neP : Nonempty P]
  Y : SumPar E P
  fx : Fin (Y.n + 1) × E
  d : ℕ
  e : ℕ
  Lst : ℕ → ℕ
  mC : ℕ → ℕ
  mS : ℕ → ℕ
  mW : ℕ → ℕ

attribute [instance] FoldSize.finP FoldSize.neP

section Size
variable [Fintype E] (s : FoldSize E)

/-- The statement that FOLD with its own mask, at the size s, is knowledge sound. -/
def FoldSize.HOwn : Prop := ∀ d₀, FoldOwnKnow s.Y s.fx s.d s.e s.Lst s.mC s.mS s.mW d₀

/-- The statement that FOLD whose mask was sent earlier, at the size s, is knowledge sound. -/
def FoldSize.HRide : Prop := ∀ d₀, FoldRideKnow s.Y s.fx s.d s.e s.Lst s.mC s.mS s.mW d₀

/-- Conditions, as in the library's theorem on the fold, on public data alone. -/
def FoldSize.OK : Prop := s.Y.HypK s.d s.e s.Lst s.mC s.mS s.mW

/-- The condition on fx under which no check is left. -/
def FoldSize.Pick : Prop := s.fx.2 * (HVar.plain E s.Y.n).mon s.fx.1 = 1

theorem FoldSize.hOwn (h : s.OK) : s.HOwn :=
  fun d₀ => foldOwn_know s.Y s.fx s.d s.e s.Lst s.mC s.mS s.mW d₀ h

theorem FoldSize.hRide (h : s.OK) : s.HRide :=
  fun d₀ => foldRide_know s.Y s.fx s.d s.e s.Lst s.mC s.mS s.mW d₀ h

omit [Fintype E] in
theorem FoldSize.totalOwn (h : s.Pick) (x : s.Y.Xi) (y : s.Y.Cin.Word) (τ : Tr s.Y.shapeS) :
    ((foldOwn s.Y s.fx).out x y τ).isSome := foldOwn_total s.Y s.fx h x y τ

omit [Fintype E] in
theorem FoldSize.totalRide (h : s.Pick) (x : s.Y.Xi) (y : (EiRide s.Y).Str) (τ : Tr s.Y.shapeR) :
    ((foldRide s.Y s.fx).out x y τ).isSome := foldRide_total s.Y s.fx h x y τ

theorem foldOwn_onOut : ∀ a τ b, (inOwn s.Y s.e).on a →
    (foldOwn s.Y s.fx).red.out a τ = some b → (outJ s.Y s.e).on b := fun _ _ _ _ _ => trivial

theorem foldRide_onOut : ∀ a τ b, (inRide s.Y s.e).on a →
    (foldRide s.Y s.fx).red.out a τ = some b → (outJ s.Y s.e).on b := fun _ _ _ _ _ => trivial

end Size

#print axioms FoldSize.hOwn
#print axioms FoldSize.hRide
#print axioms foldOwn_local
#print axioms foldRide_local

end Cb.Pv.Tower
