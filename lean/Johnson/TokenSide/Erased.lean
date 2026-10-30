-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Erased.lean: A TOKEN PROGRAM OF THIS FOLDER AS AN ORDINARY ORACLE ALGORITHM:
tokens are strings in a store (erase, Compile/Star.lean), and the names fbw t k of the later tries
of a search are written back to fb t (realQ, OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean). One definition
and its calculus.

General lemmas on the second form's oracles. This file states no goal of the release.

  plainOf c vs   realQ (erase c vs): the algorithm; it gives c's result and the store at the end.
  realQ_bind     realQ of a sequence (the first form's Compile/Batch/RealQ.lean has the like).
  plainOf_pure, _bind, _sample, _fresh, _reveal   constructor by constructor.
  plainOf_grows  the store only grows: on every path the store at the start is a prefix of the store
                 at the end (Post, Johnson/TokenSide/Tie.lean).
  getD_of_prefix, getD_length_append   reading a store.
  Tie.fresh      the rule "coin" of Johnson/TokenSide/Tie.lean at a fresh token of ℓ bits.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Split
import Johnson.TokenSide.Tie
import Compile.EraseKit
import Compile.Step1_life2_Erase

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {α β : Type}

theorem realQ_bind (c : OComp (typedOracleFamily lam K L) α) (g : α → OComp (typedOracleFamily lam K L) β) :
    realQ (c.bind g) = (realQ c).bind fun a => realQ (g a) := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)
  | query o q k ih =>
    cases o with
    | fbw t j => exact congrArg (OComp.query (S := typedOracleFamily lam K L) (.fb t) q) (funext ih)
    | leaf => exact congrArg (OComp.query (S := typedOracleFamily lam K L) .leaf q) (funext ih)
    | node => exact congrArg (OComp.query (S := typedOracleFamily lam K L) .node q) (funext ih)
    | rleaf => exact congrArg (OComp.query (S := typedOracleFamily lam K L) .rleaf q) (funext ih)
    | rnode => exact congrArg (OComp.query (S := typedOracleFamily lam K L) .rnode q) (funext ih)
    | fb t => exact congrArg (OComp.query (S := typedOracleFamily lam K L) (.fb t) q) (funext ih)
    | g t => exact congrArg (OComp.query (S := typedOracleFamily lam K L) (.g t) q) (funext ih)
    | ann => exact congrArg (OComp.query (S := typedOracleFamily lam K L) .ann q) (funext ih)
    | other => exact congrArg (OComp.query (S := typedOracleFamily lam K L) .other q) (funext ih)

/-- **A token program as an ordinary oracle algorithm**, from the store vs: its result and the store
at the end. -/
def plainOf (c : StT lam K L α) (vs : List Bits) : TypedOracleComputation lam K L (α × List Bits) := realQ (erase c vs)

theorem plainOf_pure (a : α) (vs : List Bits) :
    plainOf (Step.pure a : StT lam K L α) vs = .pure (a, vs) := rfl

theorem plainOf_bind (c : StT lam K L α) (g : α → StT lam K L β) (vs : List Bits) :
    plainOf (c.bind g) vs = (plainOf c vs).bind fun p => plainOf (g p.1) p.2 := by
  unfold plainOf
  rw [erase_bind, realQ_bind]

theorem plainOf_sample (n : ℕ) (k : Fin (n + 1) → StT lam K L α) (vs : List Bits) :
    plainOf (Step.sample n k) vs = .sample n fun r => plainOf (k r) vs := rfl

theorem plainOf_fresh (ℓ : ℕ) (k : Tok → StT lam K L α) (vs : List Bits) :
    plainOf (Step.fresh ℓ k) vs = .sample (2 ^ ℓ - 1) fun r =>
      plainOf (k vs.length) (vs ++ [List.ofFn (Life2.bitsE ℓ r)]) := rfl

theorem plainOf_reveal (ts : List Tok) (k : List Bits → StT lam K L α) (vs : List Bits) :
    plainOf (Step.reveal ts k) vs = plainOf (k (ts.map fun u => vs.getD u [])) vs := rfl

/-- realQ keeps a property of all outputs. -/
theorem post_realQ {P : α → Prop} : ∀ {c : OComp (typedOracleFamily lam K L) α}, Post P c → Post P (realQ c)
  | .pure _, h => h
  | .sample _ _, h => fun r => post_realQ (h r)
  | .query .leaf _ _, h => fun r => post_realQ (h r)
  | .query .node _ _, h => fun r => post_realQ (h r)
  | .query .rleaf _ _, h => fun r => post_realQ (h r)
  | .query .rnode _ _, h => fun r => post_realQ (h r)
  | .query (.fb _) _ _, h => fun r => post_realQ (h r)
  | .query (.g _) _ _, h => fun r => post_realQ (h r)
  | .query .ann _ _, h => fun r => post_realQ (h r)
  | .query .other _ _, h => fun r => post_realQ (h r)
  | .query (.fbw _ _) _ _, h => fun r => post_realQ (h r)

theorem post_erase_grows {S : OSpec} {sp : Split S} (c : Step S sp α) :
    ∀ vs ws : List Bits, ws <+: vs → Post (fun p : α × List Bits => ws <+: p.2) (erase c vs) := by
  induction c with
  | pure a => exact fun _ _ h => h
  | sample n k ih => exact fun vs ws h r => ih r vs ws h
  | plain o q k ih => exact fun vs ws h r => ih r vs ws h
  | fresh ℓ k ih => exact fun vs ws h r => ih _ _ ws (h.trans (List.prefix_append _ _))
  | marked o t us pt inj k ih =>
    exact fun vs ws h r => ih _ _ _ ws (h.trans (List.prefix_append _ _))
  | reveal ts k ih => exact fun vs ws h => ih _ vs ws h

/-- **The store only grows.** -/
theorem plainOf_grows (c : StT lam K L α) (vs : List Bits) :
    Post (fun p : α × List Bits => vs <+: p.2) (plainOf c vs) :=
  post_realQ (post_erase_grows c vs vs List.prefix_rfl)

/-! ## Reading a store -/

theorem getD_of_prefix {vs ws : List Bits} (h : vs <+: ws) {t : ℕ} (ht : t < vs.length) :
    ws.getD t [] = vs.getD t [] := by
  obtain ⟨l, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem getD_length_append (vs : List Bits) (v : Bits) (l : List Bits) :
    (vs ++ v :: l).getD vs.length [] = v := by
  simp [List.getD_eq_getElem?_getD]

end OnBytes.TokenSide

namespace Rom.Tie
open Prob _root_.Compile

variable {S : OSpec} {Ω α β : Type} {μ : PMF Ω} {φ : α → Ω → β} {Q : α → Prop}

/-- The rule "coin" at a draw of ℓ bits in the form in which erase writes a fresh token. -/
theorem fresh (ℓ : ℕ) {k : Fin (2 ^ ℓ - 1 + 1) → OComp S α} {g : Ω → OComp S β}
    (upd : (Fin ℓ → Bool) → Ω → Ω) (hμ : Resamples μ (unif (Fin ℓ → Bool)) upd)
    (hk : ∀ r, Tie μ φ Q (k r) fun ω => g (upd (Life2.bitsE ℓ r) ω)) :
    Tie μ φ Q (.sample (2 ^ ℓ - 1) k) g :=
  .coin (Life2.bitsE ℓ) upd (map_unif_equiv (Life2.bitsE ℓ)) hμ hk

end Rom.Tie

#print axioms OnBytes.TokenSide.plainOf_grows
#print axioms Rom.Tie.fresh
