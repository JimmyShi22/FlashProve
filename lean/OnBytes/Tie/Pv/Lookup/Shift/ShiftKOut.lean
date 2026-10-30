-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Shift/ShiftKOut.lean.
What the verifier of the shift and the whole lookup puts out, for all inputs.

`thetaOf P several b τ` is what the shift's round draws (the first round's challenge), or 0 if there
is no such round; `restOf P several b τ` is the transcript of the block b behind it.
 * `lkV`, `lkV_eq`, `lkK_tot`: if b's verifier refuses nothing, copies the oracles and has the value
   f, so does the shift with b, with the value f (st, theta) (the rest).
 * `lkK_red`: with several calls the reduction is the draw's joined with b's by `Reduction.seq`.
   `lkK_out0`: with one call it is b's at (st, 0).
 * `lkK_out`, `allKS_out`, `allK₀_out`: the out for all inputs: behind any such b; at the whole
   lookup for short sumcheck blocks with a total value; at the named ones, without a premise.
 * `allK₀_st`: the statement that is put out holds the caller's state and theta.
 * `thetaOf_app`, `restOf_app`: at a transcript that is the draw's round and then a rest, they give
   the draw and the rest back.
The value functions here are typed over the library's shapes and stand in theorems; nothing in this
file is meant to be run.

-/
import OnBytes.Tie.Pv.Lookup.Shift.ShiftK
import OnBytes.Tie.Pv.Lookup.Out.TwOutEq

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

noncomputable section
section
variable {E St J Xo : Type} [Field E] [Fintype E] {Ex : ExtSpec} (P : ShiftQ E St (J → E))

/-- What the shift's round draws; 0 if there is none. -/
def thetaOf : (several : Bool) → (b : BkK (St × E) Xo Ex) → Tr (P.lkK several b).R.shape → E
  | true, b, τ => drawn (Tr.fst (s := [drawRound E]) (t := b.R.shape) τ)
  | false, _, _ => 0

/-- The transcript behind the shift's round. -/
def restOf : (several : Bool) → (b : BkK (St × E) Xo Ex) → Tr (P.lkK several b).R.shape →
    Tr b.R.shape
  | true, b, τ => Tr.snd (s := [drawRound E]) (t := b.R.shape) τ
  | false, _, τ => τ

/-- The value of the shift, then b. -/
def lkV : (several : Bool) → {b : BkK (St × E) Xo Ex} → Val b → Val (P.lkK several b)
  | true, _, f => bseqV (drawV E (Prod.mk : St → E → St × E) Ex (2 ^ P.d)) f
  | false, _, f => bpreV f fun st => (st, (0 : E))

theorem lkV_eq (several : Bool) {b : BkK (St × E) Xo Ex} (f : Val b) (st : St)
    (τ : Tr (P.lkK several b).R.shape) :
    lkV P several f st τ = f (st, thetaOf P several b τ) (restOf P several b τ) := by
  cases several <;> rfl

theorem lkK_tot (several : Bool) {b : BkK (St × E) Xo Ex} {f : Val b} (h : Tot b.R f) :
    Tot (P.lkK several b).R (lkV P several f) := by
  cases several with
  | true => exact tot_bseq (tot_draw _ _ _) h
  | false => exact tot_bpre h _

/-- Several calls: the reduction is the draw's joined with b's by Reduction.seq. -/
theorem lkK_red (b : BkK (St × E) Xo Ex) :
    (P.lkK true b).R.red = (P.bkK Ex).R.red.seq b.R.red := bk_seq_red _ _

/-- One call: no round: b's out at (st, 0). -/
theorem lkK_out0 (b : BkK (St × E) Xo Ex) (a : St × Ex.Str) (τ : Tr b.R.shape) :
    (P.lkK false b).R.red.out a τ = b.R.red.out ((a.1, (0 : E)), a.2) τ := rfl

/-- For all inputs, behind any block that never refuses. -/
theorem lkK_out (several : Bool) {b : BkK (St × E) Xo Ex} {f : Val b} (h : Tot b.R f)
    (a : St × Ex.Str) (τ : Tr (P.lkK several b).R.shape) :
    (P.lkK several b).R.red.out a τ =
      some (f (a.1, thetaOf P several b τ) (restOf P several b τ), a.2) := by
  rw [(lkK_tot P several h).red_out a τ, lkV_eq]

theorem thetaOf_app (b : BkK (St × E) Xo Ex) (τ₁ : Tr [drawRound E]) (τ₂ : Tr b.R.shape) :
    thetaOf P true b (Tr.app τ₁ τ₂) = drawn τ₁ := by
  show drawn (Tr.fst (Tr.app τ₁ τ₂)) = _
  rw [Tr.fst_app]

theorem restOf_app (b : BkK (St × E) Xo Ex) (τ₁ : Tr [drawRound E]) (τ₂ : Tr b.R.shape) :
    restOf P true b (Tr.app τ₁ τ₂) = τ₂ := by
  show Tr.snd (s := [drawRound E]) (Tr.app τ₁ τ₂) = _
  rw [Tr.snd_app]

end

section
variable {E St : Type} [Field E] [Fintype E] (Ex : ExtSpec) (A0 : LkAsmH E)
  (P : ShiftQ E St (A0.J → E)) (several : Bool)

/-- For every letter whose value is total at the lookup's own sumchecks. -/
theorem allKS_out {SK : PscLtK E Ex} (SV : PscLtV SK) (h : LtV SV (P.asmH A0)) (a : St × Ex.Str)
    (τ : Tr (P.lkK several ((P.asmH A0).baseKS SK)).R.shape) :
    (P.lkK several ((P.asmH A0).baseKS SK)).R.red.out a τ =
      some ((P.asmH A0).rd (chnV SV (P.asmH A0)
        (a.1, thetaOf P several ((P.asmH A0).baseKS SK) τ)
        (restOf P several ((P.asmH A0).baseKS SK) τ)), a.2) :=
  lkK_out P several (baseKS_tot SV (P.asmH A0) h) a τ

/-- The block at the named short sumcheck blocks, in the letters in which its value is stated. -/
theorem allK₀_eq : P.allK A0 several V₀ V₀C (Ex := Ex) =
    P.lkK several ((P.asmH A0).baseKS (SK₀ E Ex)) := rfl

/-- At the named short sumcheck blocks, for all inputs. -/
theorem allK₀_out (a : St × Ex.Str) (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape) :
    (P.allK A0 several V₀ V₀C (Ex := Ex)).R.red.out a τ =
      some ((P.asmH A0).rd (chnV (SV₀ E Ex) (P.asmH A0)
        (a.1, thetaOf P several ((P.asmH A0).baseKS (SK₀ E Ex)) τ)
        (restOf P several ((P.asmH A0).baseKS (SK₀ E Ex)) τ)), a.2) :=
  allKS_out Ex A0 P several (SV₀ E Ex) (ltV₀ Ex (P.asmH A0)) a τ

/-- The shift's draw is in the state: whatever is put out holds the caller's state and θ. -/
theorem allK₀_st (a : St × Ex.Str) (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape)
    (b : TX (P.asmH A0).St E (P.asmH A0).J × Ex.Str)
    (hb : (P.allK A0 several V₀ V₀C (Ex := Ex)).R.red.out a τ = some b) :
    b.1.1 = (a.1, thetaOf P several ((P.asmH A0).baseKS (SK₀ E Ex)) τ) ∧ b.2 = a.2 := by
  rw [allK₀_out] at hb
  obtain rfl := Option.some.inj hb
  exact ⟨run_st Ex (P.asmH A0) _ _, rfl⟩

end
end
end Tw
