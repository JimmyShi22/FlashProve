-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvAttentionClaimsA.lean.
The routines of OnBytes/Model/AttentionClaimsA.lean keep every property of the state that has
`Prim`.

One statement a routine: `Inv I` (OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a routine of a
link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvAttentionDivide
import OnBytes.Model.AttentionClaimsA

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem _root_.Fo.inv_Attention_u3at (h : Heard) (t i : Nat)  :
    Inv I (OnBytes.Attention.u3at h t i) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_u3at)

theorem _root_.Fo.inv_Attention_weighted (n : Nat) (w : Array E) (f : Nat → SubM Aff) (h_f : ∀ x0,
    Inv I (f x0)) :
    Inv I (OnBytes.Attention.weighted n w f) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_weighted)

theorem _root_.Fo.inv_Attention_plane (h : Heard) (t x lam a : Nat) (z : Array E) (isD : Bool)  :
    Inv I (OnBytes.Attention.plane h t x lam a z isD) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_plane)

theorem _root_.Fo.inv_Attention_shV (h : Heard) (t off nl J lam j : Nat)  :
    Inv I (OnBytes.Attention.shV h t off nl J lam j) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_shV)

theorem _root_.Fo.inv_Attention_xl (h : Heard) (t : Nat) (X : TenAt) (lam hd : Nat) (zc : Array E)
     :
    Inv I (OnBytes.Attention.xl h t X lam hd zc) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_xl)

theorem _root_.Fo.inv_Attention_overG (h : Heard) (zg : Array E) (f : Nat → SubM Aff) (h_f : ∀ x0,
    Inv I (f x0)) :
    Inv I (OnBytes.Attention.overG h zg f) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_overG)

theorem _root_.Fo.inv_Attention_readDenominator (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat)
     :
    Inv I (OnBytes.Attention.readDenominator h t zg lam a) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Attention_readDenominator)

theorem _root_.Fo.inv_Attention_readMaximum (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat)  :
    Inv I (OnBytes.Attention.readMaximum h t zg lam a) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Attention_readMaximum)

theorem _root_.Fo.inv_Attention_readIndexBit (h : Heard) (t : Nat) (zg : Array E) (lam a k : Nat) 
    :
    Inv I (OnBytes.Attention.readIndexBit h t zg lam a k) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply Fo.inv_Attention_readIndexBit)

theorem _root_.Fo.inv_Attention_readHead (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam
    a : Nat)  :
    Inv I (OnBytes.Attention.readHead h t X zg zc lam a) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_readHead)

theorem _root_.Fo.inv_Attention_readGroup (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam
    : Nat)  :
    Inv I (OnBytes.Attention.readGroup h t X zg zc lam) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_readGroup)

theorem _root_.Fo.inv_Attention_lessPieces (start : Aff) (pw : Array PW) (f : PW → SubM Aff) (h_f
    : ∀ x0, Inv I (f x0)) :
    Inv I (OnBytes.Attention.lessPieces start pw f) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_lessPieces)

theorem _root_.Fo.inv_Attention_linPlanes (h : Heard) (pc : PlaneClaim)  :
    Inv I (OnBytes.Attention.linPlanes h pc) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_linPlanes)

theorem _root_.Fo.inv_Attention_callKR (h : Heard) (q : Nat)  :
    Inv I (OnBytes.Attention.callKR h q) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_callKR)

theorem _root_.Fo.inv_Attention_claim3 (h : Heard) (j : Joins)  :
    Inv I (OnBytes.Attention.claim3 h j) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_claim3)

theorem _root_.Fo.inv_Attention_endValues (h : Heard) (k : Score) (tb : ScoreTables) (rc : Array
    E) (b : Nat) (w : PW)  :
    Inv I (OnBytes.Attention.endValues h k tb rc b w) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_endValues)

theorem _root_.Fo.inv_Attention_unitKFD (h : Heard) (i : Nat) (k : Score)  :
    Inv I (OnBytes.Attention.unitKFD h i k) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_unitKFD)

theorem _root_.Fo.inv_Attention_callKFD (h : Heard) (q : Nat) (c : ACall)  :
    Inv I (OnBytes.Attention.callKFD h q c) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_callKFD)

theorem _root_.Fo.inv_Attention_claim4 (h : Heard) (j : Joins)  :
    Inv I (OnBytes.Attention.claim4 h j) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply Fo.inv_Attention_claim4)

end OnBytes.Attention
