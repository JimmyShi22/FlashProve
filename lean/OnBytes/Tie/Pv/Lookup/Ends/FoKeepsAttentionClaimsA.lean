-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsAttentionClaimsA.lean.
The routines of OnBytes/Model/AttentionClaimsA.lean keep what lies under the filled slots.

One statement for each routine: `Keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean)
or, for a routine of a link, `KeepsL` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine
takes routines as arguments, the statement has the premise that each of these has `Keeps`. Neither
property says anything of a run in which the routine refuses. Each statement is also given as a rule
to the tactic `keeps` (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsAttentionDivide
import OnBytes.Model.AttentionClaimsA

set_option autoImplicit false

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.keeps_Attention_u3at (h : Heard) (t i : Nat)  :
    Keeps (OnBytes.Attention.u3at h t i) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_u3at)

theorem _root_.Fo.keeps_Attention_weighted (n : Nat) (w : Array E) (f : Nat → SubM Aff) (h_f : ∀ x0,
    Keeps (f x0)) :
    Keeps (OnBytes.Attention.weighted n w f) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_weighted)

theorem _root_.Fo.keeps_Attention_plane (h : Heard) (t x lam a : Nat) (z : Array E) (isD : Bool)  :
    Keeps (OnBytes.Attention.plane h t x lam a z isD) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_plane)

theorem _root_.Fo.keeps_Attention_shV (h : Heard) (t off nl J lam j : Nat)  :
    Keeps (OnBytes.Attention.shV h t off nl J lam j) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_shV)

theorem _root_.Fo.keeps_Attention_xl (h : Heard) (t : Nat) (X : TenAt) (lam hd : Nat) (zc : Array E)
     :
    Keeps (OnBytes.Attention.xl h t X lam hd zc) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_xl)

theorem _root_.Fo.keeps_Attention_overG (h : Heard) (zg : Array E) (f : Nat → SubM Aff) (h_f : ∀ x0,
    Keeps (f x0)) :
    Keeps (OnBytes.Attention.overG h zg f) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_overG)

theorem _root_.Fo.keeps_Attention_readDenominator (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat)
     :
    Keeps (OnBytes.Attention.readDenominator h t zg lam a) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Attention_readDenominator)

theorem _root_.Fo.keeps_Attention_readMaximum (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat)  :
    Keeps (OnBytes.Attention.readMaximum h t zg lam a) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Attention_readMaximum)

theorem _root_.Fo.keeps_Attention_readIndexBit (h : Heard) (t : Nat) (zg : Array E) (lam a k : Nat) 
    :
    Keeps (OnBytes.Attention.readIndexBit h t zg lam a k) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply Fo.keeps_Attention_readIndexBit)

theorem _root_.Fo.keeps_Attention_readHead (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam
    a : Nat)  :
    Keeps (OnBytes.Attention.readHead h t X zg zc lam a) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_readHead)

theorem _root_.Fo.keeps_Attention_readGroup (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam
    : Nat)  :
    Keeps (OnBytes.Attention.readGroup h t X zg zc lam) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_readGroup)

theorem _root_.Fo.keeps_Attention_lessPieces (start : Aff) (pw : Array PW) (f : PW → SubM Aff) (h_f
    : ∀ x0, Keeps (f x0)) :
    Keeps (OnBytes.Attention.lessPieces start pw f) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_lessPieces)

theorem _root_.Fo.keeps_Attention_linPlanes (h : Heard) (pc : PlaneClaim)  :
    Keeps (OnBytes.Attention.linPlanes h pc) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_linPlanes)

theorem _root_.Fo.keeps_Attention_callKR (h : Heard) (q : Nat)  :
    Keeps (OnBytes.Attention.callKR h q) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_callKR)

theorem _root_.Fo.keeps_Attention_claim3 (h : Heard) (j : Joins)  :
    Keeps (OnBytes.Attention.claim3 h j) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_claim3)

theorem _root_.Fo.keeps_Attention_endValues (h : Heard) (k : Score) (tb : ScoreTables) (rc : Array
    E) (b : Nat) (w : PW)  :
    Keeps (OnBytes.Attention.endValues h k tb rc b w) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_endValues)

theorem _root_.Fo.keeps_Attention_unitKFD (h : Heard) (i : Nat) (k : Score)  :
    Keeps (OnBytes.Attention.unitKFD h i k) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_unitKFD)

theorem _root_.Fo.keeps_Attention_callKFD (h : Heard) (q : Nat) (c : ACall)  :
    Keeps (OnBytes.Attention.callKFD h q c) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_callKFD)

theorem _root_.Fo.keeps_Attention_claim4 (h : Heard) (j : Joins)  :
    Keeps (OnBytes.Attention.claim4 h j) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply Fo.keeps_Attention_claim4)

end OnBytes.Attention
