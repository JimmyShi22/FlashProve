-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysAttentionClaimsA.lean.
Routines of OnBytes/Model/AttentionClaimsA.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysAttentionDivide
import OnBytes.Model.AttentionClaimsA

set_option autoImplicit false

namespace OnBytes.Attention
open Fo OnBytes.PscRun
open OnBytes.Model

theorem _root_.Fo.stays_Attention_u3at (h : Heard) (t i : Nat)  :
    DryS (OnBytes.Attention.u3at h t i) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_u3at)

theorem _root_.Fo.stays_Attention_weighted (n : Nat) (w : Array E) (f : Nat → SubM Aff) (h_f : ∀ x0,
    DryS (f x0)) :
    DryS (OnBytes.Attention.weighted n w f) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_weighted)

theorem _root_.Fo.stays_Attention_plane (h : Heard) (t x lam a : Nat) (z : Array E) (isD : Bool)  :
    DryS (OnBytes.Attention.plane h t x lam a z isD) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_plane)

theorem _root_.Fo.stays_Attention_shV (h : Heard) (t off nl J lam j : Nat)  :
    DryS (OnBytes.Attention.shV h t off nl J lam j) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_shV)

theorem _root_.Fo.stays_Attention_xl (h : Heard) (t : Nat) (X : TenAt) (lam hd : Nat) (zc : Array E)
     :
    DryS (OnBytes.Attention.xl h t X lam hd zc) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_xl)

theorem _root_.Fo.stays_Attention_overG (h : Heard) (zg : Array E) (f : Nat → SubM Aff) (h_f : ∀ x0,
    DryS (f x0)) :
    DryS (OnBytes.Attention.overG h zg f) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_overG)

theorem _root_.Fo.stays_Attention_readDenominator (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat)
     :
    DryS (OnBytes.Attention.readDenominator h t zg lam a) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Attention_readDenominator)

theorem _root_.Fo.stays_Attention_readMaximum (h : Heard) (t : Nat) (zg : Array E) (lam a : Nat)  :
    DryS (OnBytes.Attention.readMaximum h t zg lam a) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Attention_readMaximum)

theorem _root_.Fo.stays_Attention_readIndexBit (h : Heard) (t : Nat) (zg : Array E) (lam a k : Nat) 
    :
    DryS (OnBytes.Attention.readIndexBit h t zg lam a k) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply Fo.stays_Attention_readIndexBit)

theorem _root_.Fo.stays_Attention_readHead (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam
    a : Nat)  :
    DryS (OnBytes.Attention.readHead h t X zg zc lam a) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_readHead)

theorem _root_.Fo.stays_Attention_readGroup (h : Heard) (t : Nat) (X : TenAt) (zg zc : Array E) (lam
    : Nat)  :
    DryS (OnBytes.Attention.readGroup h t X zg zc lam) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_readGroup)

theorem _root_.Fo.stays_Attention_lessPieces (start : Aff) (pw : Array PW) (f : PW → SubM Aff) (h_f
    : ∀ x0, DryS (f x0)) :
    DryS (OnBytes.Attention.lessPieces start pw f) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_lessPieces)

theorem _root_.Fo.stays_Attention_linPlanes (h : Heard) (pc : PlaneClaim)  :
    DryS (OnBytes.Attention.linPlanes h pc) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_linPlanes)

theorem _root_.Fo.stays_Attention_callKR (h : Heard) (q : Nat)  :
    DryS (OnBytes.Attention.callKR h q) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_callKR)

theorem _root_.Fo.stays_Attention_claim3 (h : Heard) (j : Joins)  :
    DryS (OnBytes.Attention.claim3 h j) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_claim3)

theorem _root_.Fo.stays_Attention_endValues (h : Heard) (k : Score) (tb : ScoreTables) (rc : Array
    E) (b : Nat) (w : PW)  :
    DryS (OnBytes.Attention.endValues h k tb rc b w) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_endValues)

theorem _root_.Fo.stays_Attention_unitKFD (h : Heard) (i : Nat) (k : Score)  :
    DryS (OnBytes.Attention.unitKFD h i k) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_unitKFD)

theorem _root_.Fo.stays_Attention_callKFD (h : Heard) (q : Nat) (c : ACall)  :
    DryS (OnBytes.Attention.callKFD h q c) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_callKFD)

theorem _root_.Fo.stays_Attention_claim4 (h : Heard) (j : Joins)  :
    DryS (OnBytes.Attention.claim4 h j) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply Fo.stays_Attention_claim4)

end OnBytes.Attention
