-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAttForms.lean.
The attention sub-proof's claims as data, made of named parts.

`fixedD_claim3` … `fixedD_claim8` (OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAtt.lean) hold the value and
the list of each claim's routine as data. The tactic that makes them opens every inner routine anew
at each call. Here each inner routine gets its own data, made once, and the claims' data are made of
these.

 * For the routines that read a table: `fixedD_weighted`, `fixedD_plane`, `fixedD_shV`, `fixedD_xl`,
   `fixedD_overG`, `fixedD_readDenominator`, `fixedD_readMaximum`, `fixedD_readIndexBit`,
   `fixedD_readHead`, `fixedD_readGroup`, `fixedD_lessPieces`. Three of them take a routine f as an
   argument: they ask for the data of f at each of its arguments.
 * For the routines that add claims: `fixedD_linPlanes`, `fixedD_callKR`, `fixedD_endValues`,
   `fixedD_unitKFD`, `fixedD_callKFD`, `fixedD_endValuesE`, `fixedD_valueProduct`.
 * `formsD_claim3` … `formsD_claim8`: the data of the six claims, made of these.

That the six have the same lists and values as `fixedD_claim3` … `fixedD_claim8` is no statement
here: OnBytes/Tie/Pv/Lookup/Test/TestFoFixedDAttForms.lean has the twelve equations as examples,
each by definition. Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean and
OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAtt.lean.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed here that a heard record is good: for the records of the checks' own runs that is
good_aHeard (OnBytes/Tie/Pv/Lookup/Ends/FoRetJoin.lean).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedDAtt

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

section
variable {t0 : ℕ}

def fixedD_weighted (n : ℕ) (w : Array E) (f : ℕ → SubM Aff) (hf : ∀ i, FixedD t0 (f i)) :
    FixedD t0 (weighted n w f) := by fixedd

def fixedD_lessPieces (start : Aff) (pw : Array PW) (f : PW → SubM Aff) [Good t0 start]
    (hf : ∀ w, FixedD t0 (f w)) : FixedD t0 (lessPieces start pw f) := by fixedd

end

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible first
  | refine fixedD_weighted _ _ _ ?_ | refine @fixedD_lessPieces _ _ _ _ ?_ ?_)

def fixedD_plane (h : Attention.Heard) (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    FixedD h.iU3 (plane h t x lam a z isD) := by fixedd

def fixedD_shV (h : Attention.Heard) (t off nl J lam j : ℕ) :
    FixedD h.iU3 (shV h t off nl J lam j) := by fixedd

def fixedD_xl (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) :
    FixedD h.iU3 (xl h t X lam hd zc) := by fixedd

def fixedD_overG {t0 : ℕ} (h : Attention.Heard) (zg : Array E) (f : ℕ → SubM Aff)
    (hf : ∀ g, FixedD t0 (f g)) : FixedD t0 (overG h zg f) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible first
  | exact fixedD_plane _ _ _ _ _ _ _ | exact fixedD_shV _ _ _ _ _ _ _ | exact fixedD_xl _ _ _ _ _ _
  | refine fixedD_overG _ _ _ ?_)

def fixedD_readDenominator (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    FixedD h.iU3 (readDenominator h t zg lam a) := by fixedd

def fixedD_readMaximum (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    FixedD h.iU3 (readMaximum h t zg lam a) := by fixedd

def fixedD_readIndexBit (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a k : ℕ) :
    FixedD h.iU3 (readIndexBit h t zg lam a k) := by fixedd

def fixedD_readHead (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    FixedD h.iU3 (readHead h t X zg zc lam a) := by fixedd

def fixedD_readGroup (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    FixedD h.iU3 (readGroup h t X zg zc lam) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible first
  | exact fixedD_readDenominator _ _ _ _ _ | exact fixedD_readMaximum _ _ _ _ _
  | exact fixedD_readIndexBit _ _ _ _ _ _ | exact fixedD_readHead _ _ _ _ _ _ _
  | exact fixedD_readGroup _ _ _ _ _ _)

def fixedD_linPlanes (h : Attention.Heard) (pc : PlaneClaim) :
    FixedD h.iU3 (linPlanes h pc) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible exact fixedD_linPlanes _ _)

def fixedD_callKR (h : Attention.Heard) (q : ℕ) : FixedD h.iU3 (callKR h q) := by fixedd

def fixedD_endValues (h : Attention.Heard) (k : Score) [Good h.iU3 k] (tb : ScoreTables)
    (rc : Array E) (b : ℕ) (w : PW) : FixedD h.iU3 (endValues h k tb rc b w) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible first
  | exact fixedD_callKR _ _ | refine @fixedD_endValues _ _ ?_ _ _ _ _)

def fixedD_unitKFD (h : Attention.Heard) (i : ℕ) (k : Score) [Good h.iU3 k] :
    FixedD h.iU3 (unitKFD h i k) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible refine @fixedD_unitKFD _ _ _ ?_)

def fixedD_callKFD (h : Attention.Heard) [Good h.iU3 h] (q : ℕ) (c : ACall) :
    FixedD h.iU3 (callKFD h q c) := by fixedd

def fixedD_endValuesE (h : Attention.Heard) [Good h.iU3 h] (b : ℕ) (w : PW) :
    FixedD h.iU3 (endValuesE h b w) := by fixedd

def fixedD_valueProduct (h : Attention.Heard) (sc : Sc3) [Good h.iU3 sc] (tS : ℕ) (pt : Array E)
    (isD : Bool) (tV : ℕ) : FixedD h.iU3 (valueProduct h sc tS pt isD tV) := by fixedd

macro_rules | `(tactic| fixedd_rule) => `(tactic| with_reducible first
  | exact fixedD_callKFD _ _ _ | exact fixedD_endValuesE _ _ _
  | refine @fixedD_valueProduct _ _ ?_ _ _ _ _)

def formsD_claim3 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedD h.iU3 (claim3 h j) := by
  fixedd_open
  fixedd

def formsD_claim4 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedD h.iU3 (claim4 h j) := by
  fixedd_open
  fixedd

def formsD_claim5 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedD h.iU3 (claim5 h j) := by
  fixedd_open
  fixedd

def formsD_claim6 (h : Attention.Heard) [Good h.iU3 h] : FixedD h.iU3 (claim6 h) := by
  fixedd_open
  fixedd

def formsD_claim7 (h : Attention.Heard) [Good h.iU3 h] : FixedD h.iU3 (claim7 h) := by
  fixedd_open
  fixedd

def formsD_claim8 (h : Attention.Heard) [Good h.iU3 h] : FixedD h.iU3 (claim8 h) := by
  fixedd_open
  fixedd

end Fo
