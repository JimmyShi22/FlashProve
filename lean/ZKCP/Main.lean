-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Main.lean: the form of a top-level theorem for a construction that is defined for every λ.

The form is one top-level statement that names the relation and the protocol and gives three error
bounds, for completeness, index binding and index hiding (`HasIndexPrivacy`, ZKCP/Defs.lean).

Everything marked PLACEHOLDER is a section variable, not an axiom: this file asserts nothing about a
construction. For a construction that is defined for every λ each placeholder is a closed def, and
the last lines read

      theorem main_with (lam : ℕ) :
          IsZKCPArgWith R_model (Construction lam) (Ext lam) (Sim lam) (alpha lam) (eps lam)
            (zeta lam) := ...
      theorem main (lam : ℕ) :
          IsZKCPArg R_model (Construction lam) (alpha lam) (eps lam) (zeta lam) :=
            (main_with lam).toIsZKCPArg
      #print axioms main     -- expected: propext, Classical.choice, Quot.sound and nothing else

with no hypothesis: lam is a parameter. To trust main a reader checks R_model, Construction, the
three bounds and ZKCP/Defs.lean; Lean checks the rest. ZKCP/HashToy.lean (`hash_main_with`,
`hash_main`) proves two theorems of this form, with one more parameter M.

The compiler theorem `mainBatchKEGrWithBOf` (Compile/Batch/PubProgMainBGr.lean), generic in the
protocols and under its hypotheses, is proved for every λ (`Gen.IsZKCPArgWith`, ZKCP/Gen.lean).
In the statements of VerifiableInference/ λ is the numeral 256 (`Digest`,
VerifiableInference/RandomOracleModel.lean).
-/
import ZKCP.Basic

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

/-- The algorithm draws no coin (for the companion "V is deterministic"; in ZKCP/Defs.lean V may
draw coins). -/
def OComp.DrawsNoCoin {lam : ℕ} {α : Type} : OComp lam α → Prop
  | .pure _ => True
  | .query _ k => ∀ r, (k r).DrawsNoCoin
  | .sample _ _ => False

section Main

/- PLACEHOLDER: the types of indices (model weights), instances (request and reply), witnesses and
public parameters (architecture and sizes). -/
variable {Index Instance Witness PubParams : Type}
/- PLACEHOLDER: the types of keys and proofs; they may depend on λ (a key contains λ-bit
digests). -/
variable {IVK ISK Proof : ℕ → Type}
/- PLACEHOLDER: the indexed relation, which models the target AI computation. -/
variable (R_model : IndexedRelation Index Instance Witness PubParams)
/- PLACEHOLDER: the protocol, the hash-based construction (C, P, V), for every λ. -/
variable (Construction : (lam : ℕ) → Arg lam Index Instance Witness (IVK lam) (ISK lam) (Proof lam))
/- PLACEHOLDER: the extractor and the simulator, as closed terms that a reader can inspect. -/
variable (Ext : (lam : ℕ) → Extractor lam Index Instance Witness (IVK lam) (Proof lam))
variable (Sim : (lam : ℕ) → Simulator lam PubParams (IVK lam) Instance (Proof lam))
/- PLACEHOLDER: the three error bounds, in λ, in (λ, t_C, t_P) and in (λ, t_V, N), as closed
formulas. -/
variable (alpha : ℕ → ℝ≥0∞) (eps zeta : ℕ → ℕ → ℕ → ℝ≥0∞)

/-- The statement in the form IsZKCPArg, for every λ. -/
def MainStatement : Prop :=
  ∀ lam : ℕ, IsZKCPArg R_model (Construction lam) (alpha lam) (eps lam) (zeta lam)

/-- The statement with extractor and simulator named and privacy in the stronger form, for every
λ. -/
def MainStatementWith : Prop :=
  ∀ lam : ℕ,
    IsZKCPArgWith R_model (Construction lam) (Ext lam) (Sim lam) (alpha lam) (eps lam) (zeta lam)

theorem MainStatementWith.toMainStatement
    (h : MainStatementWith R_model Construction Ext Sim alpha eps zeta) :
    MainStatement R_model Construction alpha eps zeta :=
  fun lam => (h lam).toIsZKCPArg

/-- Companions of the top theorem: facts outside the definition without which one of its clauses
would say less than it seems to. (The three bounds must also be evaluated at the target parameters:
a bound that is 1 or more makes its clause trivially true.) -/
structure MainCompanions : Prop where
  /-- else (if there is at least one ivk, one instance and one proof) no extractor exists and
  ZKCP/Defs.lean, `HasIndexBinding` is false for a trivial reason, even for a verifier that rejects
  everything -/
  witnessNonempty : Nonempty Witness
  /-- then V has no coins. In ZKCP/Defs.lean V may draw coins: they count in every probability of
  completeness and binding, and in `badKeys` in the inner one; for a V without coins
  nothing changes -/
  verifierDeterministic : ∀ lam ivk x π, ((Construction lam).V ivk x π).DrawsNoCoin
  /-- else pp reveals the index and privacy says nothing -/
  ppNotInjective : ¬ Function.Injective R_model.pp

end Main
end ZKCP
