-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/OverOneNGen.lean: the condition `FacOK ag A`: at every query, committer, prover and verifier of
a scheme A of ZKCP/Gen.lean go on with the same program after any two answers that the relation ag
relates (`OComp.FactorsBy ag`, Rom/OverOneN.lean). Generic in the scheme and in the family of
oracles.

Notation:
  `ag`: for each oracle o and query q, a relation on two answers, of type
      `∀ o, S.Dom o → S.Rng o → S.Rng o → Prop`
  `Gen.Arg` (ZKCP/Gen.lean): ARG = (C, P, V) over the family S; `A.C i`, `A.P k b`, `A.V v x π`: its
      three algorithms at an index i, at a key k and a batch b, at a key v and one pair (x, π)
  `Gen.Slots Pf b` (ZKCP/Gen.lean): one entry for each slot of the batch b: a list of the same
      length
  `CostBoundAt w t` (Rom/OverOneN.lean): on every path, whatever the answers and the coins, the
      weights w o q of the queries add up to at most t

Limits: nothing on a step to one hash function. For a whole scheme, this library does not have the
form of that step in which only marked hash blocks are queried (the second exit), what carries over
under it, or bounds on its queries to the hash function (for one algorithm: `OComp.overOneN`,
Rom/OverOneN.lean).
-/
import Rom.OverOneN
import Rom.ExitBind
import ZKCP.GenSameRun
import ZKCP.SpecialAny

set_option autoImplicit false

open scoped ENNReal

namespace Rom

open ZKCP

variable {S : OSpec} {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-! ## The condition; post-processing -/

/-- The three algorithms read an answer only up to a relation ag on answers. No query encoding
(`OracleCoding`) occurs: so the condition can be proved once, for a relation that is stated on the answers
of a particular family. -/
structure FacOK (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop) (A : Gen.Arg S I X W IVK ISK Pf) :
    Prop where
  C : ∀ i, (A.C i).FactorsBy ag
  P : ∀ k b, (A.P k b).FactorsBy ag
  V : ∀ v x π, (A.V v x π).FactorsBy ag

/-- An algorithm followed by a function of its output keeps the condition. -/
theorem OComp.FactorsBy.map {α β : Type} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}
    {c : OComp S α} (h : c.FactorsBy ag) (f : α → β) :
    (c.bind fun a => .pure (f a)).FactorsBy ag :=
  h.bind fun _ => trivial

/-- An algorithm followed by a function of its output keeps its cost bound. -/
theorem OComp.CostBoundAt.map {α β : Type} {w : (o : S.ι) → S.Dom o → ℕ} {c : OComp S α} {t : ℕ}
    (h : c.CostBoundAt w t) (f : α → β) :
    (c.bind fun a => .pure (f a)).CostBoundAt w t :=
  OComp.CostBoundAt.bind (g := fun a => (.pure (f a) : OComp S β))
    (t := 0) (fun a => OComp.CostBoundAt.pure (f a) 0) h

section Wrap
variable {IVK' ISK' Pf' : Type} {ag ag' : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}

/-- If every pair of answers that ag' relates is related by ag, the condition for ag gives the
condition for ag'. -/
theorem FacOK.mono {A : Gen.Arg S I X W IVK ISK Pf}
    (hag : ∀ o q r r', ag' o q r r' → ag o q r r') (h : FacOK ag A) : FacOK ag' A :=
  ⟨fun i => (h.C i).mono hag, fun k b => (h.P k b).mono hag, fun v x π => (h.V v x π).mono hag⟩

variable (A : Gen.Arg S I X W IVK ISK Pf) (fC : IVK × ISK → IVK' × ISK') (fK : ISK' → ISK)
  (fP : (k : ISK') → (b : List (X × W)) → Gen.Slots Pf b → Gen.Slots Pf' b)
  (fV : IVK' → X → Pf' → IVK × X × Pf)

/-- The condition carries over from A to any scheme A' whose C is A's followed by a function of the
keys, whose P is A's on some key followed by a function of the proofs, and whose V returns a bit
without a query or a coin, or is A's on other inputs. -/
theorem FacOK.of_shape {A : Gen.Arg S I X W IVK ISK Pf} (h : FacOK ag A)
    {A' : Gen.Arg S I X W IVK' ISK' Pf'}
    (hC : ∀ i, ∃ f : IVK × ISK → IVK' × ISK', A'.C i = (A.C i).bind fun key => .pure (f key))
    (hP : ∀ k b, ∃ (k0 : ISK) (f : Gen.Slots Pf b → Gen.Slots Pf' b),
      A'.P k b = (A.P k0 b).bind fun πs => .pure (f πs))
    (hV : ∀ v x π, (∃ c, A'.V v x π = .pure c) ∨ ∃ v0 x0 π0, A'.V v x π = A.V v0 x0 π0) :
    FacOK ag A' where
  C i := by
    obtain ⟨f, e⟩ := hC i
    rw [e]
    exact (h.C i).map f
  P k b := by
    obtain ⟨k0, f, e⟩ := hP k b
    rw [e]
    exact (h.P k0 b).map f
  V v x π := by
    rcases hV v x π with ⟨c, e⟩ | ⟨v0, x0, π0, e⟩
    · rw [e]
      trivial
    · rw [e]
      exact h.V v0 x0 π0

variable {w : (o : S.ι) → S.Dom o → ℕ}



end Wrap

end Rom
