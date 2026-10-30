-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinAlgorithm.lean: the committer that runs, as a deterministic algorithm that queries
the hash function; its value at every hash function; its number of queries.

The committer (Johnson/Bind/Twin.lean) is one text over a variable monad, with the hash as an
argument. Here it is taken at the library's monad of trees of queries (`ZKCP.OComp 256`) and at the
hash that asks the one oracle (`Fmt.HM Run.askB`, Run/OCompM.lean): every call of the hash is a
query at the call's string (`Fmt.oStr`), two under the number 162.
`VerifiableInference.deterministicOf` makes of that tree a deterministic algorithm of
VerifiableInference/RandomOracleModel.lean.

Main definitions.
   `outTree S files T`: the committer as a tree of queries, with all that it computes.
   `twinID S pol lay KL T`: the deterministic algorithm that returns the commitment ID as a digest.
Main theorems.
   `evaluate_twinID`: at every hash function g the algorithm's value is the ID that the committer as
      a function (`commitO`) computes over the oracle `Run.oB g`: g read on byte strings.
   `queryBound_twinID`: it makes at most 2 · `calls S` queries (Johnson/Bind/TwinCost.lean), at
      every shape, all files and every table.
   `calls_le`: `calls S` is at most 2^(a + 1) + 2 + `seedCalls S`.
Limits.
(1) Nothing on a binding of the commitment or on correctness of extraction. No theorem ties the
    committer to the programs (the C++ implementation that comes with this Lean code). Evaluations
    have compared it with runs of the programs at the small stored example's public files, on
    synthetic weights, and nowhere else; what was compared, and what was not, stands in
    Johnson/Bind/README.md ("What is run, not proved").
(2) The factor 2 is the bound for one call of the hash; only the calls under the number 162 make two
    queries.
(3) A run at the format's own hash is `commit`; that it is `commitO Fmt.oracle` is tested at a small
    shape (Johnson/Bind/TwinKnown.lean); no theorem of this file says it.

-/
import Johnson.Bind.TwinHom
import Johnson.Bind.TwinCost
import Run.OCompHom
import Run.OCompCostP
import VerifiableInference.Deterministic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open VerifiableInference

/-- The committer as a tree of queries to the one oracle. -/
def outTree (S : Shape) (files : List ByteArray) (T : Table) : ZKCP.OComp 256 Out :=
  commitW (Fmt.HM Run.askB) S files T

/-- The same, returning the commitment ID alone, as a digest. -/
def idTree (S : Shape) (files : List ByteArray) (T : Table) : ZKCP.OComp 256 Commitment :=
  outTree S files T >>= fun o => pure (Run.bytesToDig o.id)

/-- The committer as a deterministic algorithm: from the shape, the three public files and the table
to the commitment ID. -/
def twinID (S : Shape) (pol lay KL : ByteArray) (T : Table) : DeterministicAlgorithm Commitment :=
  deterministicOf (idTree S [pol, lay, KL] T)

/-- The tree, run at an oracle, gives what the committer as a function gives over that oracle. -/
theorem det_outTree (f : ZKCP.Oracle 256) (S : Shape) (files : List ByteArray) (T : Table) :
    (outTree S files T).det f = commitO (Run.oB f) S files T := by
  have h := hom_commitW (Run.detHom f) (Fmt.HM Run.askB) S files T
  rw [Run.detHom_on_HM] at h
  have e : Fmt.HM (m := Id) (Run.oB f) = Fmt.HO (Run.oB f) := by
    funext number tree index start bytes
    exact Fmt.HM_id _ _ _ _ _ _
  unfold commitO
  rw [e]
  exact h

/-- The tree tosses no coin and asks at most 2 · `calls S` queries. -/
theorem qp_outTree (S : Shape) (files : List ByteArray) (T : Table) :
    (Run.qp 256).le (outTree S files T) (calls S * 2) fun _ => True :=
  cost_commitW (Run.qp 256) (Fmt.HM Run.askB) 2 Run.qp_HM S files T

theorem qp_idTree (S : Shape) (files : List ByteArray) (T : Table) :
    (Run.qp 256).le (idTree S files T) (calls S * 2) fun _ => True :=
  (Run.qp 256).bindPure _ _ _ _ _ (qp_outTree S files T) fun _ _ => trivial

theorem det_idTree (f : ZKCP.Oracle 256) (S : Shape) (files : List ByteArray) (T : Table) :
    (idTree S files T).det f = Run.bytesToDig (commitO (Run.oB f) S files T).id := by
  unfold idTree
  rw [ZKCP.OComp.det_bind', det_outTree]
  rfl

/-- **At every hash function the algorithm's value is the ID that the committer as a function
computes over that hash function, read on byte strings.** -/
theorem evaluate_twinID (g : Hash) (S : Shape) (pol lay KL : ByteArray) (T : Table) :
    (twinID S pol lay KL T).evaluate g =
      Run.bytesToDig (commitO (Run.oB g) S [pol, lay, KL] T).id := by
  unfold twinID
  refine evaluate_deterministicOf g _ _ ?_
  rw [ZKCP.OComp.run_of_noCoin g _ (qp_idTree S [pol, lay, KL] T).1, det_idTree]

/-- **The algorithm makes at most 2 · `calls S` queries.** -/
theorem queryBound_twinID (S : Shape) (pol lay KL : ByteArray) (T : Table) :
    (twinID S pol lay KL T).toRandomized.QueryBound (calls S * 2) :=
  queryBound_deterministicOf _ _ (qp_idTree S [pol, lay, KL] T).2.1

theorem calls_le (S : Shape) : calls S ≤ 2 ^ (S.a + 1) + 2 + seedCalls S := by
  unfold calls
  rw [Nat.pow_succ]
  omega

end Bind.Twin

#print axioms Bind.Twin.det_outTree
#print axioms Bind.Twin.qp_outTree
#print axioms Bind.Twin.qp_idTree
#print axioms Bind.Twin.det_idTree
#print axioms Bind.Twin.evaluate_twinID
#print axioms Bind.Twin.queryBound_twinID
#print axioms Bind.Twin.calls_le
