-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/TableFrom.lean: THE CODE SWITCH's TYPED TABLE (K2Caller.tableOf,
Johnson/Top/H0/K2Caller/Table.lean) AS A FUNCTION OF THREE LETTERS, BOUND ONCE: the planner's
sizes of a proof z, its sub-proofs sub, and the rows of the sendings R. An unfolding, of all public
files. A law file; no running text imports it.

Why. tableOf reads the three public files anew, by two roads: the planner of verify-on-bytes
(OnBytes.Model.Verify.planned) and Johnson.G.sendRowsOf. Whoever brings «z is the written value» and
«R are the written rows» needs the table as a term in z, sub and R alone, so that what is left is a
closed comparison.

  tableFrom z sub R   the rows: Table.lean's placesOf's last expression, with its rows taken.
  tableOf_from        Verify.planned pol KL (some lay) = .ok p · sendRowsOf pol lay KL = .ok R ⟹
                      tableOf pol lay KL = .ok (tableFrom p.chains.made.sized.proof
                        (subproofsWith p.X p.chains.made.sized.proof.request.link) R).
  tableOf_iff         tableOf returns just where both return; then its value is that term.
Limits. NOTHING SAYS AT WHICH FILES THE TWO RETURN, OR WHAT. Nothing on soundness.

-/
import Johnson.Top.H0.Opts.SpotsOfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Plan

/-- **The typed table, of the three letters.** -/
def tableFrom (z : ProofSized) (sub : Subproofs) (R : List Johnson.G.SendRow) : List SwRow :=
  ((framesOf z sub).filter fun n => n.l != 0).map fun n =>
    rowOf z (Johnson.G.linkList R (n.l - 1))
      (((Johnson.G.linkRows R n.l).head?.map (·.sampled)).getD [])
      (keptAt (tagsOf z (n.l - 1) ((reqGroups z.request).toList.getD (n.l - 1) default)
        (z.request.link.getD (n.l - 1) default)) n.group) n

/-- **Where the two readings return.** -/
theorem tableOf_from {pol lay KL : ByteArray} {p : OnBytes.Model.Verify.Planned}
    {R : List Johnson.G.SendRow} (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p)
    (hR : Johnson.G.sendRowsOf pol lay KL = .ok R) :
    tableOf pol lay KL = .ok (tableFrom p.chains.made.sized.proof
      (OnBytes.Model.Verify.subproofsWith p.X p.chains.made.sized.proof.request.link) R) := by
  unfold tableOf placesOf tableFrom
  rw [hp, hR]
  simp only [bind, Except.bind, pure, Except.pure, List.map_map]
  rfl

/-- It returns just where both return. -/
theorem tableOf_iff {pol lay KL : ByteArray} {t : List SwRow} :
    tableOf pol lay KL = .ok t ↔ ∃ p R, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p ∧
      Johnson.G.sendRowsOf pol lay KL = .ok R ∧ t = tableFrom p.chains.made.sized.proof
        (OnBytes.Model.Verify.subproofsWith p.X p.chains.made.sized.proof.request.link) R := by
  constructor
  · intro h
    have h' := h
    unfold tableOf at h'
    obtain ⟨x, hx, -⟩ := exc_bind h'
    unfold placesOf at hx
    obtain ⟨p, hp, hx⟩ := exc_bind hx
    obtain ⟨R, hR, -⟩ := exc_bind hx
    exact ⟨p, R, hp, hR, Except.ok.inj (h.symm.trans (tableOf_from hp hR))⟩
  · rintro ⟨p, R, hp, hR, rfl⟩
    exact tableOf_from hp hR

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.tableOf_from
#print axioms VerifiableInference.Desc.First.K2Caller.tableOf_iff
