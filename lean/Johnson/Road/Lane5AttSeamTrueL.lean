-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5AttSeamTrueL.lean

The split at attention loses no request that is true under a policy. The twin of
Johnson/Road/Lane5AttSeamTrue.lean at the head with the cost ledger, the family of segments at which
linkOK_of_usual (Johnson/Road/Lane5AttSeam.lean) concludes. For every index i and every request x
that is true under the policy pol at a lawful table of scales s (Policy.IsTrueUnder s pol i x), at
every group g below 12, the list that is read off the library's honest trace with the ledger meets
both premises of the seam: AttR0 S Z and (callsA S fs Z).InTables.

The list is named: zsOf S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x)). It is
the list of ordsL_met (Johnson/Road/Lane5TopLMet.lean), whose second part is the proof here; that
theorem is stated for one request (all weights and all tokens 0).

Main theorems: "attOrd_of_trueL", **"seam_of_trueL"**.
Under the public premises of linkOK_of_usual and three more: s is lawful; the policy is within its
bounds; the matrix "as" has at least one part.

Limits. Which true requests there are is not said here. The library exhibits some: at every lawful
table and all weights 0, every request that has its form, with y = 0 if e = 1,024, whatever its
other tokens, under a policy with 257 ≤ θ and 257 ≤ C (Policy/Rel/TrueGuards.lean: zero_all); at the
reference table alone, requests with 1,023 counted positions at made-up weights whose 48 layers are
all zero (Policy/Rel/PosGuards.lean: real_gap, step_gap). This file's conclusion at the first
family, at the plan of a group in the record that the verifier's publicOf returns (under
"Hd.PublicAt X.P" and the test "attUsualK X", if the scale file's words are "scalesKF"):
Johnson/Road/Lane5AttSeamTrueAt.lean; at real_gap's request: seam_real_gap_file,
Johnson/Road/Lane5TrueGapAt.lean. The library's model has no cell for a lookup's counts. So in this
list the matrix bA of attention is 0, which no honest prover of the protocol would commit to. The
statements do not read it. The numbering is that of these files' dictionary. For the places of
attention's cells it is written by a reading of the verifier's texts; no theorem ties it to them
(Johnson/Road/Lane5AttDef.lean). The key vectors in "InTables" are kvA
(OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library over the verifier's records, at the
cells that addrA (Johnson/Road/Lane5AttDef.lean) places. The verifier holds no key vector. "AttR0"
is the light part: the scores and the accumulators stand in "InTables".

Not claimed: that a prover's committed cells are this list; that an honest prover's proof is
accepted (completeness of the protocol); anything on a proof, a verifier's verdict, soundness or
hiding. It is a statement on integers and tables alone.

-/
import Johnson.Road.Lane5AttSeamMet
import Johnson.Road.Lane5TopLMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

variable {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape}

/-- **The list read off the honest trace with the ledger is in order.** -/
theorem attOrd_of_trueL (h : Attention.shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (h12 : cf.S = 12) (h8 : cf.rx = 8) (hN : 0 < cf.NAs) {s : Cm.Scales} (hs : s.Lawful)
    {pol : AcceptancePolicy} (hpol : Policy.PolCond pol) {g : ℕ} (hg : g < 12)
    (hsh : (s.kap (4 * g)).sh = cf.sh.getD 0 0) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder s pol i x) :
    AttOrd S (zsOf S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x))) := by
  have P := (premiseL_of_under hs hpol ht).2
  have hT := honest_smallL hs hpol ht
  have hk : 2 * g + 1 < Cm.Seg.nSeg := by
    show 2 * g + 1 < 25
    omega
  have hH := (linkOK_seg (Policy.segPol_ne _ pol (by omega)) (P.link (2 * g + 1) hk)).holds
  have hb : ∀ c : AttSeg.Raw, c.Valid All.DA →
      |Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x))
        (Cm.Seg.ownAtt g c).place| < 2 ^ 18 :=
    fun c _ => lt_trans (hT (Cm.Seg.ownAtt g c).place.1 (Cm.Seg.ownAtt g c).place.2.1
      (Cm.Seg.ownAtt g c).place.2.2) (by norm_num)
  exact ord_of_holds hg (attSized_hid h hc h12 h8) (wide_of_shaped (shaped_of_hid h) hc hN)
    (by rw [(shaped_of_hid h).cfg]; exact hsh) (exp_of_hid h h12 h8) hb hH

/-- **Every request that is true under the policy: its honest list meets both premises of the
seam.** -/
theorem seam_of_trueL (h : Attention.shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf) (hN : 0 < cf.NAs)
    {s : Cm.Scales} (hs : s.Lawful) {pol : AcceptancePolicy} (hpol : Policy.PolCond pol) {g : ℕ}
    (hg : g < 12) (hsh : (s.kap (4 * g)).sh = cf.sh.getD 0 0) (i : Cm.Idx) (x : Instance ppref)
    (ht : Policy.IsTrueUnder s pol i x) :
    AttR0 S (zsOf S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x))) ∧
      (callsA S fs
        (zsOf S g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x)))).InTables :=
  (attOrd_iff_usual h hc hkF h12 h8 U _).1
    (attOrd_of_trueL h hc h12 h8 hN hs hpol hg hsh i x ht)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.attOrd_of_trueL
#print axioms OnBytes.Road.L5.seam_of_trueL
