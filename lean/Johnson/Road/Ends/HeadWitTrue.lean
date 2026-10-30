-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadWitTrue.lean: for every request that is true under its policy, at every index,
the two premises with content of the seam before the output head's lookup hold together, at named
matrices: the head's meaning without its clause on keys (HeadR0, Johnson/Road/Lane5SplitH.lean) and
the clause ForInH (Johnson/Road/Ends/HeadForIn.lean).

One definition and one theorem, at the public part X that the verifier's function publicOf returns.
  mhTrue X pl i x: the matrices behind the head's sub-proof that these files' dictionary makes of
    the library's honest trace with the ledger (Hd.mzH X.hS X.y of zTrue … 24,
    Johnson/Road/Lane5TopLTrue.lean; Hd.zOf, Johnson/Road/HeadZ.lean; Hd.mzH,
    Johnson/Road/HeadDict.lean), at the table of scales of X's own scale words. The dictionary's
    labels are those of the verifier's plans; no function of the verifier's makes these matrices.
  headForIn_of_true: publicOf has returned X; the test headPubB says true; the scale file's words
    are scalesKF (Johnson/Road/FormsKeysRunK.lean); the policy is within its bounds; x is true under
    the policy at the index i: then HeadR0 and ForInH hold at mhTrue X pl i x and Wz := i.mat.
By ordsL_of_true (Johnson/Road/Lane5TopLTrue.lean) and headOrd_iff_forIn_test
(Johnson/Road/Ends/HeadWit.lean).

Limits: the matrices are made of the library's honest trace: that a prover's committed cells are
these is not said. Which requests are true is not said here. At every lawful table and all weights
0: Policy.TrueGuards.zero_all. At weights that are not all 0 a true request is known at the
reference table Cm.sRef alone; that X's table is that table is scales_at_ref
(Johnson/Road/Lane5ScalesRef.lean), and true_real_gap_file (Johnson/Road/Lane5TrueGapAt.lean) names
such a request at X's table; neither is put in here. In those requests too all 48 layers' weights
are 0; at an index whose layer 0 is not zero: headForIn_layer_file,
Johnson/Road/Lane5TrueLayerAt.lean. Nothing on a form or a protocol. The reference sizes.

-/
import Johnson.Road.Lane5TopLTrue
import Johnson.Road.Ends.HeadWit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model.Verify (Public publicOf borderOf layerShape)
open Inst.Model (Mat ppref AcceptancePolicy Instance)

/-- The matrices behind the head's sub-proof, of the library's honest trace with the ledger. -/
noncomputable def mhTrue (X : Public) (pl : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) : Mats ℤ :=
  mzH X.hS X.y (L5.zTrue (scalesOf (layerShape X.P) X.layers.sc (npOf X.hS)) pl i x 24)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **Every true request has matrices that meet both premises together.** -/
theorem headForIn_of_true (h : publicOf pol KL lay = .ok X) (t : headPubB X = true)
    (hW : Model.fileWords KL = scalesKF.toArray) {pl : AcceptancePolicy} (hpol : Policy.PolCond pl)
    {R0 : Model.Head.Run} (e1 : R0.h = X.hS) (e2 : R0.L = X.HLy) (i : Cm.Idx)
    (x : Instance ppref)
    (ht : Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (npOf X.hS)) pl i x) :
    L5.HeadR0 X.hS X.HLy X.y (npOf X.hS) pl x (mhTrue X pl i x) ∧
      ForInH (runReq R0 x)
        (callsH (runReq R0 x) (borderOf X.y) X.layers.wsLay (mhTrue X pl i x) i.mat).K := by
  have A : PublicAt X.P := by
    have t' := t
    simp only [headPubB, Bool.and_eq_true, decide_eq_true_eq] at t'
    exact t'.1.1.1.1.1
  have B := public_of_publicOf h A
  have O := L5.ordsL_of_true B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head
    (fun _ hg => (L5.att_of_at' h A hg).1) (fun _ hg => (L5.att_of_at' h A hg).2.2.2)
    (fun _ hg => (L5.att_of_at' h A hg).2.1) (fun _ hg => (L5.att_of_at' h A hg).2.2.1)
    (L5.lawful_of_at h A hW) hpol i x ht
  exact (headOrd_iff_forIn_test h t e1 e2 pl x i.mat _).1 O.head

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.headForIn_of_true
