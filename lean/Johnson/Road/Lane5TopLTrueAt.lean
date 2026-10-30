-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5TopLTrueAt.lean

The bundle "OrdsL" (Johnson/Road/Lane5TopL.lean) at true requests that the library exhibits: with
counted positions, and at weights that are not all 0.

"ordsL_of_true" (Johnson/Road/Lane5TopLTrue.lean) gives "OrdsL" at the honest trace of every request
that is true under its policy. It does not say which requests are true. The one case that was
written out ("ordsL_met", Johnson/Road/Lane5TopLMet.lean) has all weights and all tokens 0 and no
counted position, so the policy's two clauses on costs are met for free there. Here two of the
library's own families of true requests are put in.

Main theorems, both under the public hypotheses of "ordsL_met":
* "ordsL_zero_all": at every lawful table, all weights 0 and a policy with "Policy.PolCond", 257 ≤
  theta and 257 ≤ C: at every request that has its form ("Head3"; y = 0 if e = 1,024), whatever its
  other tokens. Such a request may have up to 1,023 counted positions. By
  "Policy.TrueGuards.zero_all" (Policy/Rel/TrueGuards.lean).
* "ordsL_real_gap": where the table of scales is the reference table "Cm.sRef": at the policy C =
  2304, theta = 259, cap = 0, the index "Policy.PosGuards.idx0" and the request "xOne". By
  "Policy.PosGuards.real_gap" (Policy/Rel/PosGuards.lean). That file's head says of its weights "wts
  σ τ": "token t is embedded in channel σ t, channel j votes for token τ j, all layers are zero";
  "idx0" is "wts" at σ and τ constantly 0. By the same head the request "misses at position 0
  alone", "with the gap 2,048". It has 1,023 counted positions ("nb_one",
  Inst/Model/ProgramRGuards.lean).

Limits. No case is shown in this file in which a layer's weights are not 0 (one with values and an
output projection in layer 0: Johnson/Road/Lane5TrueLayerAt.lean): by the head of
Policy/Rel/PosGuards.lean its weights are made up and all 48 layers are zero, so the logits at a
position depend on that position's token alone. That the table of scales is the reference table is a
hypothesis of "ordsL_real_gap"; at the shape and scales that Johnson/Road/FormsKeysRunK.lean writes
out it is "scales_ref" (Johnson/Road/FormsKeysLaw.lean); at the record that the verifier's publicOf
returns (under "Hd.PublicAt X.P", if the scale file's words are "scalesKF"), with all the other
public hypotheses: "ordsL_real_gap_file" (Johnson/Road/Lane5ScalesRef.lean). The library's model has
no cell for a lookup's counts. So in "zTrue" the matrix b of a group of layers and in "zaTrue" the
matrix bA of attention are 0, which no honest prover of the protocol would commit to. The statements
do not read them.

Not claimed: that a prover's committed cells are these matrices; that an honest prover's proof is
accepted (completeness of the protocol); that a proof file which a verifier accepts has such
matrices. It is a statement on integers and tables alone.

-/
import Johnson.Road.Lane5TopLTrue
import Policy.Rel.PosGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Layer (Lay matIx)

section TrueAt

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {tau : Array F} {L : Model.Head.HL} {sc : Model.Layer.Scales}
  {nf : NormPar} {SA : ℕ → Attention.Shape}

/-- **At all weights 0: every request that has its form, with y = 0 if e = 1,024, whatever
its other tokens.** -/
theorem ordsL_zero_all {pol : AcceptancePolicy} (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hw : ∀ g < 12, 7200 ≤ (SA g).kAs / (SA g).cf.NAs * (SA g).cf.NAs)
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hs : (scalesOf hL sc nf).Lawful) (hpol : Policy.PolCond pol) (hθ : 257 ≤ pol.theta)
    (hC : 257 ≤ pol.C) (x : Instance ppref) (h3 : Head3 x) (hy0 : x.e = ppref.T → x.y.val = 0) :
    OrdsL hL sc y hH L nf pol SA (Cm.Idx.ofIndex ScalesSanity.iZero).mat x
      (zTrue (scalesOf hL sc nf) pol (Cm.Idx.ofIndex ScalesSanity.iZero) x)
      (zaTrue SA (scalesOf hL sc nf) pol (Cm.Idx.ofIndex ScalesSanity.iZero) x) :=
  ordsL_of_true hy S Zd Z2 hp4 h12 hF hLy hSA hw hsh hE hs hpol _ x
    (Policy.TrueGuards.zero_all hs pol hθ hC x h3 hy0)

/-- **At the reference table: weights that are not all 0, and 1,023 counted positions.** -/
theorem ordsL_real_gap (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hw : ∀ g < 12, 7200 ≤ (SA g).kAs / (SA g).cf.NAs * (SA g).cf.NAs)
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (e : scalesOf hL sc nf = Cm.sRef) :
    OrdsL hL sc y hH L nf ⟨2304, 259, 0⟩ SA Policy.PosGuards.idx0.mat ProgramRGuards.xOne
      (zTrue (scalesOf hL sc nf) ⟨2304, 259, 0⟩ Policy.PosGuards.idx0 ProgramRGuards.xOne)
      (zaTrue SA (scalesOf hL sc nf) ⟨2304, 259, 0⟩ Policy.PosGuards.idx0 ProgramRGuards.xOne) := by
  have hs : (scalesOf hL sc nf).Lawful := by
    rw [e]
    exact Cm.lawful_sRef
  have hpol : Policy.PolCond (⟨2304, 259, 0⟩ : AcceptancePolicy) := ⟨by norm_num, by norm_num, by norm_num⟩
  have ht : Policy.IsTrueUnder (scalesOf hL sc nf) ⟨2304, 259, 0⟩ Policy.PosGuards.idx0
      ProgramRGuards.xOne := by
    rw [e]
    exact Policy.PosGuards.real_gap.1
  exact ordsL_of_true hy S Zd Z2 hp4 h12 hF hLy hSA hw hsh hE hs hpol _ _ ht

end TrueAt

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.ordsL_zero_all
#print axioms OnBytes.Road.L5.ordsL_real_gap
