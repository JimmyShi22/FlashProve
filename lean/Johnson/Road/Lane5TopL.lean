-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5TopL.lean

The premise of Lane5.lean, written a second time in list numbers and labels: the head with the cost
ledger.

The twin of Lane5Top.lean, and like it a translation, not a step towards a proof file: read its head
first; all that it says of the statements, of the numbering and of the matrices holds here. The
family of segments is "Policy.segPol s pol", the head's shape "Cm.Seg.Hd.main". The 24 links before
the head are those of Lane5Top.lean: the same statements "LayerOrd" and "AttOrd" on the same
matrices; they are carried to this family by "linkOK_pol" (Lane5LedgerLinks.lean) or shown at it
directly ("linkA_of_ordL"). The head's statement is "Hd.HeadOrdLB" (HeadL5BL.lean).

The theorems are stated for every request with r < e, judged by its policy on the costs of its
tokens. They do not say that a request has such matrices: whether it has depends on the policy, and
under a policy that no counted position can meet none with a counted position has ("no_premiseL",
Lane5LedgerGuards.lean).

Main definitions and theorems:
* "OrdsL": the 25 statements, the 12 ties and the 24 families of equations.
* "premiseL_of_ords": under the eleven public hypotheses of Lane5Top.lean, OrdsL gives the premise
  of Lane5.lean at the ledger's head.
* "under_of_ords": so, besides at a lawful table, a policy within its bounds, the matrix of an index
  and r < e, the request is true under its policy.

Not claimed: that a proof file which a verifier accepts has matrices with OrdsL; all that the
imported files do not claim. That OrdsL can be met: Lane5TopLMet.lean.
-/
import Johnson.Road.Lane5Top
import Johnson.Road.Lane5Ledger
import Johnson.Road.Lane5LedgerLinks
import Johnson.Road.HeadL5BL
import Johnson.Road.Lane5AttLinkL

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Layer (Lay matIx)

/-- **Every link is in order, and every copy is its original**, said of integer matrices that are
numbered as the verifier's lists number a sub-proof's arrays. The head with the cost ledger. -/
structure OrdsL (hL : Model.Layer.Shape) (sc : Model.Layer.Scales) (y : Lay)
    (hH : Model.Head.Shape) (L : Model.Head.HL) (nf : NormPar) (pol : AcceptancePolicy)
    (SA : ℕ → Attention.Shape) (Wz : Mat) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ)
    (ZA : ℕ → Zs) : Prop where
  layer : ∀ g < 12, LayerOrd hL sc y g (mzA y (Z (2 * g)) g) Wz x
  att : ∀ g < 12, AttOrd (SA g) (ZA g)
  qa : ∀ g < 12, ∀ r c,
    Z (2 * g + 1) (labA y g (matIx y).iQA) r c = ZA g ((SA g).cf.NAs + 3) r c
  head : Hd.HeadOrdLB hH L y nf pol Wz x (Hd.mzH hH y (Z 24))
  labels : Hd.LabelsAgree y Z

section TopL

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {tau : Array F} {L : Model.Head.HL} {sc : Model.Layer.Scales}
  {nf : NormPar} {pol : AcceptancePolicy} {SA : ℕ → Attention.Shape} {Wz : Mat} {x : Instance ppref}
  {Z : ℕ → ℕ → ℕ → ℕ → ℤ} {ZA : ℕ → Zs}

/-- **Under eleven public hypotheses OrdsL gives the premise at the ledger's head.** -/
theorem premiseL_of_ords (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (O : OrdsL hL sc y hH L nf pol SA Wz x Z ZA) :
    Premise Cm.Seg.Hd.main (Policy.segPol (scalesOf hL sc nf) pol) Wz x
      (allMx hH y SA ZA Z) := by
  refine ⟨fun k hk => ?_,
    Hd.seam_reads Cm.Seg.Hd.main hH (fun _ => atOf SA ZA) O.labels⟩
  rcases Cm.Seg.seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
  · have hg' : g < 12 := hg
    exact linkOK_congr (laws_main _ pol) hk
      (dict_D5 hy S Zd Z2 hp4 hH Cm.Seg.Hd.main (atOf SA ZA) (Z (2 * g)) hg)
      (linkOK_pol pol (by omega)
        (linkOK_layer hy S Zd Z2 hp4 Cm.Seg.Hd.main hg nf (O.layer g hg)))
  · exact linkOK_congr (laws_main _ pol) hk
      (attMx_D5 Cm.Seg.Hd.main hH y (SA g) hg (ZA g) (atOf SA ZA) (Z (2 * g + 1))
        (fun _ _ => rfl) (O.qa g hg))
      (linkA_of_ordL hg (hSA g hg) (hsh g hg) (hE g hg) (O.att g hg) pol Wz x)
  · exact linkOK_congr (laws_main _ pol) hk
      (Hd.headMx_D5 Cm.Seg.Hd.main hH h12 (atOf SA ZA) (Z 24))
      (Hd.linkOKL_24B hF hLy hy S Zd Z2 (s := scalesOf hL sc nf) O.head)

/-- **So, at a lawful table, a policy within its bounds, the matrix of an index and r < e, the
request is true under its policy.** -/
theorem under_of_ords {i : Cm.Idx} (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hs : (scalesOf hL sc nf).Lawful) (hpol : Policy.PolCond pol) (hre : x.r < x.e)
    (O : OrdsL hL sc y hH L nf pol SA i.mat x Z ZA) :
    Policy.IsTrueUnder (scalesOf hL sc nf) pol i x :=
  under_of_premise hs hpol hre (premiseL_of_ords hy S Zd Z2 hp4 h12 hF hLy hSA hsh hE O)

end TopL

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.premiseL_of_ords
#print axioms OnBytes.Road.L5.under_of_ords
