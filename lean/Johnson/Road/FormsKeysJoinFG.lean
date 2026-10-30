-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysJoinFG.lean: the weight claims of a panel of the verifier's own list, in the
library's words.

Three files are joined here. Johnson/Road/FormsKeysFold.lean says which claims of the verifier's
list of weight claims belong to a panel of its list of panels: for a panel b with the number v0, the
predicates AtA, AtQK and AtR name the segment g of which b is the panel, and say that the claims
from number v0 on are those that claimsA or claimsT returns for g. Johnson/Road/FormsKeysAim.lean
and, for the segment QK, Johnson/Road/FormsKeysQKF.lean say what a claim of each of ten named lists
claims: the sum that it speaks of in the matrix W of weights (claimVal) is the library's value of a
tensor claim of a panel (Pan.TnRow, Pan.TnPan), at the weights that the library's layout reads in
the same W.

What is compared with what: the verifier's claim number v0 + i, for a panel of the verifier's own
list, against the library's TnRow or TnPan of the panel that has the segment's name.

Main definitions: panOf, panR: the library's panel for a segment's name.
Main theorems.
 - list_acc, list_routed: the nine statements of FormsKeysAim.lean as two, with the segment's name
   as a variable.
 - rows_of_AtA: from AtA: claim number v0 + i is there, for each row i of b, and claims TnRow of the
   panel panOf g.name at row i.
 - rows_of_AtQK: from AtQK: the same with the library's panel QK.
 - claim_of_AtR: from AtR: claim number v0 is there and claims TnPan of the panel panR g.name lm.
 - claims_in_library: all three on the verifier's own two lists.

The hypotheses are those of the three files: the record AimFits; for a panel of a family, the tie of
the call that holds the family's segment (CallTie, for that family alone); for QK those of
claims_QK; and, for claims_in_library, that the two lists are made from one environment and that
both functions return. claims_in_library asks no tie outright: what it says of a panel's claims
stands behind the tie of that panel's own call. What shows that each hypothesis can be met is said
in the heads of these files; no theorem shows that all can be met together. The ties of several
families ask one point z of the lookup to serve several calls: Johnson/Road/FormsKeysLookT.lean
shows such a point, where no call of the verifier is longer than the library's.

What is not claimed. That the hidden value under a claim's slot is claimVal is not shown. A panel is
a record without a name: see the head of FormsKeysFold.lean on what "b is the panel of g" says. See
also Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysAim
import Johnson.Road.FormsKeysQKF

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Reading WsShape WsClaim Seg CallD)
open OnBytes.Model.Layer (ClaimEnv SBlk Panels PanelEnv isAcc callsAC panelsA panelsT)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim Fam Pan Rd layerR call aC zc)

variable {K : Type} [Field K]

/-- The library's panel for a segment of the lookup's join whose key holds a product with a weight
matrix, by the segment's name: G, U, V, O, D; LR for every other name. -/
def panOf (sn : String) : Pan :=
  if sn == "G" then .G else if sn == "U" then .U else if sn == "V" then .V
  else if sn == "O" then .O else if sn == "D" then .D else .LR

/-- The library's panel for the routed product of a segment on the layer with routed experts number
lm, by the segment's name: G, U; D for every other name. -/
def panR (sn : String) (lm : ℕ) : Pan :=
  if sn == "G" then .Gr lm else if sn == "U" then .Ur lm else .Dr lm

/-- The family of the panel of a name is one of the six with a matrix product in the lookup's
join. -/
theorem panOf_fam (sn : String) :
    (panOf sn).fam ∈ [Fam.G, Fam.U, Fam.V, Fam.O, Fam.D, Fam.LR] := by
  unfold panOf
  split_ifs <;> simp [Pan.fam]

/-- So is the family of the panel of a routed product. -/
theorem panR_fam (sn : String) (lm : ℕ) :
    (panR sn lm).fam ∈ [Fam.G, Fam.U, Fam.V, Fam.O, Fam.D, Fam.LR] := by
  unfold panR
  split_ifs <;> simp [Pan.fam]

section Join

variable {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {D : Dim} {lk L0 : ℕ} {z ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)
  (W : Wm K) (r : Rd K) (tb : Tables) (zh : ℕ → K)

include A

/-- Member number i of the list of claims that claimsA returns for one of its six segments claims
TnRow of the segment's panel at row i. -/
theorem list_acc {sn : String} (hs : isAcc sn = true) (T : CallTie ρ c h D z (panOf sn).fam)
    {l : List WsClaim} (hl : c.claimsA sn = some l) {i : ℕ} {x : WsClaim} (hi : l[i]? = some x) :
    claimVal ρ c.wsLay W x =
      (panOf sn).TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  rcases (isAcc_iff sn).mp hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact list_G A W r tb zh T hl hi
  · exact list_U A W r tb zh T hl hi
  · exact list_V A W r tb zh T hl hi
  · exact list_O A W r tb zh T hl hi
  · exact list_D A W r tb zh T hl hi
  · exact list_LR A W r tb zh T hl hi

/-- Member number lm of the list of claims that claimsT returns for the segment G, U or D claims
TnPan of the panel of the segment's routed product on the layer with routed experts number lm. -/
theorem list_routed {sn : String} (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") {lm : ℕ}
    (T : CallTie ρ c h D z (panR sn lm).fam) {l : List WsClaim} (hl : c.claimsT sn = some l)
    {x : WsClaim} (hi : l[lm]? = some x) :
    claimVal ρ c.wsLay W x =
      (panR sn lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  rcases hs with rfl | rfl | rfl
  · exact list_Gr A W r tb zh T hl hi
  · exact list_Ur A W r tb zh T hl hi
  · exact list_Dr A W r tb zh T hl hi

/-- If b, with the number v0, is the panel of segment g of call q of the lookup's join (AtA), then
for each row i of b the list has a claim number v0 + i, and it claims TnRow of the library's panel
of the name of g at row i. -/
theorem rows_of_AtA {p : PanelEnv} {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg}
    (T : CallTie ρ c h D z (panOf g.name).fam) (H : AtA p c cl b v0 q g) :
    ∀ i, i < b.ni → ∃ x, cl[v0 + i]? = some x ∧ claimVal ρ c.wsLay W x =
      (panOf g.name).TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  obtain ⟨st, l, hacc, -, -, hl, hlen, hat⟩ := H
  intro i hi
  have hi' : i < l.length := by omega
  have e : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
  exact ⟨l[i], (hat i hi).trans e, list_acc A W r tb zh hacc T hl e⟩

/-- If b, with the number v0, is the panel of the routed product of segment g on the layer with
routed experts number lm (AtR), then the list has a claim number v0, and it claims TnPan of the
library's panel of the name of g and of lm. -/
theorem claim_of_AtR {p : PanelEnv} {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg} {lm : ℕ}
    (T : CallTie ρ c h D z (panR g.name lm).fam) (H : AtR p c cl b v0 q g lm) :
    ∃ x, cl[v0]? = some x ∧ claimVal ρ c.wsLay W x =
      (panR g.name lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  obtain ⟨st, st', l, -, hname, hlm, -, -, -, hl, hlen, hat⟩ := H
  have hlm' : lm < l.length := by omega
  have e : l[lm]? = some l[lm] := List.getElem?_eq_getElem hlm'
  exact ⟨l[lm], hat.trans e, list_routed A W r tb zh hname T hl e⟩

/-- If b, with the number v0, is the panel of a segment named QK (AtQK), then for each row i of b
the list has a claim number v0 + i, and it claims TnRow of the library's panel QK at row i. The
hypotheses beside AimFits are those of claims_QK in Johnson/Road/FormsKeysQKF.lean. -/
theorem rows_of_AtQK {q : ℕ} {cd : CallD} {sg : Seg} (F : QKFits c D q cd sg)
    (hrt : c.rt.size = D.lT) (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb L0 lam)
    (hz : ∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q #[]) j = zc D z (call .QK) j)
    (hzh : ∀ j < D.lT, zh j = pt ρ c.rt j) {p : PanelEnv} {cl : List WsClaim} {b : SBlk}
    {v0 q' : ℕ} {g : Seg} (H : AtQK p c cl b v0 q' g) :
    ∀ i, i < b.ni → ∃ x, cl[v0 + i]? = some x ∧ claimVal ρ c.wsLay W x =
      Pan.QK.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  obtain ⟨st, st', l, hname, -, -, -, hl, hlen, hat⟩ := H
  rw [hname] at hl
  obtain ⟨-, hall⟩ := claims_QK ρ A.claim F hrt R hz hzh r W hl
  intro i hi
  have hi' : i < l.length := by omega
  exact ⟨l[i], (hat i hi).trans (List.getElem?_eq_getElem hi'), hall i hi'⟩

/-- On the verifier's own two lists. Asked beside AimFits: the lists are made from one environment
and for the same calls, and both functions return. Then every panel b of the list that has a number
v0 is of one of three sorts. Without the selector: b is the panel of a segment g of a call of the
lookup's join, and, if the call of the family of g is tied to the library's (CallTie, for that
family alone), its claims, number v0 + i for row i, claim TnRow of the library's panel of the name
of g; or b is the panel of a segment named QK, and, under the hypotheses of claims_QK, its claims
claim TnRow of the library's panel QK. With the selector: b is the panel of the routed product of a
segment g on a layer number lm, and, if the call of the family of g is tied, its claim, number v0,
claims TnPan of the library's panel of the name of g and of lm. So what is said of one panel asks
the tie of that panel's own call alone. -/
theorem claims_in_library (p : PanelEnv) (hv : p.v = c.v) (TS : List ℕ) {pans : Panels}
    {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans)
    (hc : c.weightClaims TS = some cl) :
    ∀ b ∈ pans.bl.toList, ∀ v0, b.v0 = some v0 →
      (b.tri = false →
        (∃ q ∈ callsAC p.v.y, ∃ g ∈ (p.v.y.calls.getD q default).segs, AtA p c cl b v0 q g ∧
          (CallTie ρ c h D z (panOf g.name).fam →
            ∀ i, i < b.ni → ∃ x, cl[v0 + i]? = some x ∧ claimVal ρ c.wsLay W x =
              (panOf g.name).TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i)) ∨
        (∃ q ∈ TS, ∃ g ∈ (p.v.y.calls.getD q default).segs, AtQK p c cl b v0 q g ∧
          ∀ (q0 : ℕ) (cd : CallD) (sg : Seg), QKFits c D q0 cd sg → c.rt.size = D.lT →
            (∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb L0 lam) →
            (∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q0 #[]) j = zc D z (call .QK) j) →
            (∀ j < D.lT, zh j = pt ρ c.rt j) →
            ∀ i, i < b.ni → ∃ x, cl[v0 + i]? = some x ∧ claimVal ρ c.wsLay W x =
              Pan.QK.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i)) ∧
      (b.tri = true →
        ∃ q ∈ TS, ∃ g ∈ (p.v.y.calls.getD q default).segs, ∃ lm, AtR p c cl b v0 q g lm ∧
          (CallTie ρ c h D z (panR g.name lm).fam →
            ∃ x, cl[v0]? = some x ∧ claimVal ρ c.wsLay W x =
              (panR g.name lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ)) := by
  intro b hb v0 h0
  obtain ⟨k1, k2⟩ := (claims_of_panels p c hv TS hp hc).2 b hb v0 h0
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · rcases k1 ht with ⟨q1, hq, g, hg, H⟩ | ⟨q1, hq, g, hg, H⟩
    · exact Or.inl ⟨q1, hq, g, hg, H, fun T => rows_of_AtA A W r tb zh T H⟩
    · exact Or.inr ⟨q1, hq, g, hg, H, fun _ _ _ F hrt R hz hzh =>
        rows_of_AtQK A W r tb zh F hrt R hz hzh H⟩
  · obtain ⟨q1, hq, g, hg, lm, H⟩ := k2 ht
    exact ⟨q1, hq, g, hg, lm, H, fun T => claim_of_AtR A W r tb zh T H⟩

end Join

#print axioms list_acc
#print axioms list_routed
#print axioms rows_of_AtA
#print axioms claim_of_AtR
#print axioms rows_of_AtQK
#print axioms claims_in_library

end OnBytes.Road
