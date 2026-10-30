-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/EndsAtTok.lean: CONDITIONAL.

What is here. The hypothesis hE of TokAtX.lean's `tokAll_x`: in a world that has the true entries
and holds, under the slots of a second token sumcheck's end values, the values that the honest side
computes for them at a token point (`endsOn`, Johnson/Desc/K4/Honest/Sides.lean), EACH OF THE
VERIFIER's CLAIMS ON THESE END VALUES IS WORTH 0. A claim is a slot less a form in the reads at the
point (`termsForms`, OnBytes/Desc/First/K4/Claims.lean). The honest side values the same list of
claims, made at another hearing (`sides_ends`, Johnson/Road/K4/C/TermsField.lean), with 0 under
every slot, and takes the negative: that is the form's honest value, which is the form's value at
the true entries (`valAff_true`, Johnson/Road/K4/C/ValAff.lean); the form names no slot (the
library's `sl_rowR`, `sl_shA`, Johnson/Road/K4/Slots/Readers.lean).

  `value_noslot`   a form that names no slot is worth the same in two worlds with one entry function
  `terms_block`, `terms_pair`   two lists of claims made at two hearings, member by member: one
     form, two slots
  `claims_zero`   **each claim is worth 0**

Limits. At the reading `Reading.gl`. HYPOTHESES, as in C/ValAff.lean and C/Below.lean: the honest
reads at the point, the laying of the tables and the verifier's list of tables return, at lists of
points of which the token's two are a part; the sub-proof's list of matrices is the plan's;
`CellsAre`; the environment's list of places is the one that the laying returns and has the family
"b-bits-0". On the world: hW (its entries) and hsl (what it holds under these slots): a world can be
made so. The point is a letter: an end point or a token's corner. Of the hypotheses together no
sample is known at the full size.

No property is claimed.
-/
import Johnson.Road.K4.C.TermsEnds
import Johnson.Road.K4.C.Below
import Johnson.Road.K4.C.TermsAtOf
import Johnson.Road.K4.C.TermsField
import Johnson.Road.K4.Slots.Readers
import Johnson.Road.FormsKeysPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE negE)
open OnBytes.Model (Reading Aff World HFun HTailF2 Tsc)
open OnBytes.Model.Layer (Env Heard TableAsk TableAt layTables tableAsks funsOf)
open OnBytes.Road (Mats sentAt list_mapM_some)
open OnBytes.Road.K4 (entryOf)
open OnBytes.Road.K4.C (valAff_true terms_off endsOn_at sides_fields sides_ends CellsAre PtsPart
  tokPts)
open OnBytes.Desc.First.K4 (termsForms)
open OnBytes.Desc.First.K4.Slots (SlotsIn sl_rowR sl_shA)
open OnBytes.Desc.First.K4.Honest

/-- **A form that names no slot is worth the same in two worlds with one entry function.** -/
theorem value_noslot {a : Aff} (h : SlotsIn (fun _ => False) a) {W W' : World Cb.Gl.E}
    (he : W.entry = W'.entry) : a.value Reading.gl W = a.value Reading.gl W' := by
  have e0 : a.slots.toList = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => h x hx
  unfold Aff.value
  rw [e0]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  unfold OnBytes.Model.Ent.value
  rw [he]

/-- One stretch of the two lists: n claims, made of one function for the forms and two first slots.
-/
theorem terms_block {n : ℕ} (g : ℕ → Option Aff) (s s' : ℕ) {r r' : List Aff}
    (h : (List.range n).mapM (fun i => (g i).map fun x => Aff.slot (s + i) - x) = some r)
    (h' : (List.range n).mapM (fun i => (g i).map fun x => Aff.slot (s' + i) - x) = some r') :
    r.length = n ∧ r'.length = n ∧ ∀ k, k < n → ∃ x, g k = some x ∧
      r[k]? = some (Aff.slot (s + k) - x) ∧ r'[k]? = some (Aff.slot (s' + k) - x) := by
  obtain ⟨l1, i1⟩ := list_mapM_some _ _ _ h
  obtain ⟨l2, i2⟩ := list_mapM_some _ _ _ h'
  refine ⟨by rw [l1, List.length_range], by rw [l2, List.length_range], fun k hk => ?_⟩
  obtain ⟨b1, q1, e1⟩ := i1 k k (List.getElem?_range hk)
  obtain ⟨b2, q2, e2⟩ := i2 k k (List.getElem?_range hk)
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp e1
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp e2
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  exact ⟨x, hx, q1, q2⟩

/-- **Two lists of claims made at two hearings, member by member**: one form, which names no slot;
the slots are the two first slots plus the member's number. -/
theorem terms_pair {v : Env} {H H' : Heard} {T T' : Tsc} (hT : H.tT = some T)
    (hT' : H'.tT = some T') {l l' : List Aff} (h : termsForms v H = some l)
    (h' : termsForms v H' = some l') :
    ∀ e a', l'[e]? = some a' → ∃ x, SlotsIn (fun _ => False) x ∧
      a' = Aff.slot (T'.sEnd + e) - x ∧ l[e]? = some (Aff.slot (T.sEnd + e) - x) := by
  unfold termsForms at h h'
  obtain ⟨T0, e0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : T = T0 := Option.some.inj (hT.symm.trans e0)
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : a ++ b ++ c = l := Option.some.inj h
  obtain ⟨T1, e1, h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain rfl : T' = T1 := Option.some.inj (hT'.symm.trans e1)
  obtain ⟨a', ha', h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain ⟨b', hb', h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain ⟨c', hc', h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain rfl : a' ++ b' ++ c' = l' := Option.some.inj h'
  obtain ⟨la, la', A⟩ := terms_block (fun i => v.rowR "rt" i) T.sEnd T'.sEnd ha ha'
  obtain ⟨lb, lb', B⟩ := terms_block (fun lm => v.shA "sc" "rt" lm 0)
    (T.sEnd + v.y.NN * v.y.Lam) (T'.sEnd + v.y.NN * v.y.Lam) hb hb'
  obtain ⟨lc, lc', C⟩ := terms_block
    (fun x => v.shA "sel" "rt" (x / v.y.h.NE) (x % v.y.h.NE))
    (T.sEnd + v.y.NN * v.y.Lam + v.y.LamM) (T'.sEnd + v.y.NN * v.y.Lam + v.y.LamM) hc hc'
  intro e f hf
  by_cases c1 : e < v.y.NN * v.y.Lam
  · obtain ⟨x, hx, q, q'⟩ := A e c1
    rw [List.append_assoc, List.getElem?_append_left (by rw [la']; exact c1), q'] at hf
    refine ⟨x, sl_rowR hx, (Option.some.inj hf).symm, ?_⟩
    rw [List.append_assoc, List.getElem?_append_left (by rw [la]; exact c1), q]
  · by_cases c2 : e - v.y.NN * v.y.Lam < v.y.LamM
    · obtain ⟨x, hx, q, q'⟩ := B _ c2
      have es : ∀ s : ℕ, s + v.y.NN * v.y.Lam + (e - v.y.NN * v.y.Lam) = s + e := fun s => by omega
      rw [es] at q q'
      rw [List.append_assoc, List.getElem?_append_right (by rw [la']; omega), la',
        List.getElem?_append_left (by rw [lb']; exact c2), q'] at hf
      refine ⟨x, sl_shA hx, (Option.some.inj hf).symm, ?_⟩
      rw [List.append_assoc, List.getElem?_append_right (by rw [la]; omega), la,
        List.getElem?_append_left (by rw [lb]; exact c2), q]
    · have hlt : e - v.y.NN * v.y.Lam - v.y.LamM < v.y.LamM * v.y.h.NE := by
        by_contra c3
        rw [List.append_assoc, List.getElem?_append_right (by rw [la']; omega), la',
          List.getElem?_append_right (by rw [lb']; omega), lb',
          List.getElem?_eq_none (by rw [lc']; omega)] at hf
        cases hf
      obtain ⟨x, hx, q, q'⟩ := C _ hlt
      have es : ∀ s : ℕ, s + v.y.NN * v.y.Lam + v.y.LamM +
          (e - v.y.NN * v.y.Lam - v.y.LamM) = s + e := fun s => by omega
      rw [es] at q q'
      rw [List.append_assoc, List.getElem?_append_right (by rw [la']; omega), la',
        List.getElem?_append_right (by rw [lb']; omega), lb', q'] at hf
      refine ⟨x, sl_shA hx, (Option.some.inj hf).symm, ?_⟩
      rw [List.append_assoc, List.getElem?_append_right (by rw [la]; omega), la,
        List.getElem?_append_right (by rw [lb]; omega), lb, q]

/-- **EACH OF THE VERIFIER's CLAIMS ON THE END VALUES IS WORTH 0**, in a world with the true entries
that holds the honest side's values under the claims' slots. CONDITIONAL: on every hypothesis named.
z: the token point. -/
theorem claims_zero {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {z : Array E} {R : Reads}
    {sh : Array E} (hR : S.readsTok z = some R) (hsh : endsOn S R = some sh)
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {Mm : Mats Cb.Gl.E}
    {funs : Array HFun} {fo' : OnBytes.Model.Forest.Heard} {pts : List (String × Array E)}
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart (tokPts S.zlow z) pts)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsAre Q w Mm) (hv : S.v.tab = r.1) {tB0 : ℕ}
    (hB : S.v.tabAt "b-bits-0" = some tB0) {H : Heard} {T : Tsc} (hT : H.tT = some T)
    {lE : List Aff} (hlE : termsForms S.v H = some lE) {Wo : World Cb.Gl.E}
    (hW : Wo.entry = entryOf Reading.gl tl funs S.v.iU3 S.v.K3 Mm)
    (hsl : ∀ e, Wo.slot (T.sEnd + e) = sentAt Reading.gl sh e) :
    ∀ f ∈ lE, f.value Reading.gl Wo = 0 := by
  intro f hfm
  obtain ⟨e, he⟩ := List.getElem?_of_mem hfm
  obtain ⟨H0, T0, hT0, h0⟩ := sides_ends hS
  obtain ⟨x, hx, rfl, ha⟩ := terms_pair hT0 hT h0 hlE e f he
  obtain ⟨eQ, ew, _, _, _, _, _⟩ := sides_fields hS
  have hR' : readsAt Q w S.fo (tokPts S.zlow z) = some R := by
    have q := hR
    unfold OnBytes.Desc.First.K4.Honest.Sides.readsTok at q
    rw [eQ, ew] at q
    exact q
  obtain ⟨hfit, hs⟩ := endsOn_at hsh ha
  have hv0 := valAff_true hR' hl hf hp (Or.inl fun _ h => h) hm hNM hC hfit
    (slot := fun _ => zeroE) (W := ⟨fun _ => 0, Wo.entry⟩) hW (fun _ _ => Reading.gl.zero.symm)
    (terms_off hl hf hv hB h0 _ (List.mem_of_getElem? ha))
  rw [Aff.value_sub, Aff.value_slot] at hv0
  have es : sentAt Reading.gl sh e = x.value Reading.gl Wo := by
    unfold sentAt
    rw [Array.getD_eq_getD_getElem?, hs]
    have hneg : ∀ y : E, Reading.gl.val (negE y) = -Reading.gl.val y := OnBytes.Slice.readE_neg
    show Reading.gl.val (negE _) = _
    rw [hneg, hv0]
    show -((0 : Cb.Gl.E) - _) = _
    rw [neg_sub, sub_zero]
    exact value_noslot hx rfl
  rw [Aff.value_sub, Aff.value_slot, hsl, es, sub_self]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.value_noslot
#print axioms ProofFile.Honest.K4.terms_block
#print axioms ProofFile.Honest.K4.terms_pair
#print axioms ProofFile.Honest.K4.claims_zero
