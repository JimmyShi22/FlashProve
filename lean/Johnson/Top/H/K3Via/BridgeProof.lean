-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Via/BridgeProof.lean: the kind "lookup" (K3) at a proof file's lookup: from the
general text at faceOf h to the messages h of Johnson/Desc/First/Look/K3Lookup.lean, and the whole way
from the hearing on a view's rounds. Theorems.

Main theorems:
  `general_messages`: a tie of two flat texts on one tape: where messagesG (faceOf h) says yes and
    toHeard h leads what it heard back to the program's record, K3.lean's messages h says yes on the
    same tape with that record, the same ledger and the same rest of the tape.
  `hearV_run`: the same sentence at a shape h and no place: flRun {} (messages h) es F rs = some
    (g', G).
  `hearV_hear`: THE NEW HEARING's YES GIVES THE OLD ONE's, WITH THE SAME VALUES: hearV (faceOf h) F
    rs = some (gv, G), toHeard h (toHeardG gv) = some g', the plan's entries pass entriesFit and the
    entry-alone tests, the place has shape h and several calls: then K3.hear p es F rs = some (g',
    G). As machine words; no premise on words.

Where the two flat texts part: the shift's "if" (true by make); the public factor (`factor_eq`: the
general text folds from 1, K3.lean from the first power: 1 times a power is that power as words,
because a power is 1 or an output of the field's product: `okE_pow`); 32 - 2 sumchecks; no step from
the parts' product to a root; the claim on the planes' roots (`cT_eq`: the "if" on real planes is
idle at 32 of 32); one part's key tree; the two counts (`slots_eq`, `lins_eq`); messages' two
further tests are toHeard's one.

Limits. One way: not the other way round. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Via.BridgeEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc eqTab orderDefault)
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (readE readE_mul readE_one readE_inj)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Prod (wholeStandIn)
open VerifiableInference.Desc.First.Tape (flRun)
open VerifiableInference.Desc.K3Cut (bindM bindS pureS mustM mustS)

/-! ## The public factor -/

theorem okE_powLoop : ∀ (k : Nat) (x : E) (e : Nat) (r : E), okE r = true → okE (powLoopE k x e r) =
    true
  | 0, _, _, r, h => h
  | k + 1, x, e, r, h => by
    unfold powLoopE
    split
    · exact h
    · apply okE_powLoop k
      split
      · exact MaskedSum.okE_mul _ _
      · exact h

/-- A power has words below the prime, whatever went in. -/
theorem okE_pow (a : E) (e : Nat) : okE (powE a e) = true :=
    okE_powLoop e a e oneE MaskedSum.okE_one

/-- 1 times a power is that power, as words. -/
theorem one_mul_pow (a : E) (e : Nat) : mulE oneE (powE a e) = powE a e := by
  apply readE_inj _ _ (MaskedSum.okE_mul _ _) (okE_pow a e)
  rw [readE_mul, readE_one, one_mul]

/-- **The public factor is K3.lean's, as words.** -/
theorem factor_eq (h : Shape) (theta alpha : E) :
    (faceOf h).factor theta alpha = paddingFactor h theta alpha := by
  have hp : (faceOf h).padding = (h.emptyKeys, fun theta => Model.Forest.padKeyOf h theta 0) ::
      (List.range h.NT).map fun y =>
        ((h.pub.getD y 0, fun theta => Model.Forest.padKeyOf h theta (h.callOf.getD y 0)) :
          Nat × (E → E)) := rfl
  unfold Face.factor paddingFactor
  rw [hp, List.foldl_cons, List.foldl_map, one_mul_pow]

/-! ## The two counts -/

theorem foldl_sum (g : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat), l.foldl (fun s i => s + g i) a = a + (l.map g).sum
  | [], a => by simp
  | i :: l, a => by
    rw [List.foldl_cons, foldl_sum g l, List.map_cons, List.sum_cons]
    omega

theorem slots_eq (h : Shape) : (faceOf h).slots = Model.Forest.elems h := by
  have e1 : (fun k => 2 * k + 5) = fun mu => Model.layerSlots mu := by
    funext k
    show 2 * k + 5 = 1 + k * 2 + 2 + 2
    omega
  have e2 : (fun l => 2 * (5 + l) + 5) = fun l => Model.layerSlots (5 + l) := by
    funext l
    show 2 * (5 + l) + 5 = 1 + (5 + l) * 2 + 2 + 2
    omega
  show 7 + 6 * (32 - 2) + 5 * ([h.v].length - 1) +
      ([h.v].map fun v => ((List.range v).map fun k => 2 * k + 5).sum).sum +
      ((List.range h.d).map fun l => 2 * (5 + l) + 5).sum + (1 + 5 + 2 * h.d) +
        (1 + 2 * (5 + h.d) + 2 + 1) =
    (1 + 0 * 2 + 3 + 3) + 30 * (1 + 0 * 2 + 3 + 2) +
      (List.range h.v).foldl (fun s mu => s + Model.layerSlots mu) 0 +
      (List.range h.d).foldl (fun s l => s + Model.layerSlots (5 + l)) 0 + (1 + 2 * h.d + 5) +
      (1 + (5 + h.d) * 2 + 2 + 1)
  rw [foldl_sum (fun mu => Model.layerSlots mu), foldl_sum (fun l => Model.layerSlots (5 + l)), e1,
    e2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  omega

theorem lins_eq (h : Shape) : (faceOf h).lins = Model.Forest.lins h := by
  show (32 - 1) + ([h.v].length - 1) + [h.v].sum + h.d + 1 = 31 + h.v + h.d + 1
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  omega

/-! ## The claim on the planes' roots -/

theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ c, f c a = g c a) →
    l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a (by simp) b]
    exact foldl_congr_mem l _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem cT_eq (sG : Array Nat) (ej : Array E) :
    (List.range (2 ^ 5)).foldl
      (fun (c : Aff) j =>
        if j < 32 then Aff.addMul c (Aff.slot (sG.getD j 0)) (ej.getD j zeroE) else c +
          Aff.ofConst (ej.getD j zeroE))
      (Aff.ofConst zeroE) =
    (List.range 32).foldl (fun (f : Aff) j =>
      Aff.addMul f (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)) (Aff.ofConst zeroE) := by
  show (List.range 32).foldl _ _ = _
  apply foldl_congr_mem
  intro j hj c
  rw [if_pos (List.mem_range.1 hj)]

/-! ## The two flat texts -/

/-- **Where the general text at faceOf h says yes, so does K3.lean's messages h.** -/
theorem general_messages {h : Shape} {F G : Fork} {t u : Tape} {g : HeardG}
    {g' : Model.Forest.Heard}
    (hm : messagesG (faceOf h) F t = some (g, G, u)) (ht : toHeard h g = some g') :
      messages h F t = some (g', G, u) := by
  unfold messagesG at hm
  obtain ⟨slot0, A1, a1, k1, hm⟩ := bindS hm
  obtain ⟨o1, A2, a2, k2, hm⟩ := bindS hm
  obtain ⟨o2, A3, a3, k3, hm⟩ := bindS hm
  obtain ⟨o3, A4, a4, k4, hm⟩ := bindS hm
  -- the shift's «if» is true by make
  have hsh : (faceOf h).shifted = true := rfl
  simp only [hsh, ↓reduceIte] at hm
  obtain ⟨theta, A5, a5, k5, hm⟩ := bindS hm
  obtain ⟨alpha, A6, a6, k6, hm⟩ := bindS hm
  obtain ⟨⟨rows, sZ, sG⟩, A7, a7, k7, hm⟩ := bindS hm
  obtain ⟨⟨rows1, roots⟩, A8, a8, k8, hm⟩ := bindS hm
  obtain ⟨y, A9, a9, k9, hm⟩ := bindS hm
  obtain ⟨⟨rows2, keys⟩, A10, a10, k10, hm⟩ := bindS hm
  obtain ⟨_, A11, a11, k11, hm⟩ := bindS hm
  obtain ⟨table, A12, a12, k12, hm⟩ := bindS hm
  obtain ⟨_, A13, a13, k13, hm⟩ := bindS hm
  obtain ⟨leaves, A14, a14, k14, hm⟩ := bindS hm
  obtain ⟨⟨zb0, leaves1⟩, A15, a15, k15, hm⟩ := bindS hm
  obtain ⟨y5, A16, a16, k16, hm⟩ := bindS hm
  obtain ⟨bits, A17, a17, k17, hm⟩ := bindS hm
  obtain ⟨s1, A18, a18, k18, hm⟩ := bindS hm
  obtain ⟨_, A19, a19, k19, hm⟩ := bindS hm
  obtain ⟨eg, eG, eu⟩ := pureS hm
  subst eg eG eu
  -- no step from the parts' product to a root
  have k8' : (pure (rows, [Aff.slot sZ]) : Fl (Array Aff × List Aff)) A7 a7 =
    some ((rows1, roots), A8, a8) := k8
  obtain ⟨e1, e2, e3⟩ := pureS k8'
  cases e1
  subst e2 e3
  -- one part's key tree
  have k10' : (First.Prod.run 0 h.v (keyOrders h)
    { rows := rows, point := #[], form := Aff.slot sZ } >>= fun k =>
      (pure (k.rows, []) : Fl (Array Aff × List (Array E × Aff))) >>= fun y =>
        (pure (y.1, (k.point, k.form) :: y.2) : Fl (Array Aff × List (Array E × Aff)))) A9 a9 =
      some ((rows2, keys), A10, a10) := k10
  obtain ⟨kk, B1, b1, kr, k10'⟩ := bindS k10'
  obtain ⟨yy, B2, b2, kp, k10'⟩ := bindS k10'
  obtain ⟨e1, e2, e3⟩ := pureS kp
  subst e1 e2 e3
  obtain ⟨e1, e2, e3⟩ := pureS k10'
  cases e1
  subst e2 e3
  obtain ⟨-, e2, e3⟩ := mustS k11
  subst e2 e3
  -- toHeard's one test is messages' two
  have ht' : (if (h.iota.all fun i => decide (i ≤ h.rK)) && ((List.range h.NC).all fun c =>
        (((Array.range h.NC).map fun c =>
          (kk.point.extract h.dT kk.point.size).extract (h.rK - h.iota.getD c 0)
            (kk.point.extract h.dT kk.point.size).size ++
            kk.point.extract 0 h.dT).getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0) then some
              _ else none) =
      some g' := ht
  split at ht'
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    have eg' := Option.some.inj ht'
    subst eg'
    -- the lines of messages
    have k5' : Fl.answer .lkpShift A4 a4 = some (theta, A5, a5) := k5
    have k7' : tie (paddingFactor h theta alpha) A6 a6 = some ((rows, sZ, sG), A8, a8) := by
      rw [← factor_eq]
      exact k7
    have k9' : Fl.point .lkpPlanes 5 A8 a8 = some (y, A9, a9) := k9
    have k12' : First.Prod.run 5 h.d orderDefault
      ⟨kk.rows, y.reverse, (List.range 32).foldl (fun (f : Aff) j =>
          Aff.addMul f (Aff.slot (sG.getD j 0)) ((eqTab y.reverse).getD j zeroE))
            (Aff.ofConst zeroE)⟩ A11 a11 =
        some (table, A12, a12) := by
      rw [← cT_eq]
      exact k12
    have k19' : Fl.must (s1 == slot0 + Model.Forest.elems h &&
      (table.rows.push bits.row).size == Model.Forest.lins h) A18 a18 =
        some ((), G, u) := by
      rw [← slots_eq, ← lins_eq]
      exact k19
    unfold messages
    refine bindM k1 ?_
    refine bindM k2 ?_
    refine bindM k3 ?_
    refine bindM k4 ?_
    refine bindM k5' ?_
    refine bindM k6 ?_
    refine bindM k7' ?_
    refine bindM k9' ?_
    refine bindM kr ?_
    refine bindM k12' ?_
    refine bindM k13 ?_
    refine bindM k14 ?_
    refine bindM k15 ?_
    refine bindM k16 ?_
    refine bindM k17 ?_
    refine bindM k18 ?_
    refine bindM k19' ?_
    refine bindM (mustM hc.1 _ _) ?_
    refine bindM (mustM hc.2 _ _) ?_
    rw [factor_eq]
    rfl
  · cases ht'

/-! ## The whole bridge -/

/-- **The core, at a shape h and no place**: the new hearing's yes gives the yes of K3.lean's
messages h off the strict tape, with the same values. -/
theorem hearV_run {h : Shape} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView} {gv : HeardV}
    {g' : Model.Forest.Heard}
    (hfit : entriesFit (faceOf h) es = true) (hst : es.all staticT = true)
      (hv : hearV (faceOf h) F rs = some (gv, G))
    (ht : toHeard h (toHeardG gv) = some g') : flRun {} (messages h) es F rs = some (g', G) := by
  obtain ⟨t, k1, k2⟩ := flRun_some (hearV_general hfit hst hv)
  exact flRun_mk k1 (general_messages k2 ht)

/-- **THE NEW HEARING's YES GIVES THE OLD ONE's, WITH THE SAME VALUES.** -/
theorem hearV_hear {p : First.Look.P} {h : Shape} {es : List Fmt.Entry} {F G : Fork}
    {rs : List Fmt.RoundView} {gv : HeardV}
    {g' : Model.Forest.Heard} (hp : p.shape = some h) (hN : 1 < h.NC)
      (hfit : entriesFit (faceOf h) es = true)
    (hst : es.all staticT = true) (hv : hearV (faceOf h) F rs = some (gv, G))
      (ht : toHeard h (toHeardG gv) = some g') :
    hear p es F rs = some (g', G) := by
  unfold hear
  rw [hp]
  show (if 1 < h.NC then flRun {} (messages h) es F rs else none) = _
  rw [if_pos hN]
  exact hearV_run hfit hst hv ht

end VerifiableInference.Desc.K3

#print axioms VerifiableInference.Desc.K3.factor_eq
#print axioms VerifiableInference.Desc.K3.general_messages
#print axioms VerifiableInference.Desc.K3.hearV_run
#print axioms VerifiableInference.Desc.K3.hearV_hear
