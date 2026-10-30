-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/HeardWalk.lean: conditional, from a return: the shape of what
a lookup's hearing returns is that of `heardVSh` (Honest/K3/Shape/HeardOps.lean). Theorems; seven
small definitions (what a routine's theorem says of what a run carries and of the tie's state; the
pieces of `heardVSh` by name).

Terms. Honest/K3/GLOSSARY.md: see there hearing, heard structure, form, slot, row, sumcheck, tie,
key tree and face. `Sized F` says that the ledger's three arrays have their size; a form's shape is
`affSh` (Johnson/Desc/First/Shape/Parts.lean).

What is shown.
  `row_affSh`: the row of a masked sumcheck names its own slots, then those of its start form, then
    those of the terms that are kept.
  `sumV_out`: a masked sumcheck with end values: `sumAt`.
  `turn_out`, `run_out`, `tieV_out`, `partsV_out`, `keysV_out`: the pieces.
  `messagesV_out`: the rows, the open sumcheck's first slot and start form, the slot of the
    bits' end value, the key forms with their points' sizes: `heardVSh f F.next`. And four clauses
    more: the open sumcheck's variables are `leafVars f z` for some z; its challenges, `zb0` and
    `zb1` have mu + d entries each.

Hypotheses that remain, in `messagesV_out`.
  `h`: the return of `messagesV`.
  `hS`: `Sized F`.
  `hp`: the face has a part of keys.
In the pieces' theorems: `e`, `hw`, `hr`: the return of the routine in question (`sumV`, `openV`,
`Hr.owe`; `MaskedSum.whole`; `MaskedSum.row`). `hc`: (in `turn_out`, `run_out`) `CarAre` of what the
run carries in front. `hf`: (in `foldlM_rel`) each step keeps the relation. `hz`: (in `sumAt_bits`)
the list has m entries.

How the proof goes. It is the second walk through the hearing's text: beside the ledger
(Honest/K3/Shape/Walk.lean) it follows what each routine passes on: the end values' slots, the rows,
the forms, the points' sizes.

Users. Honest/K3/Shape/HeardTop.lean imports this file.

Limits. All statements are implications. No statement of this file says that the hearing returns.
No instance of these hypotheses is exhibited in this file. An instance:
Honest/K3/Shape/HeardGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Walk
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardOps
import Johnson.Desc.First.ProdV.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Fork Aff orderDefault)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First.Shape (LedSh ledSh AffSh affSh affSh_addMul affSh_add affSh_sub
  affSh_ofConst affSh_slot rowFormSh)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var Heard ownSlots)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV leafVars bitsCall noVar faceOf)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried levelVars levelEnds stepDown
  level_spec layBack_size)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open ProofFile.Honest.K3.Law (slot_spec must_spec drawsV_same hearV_messages)

variable {α β γ : Type}

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run
local notation "KFace" => VerifiableInference.Desc.K3.Face

/-! ## 1 Forms -/

theorem append_no (a : AffSh) : a.append noSh = a := by
  simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots, noSh]

theorem no_append (a : AffSh) : noSh.append a = a := by
  simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots, noSh]

theorem affSh_empty : affSh ({} : Aff) = noSh := rfl

theorem affSh_scale (a : Aff) (k : E) : affSh (Aff.scale a k) = affSh a := by
  unfold Aff.scale
  rw [affSh_addMul, affSh_empty, no_append]

/-- The slots first, first + 1, … set behind a form. -/
theorem affSh_onSlots (f : Aff) (first : Nat) (u : List E) :
    affSh (MaskedSum.onSlots f first u) =
      (affSh f).append (AffSh.mk [] (List.range' first u.length)) := by
  have key : ∀ (l : List E) (j : Nat) (a : Aff),
      affSh (l.foldl (fun (s : Nat × Aff) x => (s.1 + 1, Aff.addMul s.2 (Aff.slot s.1) x))
        (j, a)).2 = (affSh a).append (AffSh.mk [] (List.range' j l.length)) := by
    intro l
    induction l with
    | nil =>
      intro j a
      simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]
    | cons x l ih =>
      intro j a
      rw [List.foldl_cons, ih, affSh_addMul, affSh_slot]
      simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots, List.range'_succ]
  exact key u first f

/-- **What a masked sumcheck's row names.** No hypothesis. -/
theorem affSh_rowForm (h : Heard) (S0 : E) (kept : Aff) :
    affSh (MaskedSum.rowForm h S0 kept) =
      rowFormSh h.first (MaskedSum.hidingAt (h.vars.zip h.r)).1.length (affSh h.start)
        (affSh kept) := by
  unfold MaskedSum.rowForm
  dsimp only
  rw [affSh_addMul, affSh_addMul, affSh_onSlots, affSh_sub, affSh_ofConst, affSh_ofConst]
  simp [rowFormSh, AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]

theorem row_affSh {h : Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) :
    affSh f = rowFormSh h.first (MaskedSum.hidingAt (h.vars.zip h.r)).1.length (affSh h.start)
      (affSh kept) := by
  have e := MaskedSum.row_of_laid S0 kept (MaskedSum.laid_of_row hr)
  have e2 : f = MaskedSum.rowForm h S0 kept :=
    congrArg (·.1) (Option.some.inj (hr.symm.trans e))
  rw [e2, affSh_rowForm]

/-! ## 2 The masked sumcheck -/

/-- **Hearing and row at once: what is returned.** Conditional on the return and on `Sized`. -/
theorem whole_out {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hS : Sized F)
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) :
    (h.sEnd, affSh f, G.next) = sumAt k F.next (affSh C) := by
  obtain ⟨_, Gm, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  obtain ⟨a1, a2, a3⟩ := MaskedSum.heard_lenK hh
  obtain ⟨_, T, R, _, _, he, _⟩ := MaskedSum.hear_spec hh
  have hst : h.start = C := by rw [he]
  have hn : G.next = F.next + ownSlots k.all + k.endsN :=
    congrArg LedSh.next (whole_sh hS hw).2
  rw [row_affSh hr, a1, a2, a3, hst, hn]
  rfl

theorem sumV_out {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs rest : List Fmt.RoundView} {a : Heard × Aff} (hS : Sized F)
    (e : sumV C k endTerm F rs = some (a, G, rest)) :
    (a.1.sEnd, affSh a.2, G.next) = sumAt k F.next (affSh C) := by
  unfold sumV at e
  split at e
  · exact nomatch e
  · split at e
    · rename_i h row G' hw
      split at e
      · exact nomatch e
      · have e' := Option.some.inj e
        obtain rfl : (h, row) = a := congrArg (·.1) e'
        obtain rfl : G' = G := congrArg (·.2.1) e'
        exact whole_out hS hw
    · exact nomatch e

/-! ## 3 The product levels -/

/-- What a run carries, against its shape: the rows; the point's size; the form. -/
def CarAre (c : Carried) (s : List AffSh × Nat × AffSh) : Prop :=
  c.rows.toList.map affSh = s.1 ∧ c.point.size = s.2.1 ∧ affSh c.form = s.2.2

theorem rows_push (rows : Array Aff) (y : Aff) (sh : List AffSh)
    (h : rows.toList.map affSh = sh) : (rows.push y).toList.map affSh = sh ++ [affSh y] := by
  rw [Array.toList_push, List.map_append, h]
  rfl

/-- A level's numbers do not depend on the level's point. -/
theorem sumAt_level (m : Nat) (z : Array E) (order : List Nat) (n : Nat) (C : AffSh) :
    sumAt (VerifiableInference.Desc.First.ProdV.levelCall m z order) n C =
      sumAt { lead := 0, vs := levelVars 0 #[] order, ends := some levelEnds } n C := by
  unfold sumAt
  rw [ownSlots_blind (vs := (VerifiableInference.Desc.First.ProdV.levelCall m z order).all)
    (ws := Call.all { lead := 0, vs := levelVars 0 #[] order, ends := some levelEnds })
    (by simp [VerifiableInference.Desc.First.ProdV.levelCall, Call.all, levelVars,
      Function.comp_def, Var.d])]
  rfl

theorem turn_out {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} {c : List AffSh × Nat × AffSh} (hS : Sized F) (hc : CarAre s c)
    (h : turn order s m F rs = some (s', G, rest)) :
    CarAre s' (turnSh order m c F.next).1 ∧ G.next = (turnSh order m c F.next).2 := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  have es : ({ rows := s.rows.push o.row, point := (stepDown o).1, form := (stepDown o).2 } :
      Carried) = s' := congrArg (·.1) e
  obtain ⟨hd, line, sc, hw, _, _, hr, hL, hR⟩ := level_spec hx
  have q := whole_out hS hw
  rw [sumAt_level, hc.2.2] at q
  have q1 : hd.sEnd = _ := congrArg (·.1) q
  have q2 : affSh o.row = _ := congrArg (·.2.1) q
  have q3 : G'.next = _ := congrArg (·.2.2) q
  subst es
  refine ⟨⟨?_, ?_, ?_⟩, q3⟩
  · exact (rows_push _ _ _ hc.1).trans (by rw [q2]; rfl)
  · show (#[o.xi] ++ o.r).size = 1 + m
    rw [Array.size_append, hr, layBack_size]
    rfl
  · show affSh (Aff.scale (Aff.slot o.sL) (subE oneE o.xi) + Aff.scale (Aff.slot o.sR) o.xi) = _
    rw [affSh_add, affSh_scale, affSh_scale, affSh_slot, affSh_slot, hL, hR, q1]
    rfl

theorem fold_out (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView) (c : List AffSh × Nat × AffSh) (n : Nat),
    Sized x.2.1 → CarAre x.1 c → x.2.1.next = n →
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y →
    CarAre y.1 (runSh m0 orders l c n).1 ∧ y.2.1.next = (runSh m0 orders l c n).2
  | [], x, y, c, n, _, hc, hn, h => by
    obtain rfl : x = y := Option.some.inj h
    exact ⟨hc, hn⟩
  | i :: l, x, y, c, n, hS, hc, hn, h => by
    subst hn
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    have w1 := turn_went hS hz
    obtain ⟨c1, n1⟩ := turn_out hS hc hz
    exact fold_out m0 orders l (s', G, rest) y _ _ w1.1 c1 n1 h

theorem run_out {m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} {c : List AffSh × Nat × AffSh} (hS : Sized F) (hc : CarAre s c)
    (h : vRun m0 n orders s F rs = some (s', G, rest)) :
    CarAre s' (runSh m0 orders (List.range n) c F.next).1 ∧
      G.next = (runSh m0 orders (List.range n) c F.next).2 :=
  fold_out m0 orders _ (s, F, rs) (s', G, rest) c _ hS hc rfl h

/-! ## 4 The tie, the parts' roots, the key trees -/

theorem foldlM_rel {σ : Type} {f : β → γ → Hr β} {g : σ → σ} {R : β → Fork → σ → Prop}
    (hf : ∀ (s : β) (a : γ) (F G : Fork) (rs rest : List Fmt.RoundView) (b : β) (t : σ), Sized F →
      R s F t → f s a F rs = some (b, G, rest) → Sized G ∧ R b G (g t)) :
    ∀ (l : List γ) (s : β) (F G : Fork) (rs rest : List Fmt.RoundView) (b : β) (t : σ), Sized F →
      R s F t → (l.foldlM f s) F rs = some (b, G, rest) →
      Sized G ∧ R b G (l.foldl (fun t _ => g t) t)
  | [], s, F, G, rs, rest, b, t, hS, hR, h => by
    have h' : (pure s : Hr β) F rs = some (b, G, rest) := h
    obtain ⟨a1, a2, _⟩ := pure_spec h'
    rw [a1, a2]
    exact ⟨hS, hR⟩
  | a :: l, s, F, G, rs, rest, b, t, hS, hR, h => by
    have h' : (f s a >>= fun s' => l.foldlM f s') F rs = some (b, G, rest) := h
    obtain ⟨s', F1, r1, e1, h2⟩ := bindHr_some h'
    obtain ⟨S1, R1⟩ := hf s a F F1 rs r1 s' t hS hR e1
    exact foldlM_rel hf l s' F1 G r1 rest b (g t) S1 R1 h2

/-- The tie's state, against its shape. -/
def TieAre (s : Array Aff × Nat × Array Nat) (G : Fork) (t : List AffSh × Nat × List Nat × Nat) :
    Prop :=
  s.1.toList.map affSh = t.1 ∧ s.2.1 = t.2.1 ∧ s.2.2.toList = t.2.2.1 ∧ G.next = t.2.2.2

theorem tieV_out {w : Nat} {a : E} {F G : Fork} {rs rest : List Fmt.RoundView}
    {x : Array Aff × Nat × Array Nat} (hS : Sized F) (h : tieV w a F rs = some (x, G, rest)) :
    TieAre x G (tieSh w F.next) := by
  unfold tieV at h
  try dsimp only at h
  obtain ⟨y, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨s, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨hx, hG, _⟩ := pure_spec h
  have w1 := sumV_went hS e1
  have q := sumV_out hS e1
  rw [affSh_ofConst] at q
  have q1 : y.1.sEnd = _ := congrArg (·.1) q
  have q2 : affSh y.2 = _ := congrArg (·.2.1) q
  have q3 : F1.next = _ := congrArg (·.2.2) q
  have R0 : TieAre (#[y.2], y.1.sEnd + 1, #[y.1.sEnd + 2]) F1
      ([(sumAt (noVar 3 3) F.next noSh).2.1], (sumAt (noVar 3 3) F.next noSh).1 + 1,
        [(sumAt (noVar 3 3) F.next noSh).1 + 2], (sumAt (noVar 3 3) F.next noSh).2.2) :=
    ⟨by show [affSh y.2] = _; rw [q2]; rfl, by show y.1.sEnd + 1 = _; rw [q1]; rfl,
      by show [y.1.sEnd + 2] = _; rw [q1]; rfl, q3⟩
  obtain ⟨_, R1⟩ := foldlM_rel (g := tieStep) (R := TieAre)
    (fun s _ F G rs rest b t hS R e => by
      obtain ⟨y, F1, r1, e1, e⟩ := bindHr_some e
      obtain ⟨hb, hG, _⟩ := pure_spec e
      have w := sumV_went hS e1
      have q := sumV_out hS e1
      rw [affSh_slot, R.2.1, R.2.2.2] at q
      have q1 : y.1.sEnd = _ := congrArg (·.1) q
      have q2 : affSh y.2 = _ := congrArg (·.2.1) q
      have q3 : F1.next = _ := congrArg (·.2.2) q
      rw [hb, hG]
      refine ⟨w.1, ?_, q1, ?_, q3⟩
      · exact (rows_push _ _ _ R.1).trans (by rw [q2]; rfl)
      · show (s.2.2.push (y.1.sEnd + 1)).toList = _
        rw [Array.toList_push, R.2.2.1, q1]
        rfl) _ _ _ _ _ _ _ _ w1.1 R0 e2
  rw [hx, hG]
  refine ⟨R1.1, q1, ?_, R1.2.2.2⟩
  show (s.2.2.push s.2.1).toList = _
  rw [Array.toList_push, R1.2.2.1, R1.2.1]
  rfl

theorem partsV_out : ∀ (n : Nat) (rows : Array Aff) (C : Aff) (F G : Fork)
    (rs rest : List Fmt.RoundView) (x : Array Aff × List Aff) (sh : List AffSh), Sized F →
    rows.toList.map affSh = sh → partsV n rows C F rs = some (x, G, rest) →
    x.1.toList.map affSh = (partsSh n sh (affSh C) F.next).1 ∧
      x.2.map affSh = (partsSh n sh (affSh C) F.next).2.1 ∧
      G.next = (partsSh n sh (affSh C) F.next).2.2
  | 0, rows, C, F, G, rs, rest, x, sh, _, hr, h => by
    unfold partsV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    rw [a, b]
    exact ⟨hr, rfl, rfl⟩
  | n + 1, rows, C, F, G, rs, rest, x, sh, hS, hr, h => by
    unfold partsV at h
    obtain ⟨w, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨y, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, b, _⟩ := pure_spec h
    have w1 := sumV_went hS e1
    have q := sumV_out hS e1
    have q1 : w.1.sEnd = _ := congrArg (·.1) q
    have q2 : affSh w.2 = _ := congrArg (·.2.1) q
    have q3 : F1.next = _ := congrArg (·.2.2) q
    obtain ⟨p1, p2, p3⟩ := partsV_out n _ _ F1 F2 r1 r2 y _ w1.1 (rows_push _ _ _ hr) e2
    rw [affSh_slot, q1, q2, q3] at p1 p2 p3
    rw [a, b]
    refine ⟨p1, ?_, p3⟩
    show affSh (Aff.slot w.1.sEnd) :: y.2.map affSh = _
    rw [p2, affSh_slot, q1]
    rfl

theorem keysV_out (f : KFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff)
    (F G : Fork) (rs rest : List Fmt.RoundView) (x : Array Aff × List (Array E × Aff))
    (sh : List AffSh), Sized F → rows.toList.map affSh = sh →
    keysV f xs Cs rows F rs = some (x, G, rest) →
    x.1.toList.map affSh = (keysSh f xs (Cs.map affSh) sh F.next).1 ∧
      x.2.map (fun y => (y.1.size, affSh y.2)) = (keysSh f xs (Cs.map affSh) sh F.next).2.1 ∧
      G.next = (keysSh f xs (Cs.map affSh) sh F.next).2.2
  | [], _, rows, F, G, rs, rest, x, sh, _, hr, h => by
    unfold keysV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    rw [a, b]
    exact ⟨hr, rfl, rfl⟩
  | _ :: _, [], rows, F, G, rs, rest, x, sh, _, hr, h => by
    unfold keysV at h
    obtain ⟨a, b, _⟩ := pure_spec h
    rw [a, b]
    exact ⟨hr, rfl, rfl⟩
  | y :: xs, C :: Cs, rows, F, G, rs, rest, x, sh, hS, hr, h => by
    unfold keysV at h
    obtain ⟨k, F1, r1, e1, h⟩ := bindHr_some h
    obtain ⟨z, F2, r2, e2, h⟩ := bindHr_some h
    obtain ⟨a, b, _⟩ := pure_spec h
    have w1 : Went F F1 (levelOps 0 (f.orders y.2) (List.range y.1)) := run_went hS e1
    obtain ⟨c1, n1⟩ := run_out (c := (sh, 0, affSh C)) hS ⟨hr, rfl, rfl⟩ e1
    obtain ⟨p1, p2, p3⟩ := keysV_out f xs Cs _ F1 F2 r1 r2 z _ w1.1 c1.1 e2
    rw [n1] at p1 p2 p3
    rw [a, b]
    refine ⟨p1, ?_, p3⟩
    show (k.point.size, affSh k.form) :: z.2.map (fun y => (y.1.size, affSh y.2)) = _
    rw [p2, c1.2.1, c1.2.2]
    rfl

/-- The one claim on the planes' roots. -/
theorem join_out (f : KFace) (sG : Array Nat) (w : Nat → E) (sh : List Nat)
    (h : sG.toList = sh) :
    affSh ((List.range (2 ^ f.mu)).foldl
      (fun (c : Aff) j =>
        if j < f.planes then Aff.addMul c (Aff.slot (sG.getD j 0)) (w j)
        else c + Aff.ofConst (w j)) (Aff.ofConst zeroE)) = joinSh f sh := by
  have key : ∀ (l : List Nat) (c : Aff) (cs : AffSh), affSh c = cs →
      affSh (l.foldl (fun (c : Aff) j =>
        if j < f.planes then Aff.addMul c (Aff.slot (sG.getD j 0)) (w j)
        else c + Aff.ofConst (w j)) c) =
      l.foldl (fun c j =>
        if j < f.planes then c.append (slotSh (sh.getD j 0)) else c.append noSh) cs := by
    intro l
    induction l with
    | nil => exact fun _ _ hc => hc
    | cons j l ih =>
      intro c cs hc
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      have hg : sG.getD j 0 = sh.getD j 0 := by
        rw [← h]
        simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
      by_cases hj : j < f.planes
      · rw [if_pos hj, if_pos hj, affSh_addMul, affSh_slot, hc, hg]
        rfl
      · rw [if_neg hj, if_neg hj, affSh_add, affSh_ofConst, hc]
        rfl
  exact key _ _ _ rfl

/-! ## 5 The lookup's rounds -/

theorem owe_next {w : String} {F G : Fork} {rs rest : List Fmt.RoundView} {n : Nat}
    (e : Hr.owe w F rs = some (n, G, rest)) : G.next = F.next := by
  have e' : some ((F.owe w).1, (F.owe w).2, rs) = some (n, G, rest) := e
  cases e'
  rfl

/-- **The sumcheck that is left open: what is returned.** Conditional on the return and on `Sized`.
-/
theorem openV_out {C : Aff} {vs : List Var} {F G : Fork} {rs rest : List Fmt.RoundView} {a : Heard}
    (hS : Sized F) (e : openV C vs F rs = some (a, G, rest)) :
    a.first = F.next ∧ a.start = C ∧ a.vars = vs ∧ a.r.length = vs.length ∧
      G.next = F.next + ownSlots vs := by
  have hn : G.next = F.next + ownSlots vs := congrArg LedSh.next (openV_went hS e).2
  unfold openV at e
  split at e
  · exact nomatch e
  · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨h, G'⟩ := x
    have ea : h = a := congrArg (·.1) e
    obtain ⟨_, T, R, _, hR, he, _⟩ := MaskedSum.hear_spec hx
    have hl := MaskedSum.readAll_none_len hR
    rw [← ea, he]
    exact ⟨rfl, rfl, rfl, by show (R.rounds.map (·.2)).length = _; rw [List.length_map, hl], hn⟩

/-- A masked sumcheck with end values returns one challenge for each variable and one more. -/
theorem sumV_rlen {C : Aff} {lead : Nat} {vs : List Var} {e : MaskedSum.Ends}
    {endTerm : List E → List E → E} {F G : Fork} {rs rest : List Fmt.RoundView} {a : Heard × Aff}
    (h : sumV C ⟨lead, vs, some e⟩ endTerm F rs = some (a, G, rest)) :
    a.1.r.length = vs.length + 1 := by
  unfold sumV at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' hw
      split at h
      · exact nomatch h
      · have ea : (hd, row) = a := congrArg (·.1) (Option.some.inj h)
        obtain ⟨_, Gm, _, _, hh, _, _⟩ := MaskedSum.whole_parts hw
        obtain ⟨_, T, R, _, hR, he, _⟩ := MaskedSum.hear_spec hh
        obtain ⟨_, _, _, _, _, _, _, a4, _⟩ := MaskedSum.readAll_spec hR
        have hlen : R.rounds.length = (Call.all ⟨lead, vs, some e⟩).length :=
          (MaskedSum.VarsRead.length a4).2
        rw [← ea, he]
        show (R.rounds.map (·.2)).length = _
        rw [List.length_map, hlen]
        simp [Call.all]
    · exact nomatch h

/-- The bits' numbers depend on the number of the point's coordinates alone. -/
theorem sumAt_bits (z : List E) (m : Nat) (hz : z.length = m) (n : Nat) (C : AffSh) :
    sumAt (bitsCall z) n C = sumAt (bitsCall (List.replicate m zeroE)) n C := by
  subst hz
  unfold sumAt
  rw [ownSlots_blind (vs := (bitsCall z).all) (ws := (bitsCall (List.replicate z.length zeroE)).all)
    (by simp [Call.all, bitsCall, Function.comp_def, Var.d])]
  rfl

/-- The pieces of `heardVSh`, by name. -/
def tS (f : KFace) (n : Nat) := tieSh f.planes n
def pS (f : KFace) (n : Nat) :=
  partsSh (f.parts.length - 1) (tS f n).1 (slotSh (tS f n).2.1) (tS f n).2.2.2
def kS (f : KFace) (n : Nat) := keysSh f f.parts.zipIdx (pS f n).2.1 (pS f n).1 (pS f n).2.2
def rS (f : KFace) (n : Nat) :=
  runSh f.mu orderDefault (List.range f.d) ((kS f n).1, f.mu, joinSh f (tS f n).2.2.1) (kS f n).2.2
def bS (f : KFace) (n : Nat) :=
  sumAt (bitsCall (List.replicate (f.mu + f.d) zeroE))
    ((rS f n).2 + ownSlots (leafVars f #[])) noSh

/-- **What the lookup's rounds return, as a shape.** Conditional on the return, on `Sized` in front,
and on a face that has a part of keys. -/
theorem messagesV_out {f : KFace} {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hp : 1 ≤ f.parts.length) (h : messagesV f F rs = some (g, G, rest)) :
    g.rows.toList.map affSh = (heardVSh f F.next).rows ∧
      g.leaves.first = (heardVSh f F.next).leavesFirst ∧
      affSh g.leaves.start = (heardVSh f F.next).leavesStart ∧
      g.sBit = (heardVSh f F.next).sBit ∧
      g.keys.map (fun y => (y.1.size, affSh y.2)) = (heardVSh f F.next).keys ∧
      (∃ z, g.leaves.vars = leafVars f z) ∧ g.leaves.r.length = f.mu + f.d ∧
      g.zb0.size = f.mu + f.d ∧ g.zb1.size = f.mu + f.d := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  rw [(slot_spec e1).2] at e2
  have w2 := owe_went hS e2
  have w3 := owe_went w2.1 e3
  have w4 := owe_went w3.1 e4
  have n4 : F4.next = F.next := by rw [owe_next e4, owe_next e3, owe_next e2]
  have q5 : F5 = F4 := by
    split at e5
    · exact drawV_same e5
    · exact (pure_spec e5).2.1
  rw [drawV_same e6, q5] at e7
  have w7 := tieV_went w4.1 e7
  have t7 : TieAre (rows, sZ, sG) F7 (tS f F.next) := by
    rw [← n4]
    exact tieV_out w4.1 e7
  have t1 : rows.toList.map affSh = (tS f F.next).1 := t7.1
  have t2 : sZ = (tS f F.next).2.1 := t7.2.1
  have t3 : sG.toList = (tS f F.next).2.2.1 := t7.2.2.1
  have t4 : F7.next = (tS f F.next).2.2.2 := t7.2.2.2
  obtain ⟨w8, l8⟩ := partsV_went _ _ _ _ _ _ _ _ w7.1 e8
  have p8 := partsV_out _ _ _ _ _ _ _ _ _ w7.1 t1 e8
  rw [affSh_slot, t2, t4] at p8
  have p1 : rows2.toList.map affSh = (pS f F.next).1 := p8.1
  have p2 : roots.map affSh = (pS f F.next).2.1 := p8.2.1
  have p3 : F8.next = (pS f F.next).2.2 := p8.2.2
  rw [drawsV_same e9] at e10
  have hok : f.parts.zipIdx.length = roots.length := by
    have l8' : roots.length = f.parts.length - 1 + 1 := l8
    rw [List.length_zipIdx, l8']
    omega
  have w10 := keysV_went f _ _ _ _ _ _ _ _ hok w8.1 e10
  have k10 := keysV_out f _ _ _ _ _ _ _ _ _ w8.1 p1 e10
  rw [p2, p3] at k10
  have k1 : rows3.toList.map affSh = (kS f F.next).1 := k10.1
  have k2 : keys.map (fun y => (y.1.size, affSh y.2)) = (kS f F.next).2.1 := k10.2.1
  have k3 : F10.next = (kS f F.next).2.2 := k10.2.2
  rw [(must_spec e11).2] at e12
  have w12 := run_went w10.1 e12
  have T12 := run_out (c := ((kS f F.next).1, f.mu, joinSh f (tS f F.next).2.2.1)) w10.1
    ⟨k1, by simp [drawsV_size e9], join_out f sG _ _ t3⟩ e12
  rw [k3] at T12
  have T1 : table.rows.toList.map affSh = (rS f F.next).1.1 := T12.1.1
  have T3 : affSh table.form = (rS f F.next).1.2.2 := T12.1.2.2
  have T4 : F12.next = (rS f F.next).2 := T12.2
  rw [(must_spec e13).2] at e14
  have w14 := openV_went w12.1 e14
  obtain ⟨o1', o2', o3', o4', o5'⟩ := openV_out w12.1 e14
  rw [drawsV_same e15] at e16
  have b16 := sumV_out w14.1 e16
  rw [affSh_ofConst, sumAt_bits _ (f.mu + f.d) (by simp [drawsV_size e15]), o5', leaf_own, T4]
    at b16
  have b1 : bits.1.sEnd = (bS f F.next).1 := congrArg (·.1) b16
  have b2 : affSh bits.2 = (bS f F.next).2.1 := congrArg (·.2.1) b16
  have bl := sumV_rlen e16
  have lv : (leafVars f table.point).length = f.mu + f.d := by simp [leafVars]
  rw [hg]
  refine ⟨?_, ?_, ?_, b1, k2, ⟨_, o3'⟩, by rw [o4', lv], ?_, ?_⟩
  · exact (rows_push _ _ _ T1).trans (by rw [b2]; rfl)
  · exact o1'.trans T4
  · show affSh leaves.start = _
    rw [o2', T3]
    rfl
  · show leaves.r.toArray.size = _
    rw [List.size_toArray, o4', lv]
  · show (bits.1.r.take (f.mu + f.d)).toArray.size = _
    rw [List.size_toArray, List.length_take, bl]
    simp [drawsV_size e15]

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.append_no
#print axioms ProofFile.Honest.K3.Shape.no_append
#print axioms ProofFile.Honest.K3.Shape.affSh_empty
#print axioms ProofFile.Honest.K3.Shape.affSh_scale
#print axioms ProofFile.Honest.K3.Shape.affSh_onSlots
#print axioms ProofFile.Honest.K3.Shape.affSh_rowForm
#print axioms ProofFile.Honest.K3.Shape.row_affSh
#print axioms ProofFile.Honest.K3.Shape.whole_out
#print axioms ProofFile.Honest.K3.Shape.sumV_out
#print axioms ProofFile.Honest.K3.Shape.rows_push
#print axioms ProofFile.Honest.K3.Shape.sumAt_level
#print axioms ProofFile.Honest.K3.Shape.turn_out
#print axioms ProofFile.Honest.K3.Shape.fold_out
#print axioms ProofFile.Honest.K3.Shape.run_out
#print axioms ProofFile.Honest.K3.Shape.foldlM_rel
#print axioms ProofFile.Honest.K3.Shape.tieV_out
#print axioms ProofFile.Honest.K3.Shape.partsV_out
#print axioms ProofFile.Honest.K3.Shape.keysV_out
#print axioms ProofFile.Honest.K3.Shape.join_out
#print axioms ProofFile.Honest.K3.Shape.owe_next
#print axioms ProofFile.Honest.K3.Shape.openV_out
#print axioms ProofFile.Honest.K3.Shape.sumV_rlen
#print axioms ProofFile.Honest.K3.Shape.sumAt_bits
#print axioms ProofFile.Honest.K3.Shape.messagesV_out
