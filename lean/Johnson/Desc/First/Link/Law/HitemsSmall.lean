-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HitemsSmall.lean: `TableOwes.hitems` (LinkTable.lean), ONE ITEM's CLAUSE
(`ItemIn`, HitemsStill.lean) AT THE ENTRY "K8.equations": the approximate range proof's run of
claims, AT THE READER THAT IS LAID INTO THE READERS' FIRST HOLE (`K9.smallReader`,
Johnson/Desc/First/Batch/SmallReader.lean). Theorems.

Why. At this entry the reader is not the run itself: the run's claims are more than forms. The
reader lists the ties' and the reads' SINGLE EQUATIONS as forms over the arrays' own rows
(`rowsAff`, Johnson/Desc/First/TailClaims/SingleForms.lean). The law's run has the terms
`tm4 n q y ++ tmRest π q y` (Johnson/Desc/First/Batch/Law/K8Run.lean): FOUR TERMS MORE, in front:
those of its first four claims, which bear no number of an equation. So an equation of lists
(`ItemAt`) is false here by a count, and the clause is the inclusion.

What is said.
  `rowsAff_blank`: the forms do not read the fourteen fields that the run writes.
  `small_there`: where the reader answers, the verifier's state holds the approximate range proof's
    structure and the caller's list of tables, and the answer is their forms, with no late slot.
  `value_own`: a form whose arrays are all named by the segment's list has one worth in the table's
    world of the own rows (`worldOwn`) and in the law's (`ownWorld`) at the law's cells
    (`cellsA`).
  `item_small`: **the clause**, general in the link and in the tables of terms: from: the entry is
    of the order and a run stands there; the table of terms there is `tm4 n q y ++ tmRest π q y`;
    tm4's coefficients do not hang on the number of claims in front (v4); π reads the structure,
    blanked, and the list of tables; and at the statement: a part is there; the table's public test
    says yes. By `rowsAff_values` (Johnson/Desc/First/TailClaims/SingleFormsLaw.lean).
  `item_small_layers`, `item_small_attention`, `item_small_head`: at the three sorts' tables of
    terms.
  `four8_plain`: the run's first four claims (`four8`, Johnson/Desc/First/Batch/Law/K8Four.lean)
    bear no number of an equation.

Limits. THE FOUR FIRST CLAIMS' VALUES ARE IN NO FORM OF THIS ITEM: by the table's owners' word they
are held by the lookups' two items of the sort "worth": not here. That a run stands at the entry,
and v4, are premises. WHETHER THE PUBLIC TEST SAYS YES AT A REAL STATE IN FRONT OF A BATCHING is a
run's to show (the list is long: `K9.formsIn_small` gives the test without the list). Nothing on
soundness.
Words. "Block": a sub-protocol of the IOP as it is written in Lean. "The verifier's state": what the
verifier carries from one sub-protocol to the next.

-/
import Johnson.Desc.First.Link.Law.HitemsStill
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead
import Johnson.Desc.First.Batch.SmallReader
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Desc.First.TailClaims.SingleFormsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.TailClaims (rowsAff)
open VerifiableInference.Desc.First.TailClaims.Law (blank ownWorld rowsAff_values)

variable {α W : Type} {F : Frame}

/-- The single equations' forms do not read the fourteen written fields. -/
theorem rowsAff_blank (u tl : HTailF2) (funs : Array HFun) :
    rowsAff (blank u tl) funs = rowsAff tl funs := rfl

/-- Where the reader answers. -/
theorem small_there (s : S) (R : K9.Read) (h : K9.smallReader s = some R) :
    ∃ tl funs, s.tl? = some tl ∧ s.funs? = some funs ∧ R = ⟨rowsAff tl funs, []⟩ := by
  unfold K9.smallReader at h
  cases ht : s.tl? with
  | none =>
    rw [ht] at h
    exact nomatch h
  | some tl =>
    cases hf : s.funs? with
    | none =>
      rw [ht, hf] at h
      exact nomatch h
    | some funs =>
      rw [ht, hf] at h
      exact ⟨tl, funs, rfl, rfl, (Option.some.inj h).symm⟩

/-- A form whose arrays the segment's list names has one worth in the two worlds. -/
theorem value_own (b : K9.Part) (late : List (ℕ × E × E)) (D : Bound GQ) (f : Aff)
    (h : ∀ x ∈ f.ents.toList, (b.L.arrayOf[x.tree]?).isSome = true) :
    f.value Reading.gl (worldOwn b late D) =
      f.value Reading.gl (ownWorld (cellsA b.L.arrayOf D) (worldOwn b late D).slot) := by
  refine value_eq _ _ f (fun x hx => ?_) fun _ _ => rfl
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x hx)
  show (match b.L.arrayOf[x.tree]? with
    | some c => D.cell c.1 c.2 x.row x.idx
    | none => 0) = cellsA b.L.arrayOf D x.tree x.row x.idx
  unfold cellsA
  rw [hy, Array.getD_eq_getD_getElem?, hy]
  rfl

/-- **THE CLAUSE AT "K8.equations".** -/
theorem item_small (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hn : o.2 = "K8.equations")
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L o run) (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (tm4 : ℕ → α × Option Pub9 → Bound GE8 → List (ℕ × GE8))
    (v4 : α × Option Pub9 → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (ht : tmOf o = fun n q y => tm4 n q y ++ tmRest π q y)
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hin : K9.formsIn (K9.readersOfLink (K9.withSmall H) L) own o.1 o.2 a.1 = true) :
    ItemIn L φ tmOf lenOf (K9.readersOfLink (K9.withSmall H) L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  have hR' : K9.smallReader a.1 = some R := by
    rw [← hR, hn]
    exact (K9.forms_small H L o.1 a.1).symm
  obtain ⟨tl, funs, htl, hfu, rfl⟩ := small_there a.1 R hR'
  have he := named_of_formsIn _ own o.1 o.2 a.1 b _ hb hR hin
  have hq : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hp : π (fixed9 φ a.1).1 = (some (blank u tl), some funs) := by
    show π (φ a.1) = _
    rw [hπ, htl, hfu]
    rfl
  refine ⟨b, _, [(⟨(o.2, run), tmOf o, lenOf o⟩, fun q y => v4 q y ++ (tmRest π q y).map (·.2))],
    hb, ?_, hR, hin, fun f hf => ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht, List.map_append, h4]
  · refine List.mem_flatMap.2 ⟨_, List.mem_singleton.2 rfl, List.mem_append_right _ ?_⟩
    have e : (tmRest π (fixed9 φ a.1) (dataQ own b (rdW w))).map (·.2) =
        (rowsAff tl funs).map fun g => g.value Reading.gl
          (ownWorld (cellsA b.L.arrayOf (dataQ own b (rdW w)))
            (worldOwn b [] (dataQ own b (rdW w))).slot) := by
      simp only [tmRest, hp, hq]
      rw [List.map_map, ← rowsAff_blank u tl funs,
        rowsAff_values Reading.gl _ _ (blank u tl) funs (pubOf b).F.planClaimsF]
      rfl
    rw [e, value_own b [] _ f (he f hf)]
    exact List.mem_map.2 ⟨f, hf, rfl⟩

section
variable {β : Type}

/-- **At a layers' link.** -/
theorem item_small_layers (H : K9.LinkHoles) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (p : OnBytes.Desc.First.K4.Par) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (k : ℕ) (ho : (k, "K8.equations") ∈ L.order)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (k, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hin : K9.formsIn (K9.readersOfLink (K9.withSmall H) L) own k "K8.equations" a.1 = true) :
    ItemIn L (phiAll u ψ) (tmL p ent tm4 t3) (lenL p l3) (K9.readersOfLink (K9.withSmall H) L) own
      rdW a w (k, "K8.equations") :=
  item_small H L _ _ _ own rdW (k, "K8.equations") ho rfl run hAt u pi8 (fun _ => rfl) tm4 v4 h4 rfl
    a w b hb hin

/-- **At an attention link.** -/
theorem item_small_attention (H : K9.LinkHoles) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (rd : _) (c : _) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (k : ℕ) (ho : (k, "K8.equations") ∈ L.order)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (k, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hin : K9.formsIn (K9.readersOfLink (K9.withSmall H) L) own k "K8.equations" a.1 = true) :
    ItemIn L (phiAll u ψ) (tmA rd c ent tm4 t3) (lenA rd c l3)
      (K9.readersOfLink (K9.withSmall H) L) own rdW a w (k, "K8.equations") :=
  item_small H L _ _ _ own rdW (k, "K8.equations") ho rfl run hAt u pi8 (fun _ => rfl) tm4 v4 h4 rfl
    a w b hb hin

/-- **At the head's link.** -/
theorem item_small_head (H : K9.LinkHoles) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (h : _) (iU3 : ℕ) (p : _) (kap : _) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (k : ℕ) (ho : (k, "K8.equations") ∈ L.order)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (k, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hin : K9.formsIn (K9.readersOfLink (K9.withSmall H) L) own k "K8.equations" a.1 = true) :
    ItemIn L (phiAll u ψ) (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3)
      (K9.readersOfLink (K9.withSmall H) L) own rdW a w (k, "K8.equations") :=
  item_small H L _ _ _ own rdW (k, "K8.equations") ho rfl run hAt u pi8 (fun _ => rfl) tm4 v4 h4 rfl
    a w b hb hin

end

/-- The run's first four claims bear no number of an equation. -/
theorem four8_plain (tl : HTailF2) (g : Forest.Heard) : ∀ c ∈ four8 tl g, c.eqFirst = none := by
  intro c hc
  simp only [four8, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsAff_blank
#print axioms VerifiableInference.Desc.LinkJoin.small_there
#print axioms VerifiableInference.Desc.LinkJoin.value_own
#print axioms VerifiableInference.Desc.LinkJoin.item_small
#print axioms VerifiableInference.Desc.LinkJoin.item_small_layers
#print axioms VerifiableInference.Desc.LinkJoin.item_small_attention
#print axioms VerifiableInference.Desc.LinkJoin.item_small_head
#print axioms VerifiableInference.Desc.LinkJoin.four8_plain
