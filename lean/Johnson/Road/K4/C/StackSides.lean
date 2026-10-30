-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackSides.lean: CONDITIONAL.

Not shown here. THAT THE PANELS, THE CHALLENGES AND THE TWO WEIGHTS AT WHICH THE HONEST SIDE MAKES
ITS END VALUES (StackData.bl, the list rs, StackData.om) ARE THE VERIFIER's AT A RUN: the
verifier's call of stackEnd is asked at these letters (hfin). That the two forms name no slot (hA,
hB): the library's stackEnd_slots (Johnson/Road/K4/Slots/Panels.lean) gives it for placed panels of
the verifier's making; it is not called here. All that StackVal.lean leaves open. No example is
known. No property is claimed.

THE TWO SIDES' END VALUES OF THE BATCHED SUMCHECK ARE THE WORTHS OF THE VERIFIER's TWO FORMS. At
its end the verifier makes two forms in the reads, Alin and Blin (stackEnd,
OnBytes/Model/LayerPanels.lean), and claims that the two sides' shown values equal them. The honest
side of the sub-protocol K4 makes the same call with zeros in the place of the shown values and
values the two forms on its reads (StackData.endsAt, Johnson/Desc/K4/Honest/Stack.lean). A form is
worth x in a world: Aff.value gives x.

  LinEq          two states of stackEnd's loop have the same two forms and the same number wD.
  stackEndOf_lin, stackEnd_lin   the two forms do not read the shown values.
  endsAt_open    the honest side's end values, opened: the first, and the one behind the never-sent
                 vectors' values.
  sides_read     these two are the worths of the verifier's Alin and Blin at the true entries.
-/
import Johnson.Road.K4.C.StackVal
import Johnson.Desc.First.K4.Returns.Pub.End

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Env SBlk StackEnd stackEndOf stackEnd TableAsk TableAt layTables
  tableAsks funsOf matIx)
open OnBytes.Flat (OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.RtPub (optRel_iteB foldlM_opt_rel OptRel.of_left)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In StackData matsOf readsAt)
open OnBytes.Road.K4 (entryOf)

/-- Two states of stackEnd's loop have the same two forms and the same number wD. -/
structure LinEq (s s₀ : StackEnd) : Prop where
  A : s.Alin = s₀.Alin
  B : s.Blin = s₀.Blin
  w : s.wD = s₀.wD

/-- **One panel's step: the two forms do not read the shown values.** -/
theorem stackEndOf_lin (y : Lay) (rs : Array E) (lam : ℕ) (om H1 V H1₀ V₀ : Array E)
    {s s₀ : StackEnd} (b : SBlk) (hs : LinEq s s₀) :
    OptRel LinEq (stackEndOf y rs lam om H1 V s b) (stackEndOf y rs lam om H1₀ V₀ s₀ b) := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  unfold stackEndOf
  cases tri with
  | true =>
    cases virt with
    | some k =>
      simp only [↓reduceIte]
      exact optRel_iteB rfl trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_iteB rfl trivial (LinEq.mk hs.A hs.B hs.w))
    | none =>
      simp only [↓reduceIte]
      refine optRel_iteB rfl trivial (optRel_bind_same fun _ => optRel_bind_same fun _ => ?_)
      exact LinEq.mk (by
        show (List.range ny).foldl _ s.Alin = (List.range ny).foldl _ s₀.Alin
        rw [hs.A]) hs.B hs.w
  | false =>
    cases virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact optRel_iteB rfl trivial (optRel_bind_same fun _ => optRel_bind_same fun _ =>
        optRel_iteB (by rw [hs.w]) trivial (LinEq.mk hs.A hs.B rfl))
    | none =>
      cases v0 with
      | some v0 =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine optRel_iteB rfl trivial (optRel_bind_same fun _ => optRel_bind_same fun f => ?_)
        refine foldlM_opt_rel (R := LinEq) (fun a a₀ i ha => ?_) _ _ _ hs
        refine optRel_bind (S := LinEq) ?_ fun c c₀ hc => ?_
        · refine foldlM_opt_rel (R := LinEq) (fun c c₀ yv hc => ?_) _ _ _ ha
          refine optRel_bind_same fun x => ?_
          exact LinEq.mk (by
            show c.Alin.addMul x _ = c₀.Alin.addMul x _
            rw [hc.A]) hc.B hc.w
        · exact LinEq.mk hc.A hc.B hc.w
      | none =>
        cases B with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine optRel_iteB rfl trivial (optRel_bind_same fun _ => optRel_bind_same fun f => ?_)
          refine foldlM_opt_rel (R := LinEq) (fun a a₀ i ha => ?_) _ _ _ hs
          refine optRel_bind (S := LinEq) ?_ fun c c₀ hc => hc
          refine foldlM_opt_rel (R := LinEq) (fun c c₀ yv hc => ?_) _ _ _ ha
          exact optRel_bind_same fun _ => trivial
        | some g =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine optRel_iteB rfl trivial (optRel_bind_same fun _ => optRel_bind_same fun f => ?_)
          refine foldlM_opt_rel (R := LinEq) (fun a a₀ i ha => ?_) _ _ _ hs
          refine optRel_bind (S := LinEq) ?_ fun c c₀ hc => hc
          refine foldlM_opt_rel (R := LinEq) (fun c c₀ yv hc => ?_) _ _ _ ha
          refine optRel_bind_same fun x => optRel_bind_same fun z => ?_
          exact LinEq.mk (by
            show c.Alin.addMul x _ = c₀.Alin.addMul x _
            rw [hc.A]) (by
            show c.Blin.addMul z _ = c₀.Blin.addMul z _
            rw [hc.B]) hc.w

/-- **The end over all panels: the two forms do not read the shown values.** -/
theorem stackEnd_lin {y : Lay} {bl : Array SBlk} {rs : Array E} {lam : ℕ}
    {om H1 V H1₀ V₀ : Array E} {a b a₀ b₀ : E} {s s₀ : StackEnd}
    (h : stackEnd y bl rs lam om H1 V a b = some s)
    (h₀ : stackEnd y bl rs lam om H1₀ V₀ a₀ b₀ = some s₀) :
    s.Alin = s₀.Alin ∧ s.Blin = s₀.Blin := by
  have key : OptRel LinEq (bl.foldlM (stackEndOf y rs lam om H1 V) { As := a, Bs := b })
      (bl.foldlM (stackEndOf y rs lam om H1₀ V₀) { As := a₀, Bs := b₀ }) := by
    rw [← Array.foldlM_toList, ← Array.foldlM_toList]
    exact foldlM_opt_rel (fun _ _ x hs => stackEndOf_lin y rs lam om H1 V H1₀ V₀ x hs) _ _ _
      (LinEq.mk rfl rfl rfl)
  have all : OptRel LinEq (stackEnd y bl rs lam om H1 V a b)
      (stackEnd y bl rs lam om H1₀ V₀ a₀ b₀) := by
    unfold stackEnd
    refine optRel_bind key fun t t₀ ht => ?_
    exact optRel_iteB (by rw [ht.w]) trivial ht
  rw [h, h₀] at all
  have e : LinEq s s₀ := all
  exact ⟨e.A, e.B⟩

/-- **The honest side's end values, opened.** -/
theorem endsAt_open {D : StackData} {rs : Array E} {l : List E} (h : D.endsAt rs = some l) :
    ∃ fin A0 B0, stackEnd D.S.v.y D.bl rs D.S.Q.hp.lamS D.om (Array.replicate D.nVirt zeroE)
        (Array.replicate D.S.opens.size zeroE) zeroE zeroE = some fin ∧
      D.val fin.Alin = some A0 ∧ D.val fin.Blin = some B0 ∧ l.getD 0 zeroE = A0 ∧
      l.getD (2 + D.S.v.y.LamM) zeroE = B0 := by
  unfold StackData.endsAt at h
  dsimp only at h
  obtain ⟨fin, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨A0, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨B0, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dn, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  refine ⟨fin, A0, B0, h1, h2, h3, rfl, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
  simp

/-- **The two sides' end values are the worths of the verifier's two forms at the true entries.** l:
the honest side's end values at the challenges rs; fin: what the verifier's call of stackEnd returns
at any shown values H1, V, a, b. -/
theorem sides_read {Q : K4Pub} {w : K4In} {fo fo' : Forest.Heard}
    {pt pts : List (String × Array E)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    {tl : HTailF2} {Mm : Mats Cb.Gl.E} {G : ℕ → Prop} {funs : Array HFun} {D : StackData}
    (hR : readsAt Q w fo pt = some D.R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart pt pts)
    (hfo : (∀ i, G i → i ≠ (matIx Q.P.y).iB) ∨ fo' = fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf Q) w.cell Mm) {rs : Array E} {l : List E}
    (h : D.endsAt rs = some l) {H1 V : Array E} {a b : E} {fin : StackEnd}
    (hfin : stackEnd D.S.v.y D.bl rs D.S.Q.hp.lamS D.om H1 V a b = some fin) {W : World Cb.Gl.E}
    (hW : W.entry = entryOf Reading.gl tl funs D.S.v.iU3 D.S.v.K3 Mm)
    (hA : ∀ s ∈ fin.Alin.slots.toList, False) (hB : ∀ s ∈ fin.Blin.slots.toList, False)
    (hGA : ∀ e ∈ fin.Alin.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (e.row * D.S.v.K3 + e.idx) → G z.1.mat)
    (hGB : ∀ e ∈ fin.Blin.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (e.row * D.S.v.K3 + e.idx) → G z.1.mat) :
    Reading.gl.val (l.getD 0 zeroE) = fin.Alin.value Reading.gl W ∧
      Reading.gl.val (l.getD (2 + D.S.v.y.LamM) zeroE) = fin.Blin.value Reading.gl W := by
  obtain ⟨fin0, A0, B0, h1, h2, h3, e1, e2⟩ := endsAt_open h
  obtain ⟨eA, eB⟩ := stackEnd_lin h1 hfin
  rw [eA] at h2
  rw [eB] at h3
  rw [e1, e2]
  exact ⟨val_true hR hl hf hp hfo hm hNM hC h2 hW (fun s hs => (hA s hs).elim) hGA,
    val_true hR hl hf hp hfo hm hNM hC h3 hW (fun s hs => (hB s hs).elim) hGB⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.stackEndOf_lin
#print axioms OnBytes.Road.K4.C.stackEnd_lin
#print axioms OnBytes.Road.K4.C.endsAt_open
#print axioms OnBytes.Road.K4.C.sides_read
