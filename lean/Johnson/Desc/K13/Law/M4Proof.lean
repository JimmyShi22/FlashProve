-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/M4Proof.lean: the proof of the law of Johnson/Desc/K13/Law/M4Law.lean.
Main names:
  `rowsB_ok`: where the block says yes, at any lens. `get_mem`: what the lens at the first chain's
    state hands to the kind.
  `evalIn_withRow`, `mem_withRow`: an open row more leaves the tables; it is among the group's rows.
  `rowsB_back`: the law. No file of this tree calls it; `rowsB_core`
    (Johnson/Desc/K13/Law/AtM4.lean) is the form that other files call.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/M4.lean names.

What is not claimed. What Johnson/Desc/K13/Law/M4Law.lean says is not claimed. The premise: the pin
is carried back over the piece (`back_of_reads`, Johnson/Desc/K13/Law/Pin.lean, gives it for a pin
that reads the stored table and the trees sent in front alone).
`WIs` is given by no law yet.

-/
import Johnson.Desc.K13.Law.M4Tries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Maker
open OnBytes.Means (Words Says RowIn)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- Where the block behind W's commitment says yes, at any lens. -/
theorem rowsB_ok {T : Type} (X : Lens T) (P : Where) {t t' : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ (p : Part) (l : LinFirst) (o : LinFirst × St), X.get? t = some p ∧ p.lin = some l ∧
      rows P.lin l.claim p.ids p.d = .ok o ∧ t' = X.set t { p with lin := some o.1, d := o.2 } := by
  simp only [rowsB, still, bind_ok, there_ok, pure_ok, Lens.part] at h
  obtain ⟨p, hp, l, hl, o, ho, rfl⟩ := h
  exact ⟨p, l, o, hp, hl, ho, rfl⟩

/-- What the lens at the first chain's state hands to the kind. -/
theorem get_mem {s : S} {p : Part} (h : atS.get? s = some p) :
    ∃ a, s.here = .mem a ∧ p.lin = a.lin ∧ p.ids = a.ids ∧ p.d = dOf s := by
  cases hs : s.here with
  | mem a =>
    simp only [atS, hs] at h
    obtain rfl := Option.some.inj h
    exact ⟨a, rfl, rfl, rfl, rfl⟩
  | between =>
    have e : atS.get? s = none := by simp only [atS, hs]
    rw [e] at h
    cases h
  | lay a =>
    have e : atS.get? s = none := by simp only [atS, hs]
    rw [e] at h
    cases h
  | att a =>
    have e : atS.get? s = none := by simp only [atS, hs]
    rw [e] at h
    cases h
  | head a =>
    have e : atS.get? s = none := by simp only [atS, hs]
    rw [e] at h
    cases h
  | fin a =>
    have e : atS.get? s = none := by simp only [atS, hs]
    rw [e] at h
    cases h

/-- An open row more leaves the tables as they are. -/
theorem evalIn_withRow {St : Statement} {w : ℕ} {lay : VectorLay} {masks : MaskForm} (g : ℕ)
    (r : OnBytes.Row) (h : EvalIn St w lay masks) : EvalIn (withRow St g r) w lay masks :=
  ⟨h.there, h.size, h.masks⟩

/-- The row that is added is among the group's open rows. -/
theorem mem_withRow {St : Statement} {g : ℕ} {G : Group} (r : OnBytes.Row)
    (h : St.groups[g]? = some G) :
    ∃ G', (withRow St g r).groups[g]? = some G' ∧ r ∈ G'.rows.toList := by
  refine ⟨{ G with rows := G.rows.push r }, ?_, by simp⟩
  show (St.groups.modify g fun G => { G with rows := G.rows.push r })[g]? = _
  rw [Array.getElem?_modify, if_pos rfl, h]
  rfl

/-- **The law.** -/
theorem rowsB_back : Spec.rowsB_back := by
  intro Cl W nR F P base rwM rwW Pin hback a hon
  show ∀ b, _ = some b → _
  intro b hb
  refine ⟨trivial, fun w hw => ⟨hback a () b w hb hw.1, ?_⟩⟩
  obtain ⟨gs, hdec⟩ := quiet_ok hb
  obtain ⟨p, l, o, hp, hl, hrows, hb1⟩ := rowsB_ok atS P hdec
  obtain ⟨m₀, hs, h1, h2, h3⟩ := get_mem hp
  have hlin : linAt a.1 = some l := by
    unfold linAt
    rw [hs]
    show m₀.lin = some l
    rw [← h1, hl]
  obtain ⟨⟨row, hrow⟩, hbits⟩ := hon l hlin
  rw [h3] at hrows
  obtain ⟨d₃, r, G, hc, _, hr, hG, hin, hst, hcodes⟩ := rows_ok hrows
  have hset : b.1 = { a.1 with st := o.2.st, rowsOwed := p.owed,
                               here := .mem ⟨p.msg, p.ids, some o.1⟩ } := by
    rw [hb1]
    simp only [atS, hs]
  have hbst : b.1.st = o.2.st := by rw [hset]
  have hblin : linAt b.1 = some o.1 := by rw [hset]; rfl
  have hbc : b.1.st.codes = a.1.st.codes := by rw [hbst, hcodes]; rfl
  rw [hrow] at hr
  have hr' : linEvalRow P.lin (memberClaim row) o.1.w (linLayW a.1.st.codes P.lin) = some r := hr
  obtain ⟨hlen, hform⟩ := linEvalRow_inv P.lin _ _ _ r hr'
  have hE : EvalIn b.1.st o.1.w (linLayW a.1.st.codes P.lin) row.masks := by
    rw [hbst, hst]
    refine evalIn_withRow _ _ (evalIn_of_rowIn (G := G) ?_ ?_)
    · have : row.psi.length = P.lin.kCol := hlen
      rw [this]
      exact hbits
    · rw [← hform]
      exact hin
  have hS : Says ρg b.1.st r (rwW w) := by
    obtain ⟨G', hG', hmem⟩ := mem_withRow r hG
    rw [← hst, ← hbst] at hG'
    exact hw.2.1.rows _ G' hG' r hmem
  have hW := hw.2.2 o.1 hblin
  rw [hc, hrow, hbc] at hW
  have hH := (eval_back nR P.lin row o.1.w _ r b.1.st (rwW w) (rwM w) hbits hr' hE hW).1 hS
  intro r' hr''
  have hrows' : a.1.rows = [row] := by
    unfold S.rows
    rw [hs]
    have : m₀.lin = some l := by rw [← h1, hl]
    simp only [this, hrow, rowOfClaim_member]
  rw [hrows'] at hr''
  rw [List.mem_singleton.1 hr'']
  exact hH

end VerifiableInference.Desc.K13.Law
