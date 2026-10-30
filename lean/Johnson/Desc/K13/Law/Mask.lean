-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Mask.lean: which numbers kind K13's text behind W's commitment lays as W's
number and as the number of the first fold's mask (`LinFirst.w`, `LinFirst.mask`). The statement, a
planted copy that fails it, and the proofs.

The text (Johnson/Desc/K13/Text.lean: `rows`) takes both off the numbers that W's commitment has
handed on (ids): W is the first; the mask, where the shape says that masks go ahead, is the last;
else there is none. It receives no message. So where the numbers handed on are those of the
statement's last messages, in order, the mask is the statement's last message behind the text, and W
stands as many places from the end as numbers were handed on.
Main names:
  `MaskLaw f`: the form of the law, of any text f in the place of `rows`.
  `rowsPlantM`: a copy that lays another number for the mask.
  `Spec.plantM_fails`: wherever `rows` answers at all, the planted copy does not meet the form.
  `rows_mask`: the text meets it.
  `IdsLast ids St`: the numbers handed on are those of the statement's last messages, in order.
  `rows_mask_at`: under it, by position. `rowsB_mask`: the same of the block, at the first chain's
    state.
Used of `verify-on-bytes`: `withMessageInGroup`, `withRow`, as pure functions. Of the ground: `newGroupP`,
`joinP`, `addRowsP`.

What is not claimed. `IdsLast`: that W's commitment hands on the numbers of the messages that it has
just received, and that no block between receives a message: a premise. That the message at the
mask's number is a mask (not sampled, counts no answer, not spent, no member): the text asks none of
these. Where the shape wants a split's message, three numbers are handed on, and W stands three
places from the end. That `rows` answers somewhere: runs on honest files show it, not this file.
Nothing on soundness. The shape is the one that the text is handed: that it is the shape by which a
later chain's start asks whether masks go ahead is said by no law.

-/
import Johnson.Desc.K13.Law.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Ground (newGroupP joinP addRowsP)
open VerifiableInference.Desc.First (S)

/-- **The form of the law**: W's number is the first that was handed on; the mask's is the last,
where masks go ahead, and else there is none; no message is received. -/
def MaskLaw (f : LinShape → LinClaim → Array ℕ → St → Ans (LinFirst × St)) : Prop :=
  ∀ Sh claim ids d o, f Sh claim ids d = .ok o →
    ids[0]? = some o.1.w ∧
    (if Sh.masksAhead then ids.back?.map some else some none) = some o.1.mask ∧
    o.2.st.oracles.size = d.st.oracles.size

/-- A planted copy: as `rows`, but another number is laid for the mask. -/
def rowsPlantM (Sh : LinShape) (claim : LinClaim) (ids : Array ℕ) (d : St) :
    Ans (LinFirst × St) :=
  (rows Sh claim ids d).map fun o =>
    ({ o.1 with mask := match o.1.mask with | none => some 0 | some m => some (m + 1) }, o.2)

/-- Wherever `rows` answers at all, the planted copy does not meet the form. -/
def Spec.plantM_fails : Prop :=
  ∀ Sh claim ids d o, rows Sh claim ids d = .ok o → ¬ MaskLaw rowsPlantM

/-- The text meets the form. -/
def Spec.rows_mask : Prop := MaskLaw rows

/-- The numbers handed on are those of the statement's last messages, in order. -/
def IdsLast (ids : Array ℕ) (St : Statement) : Prop :=
  ids.size ≤ St.oracles.size ∧ ∀ i, i < ids.size → ids[i]? = some (St.oracles.size - ids.size + i)

/-- A new group receives no message. -/
theorem newGroup_osize {d : St} {c z : ℕ} {b : ℕ × St} (h : newGroupP d c z = some b) :
    b.2.st.oracles.size = d.st.oracles.size := by
  unfold newGroupP at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- Nor does a joining. -/
theorem join_osize {d d' : St} {g o : ℕ} {kept : Bool} (h : joinP d g o kept = some d') :
    d'.st.oracles.size = d.st.oracles.size := by
  unfold joinP at h
  split at h
  · cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G =>
      rw [hG] at h
      obtain rfl := Option.some.inj h
      exact Array.size_modify
  · cases h

/-- Nor do joinings in a row. -/
theorem joinAll_osize (g : ℕ) : ∀ (l : List ℕ) (d d' : St), joinAll g l d = .ok d' →
    d'.st.oracles.size = d.st.oracles.size
  | [], d, d', h => by rw [pure_ok.1 h]
  | o :: l, d, d', h => by
    simp only [joinAll, bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    rw [joinAll_osize g l d₁ d' h2, join_osize h1]

/-- **The text meets the form.** -/
theorem rows_mask : Spec.rows_mask := by
  intro Sh claim ids d o h
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, hw, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, hm, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨_, _, _, hst⟩ := addRows_one h4
  have e2 : d₂.st.oracles.size = d.st.oracles.size := by
    rw [join_osize h2, joinAll_osize _ _ _ _ h1, newGroup_osize hb]
  have e3 : d₃.st.oracles.size = d.st.oracles.size := by
    split at h3
    · rw [join_osize h3, e2]
    · rw [← Option.some.inj h3, e2]
  refine ⟨hw, hm, ?_⟩
  show d₄.st.oracles.size = d.st.oracles.size
  rw [hst]
  exact e3

/-- Wherever `rows` answers at all, the planted copy does not meet the form. -/
theorem plantM_fails : Spec.plantM_fails := by
  intro Sh claim ids d o h hlaw
  have h1 := (rows_mask Sh claim ids d o h).2.1
  have hp : rowsPlantM Sh claim ids d = .ok ({ o.1 with
      mask := match o.1.mask with | none => some 0 | some m => some (m + 1) }, o.2) := by
    unfold rowsPlantM
    rw [h]
    rfl
  have h2 := (hlaw _ _ _ _ _ hp).2.1
  rw [h1] at h2
  have h3 : o.1.mask = match o.1.mask with | none => some 0 | some m => some (m + 1) :=
    Option.some.inj h2
  cases hm : o.1.mask with
  | none =>
    rw [hm] at h3
    cases h3
  | some m =>
    rw [hm] at h3
    have := Option.some.inj h3
    omega

/-- **By position**: where the numbers handed on are those of the statement's last messages, in
order. -/
theorem rows_mask_at {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (hI : IdsLast ids d.st) (h : rows Sh claim ids d = .ok o) :
    o.1.w = o.2.st.oracles.size - ids.size ∧
      (Sh.masksAhead = true → o.1.mask = some (o.2.st.oracles.size - 1)) ∧
      (Sh.masksAhead = false → o.1.mask = none) := by
  obtain ⟨hw, hm, hs⟩ := rows_mask Sh claim ids d o h
  have h0 : 0 < ids.size := by
    by_contra hc
    have e : ids[0]? = none := Array.getElem?_eq_none (by omega)
    rw [e] at hw
    cases hw
  refine ⟨?_, fun ha => ?_, fun ha => ?_⟩
  · have e := hI.2 0 h0
    rw [hw] at e
    rw [Option.some.inj e, hs]
    omega
  · rw [if_pos ha] at hm
    have e : ids.back? = some (d.st.oracles.size - ids.size + (ids.size - 1)) :=
      hI.2 (ids.size - 1) (by omega)
    rw [e] at hm
    have e2 : some (d.st.oracles.size - ids.size + (ids.size - 1)) = o.1.mask :=
      Option.some.inj hm
    rw [← e2, hs]
    have := hI.1
    exact congrArg some (by omega)
  · rw [if_neg (by rw [ha]; exact Bool.false_ne_true)] at hm
    exact (Option.some.inj hm).symm

/-- **The same of the block**, at the first chain's state. -/
theorem rowsB_mask {Cl : Type} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s') :
    ∃ m₀ l, s.here = .mem m₀ ∧ linAt s' = some l ∧ (IdsLast m₀.ids s.st →
      l.w = s'.st.oracles.size - m₀.ids.size ∧
        (P.lin.masksAhead = true → l.mask = some (s'.st.oracles.size - 1)) ∧
        (P.lin.masksAhead = false → l.mask = none)) := by
  obtain ⟨m₀, l, o, owed, hs, _, hrows, rfl⟩ := rowsB_at h
  exact ⟨m₀, o.1, hs, rfl, fun hI => rows_mask_at hI hrows⟩

end VerifiableInference.Desc.K13.Law
