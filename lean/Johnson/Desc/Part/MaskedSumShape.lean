-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumShape.lean: the part "the masked sumcheck": what its reading of the rounds
asks, as statements. Theorems on readAll and hear of Part/MaskedSum4.lean. Core Lean alone; no
arithmetic of the field occurs.

Main names:
  `Sent r n k s d`: the round r holds just the n scalars s and drew just the k elements d.
  `VarsRead vs used l`: the rounds used are the variables' rounds, one each: d - 1 scalars and one
    element.
  `varRounds_spec`, `readAll_spec`: where the reading returns (a call with end values), the rounds
    are first :: used ++ [rY, rv], with what each holds.
  `Fit e r`: the round r holds as many scalars, and drew as many elements, as the entry e says.
  `readAll_fits`: where the reading returns, the rounds are the call's entries, entry for entry.
  `hear_spec`: where the hearing returns: shapeOk; the start form's public part; the reading; every
    field of what it hands back; the write.

Limits: one direction, from a return. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes
open OnBytes.Model (Aff Fork)

/-- The round holds just the n scalars s and drew just the k elements d. -/
def Sent (r : Fmt.RoundView) (n k : Nat) (s d : List E) : Prop :=
  scalars r.vals = some s ∧ s.length = n ∧ r.drawn.elems.length = k ∧ d = r.drawn.elems.map E.ofTriple

theorem roundOf_spec {n k : Nat} {r : Fmt.RoundView} {s d : List E} (h : roundOf n k r = some (s, d)) :
    Sent r n k s d := by
  unfold roundOf at h
  cases hs : scalars r.vals with
  | none => simp [hs] at h
  | some s' =>
    simp only [hs, Option.bind_some] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      subst e1
      exact ⟨hs, hc.1, hc.2, e2.symm⟩
    · cases h

/-- The variables' rounds, one each. -/
def VarsRead : List Var → List Fmt.RoundView → List (List E × E) → Prop
  | [], [], [] => True
  | v :: vs, r :: rs, (s, g) :: l => Sent r (v.d - 1) 1 s [g] ∧ VarsRead vs rs l
  | _, _, _ => False

theorem varRounds_spec : ∀ (vs : List Var) (rs : List Fmt.RoundView) (l : List (List E × E)) (rest : List Fmt.RoundView),
    varRounds vs rs = some (l, rest) → ∃ used, rs = used ++ rest ∧ VarsRead vs used l
  | [], rs, l, rest, h => by
    simp only [varRounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, e2⟩ := h
    subst e1 e2
    exact ⟨[], rfl, trivial⟩
  | _ :: _, [], _, _, h => by simp [varRounds] at h
  | v :: vs, r :: rs, l, rest, h => by
    unfold varRounds at h
    split at h
    · rename_i s g l' rest' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2⟩ := h
      subst e1 e2
      obtain ⟨used, a1, a2⟩ := varRounds_spec vs rs l' rest' h2
      exact ⟨r :: used, by rw [a1]; rfl, roundOf_spec h1, a2⟩
    · cases h

theorem VarsRead.length : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead vs used l → used.length = vs.length ∧ l.length = vs.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, (_, _) :: _, h => by
    obtain ⟨a, b⟩ := VarsRead.length h.2
    exact ⟨by simp [a], by simp [b]⟩
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- Where the reading of a call with ends returns. -/
theorem readAll_spec {lead : Nat} {vs : List Var} {e : Ends} {rs : List Fmt.RoundView} {R : Read}
    (h : readAll ⟨lead, vs, some e⟩ rs = some R) :
    ∃ (r0 : Fmt.RoundView) (used : List Fmt.RoundView) (rv : Fmt.RoundView) (front : List E),
      rs = r0 :: (used ++ [rv]) ∧ Sent r0 (lead + 1) 1 (front ++ [R.mu]) [R.eps] ∧ front.length = lead ∧
      VarsRead (vs ++ [.point zeroE (e.dY + 1)]) used R.rounds ∧ Sent rv e.n 0 R.values [] := by
  unfold readAll at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    simp only at h
    split at h
    · rename_i h3
      cases h3
    · rename_i x mu eps l rv e' h1 h2 h3
      cases h3
      cases hq : roundOf e.n 0 rv with
      | none => simp [hq] at h
      | some y =>
        simp only [hq, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨used, a1, a2⟩ := varRounds_spec _ _ _ _ h2
        unfold firstRound at h1
        cases hf : roundOf (lead + 1) 1 r with
        | none => simp [hf] at h1
        | some z =>
          simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨_, b2, b3⟩ := h1
          obtain ⟨z1, z2⟩ := z
          obtain ⟨y1, y2⟩ := y
          have sf := roundOf_spec hf
          have sv := roundOf_spec hq
          simp only at b2 b3
          subst b3
          refine ⟨r, used, rv, z1.take lead, by rw [a1], ?_, ?_, a2, ?_⟩
          · have : z1.take lead ++ [mu] = z1 := by rw [← b2]; exact List.take_append_drop _ _
            rw [this]
            exact sf
          · rw [List.length_take, sf.2.1]; omega
          · obtain ⟨c1, c2, c3, c4⟩ := sv
            refine ⟨c1, c2, c3, ?_⟩
            have : rv.drawn.elems = [] := List.eq_nil_of_length_eq_zero c3
            rw [this]; rfl
    · cases h

/-- The round holds as many scalars, and drew as many elements, as the entry says. -/
def Fit (e : Fmt.Entry) (r : Fmt.RoundView) : Prop :=
  (∃ s, scalars r.vals = some s ∧ e.msg = 24 * s.length) ∧ r.drawn.elems.length = e.drawE

/-- Round for round. -/
def Fits : List Fmt.Entry → List Fmt.RoundView → Prop
  | [], [] => True
  | e :: es, r :: rs => Fit e r ∧ Fits es rs
  | _, _ => False

theorem Fits.append : ∀ {a b : List Fmt.Entry} {x y : List Fmt.RoundView}, Fits a x → Fits b y → Fits (a ++ b) (x ++ y)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h1, h2 => ⟨h1.1, Fits.append h1.2 h2⟩
  | [], _, _ :: _, _, h1, _ => h1.elim
  | _ :: _, _, [], _, h1, _ => h1.elim

theorem Fits.length : ∀ {a : List Fmt.Entry} {x : List Fmt.RoundView}, Fits a x → x.length = a.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Fits.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Sent.fit {r : Fmt.RoundView} {n k : Nat} {s d : List E} (h : Sent r n k s d) (name : String) (nz : Nat) :
    Fit (entry name n k nz) r :=
  ⟨⟨s, h.1, by rw [h.2.1]; rfl⟩, h.2.2.1⟩

theorem VarsRead.fits : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)}, VarsRead vs used l →
    Fits (vs.map fun v => entry "PSC round" (v.d - 1) 1 0) used
  | [], [], [], _ => trivial
  | _ :: _, _ :: _, (_, _) :: _, h => ⟨h.1.fit _ _, VarsRead.fits h.2⟩
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- The variables' rounds, cut behind the first list. -/
theorem VarsRead.split : ∀ {vs ws : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead (vs ++ ws) used l → ∃ u1 u2 l1 l2, used = u1 ++ u2 ∧ l = l1 ++ l2 ∧ VarsRead vs u1 l1 ∧ VarsRead ws u2 l2
  | [], _, used, l, h => ⟨[], used, [], l, rfl, rfl, trivial, h⟩
  | _ :: _, _, r :: _, (s, g) :: _, h => by
    obtain ⟨u1, u2, l1, l2, a1, a2, a3, a4⟩ := VarsRead.split h.2
    exact ⟨r :: u1, u2, (s, g) :: l1, l2, by rw [a1]; rfl, by rw [a2]; rfl, ⟨h.1, a3⟩, a4⟩
  | _ :: _, _, [], _, h => h.elim
  | _ :: _, _, _ :: _, [], h => h.elim

theorem VarsRead.one {v : Var} {used : List Fmt.RoundView} {l : List (List E × E)} (h : VarsRead [v] used l) :
    ∃ r s g, used = [r] ∧ l = [(s, g)] ∧ Sent r (v.d - 1) 1 s [g] := by
  match used, l, h with
  | [r], [(s, g)], h => exact ⟨r, s, g, rfl, rfl, h.1⟩
  | _ :: _ :: _, (_, _) :: _, h => exact h.2.elim
  | [_], (_, _) :: _ :: _, h => exact h.2.elim

/-- **Where the reading returns, the rounds are the call's entries, entry for entry.** -/
theorem readAll_fits {lead : Nat} {vs : List Var} {e : Ends} {rs : List Fmt.RoundView} {R : Read}
    (h : readAll ⟨lead, vs, some e⟩ rs = some R) : Fits (entries ⟨lead, vs, some e⟩) rs := by
  obtain ⟨r0, used, rv, front, a1, a2, _, a4, a5⟩ := readAll_spec h
  obtain ⟨u1, u2, l1, l2, b1, _, b3, b4⟩ := a4.split
  obtain ⟨rY, s, g, c1, _, c3⟩ := b4.one
  subst a1 b1 c1
  show Fits ([entry "PSC epsilon" (lead + 1) 1 0] ++ (vs.map fun v => entry "PSC round" (v.d - 1) 1 0) ++
    [entry "PSC Y" e.dY 1 1, entry "PSC values" e.n 0 0]) (r0 :: (u1 ++ [rY] ++ [rv]))
  have hY : Fit (entry "PSC Y" e.dY 1 1) rY := c3.fit _ _
  have : r0 :: (u1 ++ [rY] ++ [rv]) = [r0] ++ u1 ++ [rY, rv] := by simp
  rw [this]
  have h1 : Fits [entry "PSC epsilon" (lead + 1) 1 0] [r0] := ⟨a2.fit _ _, trivial⟩
  have h2 : Fits [entry "PSC Y" e.dY 1 1, entry "PSC values" e.n 0 0] [rY, rv] := ⟨hY, a5.fit _ _, trivial⟩
  exact (h1.append b3.fits).append h2

/-- **Where the hearing returns.** -/
theorem hear_spec {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) :
    shapeOk k = true ∧ ∃ (T : E) (R : Read), F.publicPart C = some T ∧ readAll k rs = some R ∧
      h = { start := C, target := T, eps := R.eps, claim := after k.all R.rounds (addE R.mu (mulE R.eps T)),
            first := F.next, vars := k.all, r := R.rounds.map (·.2), sEnd := F.next + ownSlots k.all } ∧
      ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork).hideRun (F.next + ownSlots k.all)
        R.values.toArray ((R.rounds.map (·.2)).getLastD zeroE) = some G := by
  unfold hear at hh
  cases hs : shapeOk k with
  | false => simp [hs, guard, failure] at hh
  | true =>
    refine ⟨rfl, ?_⟩
    cases hT : F.publicPart C with
    | none => simp [hs, hT] at hh
    | some T =>
      cases hR : readAll k rs with
      | none => simp [hs, hT, hR] at hh
      | some R =>
        simp only [hs, hT, hR, guard, if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hh
        cases hG : ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork).hideRun
            (F.next + ownSlots k.all) R.values.toArray ((R.rounds.map (·.2)).getLastD zeroE) with
        | none => rw [hG] at hh; cases hh
        | some G' =>
          simp only [hG, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hh
          exact ⟨T, R, rfl, rfl, hh.1.symm, by rw [hG, hh.2]⟩

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.readAll_spec
#print axioms VerifiableInference.Desc.Part.MaskedSum.readAll_fits
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_spec
