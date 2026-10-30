-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/FormOn.lean: no soundness is claimed.
The program's own sample row (OnBytes/Iop/Send.lean: Send.form) is on its own oracle message (Means.RowOn), with no premise on the codes' lengths. Kind K1's files have the like of the kind's sample row (rowIn_sample, Johnson/Desc/K1/Law/SaysTie.lean) and tie the two rows under «every code's message length is a power of two» (form_eq, Johnson/Desc/K1/Law/FormEq.lean); a sub-protocol that sends by the program's own functions at codes read off the state has no such premise to hand.
  idx_lt · place_lt      two facts on numbers
  pad_mem                every place of the program's pad lies in a table that the message has, within it
  foldP_parts            the laying of the pad's entries writes units alone, each at a place of the pad (the walk is fold_parts', SaysTie.lean)
  **rowOn_form**         Send.form S.codes x.shape o ⟨z, β⟩ i = some r · S.oracles[o]? = some x · the message has a row · the point has the cube's coordinates ⇒ Means.RowOn S o { r with target := y }
No member. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.SaysTie
import Johnson.Desc.K1.Law.FormEq
import Johnson.Desc.Means.Order
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K1

theorem idx_lt {rows len rb le place : Nat} (hr : 0 < rows) (h1 : rows ≤ 2 ^ rb)
    (h2 : len ≤ 2 ^ le) (hp : place < len) : (rows - 1) + place * 2 ^ rb < 2 ^ (rb + le) := by
  have a : (place + 1) * 2 ^ rb ≤ 2 ^ le * 2 ^ rb := Nat.mul_le_mul_right _ (by omega)
  have b : (place + 1) * 2 ^ rb = place * 2 ^ rb + 2 ^ rb := by rw [Nat.succ_mul]
  have c : 2 ^ (rb + le) = 2 ^ le * 2 ^ rb := by rw [Nat.pow_add, Nat.mul_comm]
  rw [c]
  omega

theorem place_lt {len each answers i t : Nat} (h : ¬ len < each * answers) (hi : i < answers)
    (ht : t < each) : len - each * answers + each * i + t < len := by
  have a : each * (i + 1) ≤ each * answers := Nat.mul_le_mul_left _ hi
  have b : each * (i + 1) = each * i + each := Nat.mul_succ _ _
  omega

/-- Every place of the program's pad lies in a table that the message has, within it. -/
theorem pad_mem {codes : Codes} {s : OracleShape} {places : List PadPlace}
    (h : Send.pad codes s = some places) (hs : 0 < s.mainRows + s.maskRows) :
    ∀ p ∈ places, (Msg.of codes s).has p.part = true ∧
      p.index < 2 ^ (Msg.of codes s).bits p.part := by
  unfold Send.pad at h
  dsimp only at h
  by_cases hm : s.maskRows = 0
  · have hM : 0 < s.mainRows := by omega
    have c1 : (Send.cube codes s).hasMask = false := by simp [Send.cube, hm]
    have c2 : (Send.cube codes s).mainRowBits = ceilLog2 s.mainRows := by simp [Send.cube, hM]
    have c3 : (Send.cube codes s).mainBits =
        ceilLog2 s.mainRows + (codes.base.getD s.code default).logEll := by
      simp [Send.cube, hM]
    simp only [c1, Bool.false_eq_true, if_false, Bool.false_or] at h
    generalize (if (s.mainDeg == 3) = true then 1 else 3) = each at h
    split at h
    · cases h
    · rename_i hlen
      injection h with h
      subst h
      intro p hp
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
      obtain ⟨i, hi, t, ht, rfl⟩ := hp
      dsimp only
      refine ⟨?_, ?_⟩
      · show (s.mainRows != 0) = true
        simpa using Nat.pos_iff_ne_zero.1 hM
      · show _ < 2 ^ (Msg.of codes s).mainBits
        rw [← cube_mainBits, c3, c2]
        exact idx_lt hM (le_two_pow_ceilLog2 _) (le_two_pow_ceilLog2 _) (place_lt hlen hi ht)
  · have hM : 0 < s.maskRows := Nat.pos_of_ne_zero hm
    have c1 : (Send.cube codes s).hasMask = true := by simp [Send.cube, hM]
    have c2 : (Send.cube codes s).maskRowBits = ceilLog2 s.maskRows := by simp [Send.cube, hM]
    have c3 : (Send.cube codes s).maskBits =
        ceilLog2 s.maskRows + (codes.mask.getD s.maskCode default).logEll := by
      simp [Send.cube, hM]
    simp only [c1, if_true, Bool.true_or] at h
    split at h
    · cases h
    · rename_i hlen
      injection h with h
      subst h
      intro p hp
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
      obtain ⟨i, hi, t, ht, rfl⟩ := hp
      dsimp only
      refine ⟨?_, ?_⟩
      · show (s.maskRows != 0) = true
        simpa using hm
      · show _ < 2 ^ (Msg.of codes s).maskBits
        rw [← cube_maskBits, c3, c2]
        exact idx_lt hM (le_two_pow_ceilLog2 _) (le_two_pow_ceilLog2 _) (place_lt hlen hi ht)

/-- The laying of the pad's entries writes units alone, each at a place of the pad. -/
theorem foldP_parts (o : Nat) (c : PadPlace → E) : ∀ (l : List PadPlace) (r : OnBytes.Row),
    (l.foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index (c p)) r).terms = r.terms ∧
      (l.foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index (c p)) r).runs = r.runs ∧
      (l.foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index (c p)) r).forms = r.forms ∧
      ∀ u ∈ (l.foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index (c p)) r).units.toList,
        u ∈ r.units.toList ∨ ∃ p ∈ l, u.oracle = o ∧ u.part = p.part ∧ u.index = p.index
  | [], _ => ⟨rfl, rfl, rfl, fun _ h => Or.inl h⟩
  | x :: l, r => by
    obtain ⟨h1, h2, h3, h4⟩ := foldP_parts o c l (r.addUnit o x.part x.index (c x))
    refine ⟨h1, h2, h3, fun u hu => ?_⟩
    rcases h4 u hu with h | ⟨x', hx', h⟩
    · simp only [Row.addUnit, Array.toList_push, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨x, List.mem_cons_self, rfl, rfl, rfl⟩
    · exact Or.inr ⟨x', List.mem_cons_of_mem _ hx', h⟩

/-- **The program's sample row is on its own oracle message.** -/
theorem rowOn_form (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (z : List E) (β : E) (i : Nat) (y : E) (r : OnBytes.Row)
    (h : Send.form S.codes x.shape o ⟨z, β⟩ i = some r)
    (hs : 0 < x.shape.mainRows + x.shape.maskRows)
    (hz : (Send.cube S.codes x.shape).bits ≤ z.length) :
    Means.RowOn S o { r with target := y } := by
  have hz' : (Msg.of S.codes x.shape).v ≤ z.length := by rw [← cube_bits]; exact hz
  have hG : ({ code := 0, members := #[o] } : Group).members.contains o = true := by simp
  have hterm : ∀ part, (Msg.of S.codes x.shape).has part = true →
      Blk.placeOk S { code := 0, members := #[o] } o part
        ((Msg.of S.codes x.shape).ten z part).vars 0 = true := fun part hp => by
    unfold Blk.placeOk
    rw [hG, has_eq S o x hx part, hp, Msg.ten_vars _ z part hz', bits_eq S o x hx part hp]
    simp
  unfold Send.form at h
  simp only [ten_main, ten_mask, cube_hasMain, cube_hasMask, Option.bind_eq_bind,
    Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨places, hpl, rfl⟩ := h
  have hpm := pad_mem hpl hs
  obtain ⟨p1, p2, p3, p4⟩ := foldP_parts o (fun p =>
    subE (if p.answer == i then mulE β p.basis else zeroE)
      ((if p.part == .main then (Msg.of S.codes x.shape).ten z .main
        else (Msg.of S.codes x.shape).ten z .mask).entry p.index)) places { kind := .sample }
  refine ⟨fun t ht => ?_, fun u hu => ?_, fun w hw => ?_, fun f hf' => ?_⟩
  · cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
      cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
      simp only [hK, hZ, if_true, if_false, Bool.false_eq_true, Row.add, p1, Array.toList_push,
        List.mem_append, List.mem_singleton] at ht
    · simp at ht
    · rcases ht with ht | rfl
      · simp at ht
      · exact hterm .mask hZ
    · rcases ht with ht | rfl
      · simp at ht
      · exact hterm .main hK
    · rcases ht with (ht | rfl) | rfl
      · simp at ht
      · exact hterm .main hK
      · exact hterm .mask hZ
  · have hu' : u ∈ (places.foldl (fun (r : OnBytes.Row) p => r.addUnit o p.part p.index
        (subE (if p.answer == i then mulE β p.basis else zeroE)
          ((if p.part == .main then (Msg.of S.codes x.shape).ten z .main
            else (Msg.of S.codes x.shape).ten z .mask).entry p.index)))
        { kind := .sample }).units.toList := by
      cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
        cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
        simpa [hK, hZ, Row.add] using hu
    rcases p4 u hu' with h | ⟨q, hq, e1, e2, e3⟩
    · simp at h
    · obtain ⟨hp, hlt⟩ := hpm q hq
      rw [e1, e2, e3]
      unfold Blk.placeOk
      rw [hG, has_eq S o x hx _, hp, bits_eq S o x hx _ hp]
      simpa using hlt
  · exfalso
    cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
      cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
      simp only [hK, hZ, if_true, if_false, Bool.false_eq_true, Row.add, p2] at hw <;>
      simp at hw
  · exfalso
    cases hK : ((Msg.of S.codes x.shape).K != 0) <;>
      cases hZ : ((Msg.of S.codes x.shape).Kzk != 0) <;>
      simp only [hK, hZ, if_true, if_false, Bool.false_eq_true, Row.add, p3] at hf' <;>
      simp at hf'

end ToldDesc

#print axioms ToldDesc.pad_mem
#print axioms ToldDesc.rowOn_form
