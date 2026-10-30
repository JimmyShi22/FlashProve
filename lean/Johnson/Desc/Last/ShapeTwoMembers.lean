-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeTwoMembers.lean: "THE OWN GROUP THAT IS HANDED HAS TWO MEMBERS" (the fourth
of the six tests that the door of the last chain asks of the first chain's last record:
`doorFirstL`, Johnson/Desc/Last/DoorTexts.lean) AT THE YES OF THE BLOCK THAT LAYS THE GROUP.
Statements and proofs; no definition.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`twoMembers_rowsB`**: where K13's block behind W's commitment (`K13.rowsB` at the lens `atS`)
    says yes: if the shape wants no split's message (hsp), and the one row on the table in front
    (hr) names mask entries (hne), all of one message (hon: `K13.Law.OnLedger idx r`): then behind,
    the group at the claim's own number has two members. By `rows_count`
    (Johnson/Desc/Last/ShapeDoorItems.lean) and the library's `listOf_const`
    (OnBytes/Slice/BlkOpenN.lean).
  **`twoMembers_atM4`**: the same at `K13.atM4 P (K1.sendAtS P')`: W's sending leaves the rows on
    the table (`K1.sendAtS_rows`).

Every "there is": none.
WHO PAYS THE THREE PREMISES. hsp: at the seat's shape: `noOwnSplit_at_seat`
(Johnson/Desc/Last/ShapeNoSplit.lean); that the block's `P.lin` is that shape: not said. hr, hon,
hne: what stands behind the yes of the batching's block (M:3): "one row; on the index masks' message
alone; with a mask entry": the files of kind K13 write just that as owed (`OwedRowMasks`) and type
it; IT MUST THEN RIDE OVER THE ONE BORDER BETWEEN M:3 AND M:4: as an item of the promise, or the two
blocks are taken as one.
Limits. It says how many members, not which. It feeds h2's first half in `doorFirstB_of_items`; the
second half (one sample row each) is open. NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorItems
import Johnson.Desc.K13.Law.Agree
import Johnson.Desc.K13.Law.AtRecord
import OnBytes.Slice.BlkOpenN

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open _root_.Desc.K14.Law.Fence (memOf)
open K13.Law (OnLedger linAt)

/-- **WHERE K13's BLOCK BEHIND W's COMMITMENT SAYS YES, THE OWN GROUP HAS TWO MEMBERS**, if the
shape wants no split's message and the one row on the table in front names mask entries, all of one
message. -/
theorem twoMembers_rowsB {Cl : Type} {P : K13.Where} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.rowsB (Cl := Cl) K13.atS P).decide s rs gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {idx : ℕ} {r : TensorRow} (hr : s.rows = [r])
    (hon : OnLedger idx r) (hne : r.masks ≠ []) :
    ∀ l' G, linAt s' = some l' → s'.st.groups[l'.own]? = some G → G.members.size = 2 := by
  obtain ⟨m₀, l, o, owed, hs, hl, hrows, rfl⟩ := K13.Law.rowsB_at h
  have er : r = First.rowOfClaim l.claim := by
    have e : s.rows = [First.rowOfClaim l.claim] := by
      unfold First.S.rows
      rw [hs]
      show (match m₀.lin with
        | some l => [First.rowOfClaim l.claim]
        | none => s.out.pending) = _
      rw [hl]
    rw [hr] at e
    exact List.head_eq_of_cons_eq e
  subst er
  have e1 : l.claim.masks.toList.map (·.oracle) =
      (First.rowOfClaim l.claim).masks.map (·.1.oracle) := by
    show _ = (l.claim.masks.toList.map fun m => ((⟨m.oracle, m.index⟩ : Slot), m.coeff)).map _
    rw [List.map_map]
    rfl
  have h1 : listOfT (l.claim.masks.toList.map (·.oracle)) = [idx] := by
    rw [e1, listOfT_eq]
    refine OnBytes.Slice.listOf_const idx _ (by simpa using hne) fun y hy => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    exact hon t ht
  obtain ⟨M, hM, hc⟩ := rows_count hrows
  rw [h1, if_neg (by simp [hsp])] at hc
  intro l' G hl' hG
  obtain rfl : o.1 = l' := Option.some.inj hl'
  have hG' : o.2.st.groups[o.1.own]? = some G := hG
  unfold memOf at hM
  rw [hG'] at hM
  have eM : G.members = M := Option.some.inj hM
  rw [eM, hc]
  rfl

/-- **THE SAME AT W's COMMITMENT WITH THAT BLOCK BEHIND IT** (the block at M:4 as kind K13's files
state it): W's sending leaves the rows on the table. -/
theorem twoMembers_atM4 {Cl : Type} {P : K13.Where} {P' : K1.Par} {s s' : First.S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {idx : ℕ} {r : TensorRow} (hr : s.rows = [r])
    (hon : OnLedger idx r) (hne : r.masks ≠ []) :
    ∀ l' G, linAt s' = some l' → s'.st.groups[l'.own]? = some G → G.members.size = 2 := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := K13.Law.atM4_mid h
  have e := (K1.sendAtS_rows P' s s₁ r₁ r₂ g₁ h1).2
  exact twoMembers_rowsB h2 hsp (e.trans hr) hon hne

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.twoMembers_atM4
#print axioms VerifiableInference.Desc.Last.twoMembers_rowsB
