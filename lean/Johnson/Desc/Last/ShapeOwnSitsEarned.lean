-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeOwnSitsEarned.lean: TOWARD THE EARNING OF "K13.ownSits" (`ownSitsB V`,
Johnson/Desc/Last/OwnSits.lean: a test: the own group that is handed to the last chain
has just two members, the index masks' message and W, at the plan's places and with the plan's
shapes) AT THE BLOCK THAT LAYS THE GROUP. Statements and proofs; no definition.

Why. Of that item's clauses only "the members are just two, in that order" is
new to the promise; the two places and the two shapes stand there under other names: so the maker's
lemma owes the members' list alone. Here that list.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`rows_members`**: where K13's text behind W's commitment (`K13.rows`) answers, the claim's masks
    name the one message idx, the shape wants no split's message, and idx is smaller than W's
    number: the own group's members are #[idx, W]. `ownMembers_rowsB`, `ownMembers_atM4`: the same
    at the block `K13.rowsB`, and at `K13.atM4 P (K1.sendAtS P')` (the block at M:4 as kind K13's
    files state it).
  `w_fresh_atM4`: behind that block's yes the claim's W is the number of messages that the statement
    had IN FRONT. (Beside `K13.Law.atM4_numbers`, Johnson/Desc/K13/Law/K1Ids.lean, which counts from
    the end of the statement BEHIND, under a premise on the openings' number.)
    **`ownMembers_atM4_there`**: so "idx is the elder" is paid where the message idx is there in
    front.
  **`ownSitsB_of_members`**: on one verifier's state: `ownSitsB V s` from the members' list, that
    the group is there, and four facts: the places of idx and of W in the book, and their shapes.

Every "there is": none in a conclusion.
WHAT `ownMembers_atM4_there` ASKS, AND WHO HAS IT (others' words). hsp (no split): at the seat's
shape `noOwnSplit_at_seat` (Johnson/Desc/Last/ShapeNoSplit.lean); that the block's `P.lin` is that
shape: open. hr, hne (one row on the table in front, with a mask entry): kind K13's files' item
"K13.oneRow". hon (all its mask entries are of the message idx): those files' "K13.pileMasks", by
its name. hI (idx is there in front): the table's own tied item on the index masks' message.
Limits. THE EARNING IS NOT JOINED: these are not called at the table's tie for M:4. The four
facts of `ownSitsB_of_members` are taken from the promise BEHIND the block: each is its own name's
debt there. The keeping behind M:4: `ownSitsB_chainEnd` [not in this library].
NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorHeld
import Johnson.Desc.Last.OwnSits
import Johnson.Desc.K13.Law.K1Ids

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Ground (newGroupP joinP addRowsP)
open _root_.Desc.K14.Law.Fence (memOf joinP_mem addRowsP_mem)
open K13.Law (OnLedger linAt bind_ok there_ok pure_ok rows_is)

/-- **WHERE K13's TEXT BEHIND W's COMMITMENT ANSWERS, THE CLAIM's MASKS NAME THE ONE MESSAGE idx,
THE SHAPE WANTS NO SPLIT, AND idx IS THE ELDER OF THE TWO: the own group's members are idx, W, in
that order.** -/
theorem rows_members {Sh : Params.LinShape} {claim : LinClaim} {ids : Array ℕ} {d : K13.St}
    {o : LinFirst × K13.St} (h : K13.rows Sh claim ids d = .ok o) {idx : ℕ}
    (h1 : listOfT (claim.masks.toList.map (·.oracle)) = [idx])
    (hsp : Sh.ownSplitNeeded = false) (hlt : idx < o.1.w) :
    memOf o.2 o.1.own = some #[idx, o.1.w] := by
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, hj, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := _root_.Desc.K15.newGroupP_inv d b.2 _ _ b.1 hb
  have h0 : memOf b.2 b.1 = some #[] := by
    unfold memOf
    rw [e2, e1]
    show ((d.st.groups.push _)[d.st.groups.size]?).map (·.members) = _
    rw [Array.getElem?_push_size]
    rfl
  rw [h1] at hj
  simp only [K13.joinAll, bind_ok, there_ok] at hj
  obtain ⟨d₀, hj0, hj1⟩ := hj
  obtain rfl : d₀ = d₁ := Except.ok.inj hj1
  have m1 := (joinP_mem b.2 d₀ b.1 idx false hj0 #[] h0).1
  have m2 := (joinP_mem d₀ d₂ b.1 w false h2 _ m1).1
  rw [if_neg (by simp [hsp])] at h3
  obtain rfl := Option.some.inj h3
  rw [(addRowsP_mem d₂ d₄ b.1 [row] h4).1 b.1, m2]
  have hlt' : idx < w := hlt
  simp [hlt']

/-- **AT THE BLOCK BEHIND W's COMMITMENT.** -/
theorem ownMembers_rowsB {Cl : Type} {P : K13.Where} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.rowsB (Cl := Cl) K13.atS P).decide s rs gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {idx : ℕ} {r : TensorRow} (hr : s.rows = [r])
    (hon : OnLedger idx r) (hne : r.masks ≠ [])
    (hlt : ∀ l', linAt s' = some l' → idx < l'.w) :
    ∀ l' G, linAt s' = some l' → s'.st.groups[l'.own]? = some G →
      G.members.toList = [idx, l'.w] := by
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
  intro l' G hl' hG
  obtain rfl : o.1 = l' := Option.some.inj hl'
  have hM := rows_members hrows h1 hsp (hlt o.1 hl')
  have hG' : o.2.st.groups[o.1.own]? = some G := hG
  unfold memOf at hM
  rw [hG'] at hM
  have eM : G.members = #[idx, o.1.w] := Option.some.inj hM
  rw [eM]

/-- **AT W's COMMITMENT WITH THAT BLOCK BEHIND IT** (the block at M:4 as kind K13's files state
it). -/
theorem ownMembers_atM4 {Cl : Type} {P : K13.Where} {P' : K1.Par} {s s' : First.S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {idx : ℕ} {r : TensorRow} (hr : s.rows = [r])
    (hon : OnLedger idx r) (hne : r.masks ≠ [])
    (hlt : ∀ l', linAt s' = some l' → idx < l'.w) :
    ∀ l' G, linAt s' = some l' → s'.st.groups[l'.own]? = some G →
      G.members.toList = [idx, l'.w] := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := K13.Law.atM4_mid h
  have e := (K1.sendAtS_rows P' s s₁ r₁ r₂ g₁ h1).2
  exact ownMembers_rowsB h2 hsp (e.trans hr) hon hne hlt

/-- **W's NUMBER IS FRESH**: behind the yes of the block at M:4 the claim's W is the number of
messages that the statement had in front. -/
theorem w_fresh_atM4 {Cl : Type} {P : K13.Where} {P' : K1.Par} {s s' : First.S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') :
    ∀ l', linAt s' = some l' → l'.w = s.st.oracles.size := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := K13.Law.atM4_mid h
  obtain ⟨a, _, hh, _⟩ := K13.Law.sendAtS_full P' s s₁ r₁ r₂ g₁ h1
  obtain ⟨m₀, l, o, owed, hs, _, hrows, rfl⟩ := K13.Law.rowsB_at h2
  rw [hh] at hs
  obtain rfl : _ = m₀ := by injection hs
  obtain ⟨hw, _, _⟩ := K13.Law.rows_mask _ _ _ _ _ hrows
  intro l' hl'
  obtain rfl : o.1 = l' := Option.some.inj hl'
  have hw' : ((Array.range P'.sent.size).map (· + s.st.oracles.size))[0]? = some o.1.w := hw
  rw [Array.getElem?_map, Array.getElem?_range] at hw'
  split at hw'
  · have e : 0 + s.st.oracles.size = o.1.w := Option.some.inj hw'
    omega
  · cases hw'

/-- **THE MEMBERS' LIST AT M:4, WITH "idx IS THE ELDER" PAID**: it is enough that the message idx is
there in front. -/
theorem ownMembers_atM4_there {Cl : Type} {P : K13.Where} {P' : K1.Par} {s s' : First.S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {idx : ℕ} {r : TensorRow} (hr : s.rows = [r])
    (hon : OnLedger idx r) (hne : r.masks ≠ []) (hI : idx < s.st.oracles.size) :
    ∀ l' G, linAt s' = some l' → s'.st.groups[l'.own]? = some G →
      G.members.toList = [idx, l'.w] :=
  ownMembers_atM4 h hsp hr hon hne fun l' hl' => by rw [w_fresh_atM4 h l' hl']; exact hI

/-- **THE ITEM FROM THE MEMBERS' LIST AND FOUR FACTS THAT THE PROMISE BEHIND HOLDS UNDER OTHER
NAMES**: on one verifier's state. -/
theorem ownSitsB_of_members {V : OwnSeats} {s : First.S} {idx : ℕ}
    (hthere : ∀ l, linAt s = some l → (s.st.groups[l.own]?).isSome = true)
    (hm : ∀ l G, linAt s = some l → s.st.groups[l.own]? = some G →
      G.members.toList = [idx, l.w])
    (pI : s.book.place[idx]? = some V.index)
    (pW : ∀ l, linAt s = some l → s.book.place[l.w]? = some V.w)
    (sI : (s.st.oracles[idx]?).map (·.shape) = some V.indexShape)
    (sW : ∀ l, linAt s = some l → (s.st.oracles[l.w]?).map (·.shape) = some V.wShape) :
    ownSitsB V s = true := by
  rw [ownSitsB_iff]
  intro f hf
  obtain ⟨l, hl, e1, e2, e3⟩ := firstOfS_at hf
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 (hthere l hl)
  refine ⟨G, idx, l.w, by rw [e1, e3]; exact hG, hm l G hl hG, by rw [e2]; exact pI,
    by rw [e2]; exact pW l hl, by rw [e1]; exact sI, by rw [e1]; exact sW l hl⟩

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.ownMembers_rowsB
#print axioms VerifiableInference.Desc.Last.ownMembers_atM4
#print axioms VerifiableInference.Desc.Last.w_fresh_atM4
#print axioms VerifiableInference.Desc.Last.ownMembers_atM4_there
#print axioms VerifiableInference.Desc.Last.ownSitsB_of_members
#print axioms VerifiableInference.Desc.Last.rows_members
