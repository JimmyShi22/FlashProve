-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HandsFence.lean. x_at_cutR's | bk_at_cutR's PREMISE hF IS ASKED AT j < bs.length ALONE (the proof spends it nowhere else; beyond the length «take j» is the whole list again, and a payer would owe Fk j at the last state for every such j: payable, but a trap). The shares that want a fact along the fold: by name, below.
A LIGHT FILE: KIND-FREE: IT IMPORTS Johnson/IMR/HandsFold.lean (so Johnson/IMR/HandsDef.lean) AND
Johnson/Desc/FoldKeeps.lean ALONE: THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT
READS THE VERIFIER's STATE ALONE: Hands WITH A FENCE.
WHY. Hands' six fields run over ALL states s, s': so a fact that holds along the fold alone (FoldFacts' fields: «the link's context's group is the plan's» and the like) cannot enter them, and a share that wants such a fact has a premise that
nobody can pay (so it stood, by a list not in this repository, for «the link's context's group is the plan's» at the one equation, at K10, at K1's law and at K2's 25). THE CURE, ADDITIVE: HandsR Fk …: each field has ONE PREMISE MORE: Fk k s, Fk : ℕ → S → Prop a letter; the rule along the fold asks beside: «Fk holds at the state behind each shorter cut of this very fold». Whoever has Hands has HandsR for nothing (Hands.fenced).
ON WORDS: «the state» is the verifier's state: the value of type S that the fold of the IOP as written in Lean carries from sub-protocol (block) to sub-protocol.
FOR WHOEVER FILLS Fk: THE FIELD «mark» IS SPENT AT A STATE IN FRONT OF WHICH NOTHING IS KNOWN YET BUT THAT THE FOLD REACHES IT (it draws «no mark in front» from «no mark behind»): SO Fk MUST BE HAD AT EVERY REACHED STATE, MARKED OR NOT: at FoldFacts, whose fields stand under «no mark»: Fk k s := s.failed = none → ‹the facts at s›.

  HandsR Fk N links ps E ft k b   Hands, each field under Fk k s.
  Hands.fenced      Hands → HandsR Fk, at every Fk.
  HandsR.free       HandsR (fun _ _ => True) → Hands.
  HandsR.weaker     a stronger fence is easier to pay under: (∀ s, Fk' k s → Fk k s) → HandsR Fk → HandsR Fk'.
  HandsR.under      the seated sub-protocol's HandsR from its lot's own's (b.UnderR b').
  HandsR.step       one sub-protocol hands X on, at a fenced state.
  x_at_cutR         ALONG THE FOLD: HandsR at every sub-protocol of bs · Fk at the state behind each cut j < bs.length of this very fold · «X 0 at the first state, if it bears no mark» ⟹ X k at the state behind the first k, if it bears no mark.
  bk_at_cutR        … so the table's four fixed tests there.

What is not claimed. HandsR at any sub-protocol. Fk at any state. No soundness.
-/
import Johnson.IMR.HandsFold
import Johnson.Desc.FoldKeeps

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Chain Place foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers shapeAt rowsHeld membersHeld bookAt)
open ProofFile (Cl)

/-- **What one sub-protocol owes, at the fenced states.** -/
structure HandsR (Fk : Nat → S → Prop) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (E : Nat → S → Bool) (ft k : Nat) (b : Block S Cl) : Prop where
  mark : ∀ s s', Fk k s → Yes ft b s s' → s.failed ≠ none → s'.failed ≠ none
  shape : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → shapeAt links ps[k + 1]? s' = true
  rows : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → rowsHeld N (openAt links ps (k + 1)) s' = true
  members : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → membersHeld N (openAt links ps (k + 1)) s' = true
  book : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → bookAt N ps[k + 1]? s' = true
  more : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps E k s = true → E (k + 1) s' = true

section
variable {Fk Fk' : Nat → S → Prop} {N : Numbers} {links : List ModelPart} {ps : List Place}
  {E : Nat → S → Bool} {ft k : Nat} {b b' : Block S Cl}

/-- **Whoever has Hands has HandsR for nothing.** -/
theorem Hands.fenced (H : Hands N links ps E ft k b) : HandsR Fk N links ps E ft k b :=
  ⟨fun s s' _ => H.mark s s', fun s s' _ => H.shape s s', fun s s' _ => H.rows s s',
    fun s s' _ => H.members s s', fun s s' _ => H.book s s', fun s s' _ => H.more s s'⟩

theorem HandsR.free (H : HandsR (fun _ _ => True) N links ps E ft k b) :
    Hands N links ps E ft k b :=
  ⟨fun s s' => H.mark s s' trivial, fun s s' => H.shape s s' trivial,
    fun s s' => H.rows s s' trivial, fun s s' => H.members s s' trivial,
    fun s s' => H.book s s' trivial, fun s s' => H.more s s' trivial⟩

/-- A stronger fence is easier to pay under. -/
theorem HandsR.weaker (h : ∀ s, Fk' k s → Fk k s) (H : HandsR Fk N links ps E ft k b) :
    HandsR Fk' N links ps E ft k b :=
  ⟨fun s s' f => H.mark s s' (h s f), fun s s' f => H.shape s s' (h s f),
    fun s s' f => H.rows s s' (h s f), fun s s' f => H.members s s' (h s f),
    fun s s' f => H.book s s' (h s f), fun s s' f => H.more s s' (h s f)⟩

/-- The seated sub-protocol's from its lot's own's. -/
theorem HandsR.under (H : HandsR Fk N links ps E ft k b') (hU : b.UnderR b') :
    HandsR Fk N links ps E ft k b :=
  ⟨fun s s' f hy => H.mark s s' f (hy.under hU), fun s s' f hy => H.shape s s' f (hy.under hU),
    fun s s' f hy => H.rows s s' f (hy.under hU), fun s s' f hy => H.members s s' f (hy.under hU),
    fun s s' f hy => H.book s s' f (hy.under hU), fun s s' f hy => H.more s s' f (hy.under hU)⟩

/-- One sub-protocol hands X on, at a fenced state. -/
theorem HandsR.step (H : HandsR Fk N links ps E ft k b) {s s' : S} (hf : Fk k s)
    (hy : Yes ft b s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : XK N links ps E k s = true) : XK N links ps E (k + 1) s' = true := by
  unfold XK BK
  rw [H.shape s s' hf hy h0 h1 hx, H.rows s s' hf hy h0 h1 hx, H.members s s' hf hy h0 h1 hx,
    H.book s s' hf hy h0 h1 hx, H.more s s' hf hy h0 h1 hx]
  rfl

end

/-- One step of the fold, cut off at its end. (The same sentence stands as fold_last in Johnson/IMR/SendsFold.lean, which is not light; private here, so that the two never clash.) -/
private theorem fold_end {ft k : Nat} {bs : List (Block S Cl)} {b : Block S Cl}
    (hb : bs[k]? = some b) {s₀ : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (bs.take (k + 1)) s₀ rs cols = .ok out) :
    ∃ (t : S) (rs' : List Fmt.RoundView) (cols' : List OpenedColumn),
      foldBlocks ft (bs.take k) s₀ rs cols = .ok (t, rs', cols') ∧ Yes ft b t out.1 := by
  rw [List.take_add_one, hb] at h
  obtain ⟨t, rs', cols', h1, h2⟩ :=
    VerifiableInference.Desc.Keeps.foldBlocks_split ft [b] _ _ _ _ _ h
  obtain ⟨s', n, -, hs, hl⟩ := VerifiableInference.Desc.foldBlocks_cons ft b [] t rs' cols' out h2
  obtain rfl := VerifiableInference.Desc.foldBlocks_nil ft s' _ _ out hl
  exact ⟨t, rs', cols', h1, _, _, n, hs⟩

/-- **ALONG THE FOLD, UNDER A FENCE.** -/
theorem x_at_cutR {Fk : Nat → S → Prop} {N : Numbers} {links : List ModelPart} {ps : List Place}
    {E : Nat → S → Bool} {ft : Nat} {bs : List (Block S Cl)}
    (h : ∀ k b, bs[k]? = some b → HandsR Fk N links ps E ft k b) {s₀ : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn}
    (hF : ∀ j, j < bs.length → ∀ r, foldBlocks ft (bs.take j) s₀ rs cols = .ok r → Fk j r.1)
    (h0 : s₀.failed = none → XK N links ps E 0 s₀ = true) :
    ∀ (k : Nat), k ≤ bs.length → ∀ out : S × List Fmt.RoundView × List OpenedColumn,
      foldBlocks ft (bs.take k) s₀ rs cols = .ok out → out.1.failed = none →
      XK N links ps E k out.1 = true
  | 0, _, out, hf, hu => by
    rw [List.take_zero] at hf
    obtain rfl := VerifiableInference.Desc.foldBlocks_nil ft s₀ rs cols out hf
    exact h0 hu
  | k + 1, hk, out, hf, hu => by
    have hb := List.getElem?_eq_getElem (l := bs) (i := k) (by omega)
    obtain ⟨t, rs', cols', h1, hy⟩ := fold_end hb hf
    have H := h k _ hb
    have hfk : Fk k t := hF k (by omega) _ h1
    have ht : t.failed = none := Classical.byContradiction fun hm => H.mark t out.1 hfk hy hm hu
    exact H.step hfk hy ht hu (x_at_cutR h hF h0 k (by omega) _ h1 ht)

/-- … so the table's four fixed tests there. -/
theorem bk_at_cutR {Fk : Nat → S → Prop} {N : Numbers} {links : List ModelPart} {ps : List Place}
    {E : Nat → S → Bool} {ft : Nat} {bs : List (Block S Cl)}
    (h : ∀ k b, bs[k]? = some b → HandsR Fk N links ps E ft k b) {s₀ : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn}
    (hF : ∀ j, j < bs.length → ∀ r, foldBlocks ft (bs.take j) s₀ rs cols = .ok r → Fk j r.1)
    (h0 : s₀.failed = none → XK N links ps E 0 s₀ = true) {k : Nat} (hk : k ≤ bs.length)
    {out : S × List Fmt.RoundView × List OpenedColumn} (hf : foldBlocks ft (bs.take k) s₀ rs cols = .ok out)
    (hu : out.1.failed = none) :
    shapeAt links ps[k]? out.1 = true ∧ rowsHeld N (openAt links ps k) out.1 = true ∧
      membersHeld N (openAt links ps k) out.1 = true ∧ bookAt N ps[k]? out.1 = true := by
  obtain ⟨a, b, c', d, -⟩ := xk_parts (x_at_cutR h hF h0 k hk out hf hu)
  exact ⟨a, b, c', d⟩

end IM

#print axioms IM.Hands.fenced
#print axioms IM.HandsR.free
#print axioms IM.HandsR.weaker
#print axioms IM.HandsR.under
#print axioms IM.HandsR.step
#print axioms IM.x_at_cutR
#print axioms IM.bk_at_cutR
