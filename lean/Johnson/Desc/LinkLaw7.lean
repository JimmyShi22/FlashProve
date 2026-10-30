-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/LinkLaw7.lean: a segment's row of pieces between relations that are given from outside.

Johnson/Desc/LinkLaw4.lean's `link_row` asks that the relations at the two boundaries around a
segment's batching ARE those of Johnson/Desc/LinkLaw3.lean. Where the relations at the boundaries of
a chain are fixed by a table of what each block hands to the next, they are that table's. Here they
need only fit:
  the relation of the table in front of the batching FOLLOWS FROM "all equations of the segment hold
  at the data to which the prover is bound";
  the relation of the table behind the runs behind the batching GIVES "the one equation in the state
  holds at these data".
The boundary between the batching and the runs behind it is the segment's own: its relation stays
that of LinkLaw3.lean.

What is said.
  `goodIn_conseq`: the rule of consequence for `Piece.GoodIn`: a stronger condition in front, a
    weaker condition behind, a weaker relation in front, a stronger relation behind.
  `link_joints`: `link_row` with the two relations fitted in that way.

A member (the last section): the toy segment of LinkLaw2.lean, all five pieces of its flat list: all
premises of `link_joints` hold together (`member`); and by the rule of composition for a row of
pieces (`rowKnowIn`, Johnson/Desc/Sound/KnowInProofs.lean) the five one after the other are
knowledge sound from "all equations hold" to "the one equation holds", at the error 2 of 5
(`row_member`).

Limits. As LinkLaw4.lean's: book-keeping. The member's hearing block hears nothing and its segment
has no closing block.

-/
import Johnson.Desc.LinkLaw4
import Johnson.Desc.Sound.KnowInProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {S Cl W P Y K : Type} {C : CK} {F : Frame}

/-- **The rule of consequence.** The two steps on relations may use the conditions: the one in front
at the statement in front, the block's own promise at the statement behind. -/
theorem goodIn_conseq (p : Piece C F S Cl W) {on on₂ on' on₂' : S × F.E.Str → Prop}
    {R R₂ R' R₂' : S × F.E.Str → W → Prop} (h : p.GoodIn on on' R R')
    (hon : ∀ a, on₂ a → on a) (hon' : ∀ b, on' b → on₂' b)
    (hR : ∀ a w, on₂ a → R a w → R₂ a w) (hR' : ∀ b w, on' b → R₂' b w → R' b w) :
    p.GoodIn on₂ on₂' R₂ R₂' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h a (hon a ha))
  intro τ hτ b hb
  obtain ⟨h1, h2⟩ := hτ b hb
  exact ⟨hon' b h1, fun w hw => hR a _ ha (h2 w (hR' b w h1 hw))⟩

variable [Field K] [Fintype K] [DecidableEq K]

/-- **The whole segment between relations given from outside.** As `link_row`; hin, hout: how the
relations at the boundaries j = i + front.length and j + 2 fit. -/
theorem link_joints (X : LinkSem K S Cl P Y) (L : Link S Cl) (d : ℕ) (H : X.Premises L F.ft d)
    (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (Bound : S × F.E.Str → W → Y → Prop) (i : ℕ)
    (front back : List (Piece C F S Cl W)) (pb pq : Piece C F S Cl W)
    (hblocks : (front ++ pb :: pq :: back).map (·.b) = L.blocksInOrder.map below)
    (hlen : front.length = L.hear.length + 1)
    (hin : ∀ a w, on (i + front.length) a →
      (∃ y, Bound a w y ∧ X.AllEq L.hear (X.fixed a.1) y) → R (i + front.length) a w)
    (hmid : R (i + front.length + 1) = fun b w => ∃ y, Bound b w y ∧
      ∃ t, afterIn L.hear L.orderAfter b.1 = .ok t ∧ X.one t b.1 y = 0)
    (hout : ∀ b w, on (i + front.length + 2) b → R (i + front.length + 2) b w →
      ∃ y, Bound b w y ∧ X.one b.1 b.1 y = 0)
    (hfront : EachGoodIn on R i front)
    (hback : EachGoodIn on R (i + front.length + 2) back)
    (hextb : ∀ a τ w, pb.ext a τ w = w) (hextq : ∀ a τ w, pq.ext a τ w = w)
    (hready : ∀ a, on (i + front.length) a → X.ready a.1)
    (hbehind : ∀ a, on (i + front.length + 1) a → X.behind a.1)
    (hhandsb : ∀ a τ b, on (i + front.length) a → pb.ior.red.out a τ = some b →
      on (i + front.length + 1) b)
    (hhandsq : ∀ a τ b, on (i + front.length + 1) a → pq.ior.red.out a τ = some b →
      on (i + front.length + 2) b)
    (huniq : ∀ a w w' y y', on (i + front.length) a → Bound a w y → Bound a w' y' → y = y')
    (hcarryb : ∀ a τ b w y, on (i + front.length) a → pb.ior.red.out a τ = some b →
      Bound b w y → Bound a w y)
    (hcarryq : ∀ a τ b w y, on (i + front.length + 1) a → pq.ior.red.out a τ = some b →
      Bound b w y → Bound a w y)
    (hreads : pb.Reads X.rd d) :
    EachGoodIn on R i (front ++ pb :: pq :: back) := by
  have hsplit : L.blocksInOrder.map below =
      (L.laidB :: L.hear).map below ++ below L.batchB :: below L.behindB ::
        (L.close ++ [L.clearedB]).map below := by
    rw [Link.flat_eq]
    simp [Link.mid]
  rw [List.map_append, List.map_cons, List.map_cons, hsplit] at hblocks
  have hl : (front.map (·.b)).length = ((L.laidB :: L.hear).map below).length := by
    simp [hlen]
  obtain ⟨_, htail⟩ := List.append_inj hblocks hl
  have hb : pb.b = below L.batchB := (List.cons.inj htail).1
  have hq : pq.b = below L.behindB := (List.cons.inj (List.cons.inj htail).2).1
  refine eachGoodIn_append on R front _ i hfront ⟨?_, ?_, hback⟩
  · rw [hmid]
    exact goodIn_conseq pb
      (batch_goodIn X L d H pb hb hextb _ _ Bound hready hhandsb huniq hcarryb hreads)
      (fun _ h => h) (fun _ h => h) hin (fun _ _ _ h => h)
  · rw [show i + front.length + 1 + 1 = i + front.length + 2 from rfl, hmid]
    exact goodIn_conseq pq
      (behind_goodIn X L H.later H.after pq hq hextq _ _ Bound hbehind hhandsq hcarryq)
      (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h) hout

/-! ## A member: the toy segment's whole row of pieces -/

/-- A block without a round whose decision is a function of the state alone, as a step. -/
theorem step_noRounds {S Cl : Type} (b : Block S Cl) (f : S → Except String S) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = f s) (ft : ℕ) (s : S) (cols : List OpenedColumn) :
    b.step ft s [] cols = (f s).map fun s' => (s', 0) := by
  rw [Block.step_eq, hr, hd]
  cases h : f s <;> simp [roundsFit, groupsOf, Except.map, bind, Except.bind, pure, Except.pure]

/-- The fold over one such block. -/
theorem fold_noRounds {S Cl : Type} {b : Block S Cl} {f : S → Except String S} (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = f s) {ft : ℕ} {s s' : S} {rs rs' : List Fmt.RoundView}
    {cols cols' : List OpenedColumn} (h : foldBlocks ft [b] s rs cols = .ok (s', rs', cols')) :
    f s = .ok s' := by
  obtain ⟨s₁, k, _, hq, h2⟩ := foldBlocks_cons_yes h
  rw [hr, List.length_nil, List.take_zero, step_noRounds b f hr hd] at hq
  simp only [foldBlocks, Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, _, _⟩ := h2
  cases hf : f s with
  | error e => rw [hf] at hq; cases hq
  | ok z =>
    rw [hf] at hq
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hq
    rw [hq.1]

namespace LinkToyD
open LinkToy LinkToyB

/-- A block of the toy's without a round, as a piece without a written round. -/
def pQ (b : Block St TClaim) : Piece tC tF St TClaim Unit :=
  ⟨below b, 0, [], [], fun _ _ w => w, ()⟩

/-- The conditions at the toy segment's six boundaries. -/
def on : ℕ → St × tF.E.Str → Prop
  | 0, a | 1, a | 2, a => a.1.w = none
  | 3, a => a.1.w = none ∨ a.1.w = some 2
  | _, _ => True

/-- The relations there: all equations hold; the boundary behind the batching; the one equation
holds. -/
def R : ℕ → St × tF.E.Str → Unit → Prop
  | 0, a, w | 1, a, w | 2, a, w =>
    ∃ y, Bound a w y ∧ LinkToy.sem.AllEq meant.hear (LinkToy.sem.fixed a.1) y
  | 3, b, w => ∃ y, Bound b w y ∧
      ∃ t, afterIn meant.hear meant.orderAfter b.1 = .ok t ∧ LinkToy.sem.one t b.1 y = 0
  | _, b, w => ∃ y, Bound b w y ∧ LinkToy.sem.one b.1 b.1 y = 0

/-- A piece that hands the state and the stored table on as they are. -/
theorem pQ_same (b : Block St TClaim) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = .ok s)
    (a c : St × tF.E.Str) (τ : Iop.Tr (uLT tC (pQ b).ds)) (h : (pQ b).ior.red.out a τ = some c) :
    c.1 = a.1 ∧ dat c.2 = dat a.2 := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below (p := pQ b) rfl h
  have h1 := fold_noRounds (f := fun s => .ok s) hr hd hfold
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨(Except.ok.inj h1).symm, rfl⟩

/-- Such a piece is good between a condition and a relation that read the state and the stored table
alone, and themselves. -/
theorem pQ_goodIn (b : Block St TClaim) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = .ok s)
    (o : St → Prop) (Q : St → F5 × F5 → Prop) :
    (pQ b).GoodIn (fun a => o a.1) (fun a => o a.1) (fun a w => ∃ y, Bound a w y ∧ Q a.1 y)
      (fun a w => ∃ y, Bound a w y ∧ Q a.1 y) := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ c hout => ?_
  obtain ⟨h1, h2⟩ := pQ_same b hr hd a c τ hout
  refine ⟨by show o c.1; rw [h1]; exact ha, ?_⟩
  rintro w ⟨y, hB, hQ⟩
  exact ⟨y, hB.trans h2, h1 ▸ hQ⟩

theorem carryQ (b : Block St TClaim) (a c : St × tF.E.Str) (τ : Iop.Tr (uLT tC (pQ b).ds))
    (h : (pQ b).ior.red.out a τ = some c) : dat c.2 = dat a.2 := by
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **ALL PREMISES OF `link_joints` HOLD TOGETHER AT THE TOY SEGMENT**: its five pieces (laid, the
hearing block, the batching at its written round, the runs behind the batching, cleared) are good,
boundary by boundary, from "all equations hold" to "the one equation holds". -/
theorem member : EachGoodIn on R 0
    ([pQ meant.laidB, pQ hearB] ++ pb :: pQ meant.behindB :: [pQ meant.clearedB]) :=
  link_joints LinkToy.sem meant 2 meant_premises on R Bound 0 [pQ meant.laidB, pQ hearB]
    [pQ meant.clearedB] pb (pQ meant.behindB) rfl rfl (fun _ _ _ h => h) rfl (fun _ _ _ h => h)
    ⟨pQ_goodIn meant.laidB rfl (fun _ _ _ => rfl) (fun s => s.w = none)
        (fun s y => LinkToy.sem.AllEq meant.hear (LinkToy.sem.fixed s) y),
      pQ_goodIn hearB rfl (fun _ _ _ => rfl) (fun s => s.w = none)
        (fun s y => LinkToy.sem.AllEq meant.hear (LinkToy.sem.fixed s) y), trivial⟩
    ⟨pQ_goodIn meant.clearedB rfl (fun _ _ _ => rfl) (fun _ => True)
        (fun s y => LinkToy.sem.one s s y = 0), trivial⟩
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ h => h) (fun _ h => h)
    (fun a τ b ha hout => batch_hands LinkToy.sem meant 2 meant_premises pb rfl a b τ ha hout)
    (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ h h' => h.trans h'.symm)
    (fun a τ b _ _ _ hout hB => hB.trans (carryB a τ b hout))
    (fun a τ b _ _ _ hout hB => hB.trans (carryQ _ a b τ hout)) readsB

/-- **AND SO, BY THE RULE OF COMPOSITION FOR A ROW, THE FIVE PIECES ONE AFTER THE OTHER** are
knowledge sound and keep the promise, from "all equations of the segment hold" to "the one equation
holds", at the pieces' errors in a row: 2 of 5 at the one written round. -/
theorem row_member :
    KnowIn (rowIOR (pQ meant.laidB) [pQ hearB, pb, pQ meant.behindB, pQ meant.clearedB]).red
      (on 0) (on 5) (R 0) (R 5)
      (rowExt () (pQ meant.laidB) [pQ hearB, pb, pQ meant.behindB, pQ meant.clearedB])
      (rowErr (pQ meant.laidB) [pQ hearB, pb, pQ meant.behindB, pQ meant.clearedB]) :=
  rowKnowIn St TClaim Unit tC tF on R () 0 (pQ meant.laidB)
    [pQ hearB, pb, pQ meant.behindB, pQ meant.clearedB] member

end LinkToyD

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodIn_conseq
#print axioms VerifiableInference.Desc.Sound.link_joints
#print axioms VerifiableInference.Desc.Sound.step_noRounds
#print axioms VerifiableInference.Desc.Sound.fold_noRounds
#print axioms VerifiableInference.Desc.Sound.LinkToyD.pQ_same
#print axioms VerifiableInference.Desc.Sound.LinkToyD.pQ_goodIn
#print axioms VerifiableInference.Desc.Sound.LinkToyD.carryQ
#print axioms VerifiableInference.Desc.Sound.LinkToyD.member
#print axioms VerifiableInference.Desc.Sound.LinkToyD.row_member
