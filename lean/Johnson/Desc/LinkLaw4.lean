-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/LinkLaw4.lean: (1) the law of a hearing block's rounds (Johnson/Desc/RiderLaw.lean) in
the form that the rule of composition asks of a block, `Piece.GoodIn`; (2) a whole segment's row of
pieces, from its parts.

What is said.
  `hear_goodIn`: the piece that holds a hearing block (with the test on the words in front) has
    `GoodIn` from "the relation in front holds at the data to which the prover is bound" to "the
    relation on the state behind holds at these data". From `HearSem.Sound` and the premises of
    Johnson/Desc/LinkLaw3.lean, with `Piece.ReadsAll` in the place of `Piece.Reads`: for each drawn
    element a set of field elements, named by what a view shows before its draw, pulls back to bad
    raw challenges within the piece's errors.
  `eachGoodIn_append`: a row of good pieces behind a row of good pieces is a row of good pieces.
  `link_row`: THE WHOLE SEGMENT, AS GLUE: if the pieces of "laid" and of the hearing blocks are
    good up to the relation "all equations of the segment hold", and the pieces of the closing and
    of "cleared" are good from the relation "the one equation holds", then, with the two pieces of
    LinkLaw3.lean between them, all pieces of the segment's flat list are good, boundary by
    boundary: what the rule of composition for a chain (`EachGoodIn`) asks of this stretch.

A member (section 3): the toy of RiderLaw.lean at two written rounds: all premises of
`hear_goodIn` together: at each draw two riders, the error 1 of 5; with teeth. A second member
(section 4): both coordinates drawn in ONE written round with 25 raw challenges: the error that
`ReadsAll` then needs is the SUM over the round's elements, (1 + 1) times 5 of 25 (`cnt_pair_le`).

`huniq` (the pin) is a named hypothesis here as in LinkLaw3.lean, whose head says who owes it.

Limits. As the three files'. The member's kit of challenges has no proof of work. `link_row` is
book-keeping: it adds no mathematics, and its premises on the hearing blocks and the closing are met
by nothing yet. The data y are those to which the prover is bound at the statement IN FRONT of a
block: a hearing block in whose stretch the prover sends an oracle of which that block's own riders
speak is not covered.
`link_row` takes a segment's pieces in the order of `Link.blocksInOrder`. In the plan's order of rounds the
next place's first sending is said to stand one round in front of the closing's last round: if so,
the pieces "back" of one segment and "front" of the next do not simply stand in a row; nothing here
mends that.

-/
import Johnson.Desc.LinkLaw3
import Johnson.Desc.RiderLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S Cl W P Y K : Type} {C : CK} {F : Frame}

/-! ## 1 A hearing block's piece -/

/-- **From field elements to raw challenges, element by element**, as a premise on a piece. B names
for each drawn element, by the earlier rounds as a view shows them, the round's own message and the
elements drawn before in the round, a set of at most `deg` field elements. There is a family of bad
raw challenges within the piece's errors such that on every clean transcript on which the proofs of
work pass no drawn element lies in its set. (Where a round draws k elements at once, its error has
to bear the tuples with a bad member: at most the sum over j of deg j times the field's size to the
power k - 1, read as raw challenges.) -/
def Piece.ReadsAll (p : Piece C F S Cl W) (rd : Fmt.Ext → K) (deg : ℕ → ℕ → ℕ) : Prop :=
  ∀ B : List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Finset K,
    (∀ pre vals xs, (B pre vals xs).card ≤ deg pre.length xs.length) →
    ∀ y : F.E.Str, ∃ fam : Iop.BadFam (uLT C p.ds), fam.Within p.err ∧
      ∀ τ, fam.Clean τ → passT C p.ds (rhoT C p.ds τ) = true →
        ∀ pre r post, (p.shown y τ).rounds = pre ++ r :: post →
          ∀ xs x ys, r.drawn.elems = xs ++ x :: ys → rd x ∉ B pre r.vals xs

variable [Field K]

open Classical in
/-- The bad values of a drawn element at a statement. -/
def badHear (X : HearSem K S Y) (on : S × F.E.Str → Prop) (Bound : S × F.E.Str → W → Y → Prop)
    (a : S × F.E.Str) (pre : List Fmt.RoundView) (vals : List Fmt.ItemValue) (xs : List Fmt.Ext) : Finset K :=
  if h : on a ∧ ∃ y, ∃ w, Bound a w y then
    badRiders K (X.riders a.1 pre vals xs (Classical.choose h.2))
  else ∅

/-- **A hearing block's piece is good**, in the form that the rule of composition asks. -/
theorem hear_goodIn (X : HearSem K S Y) (b : Block S Cl) (H : X.Sound b F.ft)
    (p : Piece C F S Cl W) (hb : p.b = below b) (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : S × F.E.Str → Prop) (Bound : S × F.E.Str → W → Y → Prop)
    (hready : ∀ a, on a → X.ready a.1)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (huniq : ∀ a w w' y y', on a → Bound a w y → Bound a w' y' → y = y')
    (hcarry : ∀ a τ b w y, on a → p.ior.red.out a τ = some b → Bound b w y → Bound a w y)
    (hreads : p.ReadsAll X.rd X.deg) :
    p.GoodIn on on' (fun a w => ∃ y, Bound a w y ∧ X.In a.1 y)
      (fun b w => ∃ y, Bound b w y ∧ X.Out b.1 y) := by
  have hcard : ∀ a pre vals xs,
      (badHear X on Bound a pre vals xs).card ≤ X.deg pre.length xs.length := by
    intro a pre vals xs
    unfold badHear
    split
    · next h => exact H.1 a.1 pre vals xs _ (hready a h.1)
    · simp
  refine goodInOfBadFam S Cl W C F p on on' _ _
    (fun a => Classical.choose (hreads _ (hcard a) a.2)) ?_ ?_ ?_
  · intro a _
    exact (Classical.choose_spec (hreads _ (hcard a) a.2)).1
  · intro a τ b ha _ hout
    exact hhands a τ b ha hout
  · rintro a τ c w ha hclean hout ⟨y, hB, hO⟩
    rw [hext]
    have hBa := hcarry a τ c w y ha hout hB
    refine ⟨y, hBa, ?_⟩
    obtain ⟨hp, hw, hfold⟩ := Piece.out_below hb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    have hex : on a ∧ ∃ y, ∃ w, Bound a w y := ⟨ha, y, w, hBa⟩
    have hy : Classical.choose hex.2 = y := by
      obtain ⟨w', hw'⟩ := Classical.choose_spec hex.2
      exact huniq a w' w _ _ ha hw' hBa
    refine H.2 a.1 _ _ c.1 k y (hready a ha) hw hs (fun pre r post hpr xs x ys hx => ?_) hO
    have hnb :=
      (Classical.choose_spec (hreads _ (hcard a) a.2)).2 τ hclean hp pre r post hpr xs x ys hx
    unfold badHear at hnb
    rwa [dif_pos hex, hy] at hnb

/-! ## 2 The whole segment's row of pieces -/

omit [Field K] in
/-- A row of good pieces behind a row of good pieces. -/
theorem eachGoodIn_append (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) :
    ∀ (l l' : List (Piece C F S Cl W)) (i : ℕ), EachGoodIn on R i l →
      EachGoodIn on R (i + l.length) l' → EachGoodIn on R i (l ++ l')
  | [], l', i, _, h => by simpa using h
  | p :: l, l', i, h, h' => by
    refine ⟨h.1, eachGoodIn_append on R l l' (i + 1) h.2 ?_⟩
    rw [List.length_cons] at h'
    rwa [Nat.add_assoc, Nat.add_comm 1]

/-- **The whole segment, as glue.** front: the pieces of "laid" and of the hearing blocks. pb, pq:
the pieces of the batching and of the runs behind it. back: the pieces of the closing and of
"cleared". Boundary i lies in front of the segment; j = i + front.length in front of the batching.
The relations at the boundaries j, j + 1, j + 2 are those of LinkLaw3.lean. `hbehind`: the condition
at the boundary j + 1 gives `behind`: the batching's piece hands that on (`batch_hands`), so a
condition that holds it can be met by `hhandsb`. -/
theorem link_row [Fintype K] [DecidableEq K] (X : LinkSem K S Cl P Y) (L : Link S Cl) (d : ℕ)
    (H : X.Premises L F.ft d)
    (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (Bound : S × F.E.Str → W → Y → Prop) (i : ℕ)
    (front back : List (Piece C F S Cl W)) (pb pq : Piece C F S Cl W)
    (hblocks : (front ++ pb :: pq :: back).map (·.b) = L.blocksInOrder.map below)
    (hlen : front.length = L.hear.length + 1)
    (hRj : R (i + front.length) = fun a w => ∃ y, Bound a w y ∧ X.AllEq L.hear (X.fixed a.1) y)
    (hRj1 : R (i + front.length + 1) = fun b w => ∃ y, Bound b w y ∧
      ∃ t, afterIn L.hear L.orderAfter b.1 = .ok t ∧ X.one t b.1 y = 0)
    (hRj2 : R (i + front.length + 2) = fun b w => ∃ y, Bound b w y ∧ X.one b.1 b.1 y = 0)
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
  · rw [hRj, hRj1]
    exact batch_goodIn X L d H pb hb hextb _ _ Bound hready hhandsb huniq hcarryb hreads
  · rw [show i + front.length + 1 + 1 = i + front.length + 2 from rfl, hRj1, hRj2]
    exact behind_goodIn X L H.later H.after pq hq hextq _ _ Bound hbehind hhandsq hcarryq

/-! ## 3 A member: all premises of `hear_goodIn` together, at two written rounds -/

namespace RiderToyB
open LinkToy LinkToyB RiderToy

/-- The data to which the prover is bound: the first six words of the stored table's one leaf. -/
def dat6 (y : tF.E.Str) : Dat :=
  match (y.1 ⟨0, by decide⟩).2 with
  | a :: b :: c :: d :: e :: f :: _ =>
    ⟨(a.toNat : F5), (b.toNat : F5), (c.toNat : F5), (d.toNat : F5), (e.toNat : F5), (f.toNat : F5)⟩
  | _ => ⟨0, 0, 0, 0, 0, 0⟩

/-- The piece: the toy's hearing block at its two written rounds, at the error 1 (of 5) in each. -/
def ph : Piece tC tF Pt Bool Unit :=
  ⟨below RiderToy.meant, 0, [tRD, tRD], [], fun _ _ w => w, (1, 1, ())⟩

def Bound6 (a : Pt × tF.E.Str) (_ : Unit) (y : Dat) : Prop := y = dat6 a.2

abbrev TrH : Type := Iop.Tr (uLT tC [tRD, tRD])

theorem shownH (y : tF.E.Str) (τ : TrH) :
    ph.shown y τ =
      ⟨[rv (ext (show F5 from τ.2.1)), rv (ext (show F5 from τ.2.2.2.1))], []⟩ := by
  obtain ⟨m, c, m', c', u⟩ := τ
  rfl

theorem readsH : ph.ReadsAll rd fun _ _ => 1 := by
  intro B hB y
  refine ⟨(fun _ => {c | (show F5 from c) ∈ B [] [] []}, fun _ c =>
      (fun _ => {c' | (show F5 from c') ∈ B [rv (ext (show F5 from c))] [] []}, fun _ _ => ())),
    ⟨fun _ => (cnt_mem_le _).trans (hB [] [] []), fun _ c =>
      ⟨fun _ => (cnt_mem_le _).trans (hB [rv (ext (show F5 from c))] [] []),
        fun _ _ => trivial⟩⟩, ?_⟩
  rintro ⟨m, c, m', c', u⟩ hclean _ pre r post hpr xs x ys hx
  rw [shownH] at hpr
  have one_elem : ∀ (e : F5), (rv (ext e)).drawn.elems = xs ++ x :: ys → xs = [] ∧ x = ext e := by
    intro e he
    match xs, he with
    | [], he => exact ⟨rfl, (List.cons.inj he).1.symm⟩
    | _ :: xs, he => exact absurd (List.cons.inj he).2 (by simp)
  match pre, hpr with
  | [], hpr =>
    obtain ⟨rfl, _⟩ := List.cons.inj hpr
    obtain ⟨rfl, rfl⟩ := one_elem _ hx
    rw [rd_ext]
    exact hclean.1
  | [r₀], hpr =>
    obtain ⟨rfl, hpr'⟩ := List.cons.inj hpr
    obtain ⟨rfl, _⟩ := List.cons.inj hpr'
    obtain ⟨rfl, rfl⟩ := one_elem _ hx
    rw [rd_ext]
    exact hclean.2.1
  | _ :: _ :: pre, hpr =>
    exact absurd (List.cons.inj (List.cons.inj hpr).2).2 (by simp)

theorem carryH (a : Pt × tF.E.Str) (τ : TrH) (b : Pt × tF.E.Str)
    (h : ph.ior.red.out a τ = some b) : dat6 b.2 = dat6 a.2 := by
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **ALL PREMISES OF `hear_goodIn` HOLD TOGETHER**: at each of two draws two riders, at the error 1
of 5. -/
theorem member : ph.GoodIn (fun _ => True) (fun _ => True)
    (fun a w => ∃ y, Bound6 a w y ∧ RiderToy.sem.In a.1 y)
    (fun b w => ∃ y, Bound6 b w y ∧ RiderToy.sem.Out b.1 y) :=
  hear_goodIn RiderToy.sem RiderToy.meant RiderToy.meant_sound ph rfl (fun _ _ _ => rfl) _ _ Bound6
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ h h' => h.trans h'.symm)
    (fun a τ b _ _ _ hout hB => hB.trans (carryH a τ b hout)) readsH

/-- Oracles at which the guest's first value is 1 and all else 0. -/
def yB : tF.E.Str := (fun _ => (0, [0, 0, 0, 0, 1, 0]), fun _ => [])

/-- TEETH: there the relation in front has no witness. -/
theorem front_false : ¬ ∃ y, Bound6 (RiderToy.s0, yB) () y ∧ RiderToy.sem.In RiderToy.s0 y := by
  rintro ⟨y, rfl, h⟩
  exact absurd h.2.2.2.2.1 (by decide)

/-- TEETH: THE SECOND ROUND's ERROR IS PAID FOR SOMETHING: the guest's rider there is 1 - x: at the
raw challenges 0, then 1, the piece says yes and the relation behind it holds. -/
theorem accepts_false :
    ∃ b, ph.ior.red.out (RiderToy.s0, yB)
      ((zeroT [], ()), (0 : F5), (zeroT [], ()), (1 : F5), ()) = some b ∧
    ∃ y, Bound6 b () y ∧ RiderToy.sem.Out b.1 y :=
  ⟨((0, 1), yB), rfl, _, rfl, by
    show Dat.full (dat6 yB) 0 1
    unfold Dat.full Dat.row dat6 yB
    decide⟩

end RiderToyB

/-! ## 4 A member where one written round draws two elements: the error is the SUM -/

namespace RiderToyC
open LinkToy LinkToyB RiderToy RiderToyB
open _root_.Prob (cnt)

/-- A kit of challenges in which a round that draws has the 25 pairs of field elements as its raw
challenges. -/
def cCh : Fmt.Kind → Type
  | .nothing => Unit
  | _ => F5 × F5

instance cFin (k : Fmt.Kind) : Fintype (cCh k) := by
  cases k <;>
    first | exact (inferInstance : Fintype (F5 × F5)) | exact (inferInstance : Fintype Unit)

instance cNe (k : Fmt.Kind) : Nonempty (cCh k) := by
  cases k <;>
    first | exact (inferInstance : Nonempty (F5 × F5)) | exact (inferInstance : Nonempty Unit)

def cDr : (k : Fmt.Kind) → cCh k → Fmt.Drawn
  | .elems, c => ⟨[ext (show F5 × F5 from c).1, ext (show F5 × F5 from c).2], [], [], none⟩
  | _, _ => ⟨[], [], [], none⟩

def cC : CK where
  Ch := fun _ k => cCh k
  fin := fun _ k => cFin k
  ne := fun _ k => cNe k
  dr := fun _ k => cDr k
  front := (inferInstance : Unique Unit)

/-- The data of the one written round. -/
def cRD : RDT :=
  { entry := roundTwo.entry, kind := .elems, items := [], trees := [], opens := [], stored := [] }

/-- The piece: the block that hears both coordinates in one round, AT THE ERROR 10 OF 25: for each
of the two elements one bad value, times the five values of the other. -/
def p1 : Piece cC tF Pt Bool Unit :=
  ⟨below meantOne, 0, [cRD], [], fun _ _ w => w, (10, ())⟩

abbrev TrC : Type := Iop.Tr (uLT cC [cRD])

theorem shownC (y : tF.E.Str) (τ : TrC) :
    p1.shown y τ =
      ⟨[rv2 (ext (show F5 × F5 from τ.2.1).1) (ext (show F5 × F5 from τ.2.1).2)], []⟩ := by
  obtain ⟨m, c, u⟩ := τ
  rfl

/-- **The count of bad pairs is the sum**: at most one bad value of the first element, and for each
first element at most one bad value of the second: at most 5 + 5 of the 25 pairs. -/
theorem cnt_pair_le (B0 : Finset F5) (B1 : F5 → Finset F5) (h0 : B0.card ≤ 1)
    (h1 : ∀ a, (B1 a).card ≤ 1) :
    cnt (fun c : F5 × F5 => c.1 ∈ B0 ∨ c.2 ∈ B1 c.1) ≤ 10 := by
  classical
  unfold Prob.cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_or]
  refine (Finset.card_union_le _ _).trans ?_
  have e0 : (Finset.univ.filter fun c : F5 × F5 => c.1 ∈ B0).card ≤ 5 := by
    have hs : (Finset.univ.filter fun c : F5 × F5 => c.1 ∈ B0) ⊆ B0 ×ˢ Finset.univ := by
      intro c hc
      simpa using hc
    refine (Finset.card_le_card hs).trans ?_
    rw [Finset.card_product, Finset.card_univ, ZMod.card]
    omega
  have e1 : (Finset.univ.filter fun c : F5 × F5 => c.2 ∈ B1 c.1).card ≤ 5 := by
    have hs : (Finset.univ.filter fun c : F5 × F5 => c.2 ∈ B1 c.1) ⊆
        Finset.univ.biUnion fun a : F5 => ({a} : Finset F5) ×ˢ B1 a := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton]
      exact ⟨c.1, rfl, hc⟩
    refine (Finset.card_le_card hs).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ a : F5, (({a} : Finset F5) ×ˢ B1 a).card ≤ ∑ _a : F5, 1 :=
          Finset.sum_le_sum fun a _ => by
            rw [Finset.card_product, Finset.card_singleton, one_mul]; exact h1 a
      _ = 5 := by simp [ZMod.card]
  omega

theorem readsC : p1.ReadsAll rd fun _ _ => 1 := by
  intro B hB y
  refine ⟨(fun _ => {c | (show F5 × F5 from c).1 ∈ B [] [] [] ∨
      (show F5 × F5 from c).2 ∈ B [] [] [ext (show F5 × F5 from c).1]}, fun _ _ => ()),
    ⟨fun _ => cnt_pair_le (B [] [] []) (fun a => B [] [] [ext a]) (hB [] [] [])
      (fun a => hB [] [] [ext a]), fun _ _ => trivial⟩, ?_⟩
  rintro ⟨m, c, u⟩ hclean _ pre r post hpr xs x ys hx
  rw [shownC] at hpr
  have hc := not_or.1 hclean.1
  match pre, hpr with
  | [], hpr =>
    obtain ⟨rfl, _⟩ := List.cons.inj hpr
    match xs, hx with
    | [], hx =>
      obtain ⟨rfl, _⟩ := List.cons.inj hx
      rw [rd_ext]
      exact hc.1
    | [a], hx =>
      obtain ⟨rfl, hx'⟩ := List.cons.inj hx
      obtain ⟨rfl, _⟩ := List.cons.inj hx'
      rw [rd_ext]
      exact hc.2
    | _ :: _ :: xs, hx => exact absurd (List.cons.inj (List.cons.inj hx).2).2 (by simp)
  | _ :: pre, hpr => exact absurd (List.cons.inj hpr).2 (by simp)

theorem carryC (a : Pt × tF.E.Str) (τ : TrC) (b : Pt × tF.E.Str)
    (h : p1.ior.red.out a τ = some b) : dat6 b.2 = dat6 a.2 := by
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **ALL PREMISES OF `hear_goodIn` HOLD TOGETHER WHERE ONE ROUND DRAWS TWO ELEMENTS**: at the error
10 of 25. -/
theorem member : p1.GoodIn (fun _ => True) (fun _ => True)
    (fun a w => ∃ y, Bound6 a w y ∧ semOne.In a.1 y)
    (fun b w => ∃ y, Bound6 b w y ∧ semOne.Out b.1 y) :=
  hear_goodIn semOne meantOne meantOne_sound p1 rfl (fun _ _ _ => rfl) _ _ Bound6
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ h h' => h.trans h'.symm)
    (fun a τ b _ _ _ hout hB => hB.trans (carryC a τ b hout)) readsC

/-- TEETH: the round has 25 raw challenges. -/
theorem challenges : Nat.card (roundT cC cRD).up.Chal = 25 := by
  show Nat.card (F5 × F5) = 25
  simp

/-- TEETH: at the oracles `yB` (the guest's first value is 1) and the raw challenge (0, 1) the piece
says yes and the relation behind it holds, though the relation in front has no witness. -/
theorem accepts_false :
    ∃ b, p1.ior.red.out (RiderToy.s0, yB) ((zeroT [], ()), ((0, 1) : F5 × F5), ()) = some b ∧
    ∃ y, Bound6 b () y ∧ semOne.Out b.1 y :=
  ⟨((0, 1), yB), rfl, _, rfl, by
    show Dat.full (dat6 yB) 0 1
    unfold Dat.full Dat.row dat6 yB
    decide⟩

end RiderToyC

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.hear_goodIn
#print axioms VerifiableInference.Desc.Sound.eachGoodIn_append
#print axioms VerifiableInference.Desc.Sound.link_row
#print axioms VerifiableInference.Desc.Sound.RiderToyB.shownH
#print axioms VerifiableInference.Desc.Sound.RiderToyB.readsH
#print axioms VerifiableInference.Desc.Sound.RiderToyB.carryH
#print axioms VerifiableInference.Desc.Sound.RiderToyB.member
#print axioms VerifiableInference.Desc.Sound.RiderToyB.front_false
#print axioms VerifiableInference.Desc.Sound.RiderToyB.accepts_false
#print axioms VerifiableInference.Desc.Sound.RiderToyC.shownC
#print axioms VerifiableInference.Desc.Sound.RiderToyC.cnt_pair_le
#print axioms VerifiableInference.Desc.Sound.RiderToyC.readsC
#print axioms VerifiableInference.Desc.Sound.RiderToyC.carryC
#print axioms VerifiableInference.Desc.Sound.RiderToyC.member
#print axioms VerifiableInference.Desc.Sound.RiderToyC.challenges
#print axioms VerifiableInference.Desc.Sound.RiderToyC.accepts_false
