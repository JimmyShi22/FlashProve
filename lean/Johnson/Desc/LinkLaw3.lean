-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/LinkLaw3.lean: the law of a segment's batching (Johnson/Desc/LinkLaw2.lean) in the form
that the rule of composition for a chain asks of a block: `Piece.GoodIn`
(Johnson/Desc/Sound/GoodIn.lean). Two theorems, from named premises.

The setting. The rule of composition (Johnson/Desc/Sound/ChainRule.lean) takes each block of a chain
with the written rounds that belong to it (a `Piece`) as an interactive oracle reduction. A
statement at a boundary between two blocks is a pair: the state that the verifier carries, and the
strings of all oracles. What a block owes is `GoodIn`: from every statement with the condition
in front, at the piece's errors (for each written round a number of raw challenges), the prover has
lost towards: where the block says yes, the condition behind holds, and a witness of the relation
behind gives a witness of the relation in front.

What is said.
  `batch_goodIn`: the piece that holds a segment's batching block has `GoodIn` from "all
    equations of the segment hold at the data to which the prover is bound" to "the runs behind the
    batching return, and the one equation in the state, read at the state that they return, holds
    at these data".
  `behind_goodIn`: the piece that holds the block of the runs behind the batching has it from
    that relation to "the one equation in the state holds", at any errors.
Both pieces hold their block with the test on the words in front (`below`, ChainRule.lean,
section 7): the chain's decision makes that test once, in front of its fold.

THE PREMISES BESIDE LinkLaw2's, AND WHO OWES EACH.
  `Bound a w y`: "y is the data to which the prover is bound at the statement a, as the witness w
    holds them". A letter. `huniq`: at one statement all witnesses hold the same data: THE PIN: a
    relation at a random combination must tie what it reads of the witness to the oracles' strings,
    or some witness passes at every challenge. `hcarry`: the block does not turn the data.
    Owed by whoever fills the chain's relations.
    WHO OWES THE PIN: not this file: the law of a sending with a sample (the row
    "words_are_committed" of the list of laws owed). AS THAT ROW's OWNERS WORD IT, NOT SHOWN HERE OR
    ANYWHERE YET: near a word there may be a list of codewords; the answered sample picks one member
    of the list; that pick's price is paid at the sample's round, and the pin must be handed on from
    there; at the draws of which these files speak (a rider's; the batching's) no factor of the
    list's size stands. (By the same account such a factor does stand at rounds of the closing,
    "BAT" and "FOLD epsilon": these are not this file's draw, which the plan names "BAT-sigma".)
    Every count here (d; deg; the maximum) is right for ONE datum.
  `Piece.Reads`: every set of at most d field elements is avoided by the element that the view
    shows as drawn, on every transcript on which the proofs of work pass and that is clean for some
    family of bad raw challenges within the piece's errors. Owed by the law of the reading of a
    round.
  `hready`, `hbehind`: the condition in front gives `ready`, or `behind`. `hhands`: the block
    hands on the condition behind: this is the first half of `GoodIn`'s own conclusion, asked
    outright, at every transcript. `hext`: the piece's extractor hands the witness on as it is.

A member (section 3): the toy of LinkLaw2.lean with a written round under its batching block, a kit
of five raw challenges, and the hidden values read off a stored table: all premises of
`batch_goodIn` hold together, at the error 2 of 5; and both of these two are paid for something.

Limits. As LinkLaw2.lean's. The premises are met together by that toy alone; its kit of challenges
has no proof of work, so "on which the proofs of work pass" is met idly there. An error that is the
number of a round's challenges makes `Reads` free and the conclusion empty. Nothing on the hearing
blocks, the closing, or the whole segment.

-/
import Johnson.Desc.LinkLaw2
import Johnson.Desc.Sound.GoodInProofs
import Johnson.Desc.Sound.FoldBelowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S Cl W P Y K : Type} {C : CK} {F : Frame}

/-! ## 1 What a yes of a piece says of the fold -/

/-- What a piece's verifier is shown at the oracles' strings y and the transcript τ. -/
def Piece.shown (p : Piece C F S Cl W) (y : F.E.Str) (τ : Iop.Tr (uLT C p.ds)) : Fmt.View :=
  ⟨(sView C p.stage y τ).rounds ++ p.back, (sView C p.stage y τ).opened⟩

theorem endOk_gives {x : Except String (S × List Fmt.RoundView × List OpenedColumn)} {s : S}
    (h : endOk x = some s) : x = .ok (s, [], []) := by
  cases x with
  | error e => cases h
  | ok t =>
    obtain ⟨s', rs, cs⟩ := t
    cases rs with
    | nil =>
      cases cs with
      | nil => cases h; rfl
      | cons _ _ => cases h
    | cons _ _ => cases h

/-- Where a piece that holds `below b` says yes: the proofs of work pass, all words shown are below
the prime, and the fold over the one block b returns the state behind, with nothing left over. -/
theorem Piece.out_below {p : Piece C F S Cl W} {b : Block S Cl} (hb : p.b = below b)
    {a a' : S × F.E.Str} {τ : Iop.Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some a') :
    passT C p.ds (rhoT C p.ds τ) = true ∧ viewWordsBelowPrime (p.shown a.2 τ) = true ∧
      foldBlocks F.ft [b] a.1 (p.shown a.2 τ).rounds (p.shown a.2 τ).opened =
        .ok (a'.1, [], []) := by
  obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 h
  have h1 : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none) =
    some xo := hxo
  split at h1
  · next ht =>
    have hp : passT C p.ds (rhoT C p.ds τ) = true := by
      have ht' : (passT C p.ds (rhoT C p.ds τ) && fullOf p.ds (drawnT C p.ds (rhoT C p.ds τ)) &&
        sCarries p.stage a.2 (sWants C p.stage (rhoT C p.ds τ))) = true := ht
      simp only [Bool.and_eq_true] at ht'
      exact ht'.1.1
    have h2 : (chainAt p.b.name F.ft [p.b] a.1 (p.shown a.2 τ)).toOption = some xo := h1
    rw [chainAt_toOption, hb] at h2
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h2
    have h3 : endOk (foldBlocks F.ft ([b].map below) a.1 (p.shown a.2 τ).rounds
      (p.shown a.2 τ).opened) = some xo := h2
    rw [endOk_below] at h3
    split at h3
    · next hw => exact ⟨hp, hw, endOk_gives h3⟩
    · cases h3
  · cases h1

/-- The fold over one block, with no round left over, is the block's step on all the rounds. -/
theorem fold_one {ft : ℕ} {b : Block S Cl} {s s' : S} {rs : List Fmt.RoundView} {cols cols' : List OpenedColumn}
    (h : foldBlocks ft [b] s rs cols = .ok (s', [], cols')) :
    ∃ k, b.step ft s rs cols = .ok (s', k) := by
  obtain ⟨s₁, k, _, hs, h2⟩ := foldBlocks_cons_yes h
  simp only [foldBlocks, Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, hd, _⟩ := h2
  rw [List.take_of_length_le (List.drop_eq_nil_iff.1 hd)] at hs
  exact ⟨k, hs⟩

/-- The fold over the block of the runs behind the batching. -/
theorem behind_ok {L : Link S Cl} {ft : ℕ} {s s' : S} {rs rs' : List Fmt.RoundView}
    {cols cols' : List OpenedColumn} (h : foldBlocks ft [L.behindB] s rs cols = .ok (s', rs', cols')) :
    afterIn L.hear L.orderAfter s = .ok s' := by
  obtain ⟨s₁, k, _, hq, h2⟩ := foldBlocks_cons_yes h
  have hq : L.behindB.step ft s [] cols = .ok (s₁, k) := hq
  simp only [foldBlocks, Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, _, _⟩ := h2
  rw [Link.behindB, quiet_step] at hq
  cases ha : L.runBehind s with
  | error e => rw [ha] at hq; cases hq
  | ok z =>
    rw [ha] at hq
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hq
    rw [← hq.1]
    exact Link.afterIn_of_runBehind ha

/-! ## 2 The two pieces -/

/-- **From field elements to raw challenges**, as a premise on a piece. rd: how a drawn element, as
a view shows it, is read as an element of the field. For every set B of at most d field elements and
all oracles' strings there is a family of bad raw challenges within the piece's errors such that on
every clean transcript ON WHICH THE PROOFS OF WORK PASS the one element that the view shows as
drawn, if there is just one, is outside B. (So a raw challenge that fails the work need not be
counted as bad: the work is counted.) -/
def Piece.Reads (p : Piece C F S Cl W) (rd : Fmt.Ext → K) (d : ℕ) : Prop :=
  ∀ B : Finset K, B.card ≤ d → ∀ y : F.E.Str,
    ∃ fam : Iop.BadFam (uLT C p.ds), fam.Within p.err ∧
      ∀ τ, fam.Clean τ → passT C p.ds (rhoT C p.ds τ) = true →
        ∀ x, (p.shown y τ).rounds.flatMap (·.drawn.elems) = [x] → rd x ∉ B

variable [Field K] [Fintype K] [DecidableEq K]

open Classical in
/-- The bad field elements at a statement: those of LinkLaw2.lean at the data to which the prover
is bound there; none where the condition fails or no witness holds data. -/
def badAt (X : LinkSem K S Cl P Y) (L : Link S Cl) (on : S × F.E.Str → Prop)
    (Bound : S × F.E.Str → W → Y → Prop) (a : S × F.E.Str) : Finset K :=
  if h : on a ∧ ∃ y, ∃ w, Bound a w y then X.bad L.order (X.fixed a.1) (Classical.choose h.2)
  else ∅

/-- **The batching's piece is good**, in the form that the rule of composition asks. -/
theorem batch_goodIn (X : LinkSem K S Cl P Y) (L : Link S Cl) (d : ℕ)
    (H : X.Premises L F.ft d) (p : Piece C F S Cl W) (hb : p.b = below L.batchB)
    (hext : ∀ a τ w, p.ext a τ w = w) (on on' : S × F.E.Str → Prop)
    (Bound : S × F.E.Str → W → Y → Prop)
    (hready : ∀ a, on a → X.ready a.1)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (huniq : ∀ a w w' y y', on a → Bound a w y → Bound a w' y' → y = y')
    (hcarry : ∀ a τ b w y, on a → p.ior.red.out a τ = some b → Bound b w y → Bound a w y)
    (hreads : p.Reads X.rd d) :
    p.GoodIn on on' (fun a w => ∃ y, Bound a w y ∧ X.AllEq L.hear (X.fixed a.1) y)
      (fun b w => ∃ y, Bound b w y ∧
        ∃ t, afterIn L.hear L.orderAfter b.1 = .ok t ∧ X.one t b.1 y = 0) := by
  have hcard : ∀ a, (badAt X L on Bound a).card ≤ d := by
    intro a
    unfold badAt
    split
    · next h => exact X.bad_card_le H.square (H.exps a.1 (hready a h.1)) _
    · simp
  refine goodInOfBadFam S Cl W C F p on on' _ _
    (fun a => Classical.choose (hreads _ (hcard a) a.2)) ?_ ?_ ?_
  · intro a _
    exact (Classical.choose_spec (hreads _ (hcard a) a.2)).1
  · intro a τ b ha _ hout
    exact hhands a τ b ha hout
  · rintro a τ b w ha hclean hout ⟨y, hB, t, hat, hone⟩
    rw [hext]
    have hBa := hcarry a τ b w y ha hout hB
    refine ⟨y, hBa, ?_⟩
    obtain ⟨hp, hw, hfold⟩ := Piece.out_below hb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    obtain ⟨x, hx, hbh, hv⟩ := H.batch_value (hready a ha) hw hs
    have hnb := (Classical.choose_spec (hreads _ (hcard a) a.2)).2 τ hclean hp x hx
    have hex : on a ∧ ∃ y, ∃ w, Bound a w y := ⟨ha, y, w, hBa⟩
    have hy : Classical.choose hex.2 = y := by
      obtain ⟨w', hw'⟩ := Classical.choose_spec hex.2
      exact huniq a w' w _ _ ha hw' hBa
    unfold badAt at hnb
    rw [dif_pos hex, hy] at hnb
    have hl := (X.afterIn_keeps H.later H.after _ _ _ hbh hat).2.1
    exact H.back (by rw [← hv t y hl (H.full _ _ hbh hat)]; exact hone) hnb

omit [Fintype K] [DecidableEq K] in
/-- The batching's piece hands on `behind`: so the condition at the boundary behind it can hold it,
as `behind_goodIn` asks (`hbehind`). -/
theorem batch_hands (X : LinkSem K S Cl P Y) (L : Link S Cl) (d : ℕ)
    (H : X.Premises L F.ft d) (p : Piece C F S Cl W) (hb : p.b = below L.batchB)
    (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hr : X.ready a.1)
    (hout : p.ior.red.out a τ = some b) : X.behind b.1 := by
  obtain ⟨_, hw, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨_, _, hbh, _⟩ := H.batch_value hr hw hs
  exact hbh

omit [Fintype K] [DecidableEq K] in
/-- **The piece of the runs behind the batching is good**, at any errors. -/
theorem behind_goodIn (X : LinkSem K S Cl P Y) (L : Link S Cl) (hl : X.LaterOk)
    (hafter : X.AfterKeeps L.hear)
    (p : Piece C F S Cl W) (hb : p.b = below L.behindB)
    (hext : ∀ a τ w, p.ext a τ w = w) (on on' : S × F.E.Str → Prop)
    (Bound : S × F.E.Str → W → Y → Prop)
    (hbehind : ∀ a, on a → X.behind a.1)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (hcarry : ∀ a τ b w y, on a → p.ior.red.out a τ = some b → Bound b w y → Bound a w y) :
    p.GoodIn on on'
      (fun a w => ∃ y, Bound a w y ∧
        ∃ t, afterIn L.hear L.orderAfter a.1 = .ok t ∧ X.one t a.1 y = 0)
      (fun b w => ∃ y, Bound b w y ∧ X.one b.1 b.1 y = 0) := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ b hout => ⟨hhands a τ b ha hout, ?_⟩
  rintro w ⟨y, hB, hone⟩
  rw [hext]
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  have hat := behind_ok hfold
  refine ⟨y, hcarry a τ b w y ha hout hB, b.1, hat, ?_⟩
  rw [← (X.afterIn_keeps hl hafter _ _ _ (hbehind a ha) hat).2.2 b.1 y (hl.1 b.1)]
  exact hone

/-! ## 3 A member: all premises of `batch_goodIn` together, at a written round -/

namespace LinkToyB
open LinkToy
open _root_.Prob (cnt cnt_mono)

/-- A kit of challenges of the toy's own: a round that draws elements has the five elements of the
toy's field as its raw challenges. -/
def tCh : Fmt.Kind → Type
  | .nothing => Unit
  | _ => F5

instance tFin (k : Fmt.Kind) : Fintype (tCh k) := by
  cases k <;> first | exact (inferInstance : Fintype F5) | exact (inferInstance : Fintype Unit)

instance tNe (k : Fmt.Kind) : Nonempty (tCh k) := by
  cases k <;> first | exact (inferInstance : Nonempty F5) | exact (inferInstance : Nonempty Unit)

/-- A raw challenge as the drawn element that a view shows. -/
def ext (c : F5) : Fmt.Ext := (c.val.toUInt64, 0, 0)

def tDr : (k : Fmt.Kind) → tCh k → Fmt.Drawn
  | .elems, c => ⟨[ext (show F5 from c)], [], [], none⟩
  | _, _ => ⟨[], [], [], none⟩

def tC : CK where
  Ch := fun _ k => tCh k
  fin := fun _ k => tFin k
  ne := fun _ k => tNe k
  dr := fun _ k => tDr k
  front := (inferInstance : Unique Unit)

/-- The data of the batching's one written round. -/
def tRD : RDT :=
  { entry := LinkToy.round.entry, kind := .elems, items := [], trees := [], opens := []
    stored := [] }

/-- No tree; a stored table with one leaf. -/
def tF : Frame := ⟨0, [], id, 0⟩

/-- THE DATA TO WHICH THE PROVER IS BOUND: the two hidden values are the first two words of the
stored table's one leaf. -/
def dat (y : tF.E.Str) : F5 × F5 :=
  match (y.1 ⟨0, by decide⟩).2 with
  | a :: b :: _ => ((a.toNat : F5), (b.toNat : F5))
  | _ => (0, 0)

/-- The piece: the toy's batching block with the test on the words in front, at its written round,
at the error 2 (of 5 raw challenges). -/
def pb : Piece tC tF St TClaim Unit :=
  ⟨below meant.batchB, 0, [tRD], [], fun _ _ w => w, (2, ())⟩

def Bound (a : St × tF.E.Str) (_ : Unit) (y : F5 × F5) : Prop := y = dat a.2

abbrev TrB : Type := Iop.Tr (uLT tC [tRD])

theorem shownB (y : tF.E.Str) (τ : TrB) :
    pb.shown y τ = ⟨[rv (ext (show F5 from τ.2.1))], []⟩ := by
  obtain ⟨m, c, u⟩ := τ
  rfl

theorem rd_ext (c : F5) : rd (ext c) = c := by
  revert c
  decide

theorem cnt_mem_le (B : Finset F5) : cnt (fun c : F5 => c ∈ B) ≤ B.card := by
  unfold Prob.cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem readsB : pb.Reads rd 2 := by
  intro B hB y
  refine ⟨(fun _ => {c | (show F5 from c) ∈ B}, fun _ _ => ()),
    ⟨fun _ => (cnt_mem_le B).trans hB, fun _ _ => trivial⟩, ?_⟩
  rintro τ hclean _ x hx
  rw [shownB] at hx
  have hx' : [ext (show F5 from τ.2.1)] = [x] := hx
  obtain rfl := (List.cons.inj hx').1
  rw [rd_ext]
  exact hclean.1

theorem carryB (a : St × tF.E.Str) (τ : TrB) (b : St × tF.E.Str)
    (h : pb.ior.red.out a τ = some b) : dat b.2 = dat a.2 := by
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **ALL PREMISES OF `batch_goodIn` HOLD TOGETHER, AND SO ITS CONCLUSION**: at the error 2 of 5. -/
theorem member : pb.GoodIn (fun a => a.1.w = none) (fun _ => True)
    (fun a w => ∃ y, Bound a w y ∧ sem.AllEq meant.hear (sem.fixed a.1) y)
    (fun b w => ∃ y, Bound b w y ∧
      ∃ t, afterIn meant.hear meant.orderAfter b.1 = .ok t ∧ sem.one t b.1 y = 0) :=
  batch_goodIn sem meant 2 meant_premises pb rfl (fun _ _ _ => rfl) _ _ Bound
    (fun _ h => h) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ h h' => h.trans h'.symm)
    (fun a τ b _ _ _ hout hB => hB.trans (carryB a τ b hout)) readsB

/-- TEETH: the round has five raw challenges. -/
theorem five_challenges : Nat.card (roundT tC tRD).up.Chal = 5 := by
  show Nat.card F5 = 5
  simp

/-- Oracles at which both equations fail: the hidden values are 1, 1. -/
def y1 : tF.E.Str := (fun _ => (0, [1, 1]), fun _ => [])

/-- TEETH: there, at the scalar heard 1, the relation in front has no witness. -/
theorem front_false : ¬ ∃ y, Bound (s0, y1) () y ∧ sem.AllEq meant.hear (sem.fixed s0) y := by
  rintro ⟨y, rfl, h⟩
  exact absurd (h (0, "both") (both_mem weigh) 2 (by simp [sem, dat, y1, s0])) (by decide)

/-- TEETH: THE ERROR 2 IS PAID FOR SOMETHING: the polynomial there is 2 + 2 x ^ 2, with the roots 2
and 3: at these oracles and the raw challenge 2 the piece says yes and the relation behind it holds,
though the relation in front has no witness … -/
theorem accepts_false_2 :
    ∃ b, pb.ior.red.out (s0, y1) ((zeroT [], ()), (2 : F5), ()) = some b ∧
    ∃ y, Bound b () y ∧
      ∃ t, afterIn meant.hear meant.orderAfter b.1 = .ok t ∧ sem.one t b.1 y = 0 :=
  ⟨(⟨1, 2, (1, 4), none⟩, y1), rfl, (1, 1), rfl, ⟨1, 2, (1, 4), some 2⟩, rfl,
    show (2 : F5) * (1 * 1 + 4 * 1) = 0 by decide⟩

/-- … and at the raw challenge 3. -/
theorem accepts_false_3 :
    ∃ b, pb.ior.red.out (s0, y1) ((zeroT [], ()), (3 : F5), ()) = some b ∧
    ∃ y, Bound b () y ∧
      ∃ t, afterIn meant.hear meant.orderAfter b.1 = .ok t ∧ sem.one t b.1 y = 0 :=
  ⟨(⟨1, 3, (1, 4), none⟩, y1), rfl, (1, 1), rfl, ⟨1, 3, (1, 4), some 2⟩, rfl,
    show (2 : F5) * (1 * 1 + 4 * 1) = 0 by decide⟩

end LinkToyB

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.endOk_gives
#print axioms VerifiableInference.Desc.Sound.Piece.out_below
#print axioms VerifiableInference.Desc.Sound.fold_one
#print axioms VerifiableInference.Desc.Sound.behind_ok
#print axioms VerifiableInference.Desc.Sound.batch_goodIn
#print axioms VerifiableInference.Desc.Sound.batch_hands
#print axioms VerifiableInference.Desc.Sound.behind_goodIn
#print axioms VerifiableInference.Desc.Sound.LinkToyB.shownB
#print axioms VerifiableInference.Desc.Sound.LinkToyB.rd_ext
#print axioms VerifiableInference.Desc.Sound.LinkToyB.cnt_mem_le
#print axioms VerifiableInference.Desc.Sound.LinkToyB.readsB
#print axioms VerifiableInference.Desc.Sound.LinkToyB.carryB
#print axioms VerifiableInference.Desc.Sound.LinkToyB.member
#print axioms VerifiableInference.Desc.Sound.LinkToyB.five_challenges
#print axioms VerifiableInference.Desc.Sound.LinkToyB.front_false
#print axioms VerifiableInference.Desc.Sound.LinkToyB.accepts_false_2
#print axioms VerifiableInference.Desc.Sound.LinkToyB.accepts_false_3
