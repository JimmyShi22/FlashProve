-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
SortDigits.lean: THE SORT OF THE SEGMENT's OWN PART FROM THE LOOKUP
ON THE CALLS TO THE LOOKUP ON THE DIGITS: at each of the six borders 14 l + 3 … 14 l + 8 of a
segment l < 24: here = .lay b where the written sort is «layers», here = .att b where it is
«attention».
`SortField` has it at 14 l + 3 alone. In the form of our theorems for FoldFacts' fields:
general in «reached» and in the reader; it goes in no structure. Typed on part 5's
K3 lead's piece («the sort of the open part at the digits' border»).

WHAT IS SAID.
  digitsAll, digits_there   a test with code on the written list of places, decided by the kernel:
                     at each of the 24 numbers 14 l + 8 it has a place of kind K3 with piece 7 in
                     segment l. digits_reject: on the list without its first place it rejects.
  alone_stand · k1Reads_stand · k1_at_stand · hear_stand   the five sub-protocols between (K3 · the
                     segment's own kind · K1 · K8 · K1) each keep where the state stands.
                     THIS IS OwnAt's alone_same · k1Reads_same · k1_at_same · hear_same,
                     TYPED AGAIN WITH StandKept (Johnson/IMR/StandKept.lean) IN SameCtx's PLACE.
  stand_at           so standOf at border 14 l + 3 + n, n ≤ 5, is standOf at 14 l + 3 (after
                     OwnAt's ctx_at).
  lay_of_stand, att_of_stand   what part 5's standOf says of «here».
  lay_fold, att_fold the sort at border 14 l + 3 in the fold's form (SortField's tops' own proof).
  lay_hear_at, att_hear_at     **the tops, at all six borders.**
  lay_digits_at, att_digits_at **the piece's own text: the border 14 l + 8.**
THE PREMISES IN FRONT, BY NAME: hS · hR · O · hRch · l < 24 · the written sort at l. The fence «no
mark» stands among the binders for the form's sake and IS NOT SPENT. No test on the plan is asked.
What is not claimed. The head's segment. Anything on the merge's slot. That a state is reached: NO
MEMBER. No soundness.

-/
import Johnson.IMR.SortField
import Johnson.IMR.OwnAt
import Johnson.IMR.StandKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc (Place KindName)

/-- At each number 14 l + 8, l < 24, the list has a place of kind K3 with piece 7 in segment l. A
test with code. -/
def digitsAll (ps : List Place) : Bool :=
  (List.range 24).all fun l =>
    match ps[14 * l + 8]? with
    | some p => (p.kind == KindName.K3) && (p.piece == 7) && (p.link == some l)
    | none => false

set_option maxRecDepth 1000000 in
theorem digits_there : digitsAll placesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test. -/
theorem digits_reject : digitsAll (placesW.drop 1) = false := by decide +kernel

end IM

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-! ## The sub-protocols between keep where the state stands -/

theorem alone_stand {b b' : Block S Cl} {a : Place} (hk : a.kind ≠ KindName.K7)
    (la : IM.LaidAlone ProofFile.sameReply b b' b.name a) (W : Decides StandKept b') :
    Decides StandKept b :=
  fun s rs gs t h => W s rs gs t ((IM.yes_alone la hk s t rs gs).1 h).1

theorem k1Reads_stand (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH) (pr : Nat)
    (reads : Option (List Nat)) : Decides StandKept (IM.k1Reads Z G l X pr reads) :=
  fun s rs gs t h => by
    obtain ⟨v, a1, a2⟩ := andThen_yes h
    exact stand_trans _ _ _ ((commitAtS_stand _ _ _ _).1 s _ _ v a1)
      (stand_of_quiet ((orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2))

theorem k1_at_stand (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {i : Nat} (hi : i = 3 ∨ i = 5) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[i]? = some b) : Decides StandKept b := by
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some KindName.K1 := by
    unfold IM.subAt
    rw [if_neg (by omega : ¬ l = 24)]
    by_cases h0 : l = 0
    · subst h0
      rcases hi with rfl | rfl <;> rfl
    · have e0 : (l == 0) = false := by simpa using h0
      rw [e0]
      rcases hi with rfl | rfl <;> split <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l (by omega)) i hk
      (by rcases hi with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · exact alone_stand (by intro k; cases k) la fun s rs gs t h =>
      k1Reads_stand _ _ _ _ _ s rs gs t h
  · exact alone_stand (by intro k; cases k) la fun s rs gs t h =>
      (commitAtS_stand (Cl := Unit) _ _ _ _).1 s rs gs t h

/-- **Every hearing sub-protocol number 1 to 5 of a segment in front of the head's keeps where the
state stands.** -/
theorem hear_stand (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {j : Nat} (h1 : 1 ≤ j) (h5 : j ≤ 5) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[j]? = some b) : Decides StandKept b := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O l (by omega) false
    have ix : IM.k3Ix l false = 1 := by
      show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
      rw [if_neg (by omega : ¬ l = 24)]
      rfl
    rw [ix] at e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact alone_stand (by intro k; cases k) la (whole_stand (theStated_quiet _ _ _ _ _ _ k3)).1
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b', y, eL', e', -, la, -⟩ := IM.k4_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_stand (by intro k; cases k) la (whole_stand (blockAtC_quiet _)).1
    · obtain ⟨Lk', b', x, a, eL', e', k5, la, -⟩ := IM.k5_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_stand (by intro k; cases k) la fun s rs gs t h =>
        (whole_stand (k5AtN_quiet _ _ _ _ k5)).1 s rs gs t h
  · exact k1_at_stand hS hR O hl (Or.inl rfl) eL e
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b', Xl, hp, eL', e', -, la, -⟩ := IM.k8_of_layers hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_stand (by intro k; cases k) la (whole_stand (k8Whole_quiet _)).1
    · obtain ⟨Lk', b', Xl, a, eL', e', -, la, -⟩ := IM.k8_of_attention hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone_stand (by intro k; cases k) la (whole_stand (k8Whole_quiet _)).1
  · exact k1_at_stand hS hR O hl (Or.inr rfl) eL e

/-- **Where the state stands at border 14 l + 3 + n, n ≤ 5, is where it stands at 14 l + 3.** -/
theorem stand_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24) {s : S}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {t₁ : S} {R₁ : List Fmt.RoundView}
    {C₁ : List VerifiableInference.Desc.OpenedColumn}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) s R C = .ok (t₁, R₁, C₁)) :
    ∀ n ≤ 5, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) s R C = .ok (t, R', C') →
      standOf t = standOf t₁
  | 0, _, t, R', C', f => by
    have e : (t₁, R₁, C₁) = (t, R', C') := Except.ok.inj (f₁.symm.trans f)
    rw [← (Prod.mk.inj e).1]
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + 3 + n) f
    have k := stand_at hS hR O hl f₁ n (by omega) u Ru Cu fu
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
    rw [if_neg (by omega : ¬ l = 24)] at hlen
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 1]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : n + 1 < Lk.hear.length)⟩
    have ib : c.blocksInOrder[14 * l + 3 + n]? = some b := by
      have q := IM.hear_at_flat eL e
      rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) (n + 1)).trans
        (by omega : 14 * l + (n + 1) + 2 = 14 * l + 3 + n)] at q
    obtain ⟨rs, gs, d⟩ := fold_next ib fu f
    exact (hear_stand hS hR O hl (by omega) (by omega) eL e u rs gs t d).1.trans k

/-! ## What standOf says of the own part -/

theorem lay_of_stand {t : S} (h : standOf t = .link .layers) : ∃ b, t.here = .lay b := by
  unfold standOf at h
  split at h
  · cases h
  · exact ⟨_, by assumption⟩
  · cases h
  · split at h <;> cases h
  · cases h
  · cases h

theorem att_of_stand {t : S} (h : standOf t = .link .attention) : ∃ b, t.here = .att b := by
  unfold standOf at h
  split at h
  · cases h
  · cases h
  · exact ⟨_, by assumption⟩
  · split at h <;> cases h
  · cases h
  · cases h

/-! ## The sort at border 14 l + 3, in the fold's form -/

theorem lay_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (hw : IM.linksW[l]? = some ModelPart.layers) : ∃ b, t₁.here = .lay b := by
  obtain ⟨fs, fr, m, hfs, hf, y3⟩ := opened_at hS hR O h24 f₁
  obtain ⟨Y, hY, hk⟩ := opened_sort hfs hf y3
  have e := writtenSort_at hS hR O hY
  rw [hw] at e
  rcases hk with hk | ⟨-, hb⟩ | ⟨hk, -⟩
  · rw [hk] at e
    exact absurd e (by decide)
  · exact hb
  · rw [hk] at e
    exact absurd e (by decide)

theorem att_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (hw : IM.linksW[l]? = some ModelPart.attention) : ∃ b, t₁.here = .att b := by
  obtain ⟨fs, fr, m, hfs, hf, y3⟩ := opened_at hS hR O h24 f₁
  obtain ⟨Y, hY, hk⟩ := opened_sort hfs hf y3
  have e := writtenSort_at hS hR O hY
  rw [hw] at e
  rcases hk with hk | ⟨hk, -⟩ | ⟨-, hb⟩
  · rw [hk] at e
    exact absurd e (by decide)
  · rw [hk] at e
    exact absurd e (by decide)
  · exact hb

/-! ## The tops -/

/-- **At a layers' segment the own part is a layers' part, at all six borders 14 l + 3 + n.** -/
theorem lay_hear_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ l n a, l < 24 → n ≤ 5 → Rch (14 * l + 3 + n) a → (at_ a).2.failed = none →
      IM.linksW[l]? = some ModelPart.layers → ∃ b, (at_ a).2.here = .lay b := by
  intro l n a h24 hn hr _ hw
  obtain ⟨_, rs, cols, f⟩ := (reach_raw (hRch _ a hr)).fold
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) n f
  obtain ⟨b, hb⟩ := lay_fold hS hR O h24 f₁ hw
  refine lay_of_stand ((stand_at hS hR O h24 f₁ n hn _ _ _ f).trans ?_)
  unfold standOf
  rw [hb]

/-- **At an attention segment the own part is an attention's, at all six borders.** -/
theorem att_hear_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ l n a, l < 24 → n ≤ 5 → Rch (14 * l + 3 + n) a → (at_ a).2.failed = none →
      IM.linksW[l]? = some ModelPart.attention → ∃ b, (at_ a).2.here = .att b := by
  intro l n a h24 hn hr _ hw
  obtain ⟨_, rs, cols, f⟩ := (reach_raw (hRch _ a hr)).fold
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) n f
  obtain ⟨b, hb⟩ := att_fold hS hR O h24 f₁ hw
  refine att_of_stand ((stand_at hS hR O h24 f₁ n hn _ _ _ f).trans ?_)
  unfold standOf
  rw [hb]

/-- **In front of the lookup on the digits of a layers' segment.** -/
theorem lay_digits_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ l a, l < 24 → Rch (14 * l + 8) a → (at_ a).2.failed = none →
      IM.linksW[l]? = some ModelPart.layers → ∃ b, (at_ a).2.here = .lay b :=
  fun l a h24 hr hu hw => lay_hear_at hS hR O Rch at_ hRch l 5 a h24 (Nat.le_refl _) hr hu hw

/-- **In front of the lookup on the digits of an attention segment.** -/
theorem att_digits_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ l a, l < 24 → Rch (14 * l + 8) a → (at_ a).2.failed = none →
      IM.linksW[l]? = some ModelPart.attention → ∃ b, (at_ a).2.here = .att b :=
  fun l a h24 hr hu hw => att_hear_at hS hR O Rch at_ hRch l 5 a h24 (Nat.le_refl _) hr hu hw

end Meaning.K2

#print axioms IM.digits_there
#print axioms IM.digits_reject
#print axioms Meaning.K2.alone_stand
#print axioms Meaning.K2.k1Reads_stand
#print axioms Meaning.K2.k1_at_stand
#print axioms Meaning.K2.hear_stand
#print axioms Meaning.K2.stand_at
#print axioms Meaning.K2.lay_of_stand
#print axioms Meaning.K2.att_of_stand
#print axioms Meaning.K2.lay_fold
#print axioms Meaning.K2.att_fold
#print axioms Meaning.K2.lay_hear_at
#print axioms Meaning.K2.att_hear_at
#print axioms Meaning.K2.lay_digits_at
#print axioms Meaning.K2.att_digits_at
