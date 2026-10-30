-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyTests3Steps.lean: THE KEY FILE's LAST CHAIN: THE FACTS ON THE VERIFIER's STATE
ALONE (Tests₃, Johnson/RunOne/KeyOn3Parts.lean) AT THE CHAIN's START AND ACROSS ITS FOUR
SUB-PROTOCOLS, AT THE TABLES' LETTERS. No oracle string is read; no reading G₃, no letter coll.
Each proof is the state's share of a proof that lies already for the whole invariant:
  start₃E_lengths   the last chain's start asks in front that the codes' lengths are in order
  tests₃_start      Tests₂ at border 12 and the start's acceptance give Tests₃ at border 0, and the
                    codes' lengths in order at the new state (after seam₂On, KeySeam2On.lean)
  tests₃_01         what the first sub-protocol lays (Laid) carries Tests₃ from 0 to 1 (after
                    shape_forward | free_forward, KeyRow30.lean)
  tests₃_12         at ONE state, with the test on the taken trees' sources: from 1 to 2
  tests₃_23         across the own proximity test, from what its acceptance gives: from 2 to 3
  tests₃_34         at ONE state, with the chain's end's test: from 3 to 4
IMPLICATIONS: EACH IS EMPTY WHERE ITS PREMISE IN FRONT HOLDS OF NOTHING.
OBJECT: Tests₃ · USER: Johnson/Top/Fire/Code/KeyASide3AtFk.lean · LETTERS: the tables'.
Nothing on soundness.
-/
import Johnson.RunOne.KeyOn3Parts
import Johnson.RunOne.KeyOn2Parts
import Johnson.RunOne.KeySeam2On
import Johnson.RunOne.KeyRow30
import Johnson.Desc.K12.Law.OutK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third (FirstOut SharedOut firstOutFrom start₃ start₃E Laid Border)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open VerifiableInference.Desc.K12 (T12)

/-- The last chain's start asks in front that the codes' lengths are in order. -/
theorem start₃E_lengths (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : St₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    codes.lengthsOk = true := by
  unfold start₃E at h
  split at h
  · cases h
  · rename_i hc
    have h2 : (codes.lengthsOk && OnBytes.linOk codes S) = true := by simpa using hc
    simp only [Bool.and_eq_true] at h2
    exact h2.1

section
variable (at_ : Where) (S : LinShape) (K₁ : KPlan) (a : Nat) (idx : List Nat)
  (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **The start.** start: the start₃ of the IOP as written in Lean. -/
theorem tests₃_start (codes : Codes) (start : Xi → FirstState → St₂ → Except String St₃)
    (hst : Starts S codes start)
    (hl : ∀ s, last₁ s = true → handedB a idx s = true ∧
      K₁.orc 2 = some ((firstOf s).1.oracles.size - 2) ∧ (firstOf s).2.1.trees.size = t₁ ∧
      (∀ r, (firstOf s).2.2.2 = [r] → r.g.all (·.ok) = true) ∧ LinTie s)
    (hoff : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1)
    (x : Xi) (s₁ : FirstState) (s₂ : St₂) (s₃ : St₃) (hs : start x s₁ s₂ = .ok s₃)
    (T : Tests₂ at_ S K₁ a last₁ off₂ 12 ((x, s₁), s₂)) :
    Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 0 ((x, s₁, s₂), s₃) ∧
      s₃.st.codes.lengthsOk = true := by
  have hsh := T.shape
  obtain ⟨o, l, hlin₁, ⟨ho, hob, -, hoo⟩, he⟩ := hst x s₁ s₂ s₃ hs
  obtain ⟨hh, hw, ht, hgk, l', hl', t1, t2, t3⟩ := hl s₁ T.last
  have el : l' = l := Option.some.inj (hl'.symm.trans hlin₁)
  subst el
  have hf := form_of_shape₂ S a 12 s₂ hsh
  have hom := omega_of_shape₂ S a s₂ hsh
  obtain ⟨e1, e2, -, e4, e5, -, -, -, e9, -, -, f, hfo, eb, r₀, hr₀, hg₀⟩ :=
    start₃_full codes S _ _ _ _ _ _ _ o s₃ t1 t2 t3 he
  obtain ⟨f', -, e_st', -, -, c₁', c₂'⟩ := start₃_spec codes S _ _ _ _ _ _ _ o s₃ he
  have hcs : s₃.st.codes = codes := by rw [e_st', c₁']
  have hB : shapeB₃ S K₁ a idx src t₁ 0 s₃ = true := by
    have h1 := shape₃_first codes S a idx x s₁ s₂ o s₃ _ hf hh t1 t2 t3 he
    have h2 : (K₁.orc 2 == some s₃.loc.w) = true := by rw [hw, e4]; exact beq_self_eq_true _
    have h3 : borderB a s₃ = true := by
      unfold borderB
      rw [eb]
      have hcd : o.st.codes = s₃.st.codes := by rw [c₂', hcs]
      show (o.omega == 2 && LKFU.Shape23.msgIs o.st 2 (some a) false && f.g.all (·.ok) &&
        decide (o.st.codes = s₃.st.codes)) = true
      rw [decide_eq_true hcd, Bool.and_true, hoo, ho, hg₀, hgk r₀ hr₀, Bool.and_true]
      exact hom
    have h4 : (s₃.loc.firstTree == t₁ + 1) = true := by rw [e9, ht]; exact beq_self_eq_true _
    unfold shapeB₃
    rw [h1, h2, h3, h4]
    rfl
  have hom2 : s₂.loc.oOmega = 2 := by
    have := hom
    simp only [handed₂B, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  refine ⟨?_, by rw [hcs]; exact start₃E_lengths codes S _ _ _ _ _ _ _ o s₃ he⟩
  exact
    { shape := hB
      placed := fun _ k hk => by
        obtain ⟨o', t, h1, h2, h3⟩ := T.placed₁ k hk
        refine ⟨o', t, h1, ?_, ?_⟩
        · show s₃.book.place[o']? = some t
          rw [e2]
          exact h2
        · have e := hoff k hk
          rw [h3] at e ⊢
          exact Prod.ext e.symm rfl
      omega₀ := fun _ => ⟨_, eb, fun k hk => by
        have hk4 : k = 4 := by simpa using hk
        subst hk4
        obtain ⟨o', t, h1, h2, h3⟩ := T.placed 4 (by rw [open₂_last]; decide)
        have e1 : o' = 2 := by
          have : (plan₂ S).orc 4 = some 2 := rfl
          exact (Option.some.inj (h1.symm.trans this))
        subst e1
        refine ⟨2, t, ?_, ?_, h3⟩
        · show some o.omega = some 2
          rw [hoo, hom2]
        · show o.book.place[2]? = some t
          rw [hob]
          exact h2⟩
      omega := fun h1 => absurd h1 (by decide)
      order := by
        show Means.InOrder s₃.st
        rw [e1]
        exact T.order₁
      order₀ := fun _ => ⟨_, eb, by
        show Means.InOrder o.st
        rw [ho]
        exact T.order⟩
      maskW := by
        show MaskWith (fun i => s₃.book.place[i]?) s₃.loc.w (s₃.loc.w + 1)
        rw [e2]
        exact T.mask₁ s₃.loc.w (by rw [hw, e4])
      lin₀ := fun _ => by
        show OnBytes.linOk s₃.st.codes S = true
        rw [hcs]
        exact start₃E_lin codes S _ _ _ _ _ _ _ o s₃ he
      seatW := fun _ => by
        have hnum := seatW_of_numbers S f (firstOut_numbers S _ _ _ _ _ _ _ f hfo)
        obtain ⟨g1, -, -, g4, -⟩ := firstOutFrom_spec S _ _ _ _ _ _ _ f hfo
        obtain ⟨p1, -, p3, -⟩ := start₃_plain codes S _ _ _ _ _ _ _ o s₃ he
        show (s₃.st.oracles[s₃.loc.w]?).any (·.shape == S.w) = true
        rw [p1, p3, ← g4, ← g1]
        exact hnum
      seatOmega₀ := fun _ b hb => by
        have eb' : b = ⟨f.g, o⟩ := Option.some.inj (hb.symm.trans eb)
        subst eb'
        show (o.st.oracles[o.omega]?).any (·.shape == S.omega) = true
        rw [ho, hoo, hom2]
        exact T.seatOmega (by decide) }

variable {S}

/-- **0 → 1**: from what the first sub-protocol has laid. -/
theorem tests₃_01 (z : P₃) (s s' : St₃) {b : Border} {yO : OnBytes.Oracle} {G : OnBytes.Group}
    {dot : OnBytes.Row} (L : Laid S s s' b yO G dot) (hA : AtOk at_ off₂ off₃ t₁)
    (T : Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 0 (z, s)) :
    Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 1 (z, s') := by
  have Fr := front_of_shape S K₁ a idx src t₁ s T.shape
  have ht : s.book.trees.size = t₁ := by
    have c4 := Fr.trees
    have k2 := Fr.t₁
    omega
  have hord : Means.InOrder s'.st := by
    obtain ⟨b', hb', hO⟩ := T.order₀ rfl
    have e : b' = b := Option.some.inj (hb'.symm.trans L.border)
    exact L.order T.order (e ▸ hO)
  exact
    { shape := shape_forward S K₁ a idx src t₁ s s' L (idx_below Fr L.group T.order) T.shape
      placed := fun _ k hk => by
        obtain ⟨o, t, h1, h2, h3⟩ := T.placed (by decide) k hk
        have h2' : s.book.place[o]? = some t := h2
        exact ⟨o, t, h1, (L.oldPlaces o (Array.getElem?_eq_some_iff.1 h2').1).trans h2', h3⟩
      omega₀ := fun h0 => absurd h0 (by decide)
      omega := fun _ _ k hk => by
        have e : k = 4 := by simpa using hk
        subst e
        have eo : s'.loc.omega = s.st.oracles.size := by rw [L.loc]
        refine ⟨s'.loc.omega, (s.book.trees.size, 0), rfl, ?_, ?_⟩
        · show s'.book.place[s'.loc.omega]? = _
          rw [eo]
          exact L.place
        · rw [ht]
          exact hA.omega₃
      order := hord
      order₀ := fun h0 => absurd h0 (by decide)
      maskW := by
        obtain ⟨q, p, h1, h2⟩ := T.maskW
        have h1' : s.book.place[s.loc.w]? = some (q, p) := h1
        have h2' : s.book.place[s.loc.w + 1]? = some (q, p + 1) := h2
        have ew : s'.loc.w = s.loc.w := by rw [L.loc]
        refine ⟨q, p, ?_, ?_⟩
        · show s'.book.place[s'.loc.w]? = _
          rw [ew]
          exact (L.oldPlaces _ (Array.getElem?_eq_some_iff.1 h1').1).trans h1'
        · show s'.book.place[s'.loc.w + 1]? = _
          rw [ew]
          exact (L.oldPlaces _ (Array.getElem?_eq_some_iff.1 h2').1).trans h2'
      lin₀ := fun h0 => absurd h0 (by decide)
      seatW := fun h0 => absurd h0 (by decide)
      seatOmega₀ := fun h0 => absurd h0 (by decide) }

variable (S)

/-- **1 → 2**, at one state: the test on the taken trees' sources has accepted. -/
theorem tests₃_12 (z : P₃ × St₃) (hsrc : src z.2 = true)
    (T : Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 1 z) :
    Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 2 z :=
  { shape := by
      have hs := T.shape
      simp only [shapeB₃, Bool.and_eq_true] at hs ⊢
      exact ⟨⟨⟨⟨⟨hs.1.1.1.1.1, hs.1.1.1.1.2⟩, hs.1.1.1.2⟩, rfl⟩, by rw [hsrc]; rfl⟩, rfl⟩
    placed := fun _ => T.placed (by decide)
    omega₀ := fun h0 => absurd h0 (by decide)
    omega := fun _ _ => T.omega (by decide) (by decide)
    order := T.order
    order₀ := fun h0 => absurd h0 (by decide)
    maskW := T.maskW
    lin₀ := fun h0 => absurd h0 (by decide)
    seatW := fun h0 => absurd h0 (by decide)
    seatOmega₀ := fun h0 => absurd h0 (by decide) }

/-- **2 → 3**: across the own proximity test: tE: the state that the test leaves; the chain's local
state is not written. The three premises are what the test's acceptance gives. -/
theorem tests₃_23 (z : P₃ × St₃) (tE : T12)
    (hshape : shapeB₃ S K₁ a idx src t₁ 3
      { z.2 with st := tE.st, book := tE.book, roots := tE.roots } = true)
    (hbook : BookKeeps z.2.book tE.book) (hord : Means.InOrder z.2.st → Means.InOrder tE.st)
    (T : Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 2 z) :
    Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 3
      (z.1, { z.2 with st := tE.st, book := tE.book, roots := tE.roots }) :=
  { shape := hshape
    placed := fun c => absurd c (by omega)
    omega₀ := fun c => absurd c (by omega)
    omega := fun _ c => absurd c (by omega)
    order := hord T.order
    order₀ := fun c => absurd c (by omega)
    maskW := by
      obtain ⟨q, p, b1, b2⟩ := T.maskW
      exact ⟨q, p, hbook.place _ _ b1, hbook.place _ _ b2⟩
    lin₀ := fun c => absurd c (by omega)
    seatW := fun c => absurd c (by omega)
    seatOmega₀ := fun c => absurd c (by omega) }

/-- **3 → 4**, at one state: the chain's end's test has accepted. -/
theorem tests₃_34 (z : P₃ × St₃) (hfin : VerifiableInference.Desc.Third.fin₃ z.2 = true)
    (T : Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 3 z) :
    Tests₃ at_ S K₁ a idx src off₂ off₃ t₁ 4 z :=
  { shape := by
      have hs := T.shape
      simp only [shapeB₃, Bool.and_eq_true] at hs ⊢
      exact ⟨⟨⟨⟨⟨hs.1.1.1.1.1, hs.1.1.1.1.2⟩, hs.1.1.1.2⟩, rfl⟩, rfl⟩, by rw [hfin]; rfl⟩
    placed := fun h0 => absurd h0 (by decide)
    omega₀ := fun h0 => absurd h0 (by decide)
    omega := fun _ h0 => absurd h0 (by decide)
    order := T.order
    order₀ := fun h0 => absurd h0 (by decide)
    maskW := T.maskW
    lin₀ := fun h0 => absurd h0 (by decide)
    seatW := fun h0 => absurd h0 (by decide)
    seatOmega₀ := fun h0 => absurd h0 (by decide) }

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.start₃E_lengths
#print axioms Johnson.RunOne.KeyRows23.tests₃_start
#print axioms Johnson.RunOne.KeyRows23.tests₃_01
#print axioms Johnson.RunOne.KeyRows23.tests₃_12
#print axioms Johnson.RunOne.KeyRows23.tests₃_23
#print axioms Johnson.RunOne.KeyRows23.tests₃_34
