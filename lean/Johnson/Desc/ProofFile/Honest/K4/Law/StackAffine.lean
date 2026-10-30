-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackAffine.lean.

What is here. HOW THE END OF THE BATCHED SUMCHECK (`stackEndOf`, `stackEnd`:
OnBytes/Model/LayerPanels.lean) READS THE VALUES THAT WERE SHOWN. The verifier makes two numbers, As
and Bs, of the shown values: it starts from two of them and adds, panel by panel, a shown value
times a factor that does not read the shown values. Here, for a family of lists of shown values and
ANY property P of a family of elements that is kept when a fixed factor times a family with P is
added to a family with P: if every entry of the shown lists has P, the two numbers have P; the two
forms, the number of bits of the down product's panel, and whether the function returns at all, are
the same at all members of the family. It is spent at two properties: the family's two members read
alike; the family is a polynomial of degree at most 1 along a line. So the honest job's summand on
given end values (`StackData.summandOn`, Johnson/Desc/K4/Honest/Stack.lean) meets two of the three
premises that the cube's tie (CubeSum.lean) asks of a job. Statements and proofs.

  `Good`, `FamOK`, `famOK_none`, `famOK_pure`, `famOK_ite`, `famOK_bind`, `famOK_then`,
     `famOK_foldlM`, `P_foldl`   families of states of the loop
  `stackEndOf_fam`, `stackEnd_fam`   **one panel's step; the whole**
  `extract_getD`, `sidesOn_fam`   the honest side's call
  `summandOn_alike`, `summandOn_poly`   **the two premises**

Limits. On the verifier's public function and the honest side's call of it. THAT THE FUNCTION
RETURNS ANYWHERE IS NOT SAID. Nothing on what the two numbers are worth; the third premise (on the
true end values the summand is the cube's) is not touched. No property is claimed.
-/
import Johnson.Desc.K4.Honest.Stack
import Johnson.Desc.K4.Honest.Law.CubeInY

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE addE mulE)
open OnBytes.Model (Reading Aff)
open OnBytes.Model.Layer (Lay SBlk StackEnd stackEndOf stackEnd)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

variable {ι : Type} (P : (ι → E) → Prop)

/-- A family of states of the loop: the two forms and the number of bits are the same at all
members; the two numbers have P. -/
structure Good (s : ι → StackEnd) (A B : Aff) (w : ℕ) : Prop where
  Alin : ∀ x, (s x).Alin = A
  Blin : ∀ x, (s x).Blin = B
  wD : ∀ x, (s x).wD = w
  As : P fun x => (s x).As
  Bs : P fun x => (s x).Bs

/-- A family of answers: none at all members, or such a family of states. -/
def FamOK (g : ι → Option StackEnd) : Prop :=
  (∀ x, g x = none) ∨ ∃ s A B w, (∀ x, g x = some (s x)) ∧ Good P s A B w

variable {P}

theorem famOK_none : FamOK P fun _ : ι => none := Or.inl fun _ => rfl

theorem famOK_pure {s : ι → StackEnd} {A B : Aff} {w : ℕ} (h : Good P s A B w) :
    FamOK P fun x => pure (s x) := Or.inr ⟨s, A, B, w, fun _ => rfl, h⟩

theorem famOK_ite {c : Prop} [Decidable c] {g g' : ι → Option StackEnd} (h : FamOK P g)
    (h' : FamOK P g') : FamOK P fun x => if c then g x else g' x := by
  by_cases hc : c
  · simpa only [if_pos hc] using h
  · simpa only [if_neg hc] using h'

/-- Behind a reading that is the same at all members. -/
theorem famOK_bind {α : Type} (o : Option α) {g : α → ι → Option StackEnd}
    (h : ∀ a, FamOK P (g a)) : FamOK P fun x => o.bind fun a => g a x := by
  cases o with
  | none => exact famOK_none
  | some a => exact h a

/-- One step behind another. -/
theorem famOK_then {g : ι → Option StackEnd} {f : ι → StackEnd → Option StackEnd} (h : FamOK P g)
    (k : ∀ s A B w, Good P s A B w → FamOK P fun x => f x (s x)) :
    FamOK P fun x => (g x).bind (f x) := by
  rcases h with h | ⟨s, A, B, w, hs, hg⟩
  · exact Or.inl fun x => by
      show (g x).bind (f x) = none
      rw [h x]
      rfl
  · rcases k s A B w hg with h' | ⟨s', A', B', w', hs', hg'⟩
    · exact Or.inl fun x => by
        show (g x).bind (f x) = none
        rw [hs x]
        exact h' x
    · exact Or.inr ⟨s', A', B', w', fun x => by
        show (g x).bind (f x) = some (s' x)
        rw [hs x]
        exact hs' x, hg'⟩

/-- A loop whose step keeps such families. -/
theorem famOK_foldlM {α : Type} {f : ι → StackEnd → α → Option StackEnd}
    (h : ∀ a s A B w, Good P s A B w → FamOK P fun x => f x (s x) a) :
    ∀ (l : List α) s A B w, Good P s A B w → FamOK P fun x => l.foldlM (f x) (s x)
  | [], _, _, _, _, hg => famOK_pure hg
  | a :: l, s, A, B, w, hg => by
    have e : (fun x => (a :: l).foldlM (f x) (s x)) =
        fun x => (f x (s x) a).bind fun s' => l.foldlM (f x) s' := by
      funext x
      rw [List.foldlM_cons]
      rfl
    rw [e]
    exact famOK_then (h a s A B w hg) fun s' A' B' w' hg' => famOK_foldlM h l s' A' B' w' hg'

/-- A loop that adds to a number a fixed factor times an entry for each member of a list. -/
theorem P_foldl (hadd : ∀ (f g : ι → E) (c : E), P f → P g → P fun x => addE (f x) (mulE c (g x)))
    {α : Type} (c : α → E) (g : α → ι → E) (hg : ∀ a, P (g a)) (l : List α) :
    ∀ f : ι → E, P f → P fun x => l.foldl (fun a i => addE a (mulE (c i) (g i x))) (f x) := by
  induction l with
  | nil =>
    intro f hf
    exact hf
  | cons i l ih =>
    intro f hf
    have e : (fun x => (i :: l).foldl (fun a i => addE a (mulE (c i) (g i x))) (f x)) =
        fun x => l.foldl (fun a i => addE a (mulE (c i) (g i x)))
          (addE (f x) (mulE (c i) (g i x))) := by
      funext x
      rw [List.foldl_cons]
    rw [e]
    exact ih _ (hadd f (g i) (c i) hf (hg i))

/-! ## 1 One panel's step; the whole -/

/-- **One panel's step.** H1, V: the families of the shown values of the never-sent vectors and of
the weight claims. -/
theorem stackEndOf_fam
    (hadd : ∀ (f g : ι → E) (c : E), P f → P g → P fun x => addE (f x) (mulE c (g x)))
    (y : Lay) (rs : Array E) (lam : ℕ) (om : Array E) (H1 V : ι → Array E)
    (hH : ∀ k, P fun x => (H1 x).getD k zeroE) (hV : ∀ k, P fun x => (V x).getD k zeroE)
    (b : SBlk) (s : ι → StackEnd) (A B : Aff) (w : ℕ) (hs : Good P s A B w) :
    FamOK P fun x => stackEndOf y rs lam om (H1 x) (V x) (s x) b := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, wb, off, sA, sB, wt, sl, xx, virt⟩ := b
  unfold stackEndOf
  cases tri with
  | true =>
    cases virt with
    | some k =>
      simp only [↓reduceIte]
      refine famOK_ite famOK_none (famOK_bind _ fun _ => famOK_bind _ fun v0' =>
        famOK_ite famOK_none (famOK_pure (A := A) (B := B) (w := w)
          ⟨hs.Alin, hs.Blin, hs.wD, hadd _ _ _ hs.As (hH k), hadd _ _ _ hs.Bs (hV v0')⟩))
    | none =>
      simp only [↓reduceIte, hs.Alin]
      refine famOK_ite famOK_none (famOK_bind _ fun _ => famOK_bind _ fun v0' =>
        famOK_pure (B := B) (w := w)
          ⟨fun _ => rfl, hs.Blin, hs.wD, hs.As, hadd _ _ _ hs.Bs (hV v0')⟩)
  | false =>
    cases virt with
    | some k =>
      simp only [Bool.false_eq_true, ↓reduceIte, hs.wD]
      refine famOK_ite famOK_none (famOK_bind _ fun _ => famOK_bind _ fun v0' =>
        famOK_ite famOK_none (famOK_pure (A := A) (B := B) (w := wb)
          ⟨hs.Alin, hs.Blin, fun _ => rfl, hadd _ _ _ hs.As (hH k),
            P_foldl hadd
              (fun i => mulE (mulE (mulE (OnBytes.Model.eqLowAt rs wb lam (off / 2 ^ wb))
                ((OnBytes.Model.eqLow rs wy wb).getD i zeroE)) ec) (wt.getD i zeroE))
              (fun i x => (V x).getD (v0' + i) zeroE) (fun i => hV (v0' + i)) (List.range ni)
              (fun x => (s x).Bs) hs.Bs⟩))
    | none =>
      cases v0 with
      | some v0' =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine famOK_ite famOK_none (famOK_bind _ fun _ => famOK_bind _ fun f => ?_)
        refine famOK_foldlM (fun i s A B w hs => famOK_then ?_ fun s A B w hs => ?_) _ s A B w hs
        · refine famOK_foldlM (fun yv s A B w hs => ?_) _ s A B w hs
          simp only [hs.Alin]
          exact famOK_bind _ fun a => famOK_pure (B := B) (w := w)
            ⟨fun _ => rfl, hs.Blin, hs.wD, hs.As, hs.Bs⟩
        · have hB := hadd (fun x => (s x).Bs) (fun x => (V x).getD (v0' + i) zeroE)
            (mulE (OnBytes.Model.eqLowAt rs wb lam (off / 2 ^ wb))
              ((OnBytes.Model.eqLow rs wy wb).getD i zeroE)) hs.Bs (hV (v0' + i))
          exact famOK_pure
            (s := fun x => { s x with
              Bs := addE (s x).Bs (mulE (mulE (OnBytes.Model.eqLowAt rs wb lam (off / 2 ^ wb))
                ((OnBytes.Model.eqLow rs wy wb).getD i zeroE)) ((V x).getD (v0' + i) zeroE)) })
            (A := A) (B := B) (w := w) ⟨hs.Alin, hs.Blin, hs.wD, hs.As, hB⟩
      | none =>
        cases sB with
        | none =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine famOK_ite famOK_none (famOK_bind _ fun _ => famOK_bind _ fun f => ?_)
          refine famOK_foldlM (fun i s A B w hs => famOK_then ?_ fun s A B w hs =>
            famOK_pure hs) _ s A B w hs
          refine famOK_foldlM (fun yv s A B w hs => ?_) _ s A B w hs
          exact famOK_bind _ fun a => famOK_none
        | some g =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine famOK_ite famOK_none (famOK_bind _ fun _ => famOK_bind _ fun f => ?_)
          refine famOK_foldlM (fun i s A B w hs => famOK_then ?_ fun s A B w hs =>
            famOK_pure hs) _ s A B w hs
          refine famOK_foldlM (fun yv s A B w hs => ?_) _ s A B w hs
          simp only [hs.Alin, hs.Blin]
          exact famOK_bind _ fun a => famOK_bind _ fun c => famOK_pure (w := w)
            ⟨fun _ => rfl, fun _ => rfl, hs.wD, hs.As, hs.Bs⟩

/-- **The end over all panels.** a0, b0: the families of the two shown values from which the two
numbers start. -/
theorem stackEnd_fam
    (hadd : ∀ (f g : ι → E) (c : E), P f → P g → P fun x => addE (f x) (mulE c (g x)))
    (y : Lay) (bl : Array SBlk) (rs : Array E) (lam : ℕ) (om : Array E) (H1 V : ι → Array E)
    (a0 b0 : ι → E) (hH : ∀ k, P fun x => (H1 x).getD k zeroE)
    (hV : ∀ k, P fun x => (V x).getD k zeroE) (ha : P a0) (hb : P b0) :
    FamOK P fun x => stackEnd y bl rs lam om (H1 x) (V x) (a0 x) (b0 x) := by
  unfold stackEnd
  simp only [← Array.foldlM_toList]
  refine famOK_then (famOK_foldlM (fun b s A B w hs =>
    stackEndOf_fam hadd y rs lam om H1 V hH hV b s A B w hs) bl.toList
      (fun x => { As := a0 x, Bs := b0 x }) {} {} 0
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ha, hb⟩) fun s A B w hs => ?_
  simp only [hs.wD]
  exact famOK_ite famOK_none (famOK_pure hs)

/-! ## 2 The two premises -/

/-- An entry of a stretch of an array. -/
theorem extract_getD (e : Array E) (a b k : ℕ) :
    (e.extract a b).getD k zeroE =
      if a + k < min b e.size then e.getD (a + k) zeroE else zeroE := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  by_cases h : k < min b e.size - a
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
    rfl

/-- **The two numbers that the honest side's call makes of a family of lists of end values.** n: the
lists' one length. -/
theorem sidesOn_fam
    (hadd : ∀ (f g : ι → E) (c : E), P f → P g → P fun x => addE (f x) (mulE c (g x)))
    (hzero : P fun _ => zeroE) (D : StackData) (rs : Array E) (e : ι → Array E) (n : ℕ)
    (hn : ∀ x, (e x).size = n) (hent : ∀ k, P fun x => (e x).getD k zeroE) :
    (∀ x, D.sidesOn rs (e x) = none) ∨
      ∃ a b : ι → E, (∀ x, D.sidesOn rs (e x) = some (a x, b x)) ∧ P a ∧ P b := by
  have hex : ∀ u v k, P fun x => ((e x).extract u v).getD k zeroE := by
    intro u v k
    simp only [extract_getD, hn]
    by_cases h : u + k < min v n
    · simpa only [if_pos h] using hent (u + k)
    · simpa only [if_neg h] using hzero
  have key := stackEnd_fam hadd D.S.v.y D.bl rs D.S.Q.hp.lamS D.om
    (fun x => (e x).extract 1 (1 + D.nVirt)) (fun x => (e x).extract (2 + D.nVirt) n)
    (fun x => (e x).getD 0 zeroE) (fun x => (e x).getD (1 + D.nVirt) zeroE)
    (hex 1 (1 + D.nVirt)) (hex (2 + D.nVirt) n) (hent 0) (hent (1 + D.nVirt))
  have hs : ∀ x, D.sidesOn rs (e x) =
      (stackEnd D.S.v.y D.bl rs D.S.Q.hp.lamS D.om ((e x).extract 1 (1 + D.nVirt))
        ((e x).extract (2 + D.nVirt) n) ((e x).getD 0 zeroE)
        ((e x).getD (1 + D.nVirt) zeroE)).bind fun fin => some (fin.As, fin.Bs) := by
    intro x
    unfold StackData.sidesOn
    rw [hn x]
    rfl
  rcases key with h | ⟨s, A, B, w, h, g⟩
  · exact Or.inl fun x => by
      have h1 := h x
      dsimp only at h1
      rw [hs x, h1]
      rfl
  · exact Or.inr ⟨fun x => (s x).As, fun x => (s x).Bs, fun x => by
      have h1 := h x
      dsimp only at h1
      rw [hs x, h1]
      rfl, g.As, g.Bs⟩

/-- **On two lists that read alike the summand's values read alike.** -/
theorem summandOn_alike (D : StackData) (rs : Array E) :
    ReadsAlike fun e => (D.summandOn rs e.toArray).getD zeroE := by
  intro a b hab
  have hlen : a.length = b.length := by
    have := congrArg List.length hab
    simpa using this
  have e1 : ∀ (l : List E) k, Reading.gl.val (l.toArray.getD k zeroE) =
      (l.map Reading.gl.val).getD k 0 := by
    intro l k
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases l[k]? with
    | none => exact Reading.gl.zero
    | some x => rfl
  have key := sidesOn_fam (ι := Bool)
    (P := fun f => Reading.gl.val (f true) = Reading.gl.val (f false))
    (fun f g c hf hg => by
      show Reading.gl.val (addE (f true) (mulE c (g true))) =
        Reading.gl.val (addE (f false) (mulE c (g false)))
      rw [Reading.gl.add, Reading.gl.add, Reading.gl.mul, Reading.gl.mul, hf, hg])
    rfl D rs (fun x => if x then a.toArray else b.toArray) a.length
    (fun x => by cases x <;> simp [hlen])
    (fun k => by
      show Reading.gl.val (a.toArray.getD k zeroE) = Reading.gl.val (b.toArray.getD k zeroE)
      rw [e1, e1, hab])
  show Reading.gl.val ((D.summandOn rs a.toArray).getD zeroE) =
    Reading.gl.val ((D.summandOn rs b.toArray).getD zeroE)
  unfold StackData.summandOn
  rcases key with h | ⟨u, v, h, hu, hv⟩
  · have h1 : D.sidesOn rs a.toArray = none := h true
    have h2 : D.sidesOn rs b.toArray = none := h false
    rw [h1, h2]
  · have h1 : D.sidesOn rs a.toArray = some (u true, v true) := h true
    have h2 : D.sidesOn rs b.toArray = some (u false, v false) := h false
    rw [h1, h2]
    show Reading.gl.val (mulE (u true) (v true)) = Reading.gl.val (mulE (u false) (v false))
    rw [Reading.gl.mul, Reading.gl.mul, hu, hv]

/-- **Along a line in the end values the summand is a polynomial of degree at most 2.** -/
theorem summandOn_poly (D : StackData) (rs : Array E) (ends m : List E) :
    PolyOn 2 fun y => (D.summandOn rs (maskedEnds ends m y).toArray).getD zeroE := by
  have key := sidesOn_fam (ι := E) (P := PolyOn 1)
    (fun f g c hf hg => hf.add (((PolyOn.const c).mul hg).mono (by omega)))
    ((PolyOn.const zeroE).mono (by omega)) D rs (fun y => (maskedEnds ends m y).toArray)
    (min ends.length m.length) (fun y => by simp [maskedEnds])
    (fun k => PolyOn.entryA ends m k)
  unfold StackData.summandOn
  rcases key with h | ⟨u, v, h, hu, hv⟩
  · simp only [h]
    exact (PolyOn.const zeroE).mono (by omega)
  · simp only [h]
    exact hu.mul hv

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.famOK_none
#print axioms ProofFile.Honest.K4.famOK_pure
#print axioms ProofFile.Honest.K4.famOK_ite
#print axioms ProofFile.Honest.K4.famOK_bind
#print axioms ProofFile.Honest.K4.famOK_then
#print axioms ProofFile.Honest.K4.famOK_foldlM
#print axioms ProofFile.Honest.K4.P_foldl
#print axioms ProofFile.Honest.K4.stackEndOf_fam
#print axioms ProofFile.Honest.K4.stackEnd_fam
#print axioms ProofFile.Honest.K4.extract_getD
#print axioms ProofFile.Honest.K4.sidesOn_fam
#print axioms ProofFile.Honest.K4.summandOn_alike
#print axioms ProofFile.Honest.K4.summandOn_poly
