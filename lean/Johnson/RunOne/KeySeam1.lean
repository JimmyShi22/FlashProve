-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeam1.lean: THE SEAM BETWEEN THE KEY FILE's FIRST AND SHARED CHAIN. Premises on public values: the shared chain's codes are the one-time plan's (hcodes); its shape is the plan's (hlin).
At the shared chain's own three messages ArrOk (harr) and ReadsPinned (hreads) are premises on the letters; Free₂.reads at messages 0 and 2 comes from the first chain's last promise.
  Agree₁          the two readings are one reading, seen from the two records on the two sides of the seam: AT THE SHARED CHAIN's FIRST RECORD, AND AT THE MESSAGES WHOSE PIN IS OPEN THERE, ALONE · agree₁_of_base: a member (KeyOneReading.lean's one base)
  seam₁L          PROVED: the claims' half: L₂ 0 at ((x, s₁), start x) ⇒ L₁ 19 at (x, s₁): item by item the same sentence on the same witness
  shape₂_first    PROVED: the shared chain's first record meets the book-keeping Bool of boundary 0
  seam₁On         PROVED: the promises' half: on₁ 19 at (x, s₁) ⇒ on₂ 0 at ((x, s₁), K14.first codes x.key): the record, «no collision», the open pins' samples pass by Agree₁; «handed» by shape₁_handed (Johnson/Desc/Key/KeyShape.lean)
  seam₁_rows      PROVED: both, in the letters of the top's RowsOwed.seam₁
At a key file with two lookups (both stored sizes) · K₁ := the first chain's own plan₁ one · a := the one-time plan's samples · idx := [0].
Limits. Whether on₁ 19 is ever met is not shown here. Nothing on soundness.

-/
import Johnson.RunOne.KeyRows1At
import Johnson.RunOne.KeyOneReading

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ n₁ slots₁ meaning₁At open₁ on₁ L₁ R₁ ties₁ tiesA sizesB moreB counts₁ on₁_two)

/-- **The first chain's last book-keeping**, as the letter last₁ of the shared chain's promise. -/
def last₁At (one : OneTime) (s : FirstState) : Bool := shape₁ (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) (2 + 6 * n₁ one + 5) s

theorem open₁_last : open₁ 2 19 = end₁ := by decide
theorem end₁_seam : end₁ = seam := by decide

section
variable {XI Cells M Smp Rec : Type} {F : FileDescription XI} {Fr₁ Fr₂ : Frame}
  {G₁ : Reading (Xi × FirstState) Cells M Smp Rec} {G₂ : Reading (P₂ × St₂) Cells M Smp Rec} {at_ : Where}
  {S : LinShape} {one : OneTime} {R : KRead Cells M} {enc : (Nat → OnBytes.E) → Nat → OnBytes.E} {rad : Nat}
  {coll : Strs → Rec → Prop} {off₂ : Nat → Nat}

/-- The two readings are one, at the records on the two sides of the seam. start: the description's start₂. -/
structure Agree₁ (G₁ : Reading (Xi × FirstState) Cells M Smp Rec) (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where) (start : Xi → St₂) : Prop where
  arr : G₂.arr = G₁.arr
  lay : G₂.lay = G₁.lay
  enc : G₂.enc = G₁.enc
  rad : G₂.rad = G₁.rad
  meets : G₂.meets = G₁.meets
  decT : G₂.decT = G₁.decT
  /-- at the messages whose pin is open at the seam alone -/
  smp : ∀ (x : Xi) (s₁ : FirstState), ∀ k ∈ pinned seam, G₂.smp ((x, s₁), start x) (at_ k).1 (at_ k).2 = G₁.smp (x, s₁) (at_ k).1 (at_ k).2
  recOf : ∀ (x : Xi) (s₁ : FirstState), G₂.recOf ((x, s₁), start x) = G₁.recOf (x, s₁)

theorem agree₁_of_base (B : Base Cells M Smp Rec) (at_ : Where) (start : Xi → St₂) (h : ∀ k ∈ pinned seam, (at_ k).1 < B.t₁) : Agree₁ B.g₁ B.g₂ at_ start :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun x s₁ k hk => by simp only [Base.g₁, Base.g₂, if_pos (h k hk)], fun _ _ => rfl⟩

theorem agree₁_of_baseSt (T : BaseSt Cells M Smp Rec) (at_ : Where) (start : Xi → St₂) (h : ∀ k ∈ pinned seam, T.arr (at_ k).1 (at_ k).2 < 3) : Agree₁ T.h₁ T.h₂ at_ start :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun x s₁ k hk => by simp only [BaseSt.h₁, BaseSt.h₂, if_pos (h k hk)], fun _ _ => rfl⟩

theorem pin_agree₁ {start : Xi → St₂} (A : Agree₁ G₁ G₂ at_ start) (k : Nat) (hk : k ∈ pinned seam) (x : Xi) (s₁ : FirstState) (y : Strs) (w : Wit Cells Unit M)
    (h : PIN F G₂ (at_ k).1 (at_ k).2 ((x, s₁), start x) y w) : PIN F G₁ (at_ k).1 (at_ k).2 (x, s₁) y w := by
  obtain ⟨o, z, ho, hz, hm⟩ := h
  refine ⟨o, z, ho, (A.smp x s₁ k hk) ▸ hz, ?_⟩
  unfold Member msgOf at hm ⊢
  rw [A.arr, A.lay, A.enc, A.rad, A.meets] at hm
  exact hm

/-- **The claims' half.** -/
theorem seam₁L (start : Xi → St₂) (A : Agree₁ G₁ G₂ at_ start) (hn : n₁ one = 2) (x : Xi) (s₁ : FirstState) (y₁ : Fr₁.E.Str) (y₂ : Fr₂.E.Str) (hy : strsOf Fr₂ y₂ = strsOf Fr₁ y₁)
    (h : L₂ F Fr₂ G₂ at_ S (plan₁ one) R enc rad 0 (((x, s₁), start x), y₂)) : L₁ F Fr₁ G₁ at_ one R 19 ((x, s₁), y₁) := by
  obtain ⟨w, hw⟩ := h
  have hw0 : relAt F G₂ at_ (meaning₂ S (plan₁ one) R enc rad) (open₂ 0) ((x, s₁), start x) (strsOf Fr₂ y₂) w := hw
  rw [hy] at hw0
  refine ⟨w, fun i hi => ?_⟩
  rw [hn, open₁_last, end₁_seam] at hi
  have H := hw0 i (by rw [open₂_first]; exact hi)
  simp only [seam, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · obtain ⟨r, hr, hd⟩ : PINW G₂ ((x, s₁), start x) (strsOf Fr₁ y₁) w := H
    exact ⟨r, (A.recOf x s₁) ▸ hr, A.decT ▸ hd⟩
  · exact pin_agree₁ A _ (by decide) x s₁ _ w H
  · have H' : srowAt R (plan₁ one) s₁.d.st 0 w := by simpa [KItem.holds, meaning₂, readers₂, firstOf] using H
    exact H'
  · exact H
  · exact pin_agree₁ A _ (by decide) x s₁ _ w H
  · have H' : srowAt R (plan₁ one) s₁.d.st 2 w := by simpa [KItem.holds, meaning₂, readers₂, firstOf] using H
    exact H'

theorem shape₂_first (S : LinShape) (a : Nat) (codes : Codes) (key : TableKey) (hf : LKFU.Shape23.formOk S = true) :
    LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 0 (_root_.Desc.K14.first codes key)) = true := by
  simp [LKFU.Shape23.ok, LKFU.Shape23.shape₂, _root_.Desc.K14.first, hf]
  rfl

theorem member_agree₁ {start : Xi → St₂} (A : Agree₁ G₁ G₂ at_ start) (o : VerifiableInference.Desc.Oracle) (j t : Nat) (y : Strs) (z : Smp) (m : M)
    (h : Member F G₂ o j t y z m) : Member F G₁ o j t y z m := by
  unfold Member at h ⊢
  rw [A.enc, A.rad, A.meets] at h
  exact h

/-- The first chain's ties hold the codes. -/
theorem codes_of_last (one : OneTime) (b : Nat) (s : FirstState) (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) b s = true) : s.d.st.codes = one.codes := by
  have ht : ties₁ one b s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ tiesA at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ht.1.1.1.1.2

/-- **The promises' half.** hcodes | hlin: facts on public values: the shared chain starts at the one-time plan's codes; the shape is the plan's. harr: what PIN pins at the shared chain's own messages (a condition on the letters G₂ and at_). -/
theorem seam₁On (codes : Codes) (A : Agree₁ G₁ G₂ at_ fun x => _root_.Desc.K14.first codes x.key) (hf : LKFU.Shape23.formOk S = true)
    (hcodes : one.codes = codes) (hlin : one.lin = S) (harr : ArrOk G₂ at_ [3, 4, 5]) (hreads : ReadsPinned G₂ at_ R [3, 4, 5])
    (x : Xi) (s₁ : FirstState) (y₁ : Fr₁.E.Str) (y₂ : Fr₂.E.Str) (hy : strsOf Fr₂ y₂ = strsOf Fr₁ y₁) (h : on₁ F Fr₁ G₁ at_ one R coll 19 ((x, s₁), y₁)) :
    on₂ F Fr₂ G₂ at_ S (plan₁ one) R enc rad one.given.plan.samples coll (last₁At one) off₂ 0 (((x, s₁), _root_.Desc.K14.first codes x.key), y₂) := by
  have hn : n₁ one = 2 := on₁_two F Fr₁ G₁ at_ one R coll 19 _ h
  show onAt F G₂ at_ (meaning₂ S (plan₁ one) R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S one.given.plan.samples 0 d))
    (Free₂ F G₂ at_ S (plan₁ one) R coll (last₁At one) off₂ 0) (open₂ 0) ((x, s₁), _root_.Desc.K14.first codes x.key) (strsOf Fr₂ y₂)
  rw [hy]
  cases h with
  | inl hm => exact absurd rfl hm
  | inr hr =>
    obtain ⟨hsh, hsm, ⟨⟨r, hr', hc⟩, ⟨ha, hrd⟩, hp, hev, hsi, hoi, hO, hshn, hfit, -, hmv⟩, hnc⟩ := hr
    have hh : last₁At one s₁ = true := by
      unfold last₁At
      rw [hn]; rw [hn] at hsh; exact hsh
    rw [hn, open₁_last, end₁_seam] at hsm hnc
    have hF : Free₂ F G₂ at_ S (plan₁ one) R coll (last₁At one) off₂ 0 ((x, s₁), _root_.Desc.K14.first codes x.key) (strsOf Fr₁ y₁) :=
      { record := ⟨r, (A.recOf x s₁).trans hr', hc⟩
        last := hh
        eval := hlin ▸ hev (by decide)
        placed₁ := fun k hk => hp k (by rw [open₁_last, end₁_seam]; revert k; decide)
        in₁ := ⟨fun k hk => hsi k (by rw [open₁_last, end₁_seam]; revert k; decide), hoi (by decide)⟩
        key := rfl
        codes := by
          show codes = s₁.d.st.codes
          rw [codes_of_last one _ s₁ hsh, hcodes]
        lay := fun h3 => absurd h3 (by decide)
        arr := fun k hk => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl
          · rw [A.arr]; exact ha 0 (by decide)
          · rw [A.arr]; exact ha 2 (by decide)
          · exact harr 3 (by decide)
          · exact harr 4 (by decide)
          · exact harr 5 (by decide)
        reads := fun w k hk => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl
          · unfold msgOf; rw [A.arr, A.lay]; exact hrd w 0 (by decide)
          · unfold msgOf; rw [A.arr, A.lay]; exact hrd w 2 (by decide)
          · exact hreads w 3 (by decide)
          · exact hreads w 4 (by decide)
          · exact hreads w 5 (by decide)
        placed := fun k hk => absurd hk (by rw [open₂_first]; revert k; decide)
        samples := fun k hk => absurd hk (by rw [open₂_first]; revert k; decide)
        rowsIn := fun h2 => absurd h2 (by decide)
        order₁ := hO
        order := Means.InOrder.start codes
        linOk := fun h2 => absurd h2 (by decide)
        seatU := fun h2 => absurd h2 (by decide)
        seatOmega := fun h2 => absurd h2 (by decide)
        shown := fun j hj => hshn j (by rw [open₁_last, end₁_seam]; rw [open₂_first] at hj; exact hj)
        fits := hlin ▸ hfit
        mask₁ := hmv (by decide)
        maskU := fun h2 => absurd h2 (by decide) }
    refine Or.inr ⟨shape₂_first S _ codes x.key hf, ?_, hF, ?_⟩
    · rw [open₂_first]
      refine List.all_eq_true.2 fun k hk => ?_
      have := List.all_eq_true.1 hsm k hk
      unfold hasSmp at this ⊢
      rw [A.smp x s₁ k hk]
      exact this
    · rw [open₂_first]
      intro k hk o z ho hz m m' hm hm'
      exact hnc k hk o z ho ((A.smp x s₁ k hk) ▸ hz) m m' (member_agree₁ A o _ _ _ z m hm) (member_agree₁ A o _ _ _ z m' hm')

/-- **Both halves, in the form that the top asks** (RowsOwed.seam₁; there the boundary's number is written 0 + 1 + the later blocks' number: 19 at nineteen blocks). -/
theorem seam₁_rows (codes : Codes) (A : Agree₁ G₁ G₂ at_ fun x => _root_.Desc.K14.first codes x.key) (hf : LKFU.Shape23.formOk S = true)
    (hcodes : one.codes = codes) (hlin : one.lin = S) (harr : ArrOk G₂ at_ [3, 4, 5]) (hreads : ReadsPinned G₂ at_ R [3, 4, 5])
    (x : Xi) (s₁ : FirstState) (y₁ : Fr₁.E.Str) (y₂ : Fr₂.E.Str) (hy : strsOf Fr₂ y₂ = strsOf Fr₁ y₁) (h : on₁ F Fr₁ G₁ at_ one R coll 19 ((x, s₁), y₁)) :
    on₂ F Fr₂ G₂ at_ S (plan₁ one) R enc rad one.given.plan.samples coll (last₁At one) off₂ 0 (((x, s₁), _root_.Desc.K14.first codes x.key), y₂) ∧
      (L₂ F Fr₂ G₂ at_ S (plan₁ one) R enc rad 0 (((x, s₁), _root_.Desc.K14.first codes x.key), y₂) → L₁ F Fr₁ G₁ at_ one R 19 ((x, s₁), y₁)) :=
  ⟨seam₁On codes A hf hcodes hlin harr hreads x s₁ y₁ y₂ hy h, seam₁L _ A (on₁_two F Fr₁ G₁ at_ one R coll 19 _ h) x s₁ y₁ y₂ hy⟩

end

/-- Behind V's sending the first chain's book-keeping's yes gives ownB (KeyShape.lean). -/
theorem core₁_own {σ : Type} (K : KPlan) (X : KReaders σ) (B : KBook σ) (n : Nat) (slots : Nat → Nat) (c : Nat) (s : σ) (hc : 4 ≤ c)
    (h : core₁ K X B n slots (2 + 6 * n + c) s = true) : ownB K X B s = true := by
  have hb0 : (2 + 6 * n + c == 0) = false := by simp <;> omega
  have hb1 : (2 + 6 * n + c == 1) = false := by simp <;> omega
  have hlt : ¬ (2 + 6 * n + c < 2 + 6 * n) := by omega
  have e : 2 + 6 * n + c - (2 + 6 * n) = c := by omega
  have hc0 : (c == 0) = false := by simp <;> omega
  have hc1 : (c == 1) = false := by simp <;> omega
  have hc2 : (c == 2) = false := by simp <;> omega
  have hc3 : (c == 3) = false := by simp <;> omega
  simp only [core₁, hb0, hb1, hlt, e, hc0, hc1, hc2, hc3, Bool.false_eq_true, if_false, ↓reduceIte, Bool.and_eq_true] at h
  exact h.2.1.2

/-- **And: the number under which the first chain's last state holds V is the plan's.** -/
theorem last₁_w (one : OneTime) (s : FirstState) (h : last₁At one s = true) : s.lin.map (·.w) = (plan₁ one).orc 2 := by
  unfold last₁At at h
  have ht : ties₁ one (2 + 6 * n₁ one + 5) s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ tiesA sizesB at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  have hn : n₁ one = 2 := ht.1.1.1.1.1.1
  have h7 := ht.2.1.2
  rw [hn] at h7
  simpa using h7

/-- **What the seam to the last chain spends of the first chain's last book-keeping**: «handed»; V's number in the plan counts the statement's messages; the book's trees are the plan's number. -/
theorem last₁_gives (one : OneTime) (s : FirstState) (h : last₁At one s = true) :
    handedB one.given.plan.samples [0] s = true ∧ (plan₁ one).orc 2 = some ((firstOf s).1.oracles.size - 2) ∧
      (firstOf s).2.1.trees.size = one.ranges.stages.length + 2 ∧ (∀ r, (firstOf s).2.2.2 = [r] → r.g.all (·.ok) = true) ∧ LinTie s := by
  have hw₁ := last₁_w one s h
  unfold last₁At at h
  have ht : ties₁ one (2 + 6 * n₁ one + 5) s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  have ht' := ht
  unfold ties₁ tiesA sizesB at ht'
  simp only [Bool.and_eq_true, beq_iff_eq] at ht'
  have hn : n₁ one = 2 := ht'.1.1.1.1.1.1
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, h8⟩ := ht'.2
  rw [hn] at h3 h8
  have hT : s.d.book.trees.size = one.ranges.stages.length + 2 := h3
  have hG : ∀ r, (firstOf s).2.2.2 = [r] → r.g.all (·.ok) = true := by
    intro r hr
    have h8' : (s.lin.map fun L => L.claim.g.all (·.ok)) = some true := by simpa using h8
    cases hL : s.lin with
    | none => rw [hL] at h8'; cases h8'
    | some L =>
      rw [hL] at h8'
      have e : (firstOf s).2.2.2 = [rowOfLinClaim L.claim] := by
        unfold firstOf
        rw [hL]
      rw [e] at hr
      have er : r = rowOfLinClaim L.claim := (List.cons.inj hr).1.symm
      rw [er]
      exact Option.some.inj h8'
  have hM : s.lin.any (fun l => l.own != noId && l.w != noId && l.mask == some (l.w + 1)) = true := by
    have hm := ht
    unfold ties₁ moreB at hm
    simp only [Bool.and_eq_true] at hm
    have h4 := hm.1.2.1.1.2
    rw [hn] at h4
    simpa using h4
  have ho := core₁_own (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) 5 s (by decide) ((shape₁_iff (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) _ s).1 h).2
  unfold ownB at ho
  split at ho
  · rename_i i v g e0 e2 e3
    simp only [Bool.and_eq_true, beq_iff_eq] at ho
    have hs : (firstOf s).1.oracles.size = v + 2 := ho.1.1.1
    have hg : g + 1 = (firstOf s).1.groups.size := ho.1.2
    refine ⟨shape₁_handed (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) 5 s (by decide) h, by rw [e2, hs]; rfl, hT, hG, ?_⟩
    cases hL : s.lin with
    | none => rw [hL] at hM; cases hM
    | some l =>
      rw [hL] at hM hw₁
      have e3' : (s.lin.map (·.own)) = some g := e3
      rw [hL] at e3'
      have ew : l.w = v := Option.some.inj (hw₁.trans e2)
      have eo : l.own = g := Option.some.inj e3'
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hM
      exact ⟨l, hL, by rw [ew]; exact hs.symm, by rw [eo]; exact hg, hM.2⟩
  · cases ho

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.last₁_w
#print axioms Johnson.RunOne.KeyRows23.last₁_gives
#print axioms Johnson.RunOne.KeyRows23.agree₁_of_base
#print axioms Johnson.RunOne.KeyRows23.agree₁_of_baseSt
#print axioms Johnson.RunOne.KeyRows23.seam₁L
#print axioms Johnson.RunOne.KeyRows23.seam₁On
#print axioms Johnson.RunOne.KeyRows23.seam₁_rows
