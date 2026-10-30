-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyFirst.lean: THE KEY FILE's FIRST BOUNDARY's TWO FACTS (RowsOwed.firstOn | firstClaim, Johnson/Top/Fire/Code/KeyOfRows.lean), AT THE TABLE's OWN on₁ 0 | L₁ 0 (Johnson/RunOne/KeyRows1At.lean): EACH PROVED FROM NAMED FACTS ON
THE LETTERS (AT THE STATE FirstState OF THE KEY FILE's DESCRIPTION), in plain types: RecT: the frame's records · Y: the stored table's strings · inst: records ↦ instances · s₀: the first chain's first state · str: the strings as the rule's oracles at the first boundary.
  open₁_zero          what is open at the first boundary is the goal: unmarked · pinT · inRange l for every lookup l
  FirstLetters        THE FACTS: start: the book-keeping's Bool at border 0 says yes at the first state · recAt: THE RECORD's READER GIVES THE RECORD AT ITS OWN KEY (so it is a PARTIAL INVERSE of records ↦ keys there: this is where «one to one» is spent) · coll: the table's
                      «collision» at the reading is the frame's · dec: what the reading's decoder gives is what the frame's gives, read as cells · held: THE BRIDGE: cells whose keys lie in all lookups' ranges are a message that holds an index
  firstOn_of          **PROVED**: no collision at the record's seed ⟹ on₁ 0 at the record's first statement. (RowsOwed hands it okStart and «D = none» besides: not needed.)
  firstClaim_of       **PROVED**: L₁ 0 there ⟹ the frame's decoder's answer, bound to «held», is some. With «no collision» that is D y rec ≠ none (Hiop/RecConf.lean:143-146).
WHO OWES THE FIVE: start: by unfolding the first state (a run has shown it at both sizes) · recAt: whoever fills Reading.recOf, with keyOf_injective (OnBytes/Slice/KeyOfRecInj.lean) · coll | dec: whoever fills the reading (the notions of Johnson/Desc/Sound/MsgSig.lean, called) · held: other files, by report
(KeyAny.keyTA_inT; ConfOf.lean:88's held), PLUS the step from this table's InRange (machine words under «same»; covered places) to PartsIn's conjuncts.
(Where this and lean/THEOREM.md differ, the page holds.)
Nothing on soundness.
-/
import Johnson.RunOne.KeyRows1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)

/-- What is open at the first boundary is the goal. -/
theorem open₁_zero (n : Nat) : open₁ n 0 = start₁ n := rfl

theorem pinT_open_zero (n : Nat) : KItem.pinT ∈ open₁ n 0 := by
  rw [open₁_zero]; simp [start₁]

theorem inRange_open_zero (n l : Nat) (h : l < n) : KItem.inRange l ∈ open₁ n 0 := by
  rw [open₁_zero]; simp [start₁, h]

theorem pinned_zero (n : Nat) : pinned (open₁ n 0) = [] := by
  rw [open₁_zero]; simp [start₁, pinned, List.filterMap_append, List.filterMap_map]

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)
  {RecT Y U I : Type} (inst : RecT → Xi) (s₀ : Xi → FirstState) (str : Y → Fr.E.Str) (ρ : RecT → Rec)
  (collT : Y → RecT → Prop) (dcdT : Y → RecT → Option U) (heldT : U → Option I) (cellsOf : U → Cells)

/-- **The facts on the letters.** -/
structure FirstLetters : Prop where
  start : ∀ x, shape₁ (plan₁ one) (readers₁ one) (book₁ one) (n₁ one) (slots₁ one) 0 (s₀ x) = true
  recAt : ∀ r, G.recOf (inst r, s₀ (inst r)) = some (ρ r)
  arr : ArrOk G at_ [0, 1, 2]
  reads : ReadsPinned G at_ R [0, 1, 2]
  order : ∀ x, Means.InOrder (s₀ x).d.st
  fits : ∀ r, (inst r).key.fits one.lin.fold.index = true
  coll : ∀ r y, coll (strsOf Fr (str y)) (ρ r) → collT y r
  dec : ∀ r y c, G.decT (strsOf Fr (str y)).cell (ρ r) = some c → ∃ u, dcdT y r = some u ∧ cellsOf u = c
  held : ∀ r y u, dcdT y r = some u → (∀ l, l < n₁ one → ∃ L, (plan₁ one).lookups[l]? = some L ∧ InRange R.same (plan₁ one).m L (matAt (plan₁ one).lin (R.tab (cellsOf u)))) → (heldT u).isSome

variable {F Fr G at_ one R coll inst s₀ str ρ collT dcdT heldT cellsOf}

/-- **firstOn.** -/
theorem firstOn_of (H : FirstLetters Fr G at_ one R coll inst s₀ str ρ collT dcdT heldT cellsOf) (r : RecT) (y : Y) (hc : ¬ collT y r) :
    on₁ F Fr G at_ one R coll 0 ((inst r, s₀ (inst r)), str y) := by
  refine Or.inr ⟨H.start _, ?_, ⟨⟨ρ r, H.recAt r, fun h => hc (H.coll r y h)⟩, ⟨H.arr, H.reads⟩, fun k hk => absurd hk (by rw [pinned_zero]; exact List.not_mem_nil), fun h18 => absurd h18 (by decide),
    fun k hk => absurd hk (by rw [pinned_zero]; exact List.not_mem_nil), fun h18 => absurd h18 (by decide), H.order _, fun k hk => absurd hk (by rw [pinned_zero]; exact List.not_mem_nil), H.fits r, fun h => absurd h.1 (by decide), fun h18 => absurd h18 (by decide)⟩, ?_⟩
  · rw [pinned_zero]; rfl
  · intro k hk; rw [pinned_zero] at hk; cases hk

/-- **firstClaim.** -/
theorem firstClaim_of (H : FirstLetters Fr G at_ one R coll inst s₀ str ρ collT dcdT heldT cellsOf) (r : RecT) (y : Y)
    (hL : L₁ F Fr G at_ one R 0 ((inst r, s₀ (inst r)), str y)) : ((dcdT y r).bind heldT).isSome := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨r', hr', hd⟩ : PINW G (inst r, s₀ (inst r)) (strsOf Fr (str y)) w := hw .pinT (pinT_open_zero _)
  have e : r' = ρ r := Option.some.inj (hr'.symm.trans (H.recAt r))
  subst e
  obtain ⟨u, hu, hcells⟩ := H.dec r y _ hd
  have hh : (heldT u).isSome := H.held r y u hu fun l hl => by
    have := hw (.inRange l) (inRange_open_zero _ l hl)
    rw [hcells]
    exact this
  rw [hu]
  exact hh

end

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.firstOn_of
#print axioms Johnson.RunOne.KeyRows1.firstClaim_of
