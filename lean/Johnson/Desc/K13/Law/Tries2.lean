-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Tries2.lean: tries of the form of the law of Johnson/Desc/K13/Law/Agree.lean,
and the joint of the two places. Statements with their proofs.
Main names:
  `not_sound2_yes`, `not_sound2_yes_gl`: the text that always answers, with a row that is true of
    everything, does not meet `SoundAt2`.
  `sound2_no`: the text that always refuses meets it (`batt_answers`,
    Johnson/Desc/K13/Law/Silly.lean, rules it out).
  `FreeMaskAt`, `not_freeMask`, `not_freeMask_gl`: with the matrix fixed and the ledger's mask
    entries free behind the draws, the batching's bound is false: so the second half of `AgreeAt`
    cannot be dropped.
  `atM3_at_joint`: the law of the batching's joined block at the very reader of the law behind W's
    commitment: a matrix, with ALL mask entries off one world's words.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/Free.lean names.

What is not claimed. `not_freeMask` is at one column variable and a pile of one row. That a decoder
of the release's codes is `Local`. `Declared` is a test on a plan's written rounds: an evaluation at
two stored sets' public files, a small and a full-size one, said yes, and five controls said no;
no theorem says it of a plan. `Local` asks only that the decoder reads the stored table and the
earlier trees: every such function meets it. A decoder that reads the oracles alone singles out one
member of a list whatever the samples in the record say: so the laws at such a decoder are idle for
the witness that the samples pin. The form to carry on is that of Johnson/Desc/K13/Law/PinA.lean. At
the piece the block that says yes to all is tried in Johnson/Desc/K13/Law/Tries3.lean
[not in this library], without a round.

-/
import Johnson.Desc.K13.Law.Good2
import Johnson.Desc.K13.Law.Free
import Johnson.Desc.K13.Law.AtM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Cb Iop Prob
open OnBytes.Maker (RDT)
open OnBytes.Means (Words)
open Johnson.L5.Layers (rd sRounds)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) (σ : K → E)
  (hσ : ∀ a, ρ.val (σ a) = a)

include hσ in
/-- The text that always answers with a row that is true of everything does not meet the form. -/
theorem not_sound2_yes (nR k : ℕ) (h3 : 2 < Fintype.card K) (d : St) (Ex : ExtSpec) (y : Ex.Str) :
    ¬ SoundAt2 ρ nR k sillyYes := by
  intro h
  have hD := h Unit (fun _ => (⟨fun _ _ => 0, fun _ => 0⟩ : Wit K nR k)) (fun _ => True) 0
    (fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩) none 1 [⟨[], [], [], oneE⟩] d Ex y
    (fun r hr t ht => by rw [List.mem_singleton.1 hr] at ht; cases ht)
  refine not_doomed _ _ _ (below_eps ρ nR k _ Ex h3 (by simp; omega)) (fun τ hbad => ?_) hD
  obtain ⟨m0, c, m1, e, τ'⟩ := τ
  have hh := hbad (rvMk [] (σ c))
    (rvMk [σ m1.2] (σ e) :: (backRounds σ k τ').map fun p => rvMk p.1 p.2) (σ c)
    ⟨σ m1.2, σ e, backRounds σ k τ', []⟩ (⟨[], [], [], zeroE⟩, d) (oneDrawn_mk _ _ _)
    (heard_mk _ _ _)
    (by
      show (((), ()), ρ.val (σ c), ((), ρ.val (σ m1.2)), ρ.val (σ e),
        trRounds ρ k (backRounds σ k τ')) = _
      rw [hσ, hσ, hσ, tr_back ρ σ hσ]
      rfl)
    rfl () trivial (by show lhs ρ _ _ = ρ.val zeroE; rw [lhs_nil, ρ.zero]) _
    (List.mem_singleton.2 rfl)
  have h1 : lhs ρ _ (⟨[], [], [], oneE⟩ : TensorRow) = ρ.val oneE := hh
  rw [lhs_nil, ρ.one] at h1
  exact zero_ne_one h1

/-- The same at the release's own reading, without a premise. -/
theorem not_sound2_yes_gl (nR k : ℕ) : ¬ SoundAt2 ρg nR k sillyYes :=
  not_sound2_yes ρg (fun a => E.ofTriple (ofE a)) gl_section nR k gl_three
    { st := default, book := default, roots := 0, opened := [], loc := () } extNone ()

/-- The text that always refuses meets the form. -/
theorem sound2_no (nR k : ℕ) : SoundAt2 ρ nR k sillyNo :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ _ _ _ _ hb => by cases hb

/-- The bound of `batt_doomed` with the matrix fixed, and the mask entries free behind the draws. -/
def FreeMaskAt (nR k : ℕ) : Prop :=
  ∀ (pile : List TensorRow) (fresh : List Slot) (Ex : ExtSpec) (_ : Ex.Str),
    Batt.fits k pile = true →
    Doomed (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape
      (Cb.Pv.BattShort.eps (parOf ρ nR k pile) Ex)
      fun τ => ∀ (x : E) (h : Psc.Heard) (o : Psc.Out), trOf ρ nR pile Ex x h = τ →
        Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o →
        ∀ w : Wit K nR k, (w.mat = fun _ _ => 0) → Holds ρ w (Batt.rowOf pile o) →
          ∀ r ∈ pile, Holds ρ w r

include hσ in
/-- **With the matrix fixed and the mask entries free behind the draws the bound is false.** -/
theorem not_freeMask (nR : ℕ) (h3 : 2 < Fintype.card K) (Ex : ExtSpec) (y : Ex.Str) :
    ¬ FreeMaskAt ρ nR 1 := by
  intro h
  have hf : Batt.fits 1 pile1 = true := rfl
  refine not_doomed _ _ _ (below_eps ρ nR 1 pile1 Ex h3 (by simp [pile1]; omega))
    (fun τ hbad => ?_) (h pile1 fresh1 Ex y hf)
  obtain ⟨m0, c, m1, e, τ'⟩ := τ
  obtain ⟨o, ho⟩ := run_some (x := σ c) (fresh := fresh1)
    (h := ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩) hf rfl rfl
    (fun p hp => by
      obtain ⟨m2, g, u⟩ := τ'
      obtain rfl := List.mem_singleton.1 hp
      rfl) rfl
  have htr : trOf ρ nR pile1 Ex (σ c) ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩ =
      (m0, c, m1, e, τ') := by
    show (((), ()), ρ.val (σ c), ((), ρ.val (σ m1.2)), ρ.val (σ e),
      trRounds ρ 1 (backRounds σ 1 τ')) = _
    rw [hσ, hσ, hσ, tr_back ρ σ hσ]
    rfl
  have hrow := fun w => row_iff K ρ nR 1 w pile1 fresh1 Ex (σ c)
    ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩ o hf ho
  have hfalse : ∀ a : K, ¬ Holds ρ (wit1 nR a) (⟨[{}], [zeroE], [], oneE⟩ : TensorRow) := by
    intro a hh
    have h1 : Alg.mle (colOf (wit1 nR a) (weights ρ nR [{}])) (rd ρ 1 [zeroE]) +
        formVal ρ (wit1 nR a).mask [] = ρ.val oneE := hh
    rw [mle_zero_mat, ρ.one] at h1
    simp [formVal] at h1
  obtain ⟨z, hz⟩ : ∃ z : (parOf ρ nR 1 pile1).par.Mid, z = outOf ρ nR pile1 Ex
      (trOf ρ nR pile1 Ex (σ c) ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩) := ⟨_, rfl⟩
  have hq : ∀ q : Fin pile1.length, (pile1.get q).masks = [] := by
    intro q
    have hm : pile1.get q ∈ pile1 := List.get_mem _ _
    rw [List.mem_singleton.1 hm]
  have hw := whole_eq ρ (wit1 nR z.fin) pile1 fresh1 (ρ.val (σ c)) (ρ.val (σ e))
    (pH (fmtOf K 1) (pdPlains K 2 1) z.pt)
  rw [hU_wit1] at hw
  simp only [mle_zero_mat, hq, formVal, List.map_nil, List.sum_nil, mul_zero,
    Finset.sum_const_zero, add_zero] at hw
  have hmid : (parOf ρ nR 1 pile1).par.MidHolds z (msgOf ρ (wit1 nR z.fin) pile1 fresh1) := by
    rw [hz] at hw ⊢
    exact hw
  rw [hz] at hmid
  exact hfalse _ (hbad (σ c) _ o htr ho _ rfl ((hrow _).2 hmid) _ (List.mem_singleton.2 rfl))

/-- The same at the release's own reading, without a premise. -/
theorem not_freeMask_gl (nR : ℕ) : ¬ FreeMaskAt ρg nR 1 :=
  not_freeMask ρg (fun a => E.ofTriple (ofE a)) gl_section nR gl_three extNone ()

/-- **The law of the batching's joined block at the very reader of the law behind W's commitment**:
a matrix, with all mask entries off one world's words. The pin fixes the matrix and the words of the
index masks' message alone. -/
theorem atM3_at_joint {Cl W : Type} {nR : ℕ} (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT)
    (ds : List RDT) (hD : Declared P dZ d0 ds) (idx : ℕ)
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (dec : F.E.Str → Wit GE nR P.lin.kCol) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun a => a.1.out.indexMasks = idx)
      (FrontOk P)
      (RowsHold (fun w => witOf (rwM w) (rwW w)) (pinOf2 idx (fun w => witOf (rwM w) (rwW w)) dec))
      (RowsHold (fun w => witOf (rwM w) (rwW w))
        (pinOf2 idx (fun w => witOf (rwM w) (rwW w)) dec)) :=
  atM3_goodIn_pins F P base dZ d0 ds hD idx _ dec hloc

end VerifiableInference.Desc.K13.Law
