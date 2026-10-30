-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/M3Fits.lean: what the batching's joined block promises of the record behind it,
the second half: W's vector fits its table. Statements with their proofs.
Main names:
  `vectorRoom_le`: the room for a vector in a table is at most the table's size.
  `fits_of_linOk`: the test on the shape gives that W's vector fits its table.
  `atM3_fits`: where `atM3 P` says yes, it fits under the codes of the record behind.
  `atM3_front`: so both halves of `FrontOk` hold of the record behind the block.
  `atM3_goodIn_front`: the law of the joined block with `FrontOk P` as the promise behind it.
Used of `verify-on-bytes`, pure functions: `linOk`, `vectorRoom`, `vectorLay`, `linLayW`.

What is not claimed. That the block between the two places (W's commitment) keeps the two halves. At
a reader that takes all mask entries from one world the premise on the pin cannot be met by a real
run (it fixes a value at every mask entry of every message, and messages are sent behind these
draws): there the law is true and idle. The law to carry on is that of
Johnson/Desc/K13/Law/Good2.lean. `Declared` is a test on a plan's written rounds: an evaluation at
two stored sets' public files, a small and a full-size one, said yes, and five controls said no;
no theorem says it of a plan. `Local` asks only that the decoder reads the stored table and the
earlier trees: every such function meets it. A decoder that reads the oracles alone singles out one
member of a list whatever the samples in the record say: so the laws at such a decoder are idle for
the witness that the samples pin. The form to carry on is that of Johnson/Desc/K13/Law/PinA.lean.

-/
import Johnson.Desc.K13.Law.M3On
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame)

variable {Cl : Type}

/-- A loop that only takes minima does not rise. -/
theorem foldl_min_le {α : Type} (c : α → Bool) (f : α → ℕ) : ∀ (l : List α) (m : ℕ),
    l.foldl (fun m p => if c p then min m (f p) else m) m ≤ m
  | [], _ => le_refl _
  | p :: l, m => by
    refine le_trans (foldl_min_le c f l _) ?_
    show (if c p then min m (f p) else m) ≤ m
    split
    · exact Nat.min_le_left _ _
    · exact le_refl _

/-- The room for a vector in a table is at most the table's size. -/
theorem vectorRoom_le (codes : Codes) (s : OracleShape) (rh : Bool) :
    vectorRoom codes s rh ≤ 2 ^ (vectorLay codes s rh).bits := by
  have hroom : s.mainRows * 2 ^ (vectorLay codes s rh).placeBits ≤
      2 ^ (vectorLay codes s rh).bits := by
    show _ ≤ 2 ^ (ceilLog2 s.mainRows + (vectorLay codes s rh).placeBits)
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (le_two_pow_ceilLog2 _)
  unfold vectorRoom
  simp only []
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · split
      · exact hroom
      · split
        · exact Nat.zero_le _
        · exact le_trans (foldl_min_le (fun p : PadPlace => p.part == .main) _ _ _) hroom

/-- The test on the shape gives that W's vector fits its table. -/
theorem fits_of_linOk {codes : Codes} {Sh : LinShape} (h : linOk codes Sh = true) :
    Sh.kCol ≤ (linLayW codes Sh).bits := by
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (le_trans h.2 (vectorRoom_le _ _ _))

/-- Where the quiet block says yes, the shape has passed its test under the part's codes. -/
theorem quietB_lin {T : Type} (X : Lens T) (P : Where) {t t' : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (quietB (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ (p : Part) (msg : Array OracleNotice), X.get? t = some p ∧
      linOk p.d.st.codes P.lin = true ∧ t' = X.set t { p with msg := msg } := by
  simp only [quietB, still, quiet_is, bind_ok, there_ok, need_ok, pure_ok, Lens.part] at h
  obtain ⟨p, hp, _, _, msg, ⟨_, hl, _⟩, rfl⟩ := h
  exact ⟨p, msg, hp, hl, rfl⟩

/-- Where the joined block says yes, W's vector fits its table under the codes of the record behind.
-/
theorem atM3_fits {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    P.lin.kCol ≤ (linLayW s'.st.codes P.lin).bits := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, _, h3⟩ := ebind_ok.1 h'
  obtain ⟨p, msg, hp, hl, rfl⟩ := quietB_lin atS P h3
  obtain ⟨m₂, hs2, _, _, hd⟩ := get_mem hp
  have e : (atS.set s₂ { p with msg := msg }).st = p.d.st := by simp only [atS, hs2]
  rw [e]
  exact fits_of_linOk hl

/-- **Both halves of what the block behind W's commitment is promised hold behind the batching's
joined block.** -/
theorem atM3_front {F : Frame} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (y : F.E.Str)
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') : FrontOk P ((s', y) : S × F.E.Str) :=
  fun l hl => ⟨atM3_claim h l hl, atM3_fits h⟩

/-- **The law of the batching's joined block, with the whole promise behind it.** -/
theorem atM3_goodIn_front {W : Type} {nR : ℕ} (F : Frame) (P : Where) (base : ℕ)
    (dZ d0 : OnBytes.Maker.RDT) (ds : List OnBytes.Maker.RDT) (hD : Declared P dZ d0 ds)
    (rw : W → Wit GE nR ds.length) (dec : F.E.Str → Wit GE nR ds.length) (hloc : Local base dec) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun _ => True) (FrontOk P)
      (RowsHold rw (pinOf rw dec)) (RowsHold rw (pinOf rw dec)) := by
  intro a ha
  refine Iop.Doomed.mono _ _ ?_ (atM3_goodIn_dec (Cl := Cl) F P base dZ d0 ds hD rw dec hloc a ha)
  intro τ hτ b hb
  obtain ⟨rs, gs, hdec⟩ := piece_ok _ hb
  exact ⟨atM3_front b.2 hdec, (hτ b hb).2⟩

end VerifiableInference.Desc.K13.Law
