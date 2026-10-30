-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fam/BattShortInhabited.lean: one written caller meets the condition of the kind
`KObj.KBattShortF`, the batching of tensor rows with short messages
(Johnson/Top/Fam/BattShort.lean, Johnson/Top/H/BattShort.lean, Johnson/Top/H/Batt.lean).

A theorem "for every caller that meets the kind's condition" says nothing if no caller meets it.
Here is one, over the protocol's field `Cb.Gl.E`. Definitions, statements and proofs.

The caller. A matrix of two rows and two columns (one column variable). Two claims, each with a
mask of its own; the state is any two row vectors and any two points, and the targets are any two
values. The coefficients of the two claims are the powers 1 and x of one drawn value x
(`Cb.Evader.powers`). The round polynomials have degree at most 2, so the hiding polynomial has
three coefficients. That makes nine entries: four of the matrix, two masks, three coefficients.
Each entry is the datum of an oracle message of its own, the library's toy message `Cb.GlJ3.toyS`
(Cb/GlVal/GlJ3Send.lean: two Reed-Solomon rows on eight points, distance 5, radius 3, a sample with
a pad); the signature is the family of the nine (`Cb.GlJ3.datSig`, Cb/GlVal/GlJ3RefKit.lean). No
further oracle, no further witness, and the joint that rides along asks nothing.
Main names:
  `KBattShortF_inhabited_B`, `KBattShortF_inhabited_c`: the batching's data; the caller.
  `KBattShortF_inhabited_ok`: the caller meets the condition, `BattOK`: 2 is at most the degree,
    and the coefficients evade zero (`Cb.ok_powers`).
  `KBattShortF_inhabited_shape`: the block of every caller has a round.
  `KBattShortF_inhabited_errs`, `KBattShortF_inhabited_vals`: the caller's block has three rounds;
    their errors are 1, 1, 2, as counts among as many values as the field has elements.
  `KBattShortF_inhabited_both`: at every statement some committed messages meet the two claims and
    some do not.
  `KBattShortF_inhabited_over`: over any signature whose radii are below the distance: for every
    tuple of messages a statement whose words decode to that tuple, without a collision.
  `KBattShortF_inhabited_src`: so, at the joint before the caller's block, among the statements of
    which knowledge soundness speaks one has a witness and one has none.
  `KBattShortF_inhabited`: the kind has a caller that meets its condition and whose block has a
    round.
What is not claimed: that the caller is one of the programs', or has their sizes, their code or
their radius: it is a toy. The kind's condition asks nothing of the signature; of the toy message
only its laws, its distance, that its radius is below the distance (`Cb.GlJ3.gl_j3_send`), its
plain format and the reading of its datum are used. Nothing on the joint behind the block, on an
honest prover, or on any other caller. By itself the last theorem would also be met by an idle
caller, and its clause on the round holds of every caller: what shows that the kind has a caller
worth the name is the written caller with `KBattShortF_inhabited_src`, `_errs` and `_vals`.
-/
import Johnson.Top.Fam.BattShort
import Cb.Gen.BatEvaderProofs
import Cb.GlVal.GlJ3RefKit
import Cb.Ld.LdSigProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb VerifiableInference.OnPublicFiles

/-- the number of the matrix's rows -/
abbrev KBattShortF_inhabited_rows : ℕ := 2
/-- the number of its column variables -/
abbrev KBattShortF_inhabited_vars : ℕ := 1
/-- the number of claims -/
abbrev KBattShortF_inhabited_claims : ℕ := 2
/-- the largest degree of a round polynomial -/
abbrev KBattShortF_inhabited_deg : ℕ := 2

/-- the entries: the matrix's, a mask for each claim, the hiding polynomial's coefficients -/
abbrev KBattShortF_inhabited_J : Type :=
  (Fin KBattShortF_inhabited_rows × (Fin KBattShortF_inhabited_vars → Bool)) ⊕
    Fin KBattShortF_inhabited_claims ⊕
    PIdx (List.replicate KBattShortF_inhabited_vars (pfCube Cb.Gl.E KBattShortF_inhabited_deg))

/-- The batching's data. The state holds the claims' row vectors and points. -/
@[reducible] noncomputable def KBattShortF_inhabited_B : BattPar Cb.Gl.E where
  St := (Fin KBattShortF_inhabited_claims → Fin KBattShortF_inhabited_rows → Cb.Gl.E) ×
    (Fin KBattShortF_inhabited_claims → Fin KBattShortF_inhabited_vars → Cb.Gl.E)
  J := KBattShortF_inhabited_J
  Rw := Fin KBattShortF_inhabited_rows
  k := KBattShortF_inhabited_vars
  mAt := Sum.inl
  Q := Fin KBattShortF_inhabited_claims
  g := fun st => st.1
  pt := fun st => st.2
  slM := fun q _ j => if j = Sum.inr (Sum.inl q) then 1 else 0
  Z := Evader.powers Cb.Gl.E KBattShortF_inhabited_claims
  n := KBattShortF_inhabited_deg
  wAt := fun i => Sum.inr (Sum.inr i)

/-- The caller: each entry is the datum of a toy oracle message of its own. -/
@[reducible] noncomputable def KBattShortF_inhabited_c : BattCaller Cb.Gl.E where
  B := KBattShortF_inhabited_B
  Ex := extNone
  Kc := Unit
  Wp := Unit
  Sg := Cb.GlJ3.datSig KBattShortF_inhabited_J
  A0 := (Cb.GlJ3.datSig KBattShortF_inhabited_J).pred (fun _ _ _ => True) fun _ _ _ => True
  msg := fun m j => Cb.GlJ3.datAt (I := KBattShortF_inhabited_J) m j

/-- The caller meets the kind's condition. -/
theorem KBattShortF_inhabited_ok : BattOK [KBattShortF_inhabited_c] := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact ⟨le_refl _, Cb.ok_powers Cb.Gl.E KBattShortF_inhabited_claims⟩

/-- The block of every caller begins with the round in which the coefficients are drawn. -/
theorem KBattShortF_inhabited_shape (c : KBattShortF.ι) : (KBattShortF.blk c).R.shape ≠ [] :=
  List.cons_ne_nil _ _

/-- The errors of the caller's three rounds, as counts. -/
theorem KBattShortF_inhabited_errs :
    (Cb.Pv.BattShort.eps KBattShortF_inhabited_c.B KBattShortF_inhabited_c.Ex).toList =
      [KBattShortF_inhabited_claims - 1, 1, KBattShortF_inhabited_deg] :=
  Cb.Pv.BattShort.errs _ _

/-- In each of the three rounds the verifier draws one element of the field. -/
theorem KBattShortF_inhabited_vals :
    (Cb.Pv.BattShort.R KBattShortF_inhabited_c.B KBattShortF_inhabited_c.Ex).shape.chalList =
      [Fintype.card Cb.Gl.E, Fintype.card Cb.Gl.E, Fintype.card Cb.Gl.E] :=
  Cb.Pv.BattShort.vals _ _

/-- entries with the matrix 0, given masks, and the hiding polynomial 0 -/
def KBattShortF_inhabited_vec (t : Fin KBattShortF_inhabited_claims → Cb.Gl.E) :
    KBattShortF_inhabited_J → Cb.Gl.E :=
  Sum.elim (fun _ => 0) (Sum.elim t fun _ => 0)

/-- At such entries the left side of a claim is its mask. -/
theorem KBattShortF_inhabited_lhs (st : KBattShortF_inhabited_B.St)
    (q : Fin KBattShortF_inhabited_claims) (t : Fin KBattShortF_inhabited_claims → Cb.Gl.E) :
    KBattShortF_inhabited_B.lhs st q (KBattShortF_inhabited_vec t) = t q := by
  have hc : KBattShortF_inhabited_B.col (KBattShortF_inhabited_vec t)
      (KBattShortF_inhabited_B.g st q) = 0 :=
    funext fun _ => Finset.sum_eq_zero fun _ _ => mul_zero _
  rw [BattPar.lhs, BattPar.ten, hc, Alg.mle_zero, zero_add]
  refine (Finset.sum_eq_single (Sum.inr (Sum.inl q)) (fun j _ hj => ?_) fun h => ?_).trans ?_
  · exact (congrArg (· * _) (if_neg hj)).trans (zero_mul _)
  · exact absurd (Finset.mem_univ _) h
  · exact (congrArg (· * _) (if_pos rfl)).trans (one_mul _)

/-- At every statement some committed messages meet the claims and some do not. -/
theorem KBattShortF_inhabited_both
    (x : (KBattShortF_inhabited_B.Q → Cb.Gl.E) × KBattShortF_inhabited_B.St) :
    (∃ m : KBattShortF_inhabited_c.Sg.Msg,
      KBattShortF_inhabited_c.B.InHolds x (KBattShortF_inhabited_c.msg m)) ∧
    ∃ m : KBattShortF_inhabited_c.Sg.Msg,
      ¬ KBattShortF_inhabited_c.B.InHolds x (KBattShortF_inhabited_c.msg m) := by
  have hm : ∀ v : KBattShortF_inhabited_J → Cb.Gl.E,
      KBattShortF_inhabited_c.msg (Cb.GlJ3.datMsg v) = v := fun v =>
    funext fun j => Cb.GlJ3.datAt_msg v j
  refine ⟨⟨Cb.GlJ3.datMsg (KBattShortF_inhabited_vec x.1), fun q => ?_⟩,
    ⟨Cb.GlJ3.datMsg (KBattShortF_inhabited_vec fun q => x.1 q + 1), fun h => ?_⟩⟩
  · rw [hm]
    exact KBattShortF_inhabited_lhs x.2 q x.1
  · have h0 := h ⟨0, Nat.succ_pos _⟩
    rw [hm, KBattShortF_inhabited_lhs] at h0
    exact one_ne_zero (add_left_cancel (h0.trans (add_zero _).symm))

section
variable {E : Type} [Field E]

omit [Field E] in
/-- An encoding is within 0 positions of itself. -/
theorem KBattShortF_inhabited_near (o : OMsg E) (f : o.Str) (w : o.Wit)
    (hf : o.upW f = o.C.enc w.1 w.2) : o.C.Near 0 (o.upW f) (o.C.enc w.1 w.2) := by
  rw [hf]
  exact le_of_eq (cnt_false fun _ h => h rfl)

/-- At a radius below the distance the list of an encoding has one message: no seed has a
collision. -/
theorem KBattShortF_inhabited_noClash (o : OMsg E) {d : ℕ} (hL : o.C.Laws) (hd : o.C.Dist d)
    (he : o.e < d) (f : o.Str) (w : o.Wit) (hf : o.upW f = o.C.enc w.1 w.2) (ρ : o.Z.D) :
    ¬ o.Clash f ρ := by
  have hall : ∀ m', o.InList f m' → m' = w.1 := by
    rintro m' ⟨r', hr'⟩
    exact congrArg Prod.fst (o.C.near_eq hL hd (by omega) (o.upW f) (m', r') w hr'
      (KBattShortF_inhabited_near o f w hf))
  rintro ⟨u, u', hu, hu', hne, _⟩
  exact hne ((hall u hu).trans (hall u' hu').symm)

/-- Over a signature whose radii are below the distance and whose formats reach every word: for
every tuple m of messages there is a statement, among those of which knowledge soundness speaks,
whose witnesses are those with the messages m that the base joint accepts. -/
theorem KBattShortF_inhabited_over (S : Sig E) {Kc St Wp : Type} {E₀ : ExtSpec}
    (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) {d : ℕ} (hL : ∀ i, (S.om i).C.Laws)
    (hd : ∀ i, (S.om i).C.Dist d) (he : ∀ i, (S.om i).e < d)
    (hup : ∀ i (g : (S.om i).C.Word), ∃ f, (S.om i).upW f = g) (x : St) (y : E₀.Str) (m : S.Msg)
    (hon : A.on (x, y)) :
    ∃ a, (S.over A).on a ∧
      ∀ w, (S.over A).relR a w ↔ S.msgs w.1 = m ∧ A.relR (x, y) (m, w.2) := by
  choose f hf using fun i => hup i ((S.om i).C.enc (m i) 0)
  have ρ : ∀ i, (S.om i).Z.D := fun i => Classical.arbitrary _
  have hdec : ∀ i, (S.om i).dec (f i) (ρ i, (S.om i).Z.val (ρ i) (m i)) = some (m i) := fun i =>
    sig_dec_close E (S.om i) d 0 (hL i) (hd i) (Nat.zero_le _) (he i) (f i) (m i)
      ⟨0, KBattShortF_inhabited_near (S.om i) (f i) (m i, 0) (hf i)⟩ (ρ i)
  refine ⟨((x, fun i => (ρ i, (S.om i).Z.val (ρ i) (m i))), (y, f)),
    ⟨fun i => KBattShortF_inhabited_noClash (S.om i) (hL i) (hd i) (he i) (f i) (m i, 0) (hf i)
      (ρ i), hon⟩, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hm : S.msgs w.1 = m := funext fun i => (Option.some.inj ((hdec i).symm.trans (h.1 i))).symm
    exact ⟨hm, hm ▸ h.2⟩
  · exact ⟨fun i => (hdec i).trans (congrArg some (congrFun h.1 i).symm), h.1 ▸ h.2⟩

end

/-- The joint before the caller's block: among the statements of which knowledge soundness speaks,
one has a witness and one has none. -/
theorem KBattShortF_inhabited_src :
    (∃ a w, (KBattShortF.src KBattShortF_inhabited_c).on a ∧
      (KBattShortF.src KBattShortF_inhabited_c).relR a w) ∧
    ∃ a, (KBattShortF.src KBattShortF_inhabited_c).on a ∧
      ∀ w, ¬ (KBattShortF.src KBattShortF_inhabited_c).relR a w := by
  obtain ⟨-, he, hd, hL, -⟩ := Cb.GlJ3.gl_j3_send
  have key := KBattShortF_inhabited_over KBattShortF_inhabited_c.Sg
    (KBattShortF_inhabited_c.B.baseIn KBattShortF_inhabited_c.Ex KBattShortF_inhabited_c.A0
      fun w => KBattShortF_inhabited_c.msg w.1)
    (fun _ => hL) (fun _ => hd) (fun _ => he) (fun _ g => ⟨g, rfl⟩)
    (0, (0, 0)) ()
  obtain ⟨⟨m, hm⟩, ⟨m', hm'⟩⟩ := KBattShortF_inhabited_both (0, (0, 0))
  obtain ⟨a, ha, hw⟩ := key m trivial
  obtain ⟨a', ha', hw'⟩ := key m' trivial
  exact ⟨⟨a, (fun i => (m i, 0), ()), ha, (hw _).2 ⟨rfl, trivial, hm⟩⟩,
    ⟨a', ha', fun w h => hm' ((hw' w).1 h).2.2⟩⟩

/-- The kind has a caller that meets its condition and whose block has a round. -/
theorem KBattShortF_inhabited : ∃ c : KBattShortF.ι,
    KBattShortF.mem c ∧ (KBattShortF.blk c).R.shape ≠ [] := by
  exact ⟨KBattShortF_inhabited_c, KBattShortF_inhabited_ok,
    KBattShortF_inhabited_shape KBattShortF_inhabited_c⟩

end KObj

#print axioms KObj.KBattShortF_inhabited
