-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5LeftLaw.lean: the law of kind K5: what the rows that the sumchecks leave
(Att/LeftP.lean: formOf, left) are worth. A row is worth 0 in a world exactly if the typed
sumcheck's
row claim (UHolds) holds of the typed output on what was heard; an end value's typed claim (EHolds)
holds exactly if the map at the point is what the end value's slot is worth in the ledger's world.

Main names:
  `row_any`: the part's row returns at every summand where it returns at one, and its form is
    formOf:
    the kind's copy of the part's four lines is the part's form.
  `row_uholds`: (formOf hh S0 {}).value = 0 exactly if UHolds, under (D1), (D2), (D4). The one place
    where PartRowLaw enters.
  `left_spec`: left returns formOf at the sum over b of W_b · shown(2 b) · shown(2 b + 1).
  `left3_uholds`: at letters made of a sumcheck of products, with (D4) paid from: the typed weights
    at
    the output's point read as the kind's weights (hW); the end values are those heard (hv).
  `end_slot`: EHolds in terms of the slot's worth.

Premises: PartRowLaw · (D1): the hiding polynomial's coefficients are the world's values under the
slots from the record's first on · (D2): the incoming form is worth the target less the start · hW ·
hv · the places of the mask entries: facts of the letters at a value.
Sources: what Att/K5HearLaw.lean names, and Cb/Pv/Att/Fix.lean (plain_fix); Sc3.lean (Sc3);
Cb/Ld/LdPsc.lean (UHolds, EHolds); OnBytes/Tie/Pv/Att/Flat.lean (sc3Flat, sc3Flat_read); Sc3Top.lean
(sc3Num, sc3Vals, sc3Num_lt); TiesFull.lean (plain_end_slot).
Limits: one direction where a text's return is a premise.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Att.TiesFull
import Johnson.Desc.First.Att.K5HearLaw
import Johnson.Desc.First.Att.LeftP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH plainOut sc3Flat sc3Flat_read sc3Num sc3Vals sc3Num_lt plain_end_slot)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends PartRowLaw)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The part's row returns at every summand where it returns at one; its form is formOf. -/
theorem row_any {hh : MaskedSum.Heard} {S0' : E} {kept' f : Aff} {G1 G : Fork}
    (h : MaskedSum.row hh S0' kept' G1 = some (f, G)) (S0 : E) (kept : Aff) :
    MaskedSum.row hh S0 kept G1 = some (formOf hh S0 kept, G) := by
  have hw := row_write h
  unfold MaskedSum.row
  simp only [Option.bind_eq_bind, hw, Option.bind_some, Option.pure_def]
  rfl

/-- The typed output, with the part's record's target and eps. -/
theorem out_eq {X : Type} {S : SumL K M X} (D : SumH ρ S) {hh : MaskedSum.Heard} (ht : D.t = hh.target)
    (he : hh.eps = D.H.eps) :
    D.out = plainOut ρ S.T D.st hh.target D.H.mu hh.eps D.H.rs D.H.sentY D.H.beta D.b D.v := by
  rw [he, ← ht]
  rfl

/-- **A row is worth 0 exactly if the typed row claim holds.** -/
theorem row_uholds (law : PartRowLaw) {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh)
    (h : SumAt C st riders H hh Gf) (W : World K) (S0 : E) (m : M)
    (D1 : S.T.our.par.W D.st (S.msg m) = OnBytes.Road.Hd.place W.slot (S.T.our.par.vars D.st) hh.first)
    (D2 : S.T.our.par.inc D.st (S.msg m) = ρ.val hh.target - C.value ρ W)
    (D4 : S.T.S D.st (ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt) D.out.vals = ρ.val S0) :
    (formOf hh S0 {}).value ρ W = 0 ↔ S.T.our.par.UHolds D.out (S.msg m) := by
  obtain ⟨vs, e, F, G, used, e1, sd, _⟩ := h
  obtain ⟨n, e2⟩ := hs
  rw [e1] at e2
  injection e2 with e3 e4
  subst e3 e4
  obtain ⟨_, _, hH, ht⟩ := hD
  subst hH
  have hl : D.H.rs.map (·.1.length) = List.ofFn S.T.deg := by
    rw [sd.lens, List.map_map]
    exact List.map_id _
  obtain ⟨G1, f, hr⟩ := sd.row
  have ho := out_eq D ht sd.eps
  rw [ho] at D4 ⊢
  rw [← sd.start] at D2
  exact law K ρ S.T S.ok.one (plain_fix S.T S.ok) W hh D.H.rs D.H.sentY D.H.beta D.b D.v D.H.mu S0 D.st (S.msg m) G1 G _
    ⟨sd.vars, sd.r, by rw [sd.claim, sd.eps]; rfl⟩ hl sd.lenY (row_any hr S0 {}) D1 D2 D4

/-! ## «left»: a sumcheck of products -/

theorem shown_val {F : Fork} {j : Nat} {y : E} (h : F.shown j = some y) : y = F.vp.getD j zeroE := by
  unfold Fork.shown at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem left_fold (F : Fork) (s : Nat) (W : Array E) : ∀ (l : List Nat) (a r : E),
    l.foldlM (fun a b => do
      pure (addE a (mulE (mulE (W.getD b zeroE) (← F.shown (s + 2 * b))) (← F.shown (s + (2 * b + 1)))))) a = some r →
    r = l.foldl (fun a b => addE a (mulE (mulE (W.getD b zeroE) (F.vp.getD (s + 2 * b) zeroE))
      (F.vp.getD (s + (2 * b + 1)) zeroE))) a
  | [], a, r, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h.symm
  | b :: l, a, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y1, k1, h1⟩ := Option.bind_eq_some_iff.1 h1
    obtain ⟨y2, k2, h1⟩ := Option.bind_eq_some_iff.1 h1
    simp only [Option.pure_def, Option.some.injEq] at h1
    rw [List.foldl_cons, ← shown_val k1, ← shown_val k2, h1]
    exact left_fold F s W l a' r h2

/-- «left» returns formOf at the flat summand on what lies under the end values' slots. -/
theorem left_spec {F : Fork} {hh : MaskedSum.Heard} {W : Array E} {f : Aff} (h : left F hh W = some f) :
    f = formOf hh (sc3Flat W (fun j => F.vp.getD (hh.sEnd + j) zeroE) W.size 0 zeroE) {} := by
  unfold left at h
  obtain ⟨s0, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  simp only [Option.pure_def, Option.some.injEq] at h2
  rw [← h2, left_fold F hh.sEnd W _ _ _ h1]
  unfold sc3Flat
  rw [← List.range_eq_range']

/-- **«left»'s row at a sumcheck of products.** -/
theorem left3_uholds (law : PartRowLaw) {X : Type} (T3 : Sc3 K) (n : ℕ) (cl : X → (Fin n → K) → K × T3.St)
    (msg : M → T3.J → K) (Lc : X → (Fin n → K) → M → Prop) (D : SumH ρ (SumL.of3 T3 n cl msg Lc)) {C : Aff}
    {nv : Nat} {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork}
    (hs : SizeP (SumL.of3 T3 n cl msg Lc) (products nv T3.nb)) (hD : OfP D riders H hh)
    (h : SumAt C (products nv T3.nb) riders H hh Gf) (W : World K) (m : M) {Wt : Array E} {f : Aff}
    (hf : left Gf hh Wt = some f) (hsz : Wt.size = T3.nb)
    (hv : D.v = sc3Vals ρ T3.nb H.v)
    (hW : ∀ b : Fin T3.nb, T3.W D.st b (ldPartIni T3.nv (fun _ => 3) (pDummy K 2) D.out.pt) = ρ.val (Wt.getD b.1 zeroE))
    (D1 : T3.plain.our.par.W D.st (msg m) = OnBytes.Road.Hd.place W.slot (T3.plain.our.par.vars D.st) hh.first)
    (D2 : T3.plain.our.par.inc D.st (msg m) = ρ.val hh.target - C.value ρ W) :
    f.value ρ W = 0 ↔ T3.plain.our.par.UHolds D.out (msg m) := by
  rw [left_spec hf]
  refine row_uholds law _ D hs hD h W _ m D1 D2 ?_
  obtain ⟨vs, e, F, G, used, e1, sd, hst⟩ := h
  injection e1 with _ e3
  subst e3
  have hvals : D.out.vals = D.v := OnBytes.Tie.Pv.Att.plain_vals ρ _ D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _
  show ∑ b, T3.W D.st b _ * D.out.vals (b, false) * D.out.vals (b, true) = _
  rw [hsz, sc3Flat_read, hvals, hv]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb := b.2
  have p0 := (hst _ _ _ (sd.ends (2 * b.1) (by show 2 * b.1 < 2 * T3.nb; omega))).2.1
  have p1 := (hst _ _ _ (sd.ends (2 * b.1 + 1) (by show 2 * b.1 + 1 < 2 * T3.nb; omega))).2.1
  rw [p0, p1]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (hW b) ?_) ?_
  · simp [sc3Vals, sc3Num]
  · simp [sc3Vals, sc3Num]

/-! ## An end value -/

/-- **An end value's typed claim, in the ledger's world.** j: the end value's number among those
heard. -/
theorem end_slot {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf) (m : M) (a : S.T.A)
    (j : Nat) (hj : j < H.v.length) (mask : Nat → K) (entry : Nat → Nat → Nat → K)
    (hv : D.v a = ρ.val (H.v.getD j zeroE)) (hm : S.msg m (S.T.cAt a) = mask (hh.sEnd + j)) :
    S.T.our.par.EHolds D.out (S.msg m) a ↔
      S.T.map D.st (S.msg m) a (ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt) =
        (Gf.worldOf ρ mask entry).slot (hh.sEnd + j) := by
  obtain ⟨vs, e, F, G, used, _, sd, hst⟩ := h
  obtain ⟨_, _, hH, _⟩ := hD
  subst hH
  refine plain_end_slot ρ S.T D.st D.t D.H.mu D.H.eps D.H.rs D.H.sentY D.H.beta D.b D.v (S.msg m) a _ ?_
  rw [(hst _ _ _ (sd.ends j (by rw [← sd.lenV]; exact hj))).world ρ mask entry, hv, hm]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.row_uholds
#print axioms VerifiableInference.Desc.First.Att.P.left_spec
#print axioms VerifiableInference.Desc.First.Att.P.left3_uholds
#print axioms VerifiableInference.Desc.First.Att.P.end_slot
