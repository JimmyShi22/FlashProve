-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/View.lean: the image of the merge's written rounds under `mergeMaps`
(Johnson/Top/H0/MergeLaw/Maps.lean) is the library's typed transcript of what was heard. Theorems
with
their proofs.

Main names:
  `rvOne`, `rvT_cons`: what the verifier is shown of one written round, and of a list of them.
  `HeardAs`: a list of rounds as they are shown, against what was heard.
  `mid_view`: the image of the rounds behind the first two.
  `heardAs_of_tape`: what was heard, out of the tape's equation.
  `whole_view`: the image of all the rounds is `sumTr` (OnBytes/Tie/Pv/Lay) at what was heard.

Limits. Statements on readings of transcripts. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Maps
import Johnson.Top.H0.MergeLaw.Beta

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading)
open OnBytes.K.Kc (leading)
open VerifiableInference.Desc.First.Look (elemsOf)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (MergeCaller)

/-- What the verifier is shown of one written round. -/
def rvOne (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  (rvT (ckP .two) [d] (m, c, ())).headD ⟨[], ⟨[], [], [], none⟩⟩

theorem rvT_cons (d : RDT) (ds : List RDT) (m : (wT d).Msg) (c : (wT d).Chal) (τ : Tr (uLT (ckP
    .two) ds)) :
    rvT (ckP .two) (d :: ds) (m, c, τ) = rvOne d m c :: rvT (ckP .two) ds τ := rfl

/-- The elements that the round's record of draws holds, read, are the typed values' elements. -/
theorem rvOne_elems (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) :
    (rvOne d m c).drawn.elems.map toE = elemsV _ (valsOf (toRD d) c) :=
  collect_elems _ _

/-- The elements that the maps read of the message are those among the round's items. -/
theorem rvOne_ans (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) :
    ansOf (toRD d) (msgRD d m) = (rvOne d m c).vals.filterMap fun g =>
      match g with
      | .e x => some (toE x)
      | .answer x => some (toE x)
      | _ => none := rfl

/-- Where all items are scalars, the elements among them, read, are all of them. -/
theorem ans_of_elemsOf : ∀ (l : List Fmt.ItemValue) (xs : List E), elemsOf l = some xs →
    (l.filterMap fun g =>
      match g with
      | .e x => some (toE x)
      | .answer x => some (toE x)
      | _ => none) = xs.map Reading.gl.val
  | [], xs, h => by
    have : xs = [] := by simpa [elemsOf] using h.symm
    subst this
    rfl
  | .e x :: l, xs, h => by
    simp only [elemsOf, Option.map_eq_some_iff] at h
    obtain ⟨ys, hy, rfl⟩ := h
    simp only [List.filterMap_cons, List.map_cons, ans_of_elemsOf l ys hy]
    rfl
  | .f _ :: _, _, h => by simp [elemsOf] at h
  | .word _ :: _, _, h => by simp [elemsOf] at h
  | .root _ :: _, _, h => by simp [elemsOf] at h
  | .answer _ :: _, _, h => by simp [elemsOf] at h

/-- Scalar number i that the maps read of a message all of whose items are scalars. -/
theorem sentT_of (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) (xs : List E) (h : elemsOf (rvOne d m
    c).vals = some xs)
    (i : ℕ) : sentT d m i = Reading.gl.val (xs.getD i zeroE) := by
  unfold sentT
  rw [rvOne_ans d m c, ans_of_elemsOf _ _ h]
  by_cases hi : i < xs.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi, Reading.gl.zero]

/-- The one element that the maps read of the draws. -/
theorem gOne_of (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) (x : E)
    (h : (rvOne d m c).drawn.elems.map E.ofTriple = [x]) :
    gOne _ (valsOf (toRD d) c) = Reading.gl.val x := by
  unfold gOne
  rw [← rvOne_elems d m c]
  cases hr : (rvOne d m c).drawn.elems with
  | nil => simp [hr] at h
  | cons y l =>
    cases l with
    | nil =>
      have : E.ofTriple y = x := by simpa [hr] using h
      subst this
      rfl
    | cons _ _ => simp [hr] at h

open OnBytes.Tie.Pv.Att (cubeTr lastTr) in
/-- A list of rounds as they are shown, against what was heard: each round but the last sends the
scalars s and draws the one element x;
the last sends the one scalar v. -/
def HeardAs : List Fmt.RoundView → List (List E × E) → E → Prop
  | [rV], [], v => elemsOf rV.vals = some [v]
  | r :: r' :: rs, (s, x) :: qs, v =>
    elemsOf r.vals = some s ∧ r.drawn.elems.map E.ofTriple = [x] ∧ HeardAs (r' :: rs) qs v
  | _, _, _ => False

theorem heardAs_length : ∀ (rs : List Fmt.RoundView) (qs : List (List E × E)) (v : E), HeardAs rs qs v →
    rs.length = qs.length + 1
  | [_], [], _, _ => rfl
  | r :: r' :: rs, (s, x) :: qs, v, h => by
    have := heardAs_length (r' :: rs) qs v h.2.2
    simp only [List.length_cons] at this ⊢
    omega
  | [], _, _, h => by simp [HeardAs] at h
  | [_], _ :: _, _, h => by simp [HeardAs] at h
  | _ :: _ :: _, [], _, h => by simp [HeardAs] at h

theorem rvT_length : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)), (rvT (ckP .two) ds τ).length =
    ds.length
  | [], _ => rfl
  | d :: ds, (m, c, τ) => by
    rw [rvT_cons, List.length_cons, List.length_cons, rvT_length ds τ]

open OnBytes.Tie.Pv.Att (cubeTr lastTr) in
/-- **The image of the written rounds behind the first two is the library's typed transcript of what
was heard.** -/
theorem mid_view (dY dV : RDT) (cY beta v : E) (hβ : Reading.gl.val beta ≠ 0) :
    ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) (ds ++ [dY, dV]))) (qs : List (List E × E)),
      HeardAs (rvT (ckP .two) (ds ++ [dY, dV]) τ) (qs ++ [([cY], beta)]) v →
      (midMaps dY dV ds).view τ =
        cubeTr Reading.gl (pDummy GE 1) [pRoundV GE Unit] ds.length (fun _ => 2) qs
          (lastTr Reading.gl 1 Unit [cY] beta hβ fun _ => Reading.gl.val v)
  | [], τ, qs, h => by
    have hlen := heardAs_length _ _ _ h
    rw [rvT_length] at hlen
    obtain ⟨mY', cY', mV', cV', _⟩ := τ
    cases qs with
    | cons q qs' =>
      simp only [List.nil_append, List.length_cons, List.length_nil, List.cons_append,
          List.length_append] at hlen
      omega
    | nil =>
      have h' : elemsOf (rvOne dY mY' cY').vals = some [cY] ∧
          (rvOne dY mY' cY').drawn.elems.map E.ofTriple = [beta] ∧ elemsOf (rvOne dV mV' cV').vals =
              some [v] := h
      obtain ⟨h1, h2, h3⟩ := h'
      have e1 : (fun _ : Fin 1 => sentT dY mY' 0) = Johnson.L5.Layers.rd Reading.gl 1 [cY] := by
        funext t
        rw [sentT_of dY mY' cY' _ h1 0]
        have : t = 0 := Subsingleton.elim _ _
        subst this
        rfl
      have e2 : (unitOf ((elemsV _ (valsOf (toRD dY) cY')).getD 0 0)).val = Reading.gl.val beta :=
          by
        have hg : (elemsV _ (valsOf (toRD dY) cY')).getD 0 0 = Reading.gl.val beta := gOne_of dY mY'
            cY' beta h2
        rw [hg, unitOf_val hβ]
      have e3 : sentT dV mV' 0 = Reading.gl.val v := sentT_of dV mV' cV' _ h3 0
      show (((), fun _ : Fin 1 => sentT dY mY' 0),
          (⟨(unitOf ((elemsV _ (valsOf (toRD dY) cY')).getD 0 0)).val, _⟩ : {x : GE // x ≠ 0}),
          (((), fun _ : Unit => sentT dV mV' 0), (), ())) = _
      simp only [e1, e2, e3]
      rfl
  | d :: ds, τ, qs, h => by
    have hlen := heardAs_length _ _ _ h
    rw [rvT_length] at hlen
    obtain ⟨m, c, τ⟩ := τ
    cases qs with
    | nil =>
      simp only [List.nil_append, List.length_cons, List.length_nil, List.cons_append,
          List.length_append] at hlen
      omega
    | cons q qs' =>
      obtain ⟨s, x⟩ := q
      have h' : elemsOf (rvOne d m c).vals = some s ∧ (rvOne d m c).drawn.elems.map E.ofTriple = [x]
          ∧
          HeardAs (rvT (ckP .two) (ds ++ [dY, dV]) τ) (qs' ++ [([cY], beta)]) v := by
        cases ds with
        | nil =>
          obtain ⟨m1, c1, τ1⟩ := τ
          exact h
        | cons _ _ =>
          obtain ⟨m1, c1, τ1⟩ := τ
          exact h
      obtain ⟨h1, h2, h3⟩ := h'
      have e1 : (fun t : Fin 2 => sentT d m t.val) = Johnson.L5.Layers.rd Reading.gl 2 s := by
        funext t
        exact sentT_of d m c _ h1 t.val
      have e2 : gOne _ (valsOf (toRD d) c) = Reading.gl.val x := gOne_of d m c x h2
      show (((), fun t : Fin 2 => sentT d m t.val), gOne _ (valsOf (toRD d) c), (midMaps dY dV
          ds).view τ) = _
      rw [e1, e2, mid_view dY dV cY beta v hβ ds τ qs' h3]
      rfl

open VerifiableInference.Desc.First.Look (roundS tapeS) in
/-- The strict maker's yes: all items of every round are scalars. -/
theorem tapeS_strict : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (tp : OnBytes.K.Kc.Tape), tapeS rs
    es = some tp →
    ∀ r ∈ rs, elemsOf r.vals = some (leading r.vals)
  | [], _, _, _ => fun _ hr => by simp at hr
  | _ :: _, [], _, h => by simp [tapeS] at h
  | r :: rs, e :: es, tp, h => by
    unfold tapeS at h
    split at h
    · rename_i x t hx ht
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · unfold roundS at hx
        split at hx
        · exact absurd hx (by simp)
        · rename_i sent hs
          rw [hs, leading_of_elemsOf _ _ hs]
      · exact tapeS_strict rs es t ht r' hr'
    · exact absurd h (by simp)

/-- **What was heard, out of the tape's equation**, where all items of every round are scalars. -/
theorem heardAs_of_tape (nR nY nV : String) (rY rV : Nat) (c beta v : E) :
    ∀ (qs : List (Nat × List E × E)) (rs : List Fmt.RoundView) (es : List Fmt.Entry), rs.length = es.length
        →
      (∀ r ∈ rs, elemsOf r.vals = some (leading r.vals)) →
      ((rs.zip es).map fun x => OnBytes.K.Kc.flatOf x.1 (some x.2)) =
        qs.map (rd nR 0) ++ [⟨some nY, 1, rY, [c], [beta]⟩, ⟨some nV, 0, rV, [v], []⟩] →
      HeardAs rs (qs.map (fun q => (q.2.1, q.2.2)) ++ [([c], beta)]) v
  | [], rs, es, hl, hs, h => by
    match rs, es, hl, hs, h with
    | [r1, r2], [e1, e2], _, hs, h =>
      simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
          List.nil_append, List.cons.injEq,
        and_true] at h
      obtain ⟨h1, h2⟩ := h
      have a1 : leading r1.vals = [c] := congrArg (·.sent) h1
      have a2 : r1.drawn.elems.map E.ofTriple = [beta] := congrArg (·.drawn) h1
      have a3 : leading r2.vals = [v] := congrArg (·.sent) h2
      exact ⟨by rw [hs r1 (by simp), a1], a2, show elemsOf r2.vals = some [v] by rw [hs r2 (by
          simp), a3]⟩
    | [], [], _, _, h => simp at h
    | [_], [_], _, _, h => simp at h
    | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _, _, h => simp at h
  | q :: qs, rs, es, hl, hs, h => by
    match rs, es, hl, hs, h with
    | [], [], _, _, h => simp at h
    | r :: rs, e :: es, hl, hs, h =>
      simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have a1 : leading r.vals = q.2.1 := congrArg (·.sent) h1
      have a2 : r.drawn.elems.map E.ofTriple = [q.2.2] := congrArg (·.drawn) h1
      have ih := heardAs_of_tape nR nY nV rY rV c beta v qs rs es (by simpa using hl)
        (fun r' hr' => hs r' (List.mem_cons_of_mem _ hr')) h2
      have hne := heardAs_length _ _ _ ih
      match rs, ih, hne with
      | r' :: rs', ih, _ => exact ⟨by rw [hs r (by simp), a1], a2, ih⟩

/-- The typed list of rounds at k column bits. -/
noncomputable abbrev shapeAt (k : ℕ) : Shape :=
  drawRound GE :: pRound0 GE :: (sRounds (ldPartFmt GE k (fun _ => 2) ++ [pDummy GE 1]) ++ [pRoundV
      GE Unit])

open OnBytes.Tie.Pv.Att (cubeTr) in
theorem cast_aux (n k : ℕ) (hk : n = k) (h : shapeAt n = shapeAt k) (z : Tr (shapeAt n)) (a :
    (drawRound GE).Msg)
    (b : (drawRound GE).Chal) (c : (pRound0 GE).Msg) (d : (pRound0 GE).Chal) (qs : List (List E ×
        E))
    (last : Tr (sRound (pDummy GE 1) :: [pRoundV GE Unit]))
    (hz : z = (a, b, c, d, cubeTr Reading.gl (pDummy GE 1) [pRoundV GE Unit] n (fun _ => 2) qs
        last)) :
    (h ▸ z : Tr (shapeAt k)) =
      (a, b, c, d, cubeTr Reading.gl (pDummy GE 1) [pRoundV GE Unit] k (fun _ => 2) qs last) := by
  subst hk
  exact hz

open OnBytes.Tie.Pv.Lay.Eng (sumTr) in
/-- **The image of the merge's written rounds is the typed transcript of what was heard.** -/
theorem whole_view (G : WeightsL GE) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT} (hk
    : ds.length = G.k)
    (mZ' : (wT dZ).Msg) (cZ' : (wT dZ).Chal) (m0' : (wT d0).Msg) (c0' : (wT d0).Chal)
    (τ : Tr (uLT (ckP .two) (ds ++ [dY, dV]))) (x mu eps cY beta v : E) (qs : List (List E × E))
    (hβ : Reading.gl.val beta ≠ 0)
    (h0 : (rvOne dZ mZ' cZ').drawn.elems.map E.ofTriple = [x])
    (h1 : elemsOf (rvOne d0 m0' c0').vals = some [mu])
    (h1' : (rvOne d0 m0' c0').drawn.elems.map E.ofTriple = [eps])
    (h2 : HeardAs (rvT (ckP .two) (ds ++ [dY, dV]) τ) (qs ++ [([cY], beta)]) v) :
    (mergeMaps G Ex dZ d0 ds dY dV hk).view (mZ', cZ', m0', c0', τ) =
      (((), ()), Reading.gl.val x, ((), Reading.gl.val mu), Reading.gl.val eps,
        sumTr Reading.gl G.L.toSum qs [cY] beta hβ fun _ => Reading.gl.val v) := by
  unfold mergeMaps
  rw [Maps.view_castT]
  have e0 : gOne _ (valsOf (toRD dZ) cZ') = Reading.gl.val x := gOne_of dZ mZ' cZ' x h0
  have e1 : sentT d0 m0' 0 = Reading.gl.val mu := sentT_of d0 m0' c0' _ h1 0
  have e2 : gOne _ (valsOf (toRD d0) c0') = Reading.gl.val eps := gOne_of d0 m0' c0' eps h1'
  have e3 := mid_view dY dV cY beta v hβ ds τ qs h2
  have hv : (Maps.step (mZ dZ) (Maps.step (m0 d0) (midMaps dY dV ds))).view (mZ', cZ', m0', c0', τ)
      =
      (((), ()), Reading.gl.val x, ((), Reading.gl.val mu), Reading.gl.val eps,
        OnBytes.Tie.Pv.Att.cubeTr Reading.gl (pDummy GE 1) [pRoundV GE Unit] ds.length (fun _ => 2)
            qs
          (OnBytes.Tie.Pv.Att.lastTr Reading.gl 1 Unit [cY] beta hβ fun _ => Reading.gl.val v)) :=
              by
    show (((), ()), gOne _ (valsOf (toRD dZ) cZ'), ((), sentT d0 m0' 0), gOne _ (valsOf (toRD d0)
        c0'),
      (midMaps dY dV ds).view τ) = _
    rw [e0, e1, e2, e3]
  exact cast_aux ds.length G.k hk (merge_shape G Ex ds hk) _ _ _ _ _ qs _ hv

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.mid_view
#print axioms VerifiableInference.Desc.First.MergeLaw.heardAs_of_tape
#print axioms VerifiableInference.Desc.First.MergeLaw.whole_view
