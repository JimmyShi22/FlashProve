-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Out.lean: THE EQUATION, PROVED OF THE KIND'S OWN HEARING: what hearE
leaves, with what the run "planes" leaves behind it, read, is A.lamRun at the stretch, read: the
plain function of the flat view that the typed lookup's verifier puts out (Lk6.lamS_out, not called
here).

Main names:
  fromKeys_length, al_of_homeIs: K3Key's table of homes gives the alignment.
  dataIs_of: the course's data read off the typed lookup have the face's numbers.
  hear_course: the whole hearing against the whole course, in one world of mask entries.
  rows_typed, key_typed: from all worlds to equal typed rows and claims.
  tape_flat: the strict tape, read, is the stretch, read.
  hearE_inv: a hearing that returns.
  typedShape: TypedShape. shape_hearE, fits_hearE: Rounds.shape and Rounds.fits of hearE (in fits
    the words' test bites: a drawn element that is not (0, 0, 0) reads as an element other than 0
    only if its words are below the prime).
  out_hearE: Law.out of hearE.

Limits. Where the hearing returns. The course over the field and its data dtOf are middle terms of
the proof: they stand in no statement here.

-/
import Johnson.Desc.First.Look.KeyLaw.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World eqTab orderDefault ofNat)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried)
open Lk6 (Dat Pub Pl)
open Lk6.PortSim (rdMF)
open Lk6.Mid (Dt Cs RowF rdRow rdCl cClo cZero cBits cntRowF chnC course dtOf plAt course_of)

/-! ## The table of homes -/

theorem fromKeys_length (f : Face) : (fromKeys f).length = f.slots := by
  have inner : ∀ v k : ℕ, (if k + 1 == v then own (2 * k + 3) ++ [true, true]
      else own (2 * k + 5)).length = 2 * k + 5 := by
    intro v k
    split <;> simp [own_length]
  unfold fromKeys Face.slots
  simp only [List.length_append, own_length, List.length_flatMap, inner]
  omega

theorem al_of_homeIs {f : Face} {first : ℕ} {o k home : ℕ → Slot} (h : HomeIs f first o k home) :
    Al home o k (fromKeys f) first 0 0 := by
  unfold Al
  have e := homesFrom_hs o k (fromKeys f) 0 0 f.slots (by rw [fromKeys_length]; omega)
    (by rw [fromKeys_length]; omega)
  rw [List.drop_zero, List.drop_zero] at e
  apply List.ext_getElem
  · rw [List.length_map, List.length_range', hs_length]
  · intro j h1 h2
    have hj : j < f.slots := by
      rw [List.length_map, List.length_range', fromKeys_length] at h1
      exact h1
    rw [List.getElem_map, List.getElem_range', Nat.one_mul, h j hj]
    unfold homes
    rw [e]
    simp [Array.getD_eq_getD_getElem?, h2]

/-! ## The data -/

theorem dataIs_of {A : Dat GE} {st : A.St} {f : Face} {p : ℕ} (o k : ℕ → Slot)
    (hf : FaceIs A st f) (hadm : A.toPub.Adm p) : DataIs (dtOf A st o k) f where
  pl := hf.planes.symm
  m := by
    show A.parts.length = _
    rw [hf.parts]
  mu := hf.mu.symm
  d := hf.d.symm
  v := fun i => by
    show A.parts.getD i 0 = _
    rw [hf.parts]
  two := by rw [hf.planes]; exact hadm.planes
  one := by rw [hf.parts]; exact hadm.some
  oneD := by rw [hf.d]; exact hadm.tabs
  orders := hf.orders
  factor := hf.factor

variable {home : ℕ → Slot}

/-- **The whole hearing against the whole course**, in one world of mask entries. -/
theorem hear_course (W : PscF.World) {A : Dat GE} {st : A.St} {f : Face} {p : ℕ} {o k : ℕ → Slot}
    (hf : FaceIs A st f) (hadm : A.toPub.Adm p) (hok : f.ok = true) {F G : Fork} {t u : Tape}
    {g : HeardG} (h : messagesG f F t = some (g, G, u)) (hF : Sized F)
    (hal : Al home o k (fromKeys f) F.next 0 0) :
    (course (dtOf A st o k) (flatK (t.map key)) 0 0).alpha = readE g.alpha ∧ g.theta = zeroE ∧
      (flatK (t.map key)).head? = some ([], [readE g.alpha]) ∧ Later F G ∧ Sized G ∧
      G.next = F.next + f.slots ∧ Shp t u (shapeG f) ∧
      ∀ (H H' : Fork) (pl : List PlaneClaim) (u' : Tape), Later G H →
        planesG f g H [] = some (pl, H', u') →
        Later H H' ∧ (∀ a ∈ formsOf g pl, NoEnt a) ∧
        ∀ K, Later H' K →
          (∀ i < A.m, KeyEq W (keyF K home (g.keys.getD i (#[], {})))
            ((course (dtOf A st o k) (flatK (t.map key)) 0 0).leaves i)) ∧
          List.Forall₂ (EvEq W) (rowsF K home g.rows.toList pl)
            (course (dtOf A st o k) (flatK (t.map key)) 0 0).rows := by
  have hD := dataIs_of o k hf hadm
  obtain ⟨alpha, F5, t5, rows1, sZ, sG, F6, t6, rows2, roots, F7, t7, x3, F8, t8, rows3, keys, F9,
      t9,
    table, F11, t11, lv0, F13, t13, zb0, lv, F14, t14, x5, F15, t15, bits, e5, e6, e7, e8, e9, e11,
    e13, e14, e15, e16, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := messages_inv hf.noShift h
  rw [fromKeys_cut] at hal
  obtain ⟨a1, a2, a3, a4, a5, aL, aH, a6, a7, a8⟩ :=
    front_sim (W := W) hD hok hF hal e5 e6 e7 e8 e9 e11
  obtain ⟨b1, b2, b3, b4⟩ := back_sim hD (fun al z => hf.leaf al z) hf.count a1 a2 a3 a4 a5 e13 e14
    e15 e16 g1 g2 g3 g4 g5 g7 g8
  have hm : A.m = f.parts.length := hD.m
  refine ⟨by rw [g2]; exact a5, g1, by rw [g2]; exact aH, aL.trans b1, b2, g9, ?_, ?_⟩
  · rw [shape_cut]
    have := a8.trans b3
    simpa only [List.append_assoc] using this
  · intro H H' pl u' hGH hpl
    obtain ⟨c1, c2, c3⟩ := b4 H H' pl u' hGH hpl
    refine ⟨c1, fun a ha => ?_, fun K hK => ⟨fun i hi => ?_, c3 K hK⟩⟩
    · unfold formsOf at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact c2 a ha
      · rw [g6] at ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have := (a7 i (a6 ▸ hi)).1.ne
        rwa [List.getD_eq_getElem _ _ hi] at this
    · obtain ⟨d1, d2⟩ := a7 i (hm ▸ hi)
      rw [g6]
      exact keyEq_of (d1.later (b1.trans (hGH.trans (c1.trans hK)))) d2

/-! ## From all worlds to typed rows and claims -/

theorem row_typed (A : Dat GE) (sl : Slot → A.J) {x y : RowF} (h : ∀ W, EvEq W x y) :
    rdRow A sl x = rdRow A sl y := by
  obtain ⟨h1, h2⟩ := split_ext fun W => (h W).2
  have hm := (h ⟨fun _ => 0⟩).1
  unfold rdRow
  rw [forms_ext sl h2, hm, h1]

theorem rows_typed (A : Dat GE) (sl : Slot → A.J) : ∀ {xs ys : List RowF},
    (∀ W, List.Forall₂ (EvEq W) xs ys) → xs.map (rdRow A sl) = ys.map (rdRow A sl)
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h ⟨fun _ => 0⟩
  | _ :: _, [], h => by cases h ⟨fun _ => 0⟩
  | x :: xs, y :: ys, h => by
    rw [List.map_cons, List.map_cons, row_typed A sl fun W => (List.forall₂_cons.1 (h W)).1,
      rows_typed A sl fun W => (List.forall₂_cons.1 (h W)).2]

theorem key_typed (A : Dat GE) (sl : Slot → A.J) (al : GE) (v : ℕ) {x y : PscF.PointClaim}
    (h : ∀ W, KeyEq W x y) : rdCl A sl al v x = rdCl A sl al v y := by
  have h0 := h ⟨fun _ => 0⟩
  unfold rdCl
  rw [h0.1, h0.2.1, forms_ext sl fun W => (h W).2.2]

/-! ## The tape -/

theorem tape_flat : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    First.Tape.tapeT {} rs es = some t → flatK (t.map key) = flatRV rs
  | [], [], t, h => by
    cases h
    rfl
  | [], _ :: _, t, h => by cases h
  | _ :: _, [], t, h => by cases h
  | r :: rs, e :: es, t, h => by
    unfold First.Tape.tapeT at h
    cases h1 : First.Tape.roundT {} r e with
    | none => rw [h1] at h; cases h
    | some x =>
      cases h2 : First.Tape.tapeT {} rs es with
      | none => rw [h1, h2] at h; cases h
      | some t' =>
        rw [h1, h2] at h
        cases h
        have ih := tape_flat rs es t' h2
        unfold First.Tape.roundT at h1
        cases h3 : First.Tape.elemsOf r.vals with
        | none => rw [h3] at h1; cases h1
        | some sent =>
          rw [h3] at h1
          dsimp only at h1
          split at h1
          · cases h1
            show (sent.map readE, (r.drawn.elems.map E.ofTriple).map readE) :: flatK (t'.map key) =
                _
            rw [ih]
            show _ = (((First.Tape.elemsOf r.vals).getD []).map readE, _) :: flatRV rs
            rw [h3, List.map_map]
            rfl
          · cases h1

theorem hearE_inv {f : Face} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardG}
    (h : hearE f es F rs = some (g, G)) :
    f.ok = true ∧ ∃ t, First.Tape.tapeT {} rs es = some t ∧ messagesG f F t = some (g, G, []) := by
  unfold hearE at h
  split at h
  · rename_i hok
    refine ⟨hok, ?_⟩
    unfold First.Tape.flRun at h
    cases ht : First.Tape.tapeT {} rs es with
    | none => rw [ht] at h; cases h
    | some t =>
      rw [ht] at h
      refine ⟨t, rfl, ?_⟩
      dsimp only at h
      cases hm : messagesG f F t with
      | none => rw [hm] at h; cases h
      | some x =>
        obtain ⟨a, H, u⟩ := x
        rw [hm] at h
        cases u with
        | nil => cases h; rfl
        | cons _ _ => cases h
  · cases h

theorem plAt_zero (A : Dat GE) (sl : Slot → A.J) (st : A.St) (o k : ℕ → Slot) :
    plAt A sl (dtOf A st o k) 0 0 = placesAt A sl o k := by
  unfold plAt placesAt
  have e1 : (fun n => sl ((dtOf A st o k).ms (0 + n))) = fun n => sl (o n) :=
    funext fun n => by rw [Nat.zero_add]; rfl
  have e2 : (fun n => sl ((dtOf A st o k).ix (0 + n))) = fun n => sl (k n) :=
    funext fun n => by rw [Nat.zero_add]; rfl
  rw [e1, e2]

/-! ## The rounds -/

theorem psc_fmOf (S : Pub) (q : ℕ) (deg : List ℕ) (y : Option (ℕ × ℕ)) :
    (Lk6.psc q deg y).map (Lk6.rowFm S) = (pscShape (deg.map (· - 1)) y).map fmOf := by
  rcases y with _ | ⟨a, b⟩ <;>
    simp [Lk6.psc, pscShape, Lk6.rowFm, fmOf, Lk6.LRow.short, Lk6.rowDraws, Function.comp_def] <;>
    rfl

theorem tree_fmOf (S : Pub) (q more levels : ℕ) :
    (Lk6.tree q more levels).map (Lk6.rowFm S) = (treeShape more levels).map fmOf := by
  unfold Lk6.tree treeShape
  rw [List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun l _ => ?_
  rw [List.map_append, List.map_append, psc_fmOf, List.map_replicate]
  rfl

/-- **The shape's formats are the typed lookup's.** -/
theorem typedShape : TypedShape := by
  intro A st P f hf hadm
  rw [Lk6.runD_fm A P hadm.some (fun i hi => (hadm.bits i hi).1) hadm.tabs]
  unfold Lk6.lamFm Lk6.Lam shapeG Lk6.lamHead Lk6.lamParts Lk6.lamJoin Lk6.lamKeys Lk6.lamTable
    Lk6.lamClo Lk6.lamZero Lk6.lamBits
  rw [hf.planes, hf.parts, hf.mu, hf.d]
  simp only [List.map_append, List.map_flatMap, psc_fmOf, tree_fmOf, List.map_replicate,
    List.map_nil, List.map_cons]
  rfl

/-- The alignment at tables that name one entry throughout. -/
theorem al_const (d : Slot) : ∀ (pat : List Bool) (nx a b : ℕ),
    Al (fun _ => d) (fun _ => d) (fun _ => d) pat nx a b
  | [], _, _, _ => rfl
  | false :: bs, nx, a, b => by
    unfold Al
    rw [List.length_cons, List.range'_succ, List.map_cons]
    exact congrArg (d :: ·) (al_const d bs (nx + 1) (a + 1) b)
  | true :: bs, nx, a, b => by
    unfold Al
    rw [List.length_cons, List.range'_succ, List.map_cons]
    exact congrArg (d :: ·) (al_const d bs (nx + 1) a (b + 1))

/-- **What is heard has the lookup's shape.** -/
theorem shape_hearE (A : Dat GE) (st : A.St) (f : Face) (es : List Fmt.Entry) (F : Fork)
    (rs : List Fmt.RoundView) (g : HeardG) (G : Fork) (hf : FaceIs A st f) (hadm : A.toPub.Adm Cb.Gl.p)
    (hF : Sized F) (h : hearE f es F rs = some (g, G)) :
    ∃ t, First.Tape.tapeT {} rs es = some t ∧ t.map shapeOf = shapeG f := by
  obtain ⟨hok, t, ht, hm⟩ := hearE_inv h
  obtain ⟨ks, e1, e2⟩ := (hear_course ⟨fun _ => 0⟩ hf hadm hok hm hF
    (al_const default (fromKeys f) F.next 0 0)).2.2.2.2.2.2.1
  refine ⟨t, ht, ?_⟩
  rw [List.map_nil, List.append_nil] at e1
  rw [← e2, ← e1, List.map_map]
  rfl

/-- In every round of the shape none of the drawn elements must be other than 0, or all. -/
theorem psc_simple (sent : List ℕ) (y : Option (ℕ × ℕ)) :
    ∀ x ∈ pscShape sent y, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1 := by
  intro x hx
  unfold pscShape at hx
  rcases y with _ | ⟨a, b⟩ <;> simp at hx <;> rcases hx with rfl | hx
  · exact Or.inl rfl
  · obtain ⟨g, -, rfl⟩ := hx
    exact Or.inl rfl
  · exact Or.inl rfl
  · rcases hx with ⟨g, -, rfl⟩ | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem tree_simple (more levels : ℕ) :
    ∀ x ∈ treeShape more levels, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1 := by
  intro x hx
  unfold treeShape at hx
  obtain ⟨l, -, hx⟩ := List.mem_flatMap.1 hx
  rcases List.mem_append.1 hx with hx | hx
  · exact psc_simple _ _ x hx
  · obtain rfl : x = _ := by simpa using hx
    exact Or.inl rfl

theorem shape_simple (f : Face) : ∀ x ∈ shapeG f, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1 := by
  intro x hx
  unfold shapeG at hx
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at hx
  rcases hx with ((((((((rfl | hx) | ⟨_, -, hx⟩) | ⟨_, -, hx⟩) | rfl) | ⟨_, -, hx⟩) | hx) | hx) |
    rfl) | hx
  · exact Or.inl rfl
  · exact psc_simple _ _ x hx
  · exact psc_simple _ _ x hx
  · exact psc_simple _ _ x hx
  · exact Or.inl rfl
  · exact tree_simple _ _ x hx
  · exact tree_simple _ _ x hx
  · exact psc_simple _ _ x hx
  · exact Or.inl rfl
  · exact psc_simple _ _ x hx

/-- **The strict tape of a stretch whose words are below the prime, read, fits its shapes'
formats.** -/
theorem tape_fits : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    First.Tape.tapeT {} rs es = some t → viewWordsBelowPrime ⟨rs, []⟩ = true →
    (∀ x ∈ t.map shapeOf, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1) →
    Lk6.Flat.fitsAll ((t.map shapeOf).map fmOf) (flatRV rs) = true
  | [], [], t, h, _, _ => by
    cases h
    rfl
  | [], _ :: _, t, h, _, _ => by cases h
  | _ :: _, [], t, h, _, _ => by cases h
  | r :: rs, e :: es, t, h, hw, hs => by
    unfold First.Tape.tapeT at h
    cases h1 : First.Tape.roundT {} r e with
    | none => rw [h1] at h; cases h
    | some x =>
      cases h2 : First.Tape.tapeT {} rs es with
      | none => rw [h1, h2] at h; cases h
      | some t' =>
        rw [h1, h2] at h
        cases h
        have hw' : viewWordsBelowPrime ⟨rs, []⟩ = true ∧
            (r.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true :=
                by
          unfold viewWordsBelowPrime at hw ⊢
          simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hw ⊢
          exact ⟨hw.2, hw.1.1⟩
        have ih := tape_fits rs es t' h2 hw'.1 fun y hy => hs y (List.mem_cons_of_mem _ hy)
        have hx := hs (shapeOf x) List.mem_cons_self
        unfold First.Tape.roundT at h1
        cases h3 : First.Tape.elemsOf r.vals with
        | none => rw [h3] at h1; cases h1
        | some sent =>
          rw [h3] at h1
          dsimp only at h1
          split at h1
          · rename_i hc
            cases h1
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, -⟩, -⟩, c7⟩ := hc
            show (Lk6.Flat.Fm.fits _ _ && Lk6.Flat.fitsAll _ (flatRV rs)) = true
            rw [ih, Bool.and_true, Lk6.Flat.Fm.fits_iff]
            refine ⟨?_, ?_, fun hz y hy => ?_⟩
            · show (((First.Tape.elemsOf r.vals).getD []).map readE).length = sent.length
              rw [h3]; simp
            · show (r.drawn.elems.map fun x => readE (E.ofTriple x)).length =
                (r.drawn.elems.map E.ofTriple).length
              simp
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
              have hnz : e.drawNZ ≠ 0 := by
                have hz' : (e.drawNZ != 0) = true := hz
                simpa using hz'
              have he : e.drawNZ = (r.drawn.elems.map E.ofTriple).length := hx.resolve_left hnz
              rw [List.length_map, c1] at he
              rw [he, Nat.sub_self, List.drop_zero, List.all_eq_true] at c7
              have h7 := c7 a ha
              have hok : okE (E.ofTriple a) = true := by
                have := List.all_eq_true.1 hw'.2 a ha
                simp only [Bool.and_eq_true, decide_eq_true_eq] at this
                simp only [okE, okF, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨⟨this.1.1, this.1.2⟩, this.2⟩
              intro h0
              rw [(isZeroE_iff _ hok).2 h0] at h7
              cases h7
          · cases h1

/-- **What is heard, of words below the prime, fits the typed lookup's formats.** -/
theorem fits_hearE (A : Dat GE) (st : A.St) (P : Pl A) (f : Face) (es : List Fmt.Entry) (F : Fork)
    (rs : List Fmt.RoundView) (g : HeardG) (G : Fork) (hf : FaceIs A st f) (hadm : A.toPub.Adm Cb.Gl.p)
    (hF : Sized F) (hw : viewWordsBelowPrime ⟨rs, []⟩ = true) (h : hearE f es F rs = some (g, G)) :
    Lk6.Flat.fitsAll (A.runD P).fm (flatRV rs) = true := by
  obtain ⟨t, ht, hs⟩ := shape_hearE A st f es F rs g G hf hadm hF h
  rw [typedShape A st P f hf hadm, ← hs]
  exact tape_fits rs es t ht hw (by rw [hs]; exact shape_simple f)

/-! ## The equation -/

/-- **Law.out of the kind's own hearing.** -/
theorem out_hearE (A : Dat GE) (sl : Slot → A.J) (st : A.St) (f : Face) (first : ℕ)
    (o k home : ℕ → Slot) (es : List Fmt.Entry) (F : Fork) (rs : List Fmt.RoundView) (g : HeardG)
    (G : Fork) (hf : FaceIs A st f) (hadm : A.toPub.Adm Cb.Gl.p) (hh : HomeIs f first o k home)
    (hw : viewWordsBelowPrime ⟨rs, []⟩ = true) (hn : F.next = first) (hF : Sized F)
    (h : hearE f es F rs = some (g, G)) :
    g.theta = zeroE ∧ (flatRV rs).head? = some ([], [readE g.alpha]) ∧
    Later F G ∧ Sized G ∧ G.next = first + f.slots ∧
    ∀ (H H' : Fork) (pl : List PlaneClaim) (u : Tape), Later G H →
      planesG f g H [] = some (pl, H', u) →
      Later H H' ∧ (∀ a ∈ formsOf g pl, a.ents.isEmpty = true) ∧
      ∀ K, Later H' K →
        A.lamRun (placesAt A sl o k) st (flatRV rs) = outOf A sl st K home g pl := by
  obtain ⟨hok, t, ht, hm⟩ := hearE_inv h
  have hal : Al home o k (fromKeys f) F.next 0 0 := by rw [hn]; exact al_of_homeIs hh
  have hc := fun W => hear_course W hf hadm hok hm hF hal
  rw [tape_flat rs es t ht] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -⟩ := hc ⟨fun _ => 0⟩
  refine ⟨c2, c3, c4, c5, by rw [c6, hn], fun H H' pl u hGH hpl => ?_⟩
  obtain ⟨d1, d2, -⟩ := (hc ⟨fun _ => 0⟩).2.2.2.2.2.2.2 H H' pl u hGH hpl
  refine ⟨d1, fun a ha => ?_, fun K hK => ?_⟩
  · have := d2 a ha
    unfold NoEnt at this
    simpa using this
  · have hfit := fits_hearE A st (placesAt A sl o k) f es F rs g G hf hadm hF hw h
    have hlen := Lk6.Mid.fitsAll_len _ _ hfit
    have hco := course_of (A := A) (st := st) (ms := o) (ix := k) sl 0 0 hadm (flatRV rs)
    rw [plAt_zero, ← hlen, List.take_length] at hco
    rw [(hco hfit).1]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      show rdCl A sl _ (A.v i) _ = rdCl A sl (readE g.alpha) (A.v i) _
      rw [c1]
      exact (key_typed A sl _ _ fun W =>
        (((hc W).2.2.2.2.2.2.2 H H' pl u hGH hpl).2.2 K hK).1 i i.isLt).symm
    · exact (rows_typed A sl fun W =>
        (((hc W).2.2.2.2.2.2.2 H H' pl u hGH hpl).2.2 K hK).2).symm

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.hear_course
#print axioms VerifiableInference.Desc.K3.KeyLaw.typedShape
#print axioms VerifiableInference.Desc.K3.KeyLaw.shape_hearE
#print axioms VerifiableInference.Desc.K3.KeyLaw.fits_hearE
#print axioms VerifiableInference.Desc.K3.KeyLaw.out_hearE
