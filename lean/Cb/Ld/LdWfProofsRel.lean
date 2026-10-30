-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfProofsRel.lean: lemmas that the relations at the joints of the preamble of
weights-formedness (Cb/Ld/LdWf.lean) fit: exact relations forwards, relaxed relations backwards.
Lemmas on predicates; no protocol. Beside each lemma's own premises, only the laws of the data
(`LdWfP.Laws`) are assumed: the binder `hL`, where they are used.

Main names:
  `dcd_of_enc`, `via_enc`: on the honest side the statement decodes the index to the prover's own
    message.
  `keyAt_eq`, `inR_iff`: the relaxed lookup claim of forest l, in the lookup sub-protocol's notation
    (Cb/Ld/LdLkp.lean), says what the joint after l lookups says.
  `in_rel`, `in_relR`: the joint after l lookups against the input joint of the lookup on forest l.
  `out_rel`, `out_relR`: the output joint of that lookup, filed, against the joint after l + 1
    lookups.
  `wf_rel`, `wf_relR`: weights-formedness against the joint before the sending; `send_rel`,
    `send_relR`: that joint, with the vectors in the messages, against the joint after 0 lookups.
  `lhs_eq`, `holds_iff`: a masked claim on the keys is a tensor row with masks; `done_iff`: all
    claims and rows filed hold if and only if the rows hold and the input claims of the batching
    hold.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWf

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

theorem dcd_of_enc (hL : P.Laws) {rec : C.Rec} {y : C.E0.Str} {p : C.PIdx} (h : C.Enc rec y p) :
    C.dcd y rec = some p.1.1 := by
  obtain ⟨h1, _, h3⟩ := h
  have e := hL.dcd_enc p.1.1 p.1.2 rec.1
  rw [← h3, ← h1] at e
  exact e

theorem via_enc (hL : P.Laws) {rec : C.Rec} {y : C.E0.Str} {p : C.PIdx}
    (h : C.Enc rec y p) (Q : C.Msg → Prop) : P.via rec y Q ↔ Q p.1.1 := by
  constructor
  · rintro ⟨U, hU, hQ⟩
    rw [dcd_of_enc hL h] at hU
    rw [Option.some.inj hU]
    exact hQ
  · exact fun hQ => ⟨_, dcd_of_enc hL h, hQ⟩

theorem keyAt_eq (l : ℕ) {st : P.WSt} {ym : P.M} {U : C.Msg} (h : C.dcd ym.1 st.1 = some U) :
    P.keyAt l st ym = P.key l U := by
  funext b
  show (match C.dcd ym.1 st.1 with
    | some U => P.key l U b
    | none => 0) = _
  rw [h]

/-- For l ≤ P.n (`hl`), the lookup claim, relaxed, says what the joint says. -/
theorem inR_iff {l : ℕ} (hl : l ≤ P.n) (st : P.WSt) (ym : P.M) :
    (P.lk l).inR st ym ↔
    P.via st.1 ym.1 fun U => P.Done l st U ym.2 ∧ ∀ f, l ≤ f → f ≤ P.n → P.InT f U := by
  constructor
  · rintro ⟨h1, U, hU, hD, hT⟩
    refine ⟨U, hU, hD, fun f hf hn => ?_⟩
    rcases Nat.eq_or_lt_of_le hf with rfl | hlt
    · have h1 : Lkp.InTable (P.v l) (P.d l) (P.keyAt l st ym) (P.tab l) := h1
      rw [keyAt_eq l hU] at h1
      exact h1
    · exact hT f hlt hn
  · rintro ⟨U, hU, hD, hT⟩
    refine ⟨?_, U, hU, hD, fun f hf hn => hT f (Nat.le_of_lt hf) hn⟩
    show Lkp.InTable (P.v l) (P.d l) (P.keyAt l st ym) (P.tab l)
    rw [keyAt_eq l hU]
    exact hT l (Nat.le_refl l) hl

/-- Under `hL`, for l ≤ P.n (`hl`), the joint after l lookups gives the exact input of the lookup on
forest l. -/
theorem in_rel (hL : P.Laws) {l : ℕ} (hl : l ≤ P.n) (st : P.WSt) (y : C.E0.Str)
    (w : P.S.Msg × P.Wp) (h : (P.A l).rel st y w) :
    (P.lk l).inP (P.multAt l) st (y, w.1) ∧ P.honAt l st (y, w.1) w.2 := by
  obtain ⟨hE, hD, hT⟩ := h
  refine ⟨⟨(inR_iff hl st (y, w.1)).2 ((via_enc hL hE _).2 ⟨hD, fun f hf hn => (hT f hf hn).1⟩),
      (via_enc hL hE _).2 (hT l (Nat.le_refl l) hl).2⟩,
    hE,
    (via_enc hL hE _).2 fun f hf hn => (hT f (Nat.le_of_lt hf) hn).2⟩

theorem in_relR {l : ℕ} (hl : l ≤ P.n) (a : P.WSt × C.E0.Str)
    (w : P.S.Msg × P.Wp) (h : (P.lk l).inR a.1 (a.2, w.1)) : (P.A l).relR a w :=
  (inR_iff hl a.1 (a.2, w.1)).1 h

/-- the state after the filing -/
def fileSt (l : ℕ) (x : TX P.WSt E P.N) : P.WSt :=
  (x.1.1, Function.update x.1.2.1 l x.2.1,
    Function.update x.1.2.2 l fun b => x.2.2.getD b ⟨fun _ => 0, 0⟩)

theorem file_some (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) (h : P.FileOK l x) :
    P.file l x = some (fileSt l x.1, x.2) := if_pos h

theorem file_eq (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) (x' : P.X) (e : P.file l x = some x') :
    P.FileOK l x ∧ x' = (fileSt l x.1, x.2) := by
  by_cases h : P.FileOK l x
  · rw [file_some l x h] at e
    exact ⟨h, (Option.some.inj e).symm⟩
  · unfold file at e
    rw [if_neg h] at e
    exact absurd e (by simp)

theorem fileD_eq (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) (h : P.FileOK l x) :
    P.fileD l x = (fileSt l x.1, x.2) := by
  unfold fileD
  rw [file_some l x h]
  rfl

omit [Fintype E] in
/-- coefficients that are 0 outside G are not changed by the cut -/
theorem wfCut_of_supp {J : Type} (G : J → Prop) (c : J → E) (h : ∀ j, ¬ G j → c j = 0) :
    wfCut G c = c := by
  funext j
  unfold wfCut
  by_cases hj : G j
  · rw [if_pos hj]
  · rw [if_neg hj, h j hj]

omit [Fintype E] in
theorem wfCut_out {J : Type} (G : J → Prop) (c : J → E) {j : J} (h : ¬ G j) : wfCut G c j = 0 :=
  if_neg h

/-- The rows of a list of length k (`h`) hold if and only if the rows of its vector hold. -/
theorem rows_vec (rs : List (Row E P.N)) (k : ℕ) (h : rs.length = k) (z : Row E P.N) (μ : P.N → E) :
    RowsHold rs μ ↔ ∀ b : Fin k, (rs.getD b z).Holds μ := by
  subst h
  unfold RowsHold
  constructor
  · intro hr b
    rw [List.getD_eq_getElem _ _ b.2]
    exact hr _ (List.getElem_mem _)
  · intro hr r hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have := hr ⟨i, hi⟩
    rwa [List.getD_eq_getElem _ _ hi] at this

/-- what is done after the filing -/
theorem done_file (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) (h : P.FileOK l x)
    (U : C.Msg) (m : P.S.Msg) :
    P.Done (l + 1) (fileSt l x.1) U m ↔
    x.1.2.1.Holds (P.v l) (P.key l U) (P.ent m) ∧
    RowsHold x.1.2.2 (P.ent m) ∧
    P.Done l x.1.1 U m := by
  have e1 : P.clAt l (fileSt l x.1) = x.1.2.1 := by
    unfold clAt
    have e : (fileSt l x.1).2.1 l = x.1.2.1 := Function.update_self _ _ _
    rw [e, wfCut_of_supp _ _ h.2.1]
  have e2 : ∀ b, P.rowAt l b (fileSt l x.1) = x.1.2.2.getD b ⟨fun _ => 0, 0⟩ := fun b => by
    unfold rowAt
    have e : (fileSt l x.1).2.2 l = fun b : Fin (P.nR l) => x.1.2.2.getD b ⟨fun _ => 0, 0⟩ :=
      Function.update_self _ _ _
    rw [e, wfCut_of_supp _ _ (h.2.2 b)]
  have n1 : ∀ f, f ≠ l → P.clAt f (fileSt l x.1) = P.clAt f x.1.1 := fun f hf => by
    unfold clAt
    have e : (fileSt l x.1).2.1 f = x.1.1.2.1 f := Function.update_of_ne hf _ _
    rw [e]
  have n2 : ∀ f, f ≠ l → ∀ b, P.rowAt f b (fileSt l x.1) = P.rowAt f b x.1.1 := fun f hf b => by
    unfold rowAt
    have e : (fileSt l x.1).2.2 f = x.1.1.2.2 f := Function.update_of_ne hf _ _
    rw [e]
  rw [rows_vec x.1.2.2 (P.nR l) h.1 ⟨fun _ => 0, 0⟩]
  constructor
  · intro hD
    have hl := hD l (Nat.lt_succ_self l)
    rw [e1] at hl
    refine ⟨hl.1, fun b => by rw [← e2 b]; exact hl.2 b, fun f hf => ?_⟩
    have hf' := hD f (Nat.lt_succ_of_lt hf)
    rw [n1 f (Nat.ne_of_lt hf)] at hf'
    exact ⟨hf'.1, fun b => by rw [← n2 f (Nat.ne_of_lt hf) b]; exact hf'.2 b⟩
  · rintro ⟨h1, h2, h3⟩ f hf
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hf) with rfl | hlt
    · rw [e1]
      exact ⟨h1, fun b => by rw [e2 b]; exact h2 b⟩
    · rw [n1 f (Nat.ne_of_lt hlt)]
      exact ⟨(h3 f hlt).1, fun b => by rw [n2 f (Nat.ne_of_lt hlt) b]; exact (h3 f hlt).2 b⟩

/-- Under the hypotheses below, the output of the lookup on forest l, filed, gives the joint after
`l + 1` lookups. -/
theorem out_rel (hL : P.Laws) (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp)
    (h : P.FileOK l x) (y : C.E0.Str) (w : P.S.Msg × P.Wp)
    (h1 : (P.lk l).out id P.entM x.1 (y, w.1)) (h2 : P.honAt l x.1.1 (y, w.1) w.2) :
    (P.A (l + 1)).rel (fileSt l x.1) y w := by
  obtain ⟨hE, hM⟩ := h2
  obtain ⟨hc, hr, hm⟩ := h1
  have hm' := (via_enc hL hE _).1 hm
  have hM' := (via_enc hL hE _).1 hM
  have hc : x.1.2.1.Holds (P.v l) (P.keyAt l x.1.1 (y, w.1)) (P.ent w.1) := hc
  rw [keyAt_eq l (st := x.1.1) (ym := (y, w.1)) (dcd_of_enc hL hE)] at hc
  exact ⟨hE, (done_file l x h _ _).2 ⟨hc, hr, hm'.1⟩, fun f hf hn => ⟨hm'.2 f hf hn, hM' f hf hn⟩⟩

theorem out_relR (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) (h : P.FileOK l x) (y : C.E0.Str)
    (w : P.S.Msg × P.Wp) (hw : (P.A (l + 1)).relR (fileSt l x.1, y) w) :
    (P.lk l).out id P.entM x.1 (y, w.1) := by
  obtain ⟨U, hU, hD, hT⟩ := hw
  have hU : C.dcd y x.1.1.1 = some U := hU
  obtain ⟨hc, hr, hd⟩ := (done_file l x h U w.1).1 hD
  refine ⟨?_, hr, U, hU, hd, fun f hf hn => hT f hf hn⟩
  show x.1.2.1.Holds (P.v l) (P.keyAt l x.1.1 (y, w.1)) (P.ent w.1)
  rw [keyAt_eq l (st := x.1.1) (ym := (y, w.1)) hU]
  exact hc

/-! ### The start -/

theorem wf_rel (hL : P.Laws) (rec : C.Rec) (y : C.E0.Str) (p : C.PIdx) (h : C.Rwf rec y p) :
    P.A0.rel (P.st0 rec) y (P.bodyOf p.1.1, (p, ())) := by
  obtain ⟨hE, i, η, hi⟩ := h
  have hT : ∀ f, f ≤ P.n → P.InT f p.1.1 := (hL.describes p.1.1).1 (by rw [hi, hL.held_hold]; rfl)
  exact ⟨hE, fun f hf => ⟨hT f hf, hL.multOf _ f hf (hT f hf)⟩⟩

theorem wf_relR (hL : P.Laws) (rec : C.Rec) (y : C.E0.Str) (w : P.Body × P.Wp)
    (hf : C.free (rec, y)) (h : P.A0.relR (P.st0 rec, y) w) : C.RwfR (rec, y) () := by
  obtain ⟨U, hU, hT⟩ := h
  have hU : C.dcd y rec = some U := hU
  show (C.D y rec).isSome
  unfold ConfigurationWithOutOfDomainSample.D
  rw [if_neg hf, hU]
  exact (hL.describes U).2 hT

theorem send_rel (st : P.WSt) (y : C.E0.Str)
    (w : P.S.Msg × P.Wp) (h : P.A0.rel st y (P.back w.1 w.2)) : (P.A 0).rel st y w :=
  ⟨h.1, fun f hf => absurd hf (Nat.not_lt_zero f), fun f _ hn => h.2 f hn⟩

theorem send_relR (a : P.WSt × C.E0.Str) (w : P.S.Msg × P.Wp) (h : (P.A 0).relR a w) :
    P.A0.relR a (P.back w.1 w.2) := by
  obtain ⟨U, hU, _, hT⟩ := h
  exact ⟨U, hU, fun f hn => hT f (Nat.zero_le f) hn⟩

/-! ### The batching -/

/-- the left side of a tensor row, written out -/
theorem lhs_eq (st : P.WSt) (q : Fin (P.n + 1)) (U : C.Msg) (m : P.S.Msg) :
    P.bt.lhs st q (P.msg (U, m)) =
      Alg.mle (fun c => ∑ r, P.gOf q (st.2.1 q).pt r * P.mat U (r, c)) (P.cOf q (st.2.1 q).pt) +
        ∑ i, (P.clAt q st).mf i * P.ent m i := by
  show Alg.mle (fun c => ∑ r, P.gOf q (st.2.1 q).pt r * P.mat U (r, c)) (P.cOf q (st.2.1 q).pt) +
      ∑ j : (P.Rw × (Fin P.k → Bool)) ⊕ P.N,
        Sum.elim (fun _ => (0 : E)) (P.clAt q st).mf j * Sum.elim (P.mat U) (P.ent m) j = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add]

/-- Under `hL`, a masked claim on the keys of a forest is a tensor row with masks. -/
theorem holds_iff (hL : P.Laws) (st : P.WSt) (q : Fin (P.n + 1)) (U : C.Msg) (m : P.S.Msg) :
    (P.clAt q st).Holds (P.v q) (P.key q U) (P.ent m) ↔
    P.bt.lhs st q (P.msg (U, m)) = (st.2.1 q).tg - P.off q (st.2.1 q).pt := by
  rw [lhs_eq]
  show Blocks.ext (P.v q) (P.key q U) (st.2.1 q).pt + ∑ i, (P.clAt q st).mf i * P.ent m i =
      (st.2.1 q).tg ↔
    _
  rw [hL.keyLin q (Nat.le_of_lt_succ q.2) U]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- Under `hL`, all claims and rows filed hold if and only if the rows hold and the input claims of
the batching hold. -/
theorem done_iff (hL : P.Laws) (x : P.X) (U : C.Msg) (m : P.S.Msg) :
    P.Done (P.n + 1) x.1 U m ↔ P.RowsV x.1 m ∧ P.bt.InHolds (P.toBatt x).1 (P.msg (U, m)) := by
  constructor
  · intro h
    exact ⟨fun f hf => (h f (Nat.lt_succ_of_le hf)).2,
      fun q : Fin (P.n + 1) => (holds_iff hL x.1 q U m).1 (h q q.2).1⟩
  · rintro ⟨h2, h1⟩ f hf
    exact ⟨(holds_iff hL x.1 ⟨f, hf⟩ U m).2 (h1 ⟨f, hf⟩), h2 f (Nat.le_of_lt_succ hf)⟩

end LdWfP
end Cb
