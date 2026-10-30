-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HFDoorB.lean: THE PREMISES OF `hF_of_door` (HFOfDoor.lean) THAT SPEAK OF
PUBLIC NUMBERS AND OF THE VERIFIER's STATE ALONE, AS TESTS WITH CODE, ONE A CLAUSE, EACH WITH ITS
LAW: so that they can be evaluated at a walk's state, each apart. Definitions and theorems. It
changes no other file.

  `laysB L Gr`: the layout has the group's members and flags (hLm · hLk). `agreesB lo kb L`:
    AgreesWith (hA). `sizesB rows s`: two masks · h + g challenges · the layout's two exponents
    (hm · hγ · hk · hh). `ordB lo kb kl`: the sentence on lo, kb, kl (hord).
  `planPubB G t Lp o seat a`: `PlanAt`'s public part at one message. `planAt_of_B`: with «the
    reading at the listed tree's key is Strs.col at the seat's tree» it gives PlanAt.
  `freshPubB t Lp fresh skip aF`: the fresh mask's entry in the plan's list (hfo · hfL · hfs · hfa ·
    hfskip).
  `frontPubB p t lo no rows h`: the text makes a front of t, and hFr's four facts hold of it.
  `laysB_says`, `agreesB_says`, `sizesB_says`, `ordB_says`, `freshPubB_says`, `frontPubB_says`: what
    a yes gives, in `hF_of_door`'s premises' words.
Limits. Tests and their laws. No test has been evaluated here. Nothing on the strings. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.HFOfDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.First.Close (posOf AgreesWith)
open _root_.Tw.K2 (switchNotices)

def laysB (L : GroupLayout) (Gr : Group) : Bool :=
  decide (L.members = Gr.members) && decide (L.kept = Gr.kept)

theorem laysB_says {L : GroupLayout} {Gr : Group} (h : laysB L Gr = true) :
    L.members = Gr.members ∧ L.kept = Gr.kept := by
  unfold laysB at h
  simpa using h

def agreesB (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (L : GroupLayout) : Bool :=
  decide (AgreesWith lo kb L)

theorem agreesB_says {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool} {L : GroupLayout}
    (h : agreesB lo kb L = true) : AgreesWith lo kb L := of_decide_eq_true h

def sizesB (rows : SingleRows) (s : Sg) : Bool :=
  decide (rows.masks = 2) && decide (rows.gamma.length = s.h + s.g) &&
    decide (rows.layout.k = s.h + s.g) && decide (rows.layout.h = s.h)

theorem sizesB_says {rows : SingleRows} {s : Sg} (h : sizesB rows s = true) :
    rows.masks = 2 ∧ rows.gamma.length = s.h + s.g ∧ rows.layout.k = s.h + s.g ∧
      rows.layout.h = s.h := by
  unfold sizesB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

def ordB (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (kl : List ℕ) : Bool :=
  (List.finRange lo.length).all fun i =>
    !(decide ((lo.get i).1.mainRows ≠ 0) && kb i) ||
      decide ((keptNosOf lo kb)[kl.idxOf i.val]? = some (posOf lo i))

theorem ordB_says {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool} {kl : List ℕ}
    (h : ordB lo kb kl = true) (i : Fin lo.length) (hi : memMain lo i) (hk : kb i = true) :
    (keptNosOf lo kb)[kl.idxOf i.val]? = some (posOf lo i) := by
  unfold ordB at h
  have h1 := List.all_eq_true.1 h i (List.mem_finRange i)
  have hi' : (lo.get i).1.mainRows ≠ 0 := hi
  rw [decide_eq_true hi', hk] at h1
  simpa using h1

/-- `PlanAt`'s public part at one message. -/
def planPubB {Xi : Type} (G : FileDescription Xi) (t : First.S)
    (Lp : VerifiableInference.Desc.K12.Door.Laid) (o : ℕ) (seat : ℕ × ℕ) (a : ℕ) : Bool :=
  decide (o < t.book.place.size) &&
    match Lp.places[o]? with
    | some q => decide (q.2 = seat.2) &&
      match Lp.shapes[q.1]? with
      | some sh0 => decide (sh0.logN = a) &&
        match G.oracleAt seat.1 with
        | some d =>
          decide ((sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = d.mainSkip seat.2) &&
            decide (sh0.mainWidth + (sh0.maskSymbols.extract 0 seat.2).foldl (· + ·) 0 =
              d.maskSkip seat.2)
        | none => true
      | none => false
    | none => false

theorem planAt_of_B {Xi : Type} {G : FileDescription Xi} {t : First.S}
    {Lp : VerifiableInference.Desc.K12.Door.Laid} {o : ℕ} {seat : ℕ × ℕ} {a : ℕ}
    (h : planPubB G t Lp o seat a = true) (orc : ℕ → ℕ → List UInt64) (Y : Strs)
    (hr : ∀ tp, Lp.places[o]? = some (tp, seat.2) → ∀ x, x < 2 ^ a → orc tp x = Y.col seat.1 x) :
    PlanAt G t Lp orc Y o seat a := by
  unfold planPubB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  cases hq : Lp.places[o]? with
  | none => simp [hq] at h2
  | some q =>
    obtain ⟨tp, tn⟩ := q
    simp only [hq, Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨rfl, h3⟩ := h2
    cases hs : Lp.shapes[tp]? with
    | none => simp [hs] at h3
    | some sh0 =>
      simp only [hs, Bool.and_eq_true, decide_eq_true_eq] at h3
      obtain ⟨h4, h5⟩ := h3
      refine ⟨h1, tp, sh0, hq, hs, h4, hr tp hq, fun d hd => ?_⟩
      simp only [hd, Bool.and_eq_true, decide_eq_true_eq] at h5
      exact h5

/-- The fresh mask's entry in the plan's list. -/
def freshPubB (t : First.S) (Lp : VerifiableInference.Desc.K12.Door.Laid) (fresh skip aF : ℕ) :
    Bool :=
  decide (fresh < t.book.place.size) &&
    match Lp.places[fresh]? with
    | some q =>
      match Lp.shapes[q.1]? with
      | some sh0 => decide (sh0.logN = aF) &&
        decide (sh0.mainWidth + (sh0.maskSymbols.extract 0 q.2).foldl (· + ·) 0 = skip)
      | none => false
    | none => false

theorem freshPubB_says {t : First.S} {Lp : VerifiableInference.Desc.K12.Door.Laid}
    {fresh skip aF : ℕ} (h : freshPubB t Lp fresh skip aF = true) :
    fresh < t.book.place.size ∧ ∃ tpF tnF shF0, Lp.places[fresh]? = some (tpF, tnF) ∧
      Lp.shapes[tpF]? = some shF0 ∧ shF0.logN = aF ∧
      shF0.mainWidth + (shF0.maskSymbols.extract 0 tnF).foldl (· + ·) 0 = skip := by
  unfold freshPubB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  cases hq : Lp.places[fresh]? with
  | none => simp [hq] at h2
  | some q =>
    obtain ⟨tp, tn⟩ := q
    simp only [hq] at h2
    cases hs : Lp.shapes[tp]? with
    | none => simp [hs] at h2
    | some sh0 =>
      simp only [hs, Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨h1, tp, tn, sh0, rfl, hs, h2.1, h2.2⟩

/-- The text makes a front of t, and hFr's four facts hold of it. -/
def frontPubB (p : First.K2.P2) (t : First.S) (lo : List (OracleShape × ℕ))
    (no : Fin lo.length → ℕ) (rows : SingleRows) (h : ℕ) : Bool :=
  match First.K2.frontAt p t with
  | some fx =>
    (First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
        (switchNotices fx.T fx.others)).isSome &&
      ((List.finRange lo.length).all fun i => !decide ((lo.get i).1.mainRows ≠ 0) ||
        decide (((First.K2.skelOf fx).oracles[no i]?).map (·.shape) = some (lo.get i).1)) &&
      decide (((First.K2.skelOf fx).oracles[rows.fresh]?).map (·.shape.maskRows) = some (2 ^ h)) &&
      decide (keptCount rows.layout
        (fun w => ((First.K2.skelOf fx).oracles.getD (rows.layout.members.getD w 0)
          default).shape.mainRows) (List.range rows.layout.members.size) = rows.keptRows)
  | none => false

theorem frontPubB_says {p : First.K2.P2} {t : First.S} {lo : List (OracleShape × ℕ)}
    {no : Fin lo.length → ℕ} {rows : SingleRows} {h : ℕ} (hb : frontPubB p t lo no rows h = true)
    {fx : _root_.Tw.K2.Front} (hfx : First.K2.frontAt p t = some fx) :
    (∃ B, First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
        (switchNotices fx.T fx.others) = some B) ∧
      (∀ b : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx).oracles[no b.1]? = some xo ∧
        xo.shape = (lo.get b.1).1) ∧
      (∃ xoF, (First.K2.skelOf fx).oracles[rows.fresh]? = some xoF ∧
        xoF.shape.maskRows = 2 ^ h) ∧
      keptCount rows.layout
        (fun w => ((First.K2.skelOf fx).oracles.getD (rows.layout.members.getD w 0)
          default).shape.mainRows) (List.range rows.layout.members.size) = rows.keptRows := by
  unfold frontPubB at hb
  simp only [hfx, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
  refine ⟨Option.isSome_iff_exists.1 h1, fun b => ?_, ?_, h4⟩
  · have h5 := List.all_eq_true.1 h2 b.1 (List.mem_finRange b.1)
    have hb' : (lo.get b.1).1.mainRows ≠ 0 := b.2
    simp only [hb', ne_eq, not_false_eq_true, decide_true, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] at h5
    obtain ⟨xo, x1, x2⟩ := Option.map_eq_some_iff.1 h5
    exact ⟨xo, x1, x2⟩
  · obtain ⟨xo, x1, x2⟩ := Option.map_eq_some_iff.1 h3
    exact ⟨xo, x1, x2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.laysB_says
#print axioms VerifiableInference.Desc.LinkJoin.agreesB_says
#print axioms VerifiableInference.Desc.LinkJoin.sizesB_says
#print axioms VerifiableInference.Desc.LinkJoin.ordB_says
#print axioms VerifiableInference.Desc.LinkJoin.planAt_of_B
#print axioms VerifiableInference.Desc.LinkJoin.freshPubB_says
#print axioms VerifiableInference.Desc.LinkJoin.frontPubB_says
