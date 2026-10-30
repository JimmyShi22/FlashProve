-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/JoinKeyD.lean: THE TIES AND
THE LAW OF A LOOKUP'S LINK, WHOSE ROWS MEET: what rides through the link of lookup number i, written
out; and the ties of the three blocks without a round that stand between the layer of lookup i and
the caller of lookup i + 1 ("behind the batching", "cleared", the next link's "laid"). The six seats
laid in a row as one term: LinkSeats.lean.

What rides (items i): every EARLIER lookup's rows say their claims of the witness's words and the
pending rows of its claims on the keys hold of the witness's matrix; every LATER lookup's keys, as
the matrix holds them, are numbers of rows of its range table; and whatever else rides (Oth: a
letter, blind to the lists of rows and claims: the messages' own sample rows, say). The riding joint
R i says: the messages are what a decoder gives at the statement, and items i.

What is handed to the chain at its start (p₀ : P; at a key file: the public part of the instance)
stands beside the riding part in the typed statement (TK P, RideKeyD.lean). The decoder, its
condition and Oth may read it. It lies in no block's record, so no block can write it. Every row
here is a row at one p₀; LinkSeats.lean lifts the family.

Main names:
  stm x: the statement made of the riding part: its codes and messages. stm_same: it has the tables
    of the record's own statement.
  Pend: the pending rows of a lookup's claims on the keys hold.
  items i, R i: what rides; the riding joint.
  rowJ i: the border between two links: the decoder's messages; all earlier lookups' rows and
    pending rows; the keys of lookup i and of all later ones lie in their tables; Oth.
  andQ, tie_and, law_and: a promise on the record rides beside a row.
  same_tie ("behind the batching"), cleared_tie, laid_tie: THE THREE TIES.
  Promise: Hands and Fits, lookup by lookup, as a promise that the caller leads on. It may speak of
    the lookups' rows and claims on the keys as they are laid (lays: it is handed the layer's two
    equations and that what was heard has a key for each part).
  callerJ_tie, k3Q_law, layerJ_tie: the caller's tie, the kind's block's law (for every typed
    lookup) and the layer's tie, with the promise beside. pins_R, low_R: the riding joint has Pins
    by its make, and ReadsLow where the decoder reads below (LowDec; lowDec_mono: a higher bound
    serves too).
  lay_same, after_same, clear_eq: what the link's three own steps do.

Limits. The decoder dec, its condition cond and Oth are letters, blind to the lists of rows and
claims (Blind: they read the codes, the bare messages and p₀). Hands and Fits of the next lookup
come in as a promise Q on the record in front, which the ties hand on where it is blind to the three
fields that the link's blocks overwrite (the ledger of hidden values, what was heard, the table of
homes) and outlasts the layer's two writings.
A DEBT IN TWO HALVES: Promise alone is met by the promise that never holds, and then every row here
is off everywhere and the ties say nothing. Owed beside it: that Prom 0 HOLDS at the record that
stands behind the sending of the second message, in front of the first link. The first half is paid
at a promise written out in PromKeyD.lean; the second half step by step from the chain's start in
FrontSteps.lean, at the key file's own description in FrontAtFK.lean; no seat's law spends it yet.

-/
import Johnson.RunOne.Law.LinkKeyD
import Johnson.RunOne.Law.RideKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.JoinKeyD
open Iop OnBytes OnBytes.Slice OnBytes.Params
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Block roundlessBlock afterIn need)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound (JointRow QuietTie)
open VerifiableInference.Desc.Key (FirstState Claim LookupRecord)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkKeyD
open Johnson.RunOne.Law.RideKeyD

/-- The statement made of the riding part: its codes and its messages. -/
def stm {P : Type} (x : TK P) : Statement := { codes := x.1, oracles := x.2.1 }

/-- It has the tables of the record's own statement. -/
theorem stm_same {P : Type} (p₀ : P) (i : ℕ) (s : FirstState) :
    SameTables s.d.st (stm (stK p₀ i s)) := by
  refine ⟨by simp [stm, stK], fun o part => ?_⟩
  unfold Means.tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  simp only [stm, stK, Array.getElem?_map]
  cases s.d.st.oracles[o]? <;> simp [bareO]

variable {Fr : VerifiableInference.Desc.Sound.Frame} {P : Type} (p₀ : P) (one : OneTime) (id : ℕ) (m
    : Wf.Matrix)
  (L : ℕ → WfLookup) (oL kL : ℕ → List ℕ) (idxN : ℕ) {M Wp : Type} (wd : M → Means.Words GE)
  (mx : M → ℕ → ℕ → GE) (dec : TK P × Fr.E.Str → Option M) (cond : TK P × Fr.E.Str → Prop) (n : ℕ)
  (Oth : TK P → M × Wp → Prop)

/-- The pending rows of a lookup's claims on the keys hold. -/
def Pend (l : WfLookup) (keys : List Lkp.Keys) (w : Means.Words GE) (X : ℕ → ℕ → GE) : Prop :=
  ∀ (j : ℕ) (p : WfPart), l.parts[j]? = some p →
    (Leaves.readTRow (Wf.pendingRow m l p (keys.getD j default)
      (Wf.eqPlaces m (keys.getD j default).point))).Holds ⟨fun s => w s.oracle .mask s.index⟩ X
        m.rows m.kCol

/-- The earlier lookups: their rows say their claims; their pending rows hold. -/
def Early (i : ℕ) (x : TK P) (u : M) : Prop :=
  ∀ k < i, ∃ rows keys, x.2.2.1[k]? = some rows ∧ x.2.2.2.1[k]? = some keys ∧
    Means.AllSay Reading.gl (stm x) rows (wd u) ∧ Pend m (L k) keys (wd u) (cutM m (mx u))

/-- The lookups from number i on, below n: their keys lie in their tables. -/
def Late (i : ℕ) (u : M) : Prop := ∀ k, i ≤ k → k < n → KeysIn id m (L k) (cutM m (mx u))

/-- **What rides through the link of lookup number i.** -/
def items (i : ℕ) (x : TK P) (w : M × Wp) : Prop :=
  Early m L wd mx i x w.1 ∧ Late id m L mx n (i + 1) w.1 ∧ Oth x w

/-- **The riding joint.** -/
def R (i : ℕ) : IOR.Rels Unit (TK P) Fr.E (M × Wp) :=
  ⟨fun x y w => dec (x, y) = some w.1 ∧ items id m L wd mx n Oth i x w,
    fun a w => dec a = some w.1 ∧ items id m L wd mx n Oth i a.1 w, cond, fun _ => ()⟩

/-- **The border between two links.** Q: a promise on the record. -/
def rowJ (Q : FirstState → Prop) (i : ℕ) : JointRow FirstState Fr :=
  JointRow.ofBorder (W := M × Wp)
    (fun a => cond (stK p₀ i a.1, a.2) ∧ a.1.base.rows.length = i ∧ a.1.base.keys.length = i ∧ Q
        a.1)
    fun a w => dec (stK p₀ i a.1, a.2) = some w.1 ∧ Early m L wd mx i (stK p₀ i a.1) w.1 ∧
      Late id m L mx n i w.1 ∧ Oth (stK p₀ i a.1) w

/-- The decoder and its condition are blind to the lists of rows and claims. -/
def Blind : Prop :=
  ∀ (x x' : TK P) (y : Fr.E.Str), x.1 = x'.1 → x.2.1 = x'.2.1 → x.2.2.2.2 = x'.2.2.2.2 →
    dec (x, y) = dec (x', y) ∧ (cond (x, y) ↔ cond (x', y)) ∧ ∀ w, Oth x w ↔ Oth x' w

variable {p₀ one id m L oL kL idxN wd mx dec cond n Oth}

/-- The earlier lookups' part reads the first i lists alone. -/
theorem early_take {i : ℕ} {x x' : TK P} {u : M} (h1 : x.1 = x'.1) (h2 : x.2.1 = x'.2.1)
    (h3 : ∀ k < i, x.2.2.1[k]? = x'.2.2.1[k]?) (h4 : ∀ k < i, x.2.2.2.1[k]? = x'.2.2.2.1[k]?)
    (h : Early m L wd mx i x u) : Early m L wd mx i x' u := by
  intro k hk
  obtain ⟨rows, keys, a, b, c, d⟩ := h k hk
  refine ⟨rows, keys, (h3 k hk) ▸ a, (h4 k hk) ▸ b, ?_, d⟩
  have e : stm x' = stm x := by
    unfold stm
    rw [h1, h2]
  rw [e]
  exact c

/-! ## A promise on the record that rides beside a row -/

/-- A row with one more clause on the record in its condition. -/
def andQ (X : JointRow FirstState Fr) (Q : FirstState → Prop) : JointRow FirstState Fr :=
  ⟨X.J, X.rd, fun a => X.inv a ∧ Q a.1⟩

theorem tie_and {b : Block FirstState Claim} {X Y : JointRow FirstState Fr} (h : QuietTie b X Y) (Q
    Q' : FirstState → Prop)
    (hq : ∀ s s' y rs gs, X.on (s, y) → Q s → b.decide s rs gs = .ok s' → Q' s') :
    QuietTie b (andQ X Q) (andQ Y Q') := by
  intro s s' y rs gs ha hd
  obtain ⟨h1, h2⟩ := h s s' y rs gs ⟨ha.1, ha.2.1⟩ hd
  exact ⟨⟨h1.1, h1.2, hq s s' y rs gs ⟨ha.1, ha.2.1⟩ ha.2.2 hd⟩, h2⟩

theorem law_and {b : Block FirstState Claim} {base : ℕ} {ds : List OnBytes.Maker.RDT} {back : List
    Fmt.RoundView}
    {JA JB : KObj.JK} {k : KObj.BK JA JB} {Mp : OnBytes.Flat.Maps ds k.R.red.shape}
    {rdA : FirstState × Fr.E.Str → JA.X × JA.E.Str} {X Y : JointRow FirstState Fr}
    (h : VerifiableInference.Desc.Sound.RelLaw b base ds back k Mp rdA X Y) (Q Q' : FirstState →
        Prop)
    (hq : ∀ s s' y rs gs, X.on (s, y) → Q s → b.decide s rs gs = .ok s' → Q' s') :
    VerifiableInference.Desc.Sound.RelLaw b base ds back k Mp rdA (andQ X Q) (andQ Y Q') where
  onIn := fun a ha => h.onIn a ⟨ha.1, ha.2.1⟩
  relIn := fun a w ha hw => h.relIn a w ⟨ha.1, ha.2.1⟩ hw
  step := fun s s' y τ ha h1 hv h2 hd => by
    obtain ⟨b', e1, e2, e3⟩ := h.step s s' y τ ⟨ha.1, ha.2.1⟩ h1 hv h2 hd
    exact ⟨b', e1, fun g => ⟨(e2 g).1, (e2 g).2, hq s s' y _ _ ⟨ha.1, ha.2.1⟩ ha.2.2 hd⟩, e3⟩

/-- A block that hands the record on as it is. -/
theorem same_tie {b : Block FirstState Claim} (X : JointRow FirstState Fr)
    (hb : ∀ s s' rs gs, b.decide s rs gs = .ok s' → s' = s) : QuietTie b X X := by
  intro s s' y rs gs ha hd
  obtain rfl := hb s s' rs gs hd
  exact ⟨ha, fun h => h⟩

/-! ## The three ties between two links -/

/-- The rows of the link of lookup number i, at the typed lookup without a letter. -/
abbrev row0At (p₀ : P) (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (oL kL : ℕ → List
    ℕ)
    (idxN : ℕ) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE) (dec : TK P × Fr.E.Str → Option M)
    (cond : TK P × Fr.E.Str → Prop) (n i : ℕ) (Wp : Type) (Oth : TK P → M × Wp → Prop) :
    JointRow FirstState Fr :=
  row0 one i id m (L i) (oL i) (kL i) idxN (AK one id m (L i) (oL i) (kL i) idxN (TK P)) (stK p₀ i)
    (R id m L wd mx dec cond n Oth i) (msgk one i id m (L i) (oL i) (kL i) idxN (TK P) wd mx)

abbrev row3At (p₀ : P) (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (oL kL : ℕ → List
    ℕ)
    (idxN : ℕ) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE) (dec : TK P × Fr.E.Str → Option M)
    (cond : TK P × Fr.E.Str → Prop) (n i : ℕ) (Wp : Type) (Oth : TK P → M × Wp → Prop) :
    JointRow FirstState Fr :=
  row3 one i id m (L i) (oL i) (kL i) idxN (AK one id m (L i) (oL i) (kL i) idxN (TK P)) (stK p₀ i)
    (R id m L wd mx dec cond n Oth i) wd fun u => cutM m (mx u)

/-- **"laid"**: from the border between two links to the border in front of the caller. -/
theorem laid_tie {b : Block FirstState Claim} (hb : ∀ s s' rs gs, b.decide s rs gs = .ok s' → s' =
    s)
    (Q : FirstState → Prop) (i : ℕ)
    (hQ : ∀ s, Q s → Hands one id m (L i) (oL i) (kL i) idxN s ∧
      Fits one id m (L i) (oL i) (kL i) idxN s.d.st) :
    QuietTie b (rowJ p₀ id m L wd mx dec cond n Oth Q i)
      (andQ (row0At p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) Q) := by
  intro s s' y rs gs ha hd
  obtain rfl := hb s s' rs gs hd
  obtain ⟨⟨hc, hr, -, hq⟩, -⟩ := ha
  refine ⟨⟨hc, ⟨(hQ _ hq).1, (hQ _ hq).2, hr⟩, hq⟩, fun hrel => ?_⟩
  obtain ⟨w, ⟨h1, h2, h3, h5⟩, h4⟩ := (row0_rel _ (s', y)).1 hrel
  refine ⟨w, h1, h2, fun k hk hkn => ?_, h5⟩
  rcases Nat.eq_or_lt_of_le hk with rfl | hk'
  · exact h4
  · exact h3 k hk' hkn

/-- **"cleared"**: from the border behind the layer of lookup i to the border between the links: THE
EXCHANGE OF RIDING JOINTS: lookup i's rows and pending rows pass into what rides. -/
theorem cleared_tie {b : Block FirstState Claim}
    (hb : ∀ s s' rs gs, b.decide s rs gs = .ok s' →
      s' = { s with base := { s.base with fork := none, heard := none, home := #[] } })
    (hB : Blind dec cond Oth) (Q Q' : FirstState → Prop) (i : ℕ)
    (hQ : ∀ s : FirstState, Q s →
      Q' { s with base := { s.base with fork := none, heard := none, home := #[] } }) :
    QuietTie b (andQ (row3At p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) Q)
      (rowJ p₀ id m L wd mx dec cond n Oth Q' (i + 1)) := by
  intro s s' y rs gs ha hd
  obtain rfl := hb s s' rs gs hd
  obtain ⟨⟨hc, -, hr, hk⟩, -, hq⟩ := ha
  have hc' : cond (stK p₀ i s, y) := hc
  have hr' : s.base.rows.length = i + 1 := hr
  have hk' : s.base.keys.length = i + 1 := hk
  have bl := hB (stK p₀ i s) (stK p₀ (i + 1) { s with base := { s.base with
    fork := none, heard := none, home := #[] } }) y rfl rfl rfl
  refine ⟨⟨⟨bl.2.1.1 hc', hr', hk', hQ s hq⟩, trivial⟩, fun hrel => ?_⟩
  obtain ⟨w, h1, h2, h3, h5⟩ := hrel
  have h1' : dec (stK p₀ (i + 1) { s with base := { s.base with
    fork := none, heard := none, home := #[] } }, y) = some w.1 := h1
  have h2' : Early m L wd mx (i + 1) (stK p₀ (i + 1) s) w.1 := h2
  obtain ⟨rows, keys, a1, a2, a3, a4⟩ := h2' i (Nat.lt_succ_self i)
  have a1' : (s.base.rows.take (i + 1))[i]? = some rows := a1
  have a2' : (s.base.keys.take (i + 1))[i]? = some keys := a2
  rw [List.getElem?_take_of_lt (Nat.lt_succ_self i)] at a1' a2'
  refine ⟨w, ⟨bl.1.trans h1', ?_, h3, (bl.2.2 w).2 h5⟩, rows, keys, a1', a2',
    (allSay_same Reading.gl (stm_same p₀ (i + 1) s) rows (wd w.1)).1 a3, a4⟩
  refine early_take (x := stK p₀ (i + 1) s) rfl rfl (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk => h2' k (Nat.lt_succ_of_lt hk))
  · show (s.base.rows.take (i + 1))[k]? = (s.base.rows.take i)[k]?
    rw [List.getElem?_take_of_lt (Nat.lt_succ_of_lt hk), List.getElem?_take_of_lt hk]
  · show (s.base.keys.take (i + 1))[k]? = (s.base.keys.take i)[k]?
    rw [List.getElem?_take_of_lt (Nat.lt_succ_of_lt hk), List.getElem?_take_of_lt hk]

/-! ## The six seats of a link, in a row -/

/-- **A promise on the record, lookup by lookup**: blind to the ledger of hidden values, to what was
heard and to the table of homes; at lookup i, of n, it gives Hands and Fits; the caller's two takes
lead from i to i + 1; and it outlasts the layer's writing of the lookup's rows and claims on the
keys. -/
structure Promise (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (oL kL : ℕ → List ℕ)
    (idxN n : ℕ) (Prom : ℕ → FirstState → Prop) : Prop where
  blind : ∀ (i : ℕ) (s : FirstState) (f : Option OnBytes.Model.Fork) (h : Option HeardG)
    (hm : Array Slot), Prom i s →
    Prom i { s with base := { s.base with fork := f, heard := h, home := hm } }
  lays : ∀ (i : ℕ) (s : FirstState) (F : OnBytes.Model.Fork) (g : HeardG) (cls : List Claim)
    (rows : List Row) (keys : List Lkp.Keys), Prom (i + 1) s → s.base.rows.length = i →
    s.base.keys.length = i →
    VerifiableInference.Desc.Key.rowsInOrder (Wf.planesAt one.ranges one.codes i)
      (VerifiableInference.Desc.Key.layerOrder (cls.filter fun c => c.isLeft).length) F s.base.home
          cls =
        some rows →
    keyClaims (Wf.lookupOf id m (L i)) F s.base.home g = some keys →
    g.keys.length = (L i).parts.length →
    Prom (i + 1) { s with base := { s.base with
      rows := s.base.rows ++ [rows], keys := s.base.keys ++ [keys] } }
  gives : ∀ (i : ℕ) (s : FirstState), i < n → Prom i s → Hands one id m (L i) (oL i) (kL i) idxN s ∧
    Fits one id m (L i) (oL i) (kL i) idxN s.d.st
  step : ∀ (i : ℕ) (s : FirstState) o k, Prom i s →
    VerifiableInference.Desc.Ground.takeMasksP s.d one.ranges.messageId
      ((faceOfLkp (Wf.lookupOf id m (L i))).slots -
        2 * (faceOfLkp (Wf.lookupOf id m (L i))).parts.length) = some o →
    VerifiableInference.Desc.Ground.takeMasksP o.2 s.idx
      (2 * (faceOfLkp (Wf.lookupOf id m (L i))).parts.length) = some k →
    Prom (i + 1) { s with d := k.2 }

abbrev rowInAt (p₀ : P) (one : OneTime) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup) (oL kL : ℕ →
    List ℕ)
    (idxN : ℕ) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE) (dec : TK P × Fr.E.Str → Option M)
    (cond : TK P × Fr.E.Str → Prop) (n i : ℕ) (Wp : Type) (Oth : TK P → M × Wp → Prop) :
    JointRow FirstState Fr :=
  rowIn VerifiableInference.Desc.Key.lookupSeat (AK one id m (L i) (oL i) (kL i) idxN (TK P)) (stK
      p₀ i)
    (Inv one i id m (L i) (oL i) (kL i) idxN) (R id m L wd mx dec cond n Oth i)
    (msgk one i id m (L i) (oL i) (kL i) idxN (TK P) wd mx)

abbrev rowOutAt (p₀ : P) (one : OneTime) (set : Setting) (id : ℕ) (m : Wf.Matrix) (L : ℕ → WfLookup)
    (oL kL : ℕ → List ℕ) (idxN : ℕ) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)
    (dec : TK P × Fr.E.Str → Option M) (cond : TK P × Fr.E.Str → Prop) (n i : ℕ) (Wp : Type)
    (Oth : TK P → M × Wp → Prop) : JointRow FirstState Fr :=
  rowOut VerifiableInference.Desc.Key.lookupSeat (VerifiableInference.Desc.Key.lookupPlace set i
      (Wf.lookupOf id m (L i)))
    (AK one id m (L i) (oL i) (kL i) idxN (TK P)) (slk one id m (L i) (oL i) (kL i) idxN (TK P))
    (fun j => (homeT one id m (L i) (oL i) (kL i) idxN).getD j default) (stK p₀ i)
    (Inv one i id m (L i) (oL i) (kL i) idxN) (R id m L wd mx dec cond n Oth i)
    (msgk one i id m (L i) (oL i) (kL i) idxN (TK P) wd mx)

variable {Prom : ℕ → FirstState → Prop} {set : Setting}

/-- **Seat 1: the caller**, with the promise led from i to i + 1. -/
theorem callerJ_tie (hP : Promise one id m L oL kL idxN n Prom) (i : ℕ) :
    QuietTie (VerifiableInference.Desc.Key.caller one i (Wf.lookupOf id m (L i)))
      (andQ (row0At p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom i))
      (andQ (rowInAt p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom (i + 1))) :=
  tie_and (callerK_tie _ (rides_stK p₀ i)) _ _ fun s s' _ rs gs _ hq hd => by
    obtain ⟨-, -, o, k, h1, h2, -, rfl⟩ := Johnson.RunOne.Law.AtKeyD.callerD_law hd
    exact hP.blind (i + 1) { s with d := k.2 } _ _ _ (hP.step i s o k hq h1 h2)

/-- **Seat 3: the layer.** -/
theorem layerJ_tie {b0 : Block FirstState Claim} {before : List (ℕ × ℕ)} {bits : ℕ}
    (hP : Promise one id m L oL kL idxN n Prom) (i : ℕ)
    (hadm : (Lk6.pubOf (Wf.lookupOf id m (L i))).Adm Cb.Gl.p)
    (hlo : Wf.lookupOk Wf.fBits (L i) = true) (hfm : Wf.fitsMatrix m (L i) = true)
    (hi : one.ranges.lookups[i]? = some (L i))
    (hla : ((Wf.layout one.ranges.lookups (Planes.codeOf one.ranges one.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf one.ranges one.codes).ell)) = true) :
    QuietTie (VerifiableInference.Desc.Key.layer one set i
        (Wf.lookupOf id m (L i))
        (VerifiableInference.Desc.claimsIn [b0, lookupKind VerifiableInference.Desc.Key.lookupSeat
            before bits []
          (VerifiableInference.Desc.Key.lookupPlace set i (Wf.lookupOf id m (L i)))]
          [(1, "objects"), (1, "planes"), (1, "guests")]))
      (andQ (rowOutAt p₀ one set id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom (i + 1)))
      (andQ (row3At p₀ one id m L oL kL idxN wd mx dec cond n i Wp Oth) (Prom (i + 1))) :=
  tie_and (layerK_tie _ (rides_stK p₀ i) hadm hlo hfm hi hla) _ _ fun s s'' _ rs gs ha hq hd => by
    obtain ⟨⟨-, ⟨-, -, hrl, hkl, -⟩, G, g, hG, hg, -, -, -, hgk, -⟩, -⟩ := ha
    obtain ⟨cls, s', F, g', rows, keys, c1, -, c3, c4, c5, rfl⟩ :=
      Johnson.RunOne.Law.AtKeyD.layerD_law hd
    obtain ⟨pl, H', u, -, -, rfl⟩ := Johnson.RunOne.Law.AtKeyD.claimsD_law hG hg c1
    obtain rfl : g = g' := Option.some.inj (hg.symm.trans c3)
    have hgk' : g.keys.length = (L i).parts.length := by
      rw [hgk]
      exact List.length_map _
    exact hP.blind (i + 1) _ (some (F.paid g.owedJoin)) s.base.heard s.base.home
      (hP.lays i s F g cls rows keys hq hrl hkl c4 c5 hgk')

/-- What the link lays, what stands behind its batching, and what it clears. -/
theorem lay_same {i : ℕ}
    {x : VerifiableInference.Desc.Key.Lookup} {s s' : FirstState}
    (h : (VerifiableInference.Desc.Key.lookupLink one set i x).lay s = .ok s') : s' = s := by
  have h' : (do
      need "a lookup's link: a ledger is open" s.base.fork.isNone
      pure s : Except String FirstState) = .ok s' := h
  obtain ⟨_, -, h'⟩ := bindX h'
  cases h'
  rfl

theorem clear_eq {i : ℕ}
    {x : VerifiableInference.Desc.Key.Lookup} {s s' : FirstState}
    (h : (VerifiableInference.Desc.Key.lookupLink one set i x).clear s = .ok s') :
    s' = { s with base := { s.base with fork := none, heard := none, home := #[] } } := by
  cases h
  rfl

theorem after_same {bs : List (Block FirstState Claim)} {s s' : FirstState} (h : afterIn bs [] s =
    .ok s') :
    s' = s := by
  cases h
  rfl

/-- The riding joint pins the messages: by its make. -/
theorem pins_R (i : ℕ) :
    Pins (AK one id m (L i) (oL i) (kL i) idxN (TK P)) Fr.E (R id m L wd mx dec cond n Oth i) :=
  fun _ _ _ _ _ _ _ h h' => Option.some.inj (h.1.symm.trans h'.1)

/-- The decoder and its condition read, of the oracles, the stored table and the trees below c. -/
def LowDec (dec : TK P × Fr.E.Str → Option M) (cond : TK P × Fr.E.Str → Prop) (c : ℕ) : Prop :=
  ∀ (x : TK P) (y y' : Fr.E.Str), y.1 = y'.1 →
    (∀ q : OnBytes.Maker.PosL Fr.all, (Fr.all.get q.1).no < c → y.2 q = y'.2 q) →
    dec (x, y) = dec (x, y') ∧ (cond (x, y) ↔ cond (x, y'))

theorem lowDec_mono {c c' : ℕ} (h : c ≤ c') (hd : LowDec dec cond c) : LowDec dec cond c' :=
  fun x y y' h1 h2 => hd x y y' h1 fun q hq => h2 q (lt_of_lt_of_le hq h)

theorem low_R (i c : ℕ) (hd : LowDec dec cond c) :
    ReadsLow (AK one id m (L i) (oL i) (kL i) idxN (TK P)) (R id m L wd mx dec cond n Oth i) c :=
  fun x y y' h1 h2 => ⟨(hd x y y' h1 h2).2, fun w => by
    show (dec (x, y) = some w.1 ∧ _) ↔ (dec (x, y') = some w.1 ∧ _)
    rw [(hd x y y' h1 h2).1]⟩

/-- The kind's own block's law with a promise beside that is blind to the ledger of hidden values,
to what was heard and to the table of homes: for every typed lookup. -/
theorem k3Q_law {A : Lk6.Dat GE} {sl : Slot → A.J} {stOf : FirstState → A.St} {Kc : Type}
    {R0 : IOR.Rels Kc A.St Fr.E (M × Wp)} {msg : M → A.J → GE} {l : WfLookup} {o k : List ℕ}
    (Q : FirstState → Prop)
    (hQ : ∀ (s : FirstState) (f : Option OnBytes.Model.Fork) (h : Option HeardG) (hm : Array Slot),
        Q s →
      Q { s with base := { s.base with fork := f, heard := h, home := hm } }) (i : ℕ)
    (before : List (ℕ × ℕ)) (bits base : ℕ) (ds : List OnBytes.Maker.RDT) (hst : Rides stOf i)
    (hnd : (Fr.all.map (·.no)).Nodup)
    (hf : ∀ st, FaceIs A st (faceOfLkp (Wf.lookupOf id m l))) (hadm : A.toPub.Adm Cb.Gl.p)
    (hB : ReadsLow A R0 base)
    (hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf id m l)))) (st0 : A.St) :
    VerifiableInference.Desc.Sound.RelLaw
      (lookupKind VerifiableInference.Desc.Key.lookupSeat before bits []
        (VerifiableInference.Desc.Key.lookupPlace set i (Wf.lookupOf id m l))) base ds []
      (bkLam A (placesAt A sl
        (fun j => (o.map fun t => (⟨one.ranges.messageId, t⟩ : Slot)).getD j default)
        (fun j => (k.map fun t => (⟨idxN, t⟩ : Slot)).getD j default)) Fr.E R0 msg)
      (mapsOf (Lk6.lamS_runs A (placesAt A sl
        (fun j => (o.map fun t => (⟨one.ranges.messageId, t⟩ : Slot)).getD j default)
        (fun j => (k.map fun t => (⟨idxN, t⟩ : Slot)).getD j default)) Fr.E).rd ds
        (meets_typed A st0 _ Fr.E (faceOfLkp (Wf.lookupOf id m l)) (hf st0) hadm ds
          hds).1.length_eq)
      (fun a => (stOf a.1, a.2))
      (andQ (rowIn VerifiableInference.Desc.Key.lookupSeat A stOf (Inv one i id m l o k idxN) R0
          msg) Q)
      (andQ (rowOut VerifiableInference.Desc.Key.lookupSeat
          (VerifiableInference.Desc.Key.lookupPlace set i (Wf.lookupOf id m l))
        A sl (fun j => (homeT one id m l o k idxN).getD j default) stOf
        (Inv one i id m l o k idxN) R0 msg) Q) := by
  have h := k3D_relLaw (one := one) (set := set) (i := i) (id := id) (m := m) (l := l) (oL := o)
    (kL := k) (idxN := idxN) (A := A) (sl := sl) (stOf := stOf) (R0 := R0) (msg := msg) before bits
    base ds hst hnd hf hadm hB hds st0
  refine law_and h Q Q fun s s' _ rs gs _ hq hdd => ?_
  obtain ⟨F, g, G, es, -, -, -, -, -, rfl⟩ := block_law _ before bits [] _ hdd
  exact hQ s _ _ s.base.home hq

end Johnson.RunOne.Law.JoinKeyD

#print axioms Johnson.RunOne.Law.JoinKeyD.stm_same
#print axioms Johnson.RunOne.Law.JoinKeyD.tie_and
#print axioms Johnson.RunOne.Law.JoinKeyD.law_and
#print axioms Johnson.RunOne.Law.JoinKeyD.laid_tie
#print axioms Johnson.RunOne.Law.JoinKeyD.cleared_tie
#print axioms Johnson.RunOne.Law.JoinKeyD.callerJ_tie
#print axioms Johnson.RunOne.Law.JoinKeyD.k3Q_law
#print axioms Johnson.RunOne.Law.JoinKeyD.layerJ_tie
#print axioms Johnson.RunOne.Law.JoinKeyD.clear_eq
#print axioms Johnson.RunOne.Law.JoinKeyD.lowDec_mono
#print axioms Johnson.RunOne.Law.JoinKeyD.pins_R
#print axioms Johnson.RunOne.Law.JoinKeyD.low_R
