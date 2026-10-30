-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameLabels.lean: **THE GAME OF THE PROXIMITY TEST WITH NOTHING PROMISED OF THE
RECORD** (first arm: the first fold's mask has come from outside). Definitions, statements and
proofs.

The game's one promise was `FirstOpens π num no base`: the trees that the first switch's openings
name are those at the book's places D.ts, ALONG A NUMBERING no OF THE BOOK's PLACES that is fixed
before the statement. To pay it one must know that the book is in order (the tree at the place z is
the chain's tree number z): an invariant of the whole chain in front.
BUT A LAW IN THE PLAIN FORM SPEAKS OF ONE STATEMENT AT A TIME: so the numbering may be read OFF THE
STATEMENT's OWN BOOK: the place z is numbered by THE LABEL THAT THE TREE AT z BEARS. Then the
promise says: the declared openings' labels are the labels of the trees at D.ts: and that is what
the block's own guard (g) tests (`labelsOk`): a yes gives it (`yes_labels`, Labels.lean).
  `dOf π t`: the plain data that a record fixes, as a function with code; `dOf_of_fixes`.
  `nuOf π nl t`: the numbering off the record: z ↦ nl (the number of the tree at z in the data's
    book); nl: from a label to the tree's number through the file: of the plan alone.
  `labelsPubB π num nl base` | `LabelsPub`: A TEST ON THE PLAN: of each opening that the first
    switch declares: its source's number through the file is nl of its label, and lies below base.
  `firstOpens_of_labels`: the labels' equation and that test give `FirstOpens` at `nuOf`.
  `leads_at`: a family of laws, one for each letter, taken at a letter read off the statement.
  `k12_gameV`: the game at the block's own record: PROMISE: NONE.
  `k12_gameSeatV`, `k12_game_alikeV`: at every seat; at any piece over P × S, at any type of claims,
    whose block is alike to `held` of the seat.
Limits: those of GameSeat.lean and GameAlike.lean. NO SOUNDNESS IS CLAIMED. THE CONCLUSION HAS
TURNED WITH THE PROMISE: "one tuple for all rows" now stands at the oracles that `nuOf` names:
whoever spends it (the seams) reads the trees by their labels. The own mask's arm is not typed here.

-/
import Johnson.Desc.K12.Coin.GameAlike
import Johnson.Desc.K12.Coin.Labels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk gpOf Plain opensOf made_of)

/-- The plain data that a record fixes. -/
def dOf (π : P12) (t : T12) : Option Plain :=
  match π.nums.stages, t.st.groups[t.g]?, t.st.layout t.g with
  | a :: _, some G0, some Ly =>
    gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly
  | _, _, _ => none

theorem dOf_of_fixes {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
    {Ly : GroupLayout} {D : Plain} (hf : Fixes π t a rest G0 Ly D) : dOf π t = some D := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  have f5 : gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly = some D :=
    f4 default
  unfold dOf
  rw [f1, f2, f3]
  exact f5

/-- **The numbering off the record**: a place of the book by the label of the tree there. -/
def nuOf (π : P12) (nl : ℕ → ℕ) (t : T12) (z : ℕ) : ℕ :=
  nl (H2K.First.numAt (((dOf π t).map (·.book)).getD t.book) z)

theorem nuOf_of_fixes {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
    {Ly : GroupLayout} {D : Plain} (hf : Fixes π t a rest G0 Ly D) (nl : ℕ → ℕ) (z : ℕ) :
    nuOf π nl t z = nl (H2K.First.numAt D.book z) := by
  unfold nuOf
  rw [dOf_of_fixes hf]
  rfl

/-- A test on the plan: the declared openings' sources and labels. -/
def labelsPubB (π : P12) (num : Fmt.TreeSource → ℕ) (nl : ℕ → ℕ) (base : ℕ) : Bool :=
  match π.nums.stages with
  | a :: _ => (opensOf π a.k).all fun o => num o.2 == nl o.1.tree && decide (num o.2 < base)
  | [] => false

/-- What it says. -/
def LabelsPub (π : P12) (num : Fmt.TreeSource → ℕ) (nl : ℕ → ℕ) (base : ℕ) : Prop :=
  ∀ a rest, π.nums.stages = a :: rest →
    ∀ o ∈ opensOf π a.k, num o.2 = nl o.1.tree ∧ num o.2 < base

theorem labelsPub_of_B {π : P12} {num : Fmt.TreeSource → ℕ} {nl : ℕ → ℕ} {base : ℕ}
    (h : labelsPubB π num nl base = true) : LabelsPub π num nl base := by
  intro a rest hs o ho
  unfold labelsPubB at h
  rw [hs] at h
  have h1 := List.all_eq_true.1 h o ho
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  exact h1

/-- **The labels' equation and the test on the plan give the promise, at the numbering off the
record.** -/
theorem firstOpens_of_labels (π : P12) (num : Fmt.TreeSource → ℕ) (nl : ℕ → ℕ) (base : ℕ) (t : T12)
    (hpl : LabelsPub π num nl base)
    (hl : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D →
      D.opens.map (·.1.tree) = D.ts.map (H2K.First.numAt D.book)) :
    FirstOpens π num (nuOf π nl t) base t := by
  intro a rest G0 Ly D hf
  have heq := hl a rest G0 Ly D hf
  have hop : D.opens = opensOf π a.k := (made_of π _ a Ly D (hf.2.2.2 default)).opens
  have hP : ∀ o ∈ D.opens, num o.2 = nl o.1.tree ∧ num o.2 < base := by
    rw [hop]
    exact hpl a rest hf.1
  have e1 : D.opens.map (fun o => num o.2) = (D.opens.map (·.1.tree)).map nl := by
    rw [List.map_map]
    exact List.map_congr_left fun o ho => (hP o ho).1
  have e2 : D.ts.map (nuOf π nl t) = (D.ts.map (H2K.First.numAt D.book)).map nl := by
    rw [List.map_map]
    exact List.map_congr_left fun z _ => nuOf_of_fixes hf nl z
  refine ⟨by rw [e1, e2, heq], fun z hz => ?_⟩
  have hm : H2K.First.numAt D.book z ∈ D.opens.map (·.1.tree) := by
    rw [heq]
    exact List.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨o, ho, e⟩ := List.mem_map.1 hm
  rw [nuOf_of_fixes hf, ← e, ← (hP o ho).1]
  exact (hP o ho).2

/-- A family of laws, one for each letter, taken at a letter that is read off the statement. -/
theorem leads_at {A B N : Type} {K : Reduction A B} {on : N → A → Prop} {Q : N → A → B → Prop}
    {ε : Err K.shape} (h : ∀ n, K.Leads (on n) (Q n) ε) (ν : A → N) :
    K.Leads (fun a => on (ν a) a) (fun a b => Q (ν a) a b) ε :=
  fun a ha => h (ν a) a ha

/-- **THE GAME AT THE BLOCK's OWN RECORD: NOTHING IS PROMISED.** -/
theorem k12_gameV (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (nl : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : T12 × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base) :
    (pieceOf (C := ckP .two) (F := F) (proximityTestKind guardedProximityTestParts π : Block T12 Unit) base (dB :: dt) []
        ⟨ext, (e, εt)⟩).ior.red.Leads (fun _ => True)
      (fun x _ => QN π (NTuple F π (nuOf π nl x.1) rad rd) x) (e, εt) := by
  refine leads_drop_yes (on := fun _ => True)
    (P := fun x => FirstOpens π num (nuOf π nl x.1) base x.1) ?_ ?_
  · exact Reduction.Leads.conseq
      (leads_at (fun no => k12_gameZ F W π num no L mC mS mW rad rd base dB dt ext e εt r hA hr hj
        hb1 hle) fun x => nuOf π nl x.1)
      (fun _ hx => hx.2) (fun _ _ _ _ _ q => q)
  · intro x τ b _ hy
    exact firstOpens_of_labels π num nl base x.1 hpl fun a rest G0 Ly D hf =>
      yes_labels (W := W) F π hA.early hA.planOk base dB dt e εt x τ b hy a rest G0 Ly D hf

/-- **At every seat.** -/
theorem k12_gameSeatV (S : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (nl : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base) :
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads (fun _ => True)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π (nuOf π nl t) rad rd) (t, a.2))
      (e, εt) := by
  intro a _
  exact leads_seated (pieceT F W π base dB dt e εt) enter leave (fun _ => True)
    (fun x _ => QN π (NTuple F π (nuOf π nl x.1) rad rd) x)
    (k12_gameV F W π num nl L mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r hA hr hj hb1 hle
      hpl) a (fun _ _ => trivial)

/-- **At any piece, at any type of claims, whose block is alike to the held seat.** -/
theorem k12_game_alikeV (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (nl : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π (nuOf π nl t) rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_alike
    (pieceOf (C := ckP .two) (F := F) (W := W)
      (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) base (dB :: dt) []
      ⟨fun _ _ w => w, (e, εt)⟩) p hb hbase hds h0 herr _ _
    (leads_lift (S := P × S) Prod.snd (fun t s => (t.1, s))
      (pieceOf (C := ckP .two) (F := F) (W := W)
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base (dB :: dt) []
        ⟨fun _ _ w => w, (e, εt)⟩).under
      (fun _ => True)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π (nuOf π nl t) rad rd) (t, a.2))
      (fun _ _ => rfl) (fun _ _ _ => rfl)
      (leads_under _ rfl _ _
        (k12_gameSeatV S enter leave F W π num nl L mC mS mW rad rd base dB dt (fun _ _ w => w)
          e εt r hA hr hj hb1 hle hpl)))

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.firstOpens_of_labels
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameV
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameSeatV
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_alikeV
