-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/FitsAtS.lean
(kind K9's soundness lemma): DEFINITIONS AND THEOREMS: THE HYPOTHESIS FitsM
(Law/Moves.lean: on the lens and on the other kinds' letters at the draw and at the adding) PAID AT
THE REAL THING: the record S that the proof file's first chain carries, through K9's lens atS
(Batch/AtS.lean), at letters that are written out but for two. SECOND FORM: UP TO "LATER".
WHY A SECOND FORM. Runs of K3's, K4's, K8's and K11's
FILL SLOTS BEHIND THE DRAW (Fork.hideRun: a sumcheck's hiding coefficients: shown 0, factor
-1, the mark) and mark owed claims as added. So "what was shown under the slots stays as it was, to
the array" is false at real runs. What holds, and what they have proved of their runs, is the
library's PscRun.Later (OnBytes/Tie/Pv/Psc/PscLater.lean): what lies under a FILLED slot stays.
  Pub9, pubOf   THE SNAPSHOT IN FRONT OF THE DRAW of K9's part: THE WHOLE LEDGER AS IT STANDS THERE
                (chi is not drawn yet, the sums are empty: nothing in it can hang on chi); the
                arrays' names; the walk's record (layout, frame, group); the statement.
  fixed9 φ s    (φ s, the snapshot of K9's part at s).
  Fx9 φ Ok q e  THE STATE e GOES ON FROM THE FIXED PART q: Ok q; φ e is q's; a part is there; its
                ledger is LATER than the snapshot's, with the same plan's number AND THE SAME
                LOOKS OF THE ARRAYS (kind, rows, columns, number of virtual rows:
                Johnson/Desc/First/Batch/Law/Look.lean. NOT THE NUMBERS OF COLUMNS ALONE,
                wanted by K5's files: "later" has no clause on
                the arrays, and a form that names an entry of the vector of reads divides by that
                number. An entry's worth also reads the array's number of rows and kind: with the
                widths alone the premises "at all t that go on from q" on an entry that have
                been examined, fuEq and its seven sisters in Link/Law/Pay*.lean, could be met, by
                reading, only where no such t was); names, walk's record and statement are
                the snapshot's. `goesOn_widths`: the numbers of columns follow.
  more9 φ s t   t goes on from s: φ t is φ s; where s has a part, t has one, its ledger later than
                s's, the names, the walk's record and the statement the same.
  fx_of_more    SO AT EVERY LATER STATE t OF A RUN's EQUATION Fx9 φ Ok q t HOLDS TOO: φ t IS q's. So
                the letter Fu, which sees t alone, can say "the virtual rows' weights at t are the
                function of what was heard (φ t) that the smallness test's tests ask", and a run
                whose claims name entries of virtual rows gets values that are functions of (q, y)
                (K6's files' pinch: "later" and the widths do not keep the rows' weights).
  O9 φ Ok Fu    THE LETTERS. φ: ANY READER OF THE RECORD THAT DOES NOT SEE K9's PART (hφ): what the
                hearing kinds have heard: other files' to choose. Ok: A PROMISE ON THE FIXED
                PART (the three arrays have one entry a slot; what was heard is what the snapshot's
                ledger holds; ...): other files' to say together; it is asked IN FRONT (in "ready")
                and handed to every run (in Fx9). Fu: "all that a claim's value
                reads has been laid" (every slot that a claim names is filled; the virtual rows'
                weights): other files' to say.
                  fixed := fixed9 φ   ·   more := more9 φ   ·   full := Fu
                  ready s := the promise in front of the batching (k9OnA, Law/Borders.lean), and
                             Ok (fixed9 φ s)
                  good s  := a part is there; the draw has run; one coefficient for each slot
                  behind  := good
                (cnt, eqs, exps are laid empty: nothing on the road of moves reads them.)
  fitsM_atS     **FitsM atS (O9 φ Ok Fu) (Fx9 φ Ok) p**, for every such φ, every Ok, Fu, place p.
  kept_of_more  under "more" what lies under a slot that is filled stays. part_of_more: a part is
                there.
SO RunOk, AddOk, QuietOk (Law/Gather.lean, Moves.lean) AT atS, O9 φ Ok Fu, Fx9 φ Ok ARE SENTENCES ON
THE REAL RECORD, in which a kind's run can be tried: a run must keep φ, the names, the walk's
record and the statement, leave the ledger's core, hand on a LATER ledger, and its claims' values at
a full later record must be the terms that see (the count, φ, the snapshot in front of the draw,
the data) alone. WHAT A RUN ITSELF LAYS UNDER A SLOT MUST THEREFORE COME OUT, INSIDE THE RUN's
EQUATION, AS TERMS WHOSE COEFFICIENTS ARE FUNCTIONS OF THESE: no clause of its own. (A laid value
that hangs on chi shows as other powers of chi: RunOk alone does not shut it out; the discipline on
the exponents does: Law/MemberLate.lean [not in this library]: chiOk, chi_out_of_window.)
A LIMIT. Fx9 pins what lies under the slots that are FILLED IN THE SNAPSHOT.
What a run lays behind the draw is neither in q nor pinned: a LATER run whose claim named such a
slot could not meet RunOk. At K3, K4, K5, K6, K8's claims and K11 (by
reading; K3's and K11's by laws of theirs): no run's claim names a slot that ANOTHER run fills
behind the draw; and all that is ever laid there is (shown 0, factor -1, the mark). So no clause on
it stands here; should such a run come, the clause "a slot that is filled now and was free in the
snapshot holds (0, -1)" is the cure, read as payable at all kinds that fill.
Fx9 SAYS "THE FIXED PART GOES ON" AND NO MORE: the sums, chi, the count and the marks may be
anything in a state that goes on from q. The sums, chi, the count and the plan's number are guarded
by "core" in AddOk, QuietOk and RunOk; the marks by nothing here (Law/OnLemmas.lean says who reads
them).
THE STATEMENT AND THE WALK's RECORD ARE HELD WHOLE: a run or a quiet step that writes either between
the draw and the one equation breaks "more" and Fx9. MoveDoor (Law/MovesDoor.lean) asks the same.
Not claimed: that any real run meets them; that a useful φ exists.

-/
import OnBytes.Tie.Pv.Psc.PscLater
import Johnson.Desc.First.Batch.Law.Borders
import Johnson.Desc.First.Batch.Law.Moves
import Johnson.Desc.First.Batch.Law.Look

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.K9 (atS Where drawnClean drawn)
open VerifiableInference.Desc.First (S)

/-- The snapshot of K9's part. -/
structure Pub9 where
  F : Fork
  arrayOf : Array (Nat × String)
  check : ChainCheck
  st : Statement

def pubOf (a : K9.Part) : Pub9 := ⟨a.F, a.L.arrayOf, a.L.check, a.d.st⟩

variable {α K : Type}

/-- What is fixed before the draw. -/
def fixed9 (φ : S → α) (s : S) : α × Option Pub9 := (φ s, (atS.get? s).map pubOf)

/-- The part b goes on from the snapshot u. -/
def GoesOn (u : Pub9) (b : K9.Part) : Prop :=
  Later u.F b.F ∧ b.F.planClaimsF = u.F.planClaimsF ∧
    b.F.trees.map LinkJoin.look = u.F.trees.map LinkJoin.look ∧ b.L.arrayOf = u.arrayOf ∧
    b.L.check = u.check ∧ b.d.st = u.st

/-- The state e goes on from the fixed part q. -/
def Fx9 (φ : S → α) (Ok : α × Option Pub9 → Prop) (q : α × Option Pub9) (e : S) : Prop :=
  Ok q ∧ φ e = q.1 ∧ ∃ u b, q.2 = some u ∧ atS.get? e = some b ∧ GoesOn u b

/-- The state t goes on from the state s. -/
def more9 (φ : S → α) (s t : S) : Prop :=
  φ t = φ s ∧ ∀ a, atS.get? s = some a → ∃ b, atS.get? t = some b ∧ GoesOn (pubOf a) b

/-- A part is there; the draw has run; one coefficient for each slot. -/
def good9 (s : S) : Prop :=
  ∃ a, atS.get? s = some a ∧ a.L.handed = true ∧ a.F.LS.size = a.F.ns

/-- **The letters at the real record.** -/
def O9 (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) :
    Others S (α × Option Pub9) K where
  fixed := fixed9 φ
  ready := fun s => k9OnA s = true ∧ Ok (fixed9 φ s)
  good := good9
  behind := good9
  more := more9 φ
  full := Fu
  cnt := fun _ _ => 0
  eqs := fun _ _ _ => []
  exps := fun _ _ _ => []

theorem goesOn_refl (a : K9.Part) : GoesOn (pubOf a) a :=
  ⟨Later.refl _, rfl, rfl, rfl, rfl, rfl⟩

theorem goesOn_trans {u : Pub9} {a b : K9.Part} (h1 : GoesOn u a) (h2 : GoesOn (pubOf a) b) :
    GoesOn u b :=
  ⟨h1.1.trans h2.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

/-- "Goes on" carries the arrays' looks. -/
theorem goesOn_looks {u : Pub9} {b : K9.Part} (h : GoesOn u b) :
    b.F.trees.map LinkJoin.look = u.F.trees.map LinkJoin.look := h.2.2.1

/-- So their numbers of columns. -/
theorem goesOn_widths {u : Pub9} {b : K9.Part} (h : GoesOn u b) :
    b.F.trees.map (·.K) = u.F.trees.map (·.K) := LinkJoin.widths_of_looks _ _ h.2.2.1

/-- A ledger that differs in none of the fields which "later" reads is later. -/
theorem later_of_same (F G : Fork) (h1 : G.next = F.next) (h2 : G.ns = F.ns) (h3 : G.vp = F.vp)
    (h4 : G.mf = F.mf) (h5 : G.gotF = F.gotF) : Later F G where
  next := by rw [h1]
  ns := h2
  sized := fun h => by
    unfold OnBytes.PscRun.Sized at h ⊢
    rw [h2, h3, h4, h5]
    exact h
  keep := fun j h => by
    unfold OnBytes.PscRun.Filled at h ⊢
    rw [h3, h4, h5]
    exact ⟨h, rfl, rfl⟩

/-- Whatever keeps the arrays' frame keeps their numbers of columns. -/
theorem widths_of_frame (A B : Array HTree) (h : treesFrame A = treesFrame B) :
    A.map (·.K) = B.map (·.K) := by
  have e : ∀ X : Array HTree, X.map (·.K) = (treesFrame X).map (·.1.K) := fun X => by
    simp [treesFrame, HTree.frame, Array.map_map, Function.comp_def]
  rw [e A, e B, h]

theorem fold_widths : ∀ (l : List Nat) (tr : Array HTree),
    (l.foldl (fun trees ti => trees.modify ti fillOne) tr).map (·.K) = tr.map (·.K)
  | [], _ => rfl
  | ti :: l, tr => by
    rw [List.foldl_cons, fold_widths l]
    exact map_modify_same (fun X : HTree => X.K) fillOne (fun _ => rfl) tr ti

/-- t2FillL keeps the arrays' numbers of columns. -/
theorem fill_widths (F : Fork) (T : Tail2) :
    (t2FillL F T).trees.map (·.K) = F.trees.map (·.K) := fold_widths _ _

theorem fold_looks : ∀ (l : List Nat) (tr : Array HTree),
    (l.foldl (fun trees ti => trees.modify ti fillOne) tr).map LinkJoin.look =
      tr.map LinkJoin.look
  | [], _ => rfl
  | ti :: l, tr => by
    rw [List.foldl_cons, fold_looks l]
    exact map_modify_same LinkJoin.look fillOne (fun X => LinkJoin.look_rows_map X _) tr ti

/-- t2FillL keeps the arrays' looks. -/
theorem fill_looks (F : Fork) (T : Tail2) :
    (t2FillL F T).trees.map LinkJoin.look = F.trees.map LinkJoin.look := fold_looks _ _

/-- What the draw lays is a later ledger, with the same numbers of columns. -/
theorem drawn_later (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) :
    Later F o.F ∧ o.F.trees.map (·.K) = F.trees.map (·.K) := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  have e : o' = o := Except.ok.inj h
  subst e
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  exact ⟨later_of_same _ _ rfl rfl rfl rfl rfl, fill_widths _ _⟩

/-- What the draw lays has the same looks. -/
theorem drawn_looks (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) :
    o.F.trees.map LinkJoin.look = F.trees.map LinkJoin.look := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  have e : o' = o := Except.ok.inj h
  subst e
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  exact fill_looks _ _

/-- A writing of the lens: the part that is read behind it goes on from whatever b goes on from. -/
theorem goesOn_set (s : S) (b : K9.Part) (u : Pub9) (hs : (atS.get? s).isSome = true)
    (h : GoesOn u b) : ∃ b', atS.get? (atS.set s b) = some b' ∧ GoesOn u b' ∧ b'.F = b.F ∧
      b'.L = b.L := by
  obtain ⟨b', hb', e1, e2, e3⟩ := atS_reads s b hs
  refine ⟨b', hb', ?_, e1, e2⟩
  unfold GoesOn at h ⊢
  rw [e1, e2, e3]
  exact h

/-- **FitsM at the real record.** -/
theorem fitsM_atS (φ : S → α) (hφ : ∀ s a, φ (atS.set s a) = φ s)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Where) :
    FitsM atS (O9 (K := K) φ Ok Fu) (Fx9 φ Ok) p where
  lens := fun s a h => by
    obtain ⟨a', e0, e1, _, _⟩ := atS_reads s a h
    exact ⟨a', e0, e1⟩
  moreRefl := fun _ => ⟨rfl, fun a ha => ⟨a, ha, goesOn_refl a⟩⟩
  moreTrans := fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, fun a ha => by
    obtain ⟨b, hb, g1⟩ := h1.2 a ha
    obtain ⟨c, hc, g2⟩ := h2.2 b hb
    exact ⟨c, hc, goesOn_trans g1 g2⟩⟩
  atDraw := fun s a o x hr ha ho => by
    obtain ⟨_, _, _, d4, _, _, _, _, d9, d10, d11, d12⟩ := drawnClean_ok _ _ _ _ _ _ _ ho
    have g : GoesOn (pubOf a) { a with owed := o.owed, L := o.L, F := o.F } :=
      ⟨(drawn_later _ _ _ _ _ _ _ ho).1, d4, drawn_looks _ _ _ _ _ _ _ ho, d9, d10, rfl⟩
    obtain ⟨b', hb', g', e1, e2⟩ := goesOn_set s _ _ (by simp [ha]) g
    refine ⟨⟨hr.2, hφ _ _, pubOf a, b', by simp [O9, fixed9, ha], hb', g'⟩, b', hb', ?_, ?_⟩
    · rw [e2]
      exact d11
    · rw [e1]
      exact d12
  atAdd := fun q e b G c hf hg hb hG => by
    obtain ⟨b0, hb0, g1, g2⟩ := hg
    have eb : b0 = b := Option.some.inj (hb0.symm.trans hb)
    subst eb
    obtain ⟨_, e1, e2, e3⟩ :=
      addAll_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ c b0.F G g2 hG
    have n1 : G.next = b0.F.next := by rw [e1]
    have n2 : G.ns = b0.F.ns := by rw [e1]
    have n3 : G.vp = b0.F.vp := by rw [e1]
    have n4 : G.mf = b0.F.mf := by rw [e1]
    have n5 : G.gotF = b0.F.gotF := by rw [e1]
    have n6 : G.planClaimsF = b0.F.planClaimsF := by rw [e1]
    have g : GoesOn (pubOf b0) { b0 with F := G } :=
      ⟨later_of_same _ _ n1 n2 n3 n4 n5, n6, LinkJoin.looks_of_frame _ _ e3, rfl, rfl, rfl⟩
    obtain ⟨b', hb', g', k1, k2⟩ := goesOn_set e _ _ (by simp [hb]) g
    obtain ⟨k0, f1, u, b1, hu, hb1, gu⟩ := hf
    have eb1 : b1 = b0 := Option.some.inj (hb1.symm.trans hb)
    subst eb1
    refine ⟨⟨b', hb', by rw [k2]; exact g1, by rw [k1]; exact e2⟩, ?_, ?_⟩
    · refine ⟨hφ _ _, fun a ha => ?_⟩
      have ea : a = b1 := Option.some.inj (ha.symm.trans hb)
      subst ea
      exact ⟨b', hb', g'⟩
    · exact ⟨k0, (hφ _ _).trans f1, u, b', hu, hb', goesOn_trans gu g'⟩

/-- A state that goes on from a state with a part has a part (the premise hpart of
Law/PlainRuns.lean, at these letters). -/
theorem part_of_more (φ : S → α) (e t : S) (a : K9.Part) (ha : atS.get? e = some a)
    (h : more9 φ e t) : ∃ b, atS.get? t = some b := by
  obtain ⟨b, hb, _⟩ := h.2 a ha
  exact ⟨b, hb⟩

/-- **A state that goes on from a state which goes on from q goes on from q**: so at every later
state t of a run's equation φ t is q's, and the ledger of t is later than the snapshot's. -/
theorem fx_of_more (φ : S → α) (Ok : α × Option Pub9 → Prop) (q : α × Option Pub9) (e t : S)
    (hf : Fx9 φ Ok q e) (h : more9 φ e t) : Fx9 φ Ok q t := by
  obtain ⟨k0, f1, u, b, hu, hb, gu⟩ := hf
  obtain ⟨c, hc, g⟩ := h.2 b hb
  exact ⟨k0, h.1.trans f1, u, c, hu, hc, goesOn_trans gu g⟩

/-- Under "more" what lies under a filled slot stays. -/
theorem kept_of_more (φ : S → α) (s t : S) (a b : K9.Part) (ha : atS.get? s = some a)
    (hb : atS.get? t = some b) (h : more9 φ s t) :
    Later a.F b.F ∧ b.F.planClaimsF = a.F.planClaimsF ∧
      b.F.trees.map (·.K) = a.F.trees.map (·.K) ∧ b.L.arrayOf = a.L.arrayOf ∧
      b.L.check = a.L.check ∧ b.d.st = a.d.st := by
  obtain ⟨b', hb', g⟩ := h.2 a ha
  have e : b' = b := Option.some.inj (hb'.symm.trans hb)
  subst e
  exact ⟨g.1, g.2.1, goesOn_widths g, g.2.2.2⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.drawn_later
#print axioms VerifiableInference.Desc.K9L.drawn_looks
#print axioms VerifiableInference.Desc.K9L.goesOn_widths
#print axioms VerifiableInference.Desc.K9L.fitsM_atS
#print axioms VerifiableInference.Desc.K9L.fx_of_more
#print axioms VerifiableInference.Desc.K9L.kept_of_more
