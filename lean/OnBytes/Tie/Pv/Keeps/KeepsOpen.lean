-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsOpen.lean: where no message is open in a run on a view: behind the closing
of a link of a request's chain, and at the context at which the next link's first scalars are
received. Definitions, statements and proofs.

What it is for. The rounds that a stretch of calls takes are WHOLE rounds of the view only if no
message is open where the stretch begins (`OnBytes.PscRun.Clean`, OnBytes/Tie/Pv/Psc/PscView.lean: a
run on a view, and no round is begun). Behind every `Blk.close` that holds. A link ends in
`ChainCheck.close`, whose last call on the channel is the last round of a fold. This file says so,
and carries the fact over the calls that leave the channel as it is.

Main names:
  `SameCh b`: wherever the block b succeeds it leaves the channel as it was. A class: `pure` has it,
    `bind` carries it; the calls on the statement, the tests and the notes have it.
  `clean_same`: such a call keeps "no message is open".
  `closeOne_clean`: behind `Blk.closeOne`, on a view, no message is open.
  `foldRounds_clean`, `foldVerify_clean`: the same behind a fold.
  `reqClose_clean`, `chainClose_clean`: behind `ReqFrame.close` and `ChainCheck.close`.
  `pendingRowH_clean`, `beginLink_clean`: these two keep it.
  `startOf_clean`, `chainStart_clean`: the context that is made of a view, and the one behind
    `ChainCheck.start`.
  `FirstPartsCleanEnd`: from the context c7 behind the sending or the switch to the end of the
    link's first call.
  `LinkStepClean`, `FirstPartsClean`: from "no message is open behind the link's routine" to the
    same at the link's end; from the same where a link begins to the context c4 behind `beginLink`.
Limits: one direction: from the calls' success. THAT A LINK'S ROUTINE ENDS WITH `ChainCheck.close`
AND TOUCHES THE CHANNEL NO MORE IS NOT SAID HERE: it is a fact on each kind of link's own routine.

-/
import OnBytes.Tie.Pv.Keeps.KeepsFirstLaws
import OnBytes.Tie.Pv.Psc.Run.ViewRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.Open

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5 OnBytes.Model.Road

/-- Wherever the block succeeds it leaves the channel as it was. -/
class SameCh {α : Type} (b : Blk α) : Prop where
  out : ∀ c x c', b c = .ok (x, c') → c'.ch = c.ch

instance sameCh_pure {α : Type} (a : α) : SameCh (pure a : Blk α) :=
  ⟨fun c x c' h => by cases h; rfl⟩

instance sameCh_bind {α β : Type} (b : Blk α) (f : α → Blk β) [hb : SameCh b]
    [hf : ∀ x, SameCh (f x)] : SameCh (b >>= f) :=
  ⟨fun c y c2 h => by
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind b f c c2 y).1 ((Blk.yields_iff _ _ _ _).2 h)
    exact ((hf x).out _ _ _ ((Blk.yields_iff _ _ _ _).1 h2)).trans
      (hb.out _ _ _ ((Blk.yields_iff _ _ _ _).1 h1))⟩

instance sameCh_statement : SameCh Blk.statement := ⟨fun c x c' h => by cases h; rfl⟩

instance sameCh_setStatement (S : Statement) : SameCh (Blk.setStatement S) :=
  ⟨fun c x c' h => by cases h; rfl⟩

instance sameCh_get {α : Type} (x : Option α) (n : String) : SameCh (Blk.get x n) :=
  ⟨fun c a c' h => by
    cases x with
    | none => cases h
    | some y => cases h; rfl⟩

instance sameCh_must (b : Bool) (n : String) : SameCh (Blk.must b n) :=
  ⟨fun c a c' h => by
    cases b with
    | true => cases h; rfl
    | false => cases h⟩

instance sameCh_note (w : String) (v : E) : SameCh (Blk.note w v) :=
  ⟨fun c a c' h => by
    unfold Blk.note at h
    cases h
    split <;> rfl⟩

instance sameCh_onOracle (o : Nat) (f : Oracle → Oracle) : SameCh (Blk.onOracle o f) :=
  ⟨fun c a c' h => by
    unfold Blk.onOracle at h
    split at h
    · cases h; rfl
    · cases h⟩

instance sameCh_testOnView (f : Unit → Bool) (n : String) : SameCh (Blk.testOnView f n) :=
  ⟨fun c a c' h => by
    unfold Blk.testOnView at h
    split at h
    · cases h; rfl
    · cases h⟩

instance sameCh_oracle (o : Nat) : SameCh (Blk.oracle o) := by
  unfold Blk.oracle
  infer_instance

instance sameCh_newGroup (a b : Nat) : SameCh (Blk.newGroup a b) := by
  unfold Blk.newGroup
  infer_instance

instance sameCh_takeMask (o : Nat) : SameCh (Blk.takeMask o) := by
  unfold Blk.takeMask
  infer_instance

instance sameCh_onGroup (g : Nat) (f : Group → Group) : SameCh (Blk.onGroup g f) :=
  ⟨fun c a c' h => by
    unfold Blk.onGroup at h
    split at h
    · cases h; rfl
    · cases h⟩

instance sameCh_samples : SameCh Blk.samples := ⟨fun c x c' h => by cases h; rfl⟩

instance sameCh_group (g : Nat) : SameCh (Blk.group g) := by
  unfold Blk.group
  infer_instance

instance sameCh_join (g o : Nat) (kept : Bool) : SameCh (Blk.join g o kept) := by
  unfold Blk.join
  dsimp only
  repeat (first
    | exact inferInstance
    | refine @sameCh_bind _ _ _ _ inferInstance fun _ => ?_)

instance sameCh_forIn_list {α β : Type} (l : List α) (init : β)
    (f : α → β → Blk (ForInStep β)) [hf : ∀ a b, SameCh (f a b)] : SameCh (forIn l init f) := by
  induction l generalizing init with
  | nil => rw [List.forIn_nil]; infer_instance
  | cons a l ih =>
    rw [List.forIn_cons]
    refine @sameCh_bind _ _ _ _ (hf a init) fun r => ?_
    cases r with
    | done b => exact sameCh_pure b
    | yield b => exact ih b

instance sameCh_joinOwn (f : ReqFrame) (sent : List Params.ReqMessage) (ids : Array Nat) :
    SameCh (f.joinOwn sent ids) := by
  unfold ReqFrame.joinOwn
  infer_instance

instance sameCh_reqStart (shape : Params.ReqShape) : SameCh (ReqFrame.start shape) := by
  unfold ReqFrame.start
  infer_instance

instance sameCh_rowsMake (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    SameCh (ReqRows.make shape layout) := by
  unfold ReqRows.make
  infer_instance

instance sameCh_chainStart (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    SameCh (ChainCheck.start shape layout) := by
  unfold ChainCheck.start
  infer_instance

/-- A call that leaves the channel as it was keeps "no message is open". -/
theorem clean_same {α : Type} {b : Blk α} [s : SameCh b] {c : Ctx} {x : α} {c' : Ctx}
    (h : b c = .ok (x, c')) (k : PscRun.Clean c) : PscRun.Clean c' := by
  have e := s.out c x c' h
  exact ⟨by rw [e]; exact k.1, by rw [e]; exact k.2⟩

/-- Behind closeOne, on a view, no message is open. -/
theorem closeOne_clean {name : String} {kind : Fmt.Kind} {nz : Nat} {x : E} {c c' : Ctx}
    (d : c.ch.dry = false) (h : Blk.closeOne name kind nz c = .ok (x, c')) : PscRun.Clean c' := by
  obtain ⟨dr, y, h1, -, -⟩ := closeOne_close ((Blk.yields_iff _ _ _ _).2 h)
  obtain ⟨_, _, _, _, _, _, _, _, k, _⟩ :=
    PscRun.close_view name kind nz dr c c' d ((Blk.yields_iff _ _ _ _).1 h1)
  exact k

/-- The rounds of a fold keep "no message is open". -/
theorem foldRounds_clean : ∀ (n : Nat) (claim : E) {c : Ctx} {r : List E × E} {c' : Ctx},
    PscRun.Clean c → foldRounds n claim c = .ok (r, c') → PscRun.Clean c'
  | 0, _, _, _, _, k, h => by
    cases h
    exact k
  | n + 1, claim, c, r, c', k, h => by
    have hr : Runs (foldRounds (n + 1) claim) c r c' := h
    unfold foldRounds at hr
    have d0 : View (m := Blk) c := k.1
    peel1_from hr d0 (id : Clean (m := Blk) c' → Clean (m := Blk) c') 1
    obtain ⟨-, e⟩ := runs_pure' hr
    subst e
    exact foldRounds_clean n _ (closeOne_clean d2 r3) r4

/-- Behind a fold, on a view, no message is open. -/
theorem foldVerify_clean {F : FoldShape} {row : GroupRow} {mask : Option Nat} {c : Ctx}
    {r : SingleRows} {c' : Ctx} (d : c.ch.dry = false) (h : foldVerify F row mask c = .ok (r, c')) :
    PscRun.Clean c' := by
  have hr : Runs (foldVerify F row mask) c r c' := h
  unfold foldVerify at hr
  have d0 : View (m := Blk) c := d
  peel1_from hr d0 (id : Clean (m := Blk) c' → Clean (m := Blk) c') 1
  -- r1: the first message; r2: the draw of eps; hr: the rounds
  have k2 : PscRun.Clean c2 := by
    unfold foldEpsilon at r2
    peel1_from r2 d1 b2 11
    obtain ⟨-, e⟩ := runs_pure' r2
    subst e
    exact closeOne_clean d11 r12
  unfold foldRoundsVerify at hr
  peel1_from hr d2 (id : Clean (m := Blk) c' → Clean (m := Blk) c') 21
  obtain ⟨-, e⟩ := runs_pure' hr
  subst e
  exact foldRounds_clean _ _
    (clean_same r24 (clean_same r23 (clean_same r22 (clean_same r21 k2)))) r25

/-- Behind ReqFrame.close, on a view, no message is open. -/
theorem reqClose_clean {f : ReqFrame} {c : Ctx} {r : ReqFrame} {c' : Ctx} (d : c.ch.dry = false)
    (h : f.close c = .ok (r, c')) : PscRun.Clean c' := by
  have hr : Runs f.close c r c' := h
  unfold ReqFrame.close at hr
  have d0 : View (m := Blk) c := d
  peel1_from hr d0 (id : Clean (m := Blk) c' → Clean (m := Blk) c') 1
  obtain ⟨-, e⟩ := runs_pure' hr
  subst e
  exact clean_same r8 (foldVerify_clean d6 r7)

/-- Behind ChainCheck.close, on a view, no message is open. -/
theorem chainClose_clean {k : ChainCheck} {eq : ReqEquation} {c : Ctx} {r : ChainCheck} {c' : Ctx}
    (d : c.ch.dry = false) (h : k.close eq c = .ok (r, c')) : PscRun.Clean c' := by
  have hr : Runs (k.close eq) c r c' := h
  unfold ChainCheck.close at hr
  have d0 : View (m := Blk) c := d
  peel1_from hr d0 (id : Clean (m := Blk) c' → Clean (m := Blk) c') 1
  obtain ⟨-, e⟩ := runs_pure' hr
  subst e
  exact reqClose_clean d3 r4

/-- The row that a link leaves on the committed table: the channel is as it was. -/
theorem pendingRowH_clean {wsLay : WsLay} {i : Nat} {o : WsForkOut} {n : Nat}
    {S : Params.LinShape} {c : Ctx} {r : TensorRow} {c' : Ctx} (k : PscRun.Clean c)
    (h : pendingRowH wsLay i o n S c = .ok (r, c')) : PscRun.Clean c' := by
  have hr : Runs (pendingRowH wsLay i o n S) c r c' := h
  unfold pendingRowH at hr
  have d0 : View (m := Blk) c := k.1
  peel1_from hr d0 (id : Clean (m := Blk) c' → Clean (m := Blk) c') 1
  obtain ⟨-, e⟩ := runs_pure' hr
  subst e
  exact clean_same r1 k

/-- beginLink leaves the channel as it was. -/
theorem beginLink_clean {f : ReqFrame} {c : Ctx} {g : ReqFrame} {c' : Ctx} (k : PscRun.Clean c)
    (h : f.beginLink c = .ok (g, c')) : PscRun.Clean c' := by
  obtain ⟨n, h1, -⟩ := beginLink_same f h
  exact clean_same h1 k

/-- From "no message is open behind the link's routine" to the same at the link's end. -/
theorem LinkStepClean {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx}
    {l : Nat} {X : LinkH} {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
    {r : ChainCheck × Proof.LinksResult} {c' : Ctx} {chk : ChainCheck} {o : Option WsForkOut}
    {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2)
    (k : PscRun.Clean c2) : PscRun.Clean c' := by
  by_cases hf : X.fv = true
  · obtain ⟨o', row, -, h3, -⟩ := S.row hf
    exact pendingRowH_clean k h3
  · rw [(S.noRow hf).1]
    exact k

/-- From "no message is open where the link begins" to the same behind beginLink. -/
theorem FirstPartsClean {f : ReqFrame} {cEnd c : Ctx} {r : ReqFrame × Array Nat} {c' : Ctx}
    {L : Params.ReqLink} {G : ReqGroup} {g : ReqFrame} {plain : List E} {kept ids : Array Nat}
    {mask : Nat} {j : ReqFrame} {c4 c5 c6 c7 : Ctx}
    (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7)
    (k : PscRun.Clean c) : PscRun.Clean c4 := beginLink_clean k P.begin

/-- From "no message is open behind the sending or the switch" (c7) to the same behind the whole
first call. -/
theorem FirstPartsCleanEnd {f : ReqFrame} {cEnd c : Ctx} {r : ReqFrame × Array Nat} {c' : Ctx}
    {L : Params.ReqLink} {G : ReqGroup} {g : ReqFrame} {plain : List E} {kept ids : Array Nat}
    {mask : Nat} {j : ReqFrame} {c4 c5 c6 c7 : Ctx}
    (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7)
    (k : PscRun.Clean c7) : PscRun.Clean c' := clean_same P.joined k

/-- The context that is made of a view: no message is open. -/
theorem startOf_clean (s : Start) (v : Fmt.View) : PscRun.Clean (startOf s v) := ⟨rfl, rfl⟩

/-- Behind ChainCheck.start, run from the context that is made of a view, no message is open. -/
theorem chainStart_clean {shape : Params.ReqShape} {layout : Params.ReqLayout} {s : Start}
    {v : Fmt.View} {k : ChainCheck} {c' : Ctx}
    (h : ChainCheck.start shape layout (startOf s v) = .ok (k, c')) : PscRun.Clean c' :=
  clean_same h (startOf_clean s v)

#print axioms foldVerify_clean
#print axioms chainClose_clean
#print axioms LinkStepClean
#print axioms FirstPartsClean
#print axioms FirstPartsCleanEnd
#print axioms chainStart_clean

end OnBytes.L5.Open
