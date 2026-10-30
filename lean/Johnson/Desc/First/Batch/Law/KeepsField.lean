-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/KeepsField.lean
(kind K9's soundness lemma; for the table of conditions on the statement): THEOREMS: WHATEVER OF THE
CARRIED RECORD K9's LENS DOES NOT WRITE, AND NO RUN WRITES, PASSES ALL FOUR OF K9's BLOCKS UNTURNED:
the batching (a draw with moves behind it), the block behind it (a row of moves), the one equation
(in whatever dress), "shut". f: any reading of the record. (Law/TableTabs.lean has the like for the
book alone.)
  MoveKeeps f   the duty of a move: where it returns, f reads the same.
  moves_keep, drawMoves_keep, isMoves_keep   along a row of moves; a draw with moves; a block of
                moves.
  gather_keep, steps_keep   the duty of the steps' moves from one duty a run.
  equation_keep, shut_keep  the one equation's block (from "a yes of b3's step is a yes of the one
                equation's"); "shut".
  failed_set, failed_putLink   the deferred mark (S.failed) is written neither by the lens nor by a
                writing of the link's record.
  join_keeps    at the joining's three pieces (LinkJoin.JoinAsks): f of the state behind a piece's
                yes is f of the state in front.
  join_marks    **A MARK STAYS** at these three pieces: the first of the two facts on a block's text
                that the door at the table asks (Johnson/Desc/Sound/BordersQ.lean: OwnAtTable), at
                the record S itself; under ONE DUTY A MOVE: it leaves S.failed.
  shut_mark     and at a piece that holds "shut".
  failed_puts, k8Run_failed, k8LsTail_failed, k8Tests_failed   that duty at the smallness test's
                three runs (Law/K8Run.lean, K8Step.lean, K8Tests.lean).
  join_doors    THE LINK's OWN CHECK AND THE STATEMENT STAY along the first two pieces (KeepsDoor).
  inside_of_live   the clause "inside" of JoinAsks from two things: at a state with on2 the layout
                in the link's check is a given layout; the library's public test says yes of that
                one.
Not claimed: the duty at any run of the protocol; the lift to a record that holds S as a part.

-/
import Johnson.Desc.First.Batch.Law.JoinMoves
import Johnson.Desc.First.Batch.Law.ShutLaw
import Johnson.Desc.First.Batch.Law.Steps
import Johnson.Desc.First.Batch.Law.Layout
import Johnson.Desc.First.Batch.Law.K8Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where RunOf Window gather shut)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (JoinAsks)
open _root_.Run.PQ (CK)
open _root_.Run (ckP)

section
variable {β : Type} (f : S → β)

/-- The duty of a move. -/
def MoveKeeps : Move S → Prop
  | .add g => ∀ e c e₁, g e = .ok (c, e₁) → f e₁ = f e
  | .quiet h => ∀ e e₁, h e = .ok e₁ → f e₁ = f e

theorem moves_keep (hset : ∀ s a, f (atS.set s a) = f s) :
    ∀ (ms : List (Move S)), (∀ m ∈ ms, MoveKeeps f m) →
      ∀ (e e' : S) (c : List Claim), MovesYes atS ms e e' c → f e' = f e
  | [], _, e, e', c, hy => by
    obtain ⟨rfl, _⟩ := hy
    rfl
  | m :: l, hms, e, e', c, hy => by
    obtain ⟨u, c₁, c₂, h1, h2, _⟩ := hy
    have i := moves_keep hset l (fun q hq => hms q (List.mem_cons_of_mem _ hq)) u e' c₂ h2
    have hm := hms m List.mem_cons_self
    rw [i]
    cases m with
    | add g =>
      obtain ⟨e₁, s, G, hg, _, _, rfl⟩ := h1
      rw [hset]
      exact hm e c₁ e₁ hg
    | quiet h => exact hm e u h1.1

/-- A draw with moves behind it. -/
theorem drawMoves_keep {Cl : Type} (hset : ∀ s a, f (atS.set s a) = f s) (p : Where)
    (ms : List (Move S)) (b : Block S Cl) (hb : DrawMoves atS p ms b)
    (hms : ∀ m ∈ ms, MoveKeeps f m) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S)
    (k : ℕ) (h : b.step ft s rs cols = .ok (s', k)) : f s' = f s := by
  obtain ⟨r, x, a, o, cls, _, _, _, _, hy⟩ := hb ft s rs cols s' k h
  rw [moves_keep f hset ms hms _ _ _ hy, hset]

/-- A block that is a row of moves. -/
theorem isMoves_keep {Cl : Type} (hset : ∀ s a, f (atS.set s a) = f s) (ms : List (Move S))
    (b : Block S Cl) (hb : IsMoves atS ms b) (hms : ∀ m ∈ ms, MoveKeeps f m) (ft : ℕ) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b.step ft s rs cols = .ok (s', k)) : f s' = f s := by
  obtain ⟨rs', gs, hd⟩ := step_decide b _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := hb.dec _ _ _ _ hd
  exact moves_keep f hset ms hms _ _ _ hy

/-- A gathering, if each of its runs keeps f. -/
theorem gather_keep (ws : S → List Window) (cut : List (Nat × String)) :
    ∀ (runs : List (RunOf S)), (∀ r ∈ runs, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → f e₁ = f e) →
      ∀ x x' : List Claim × S, runs.foldlM (gstep ws cut) x = .ok x' → f x'.2 = f x.2
  | [], _, x, x', h => by
    have e : x = x' := Except.ok.inj h
    rw [e]
  | r :: l, hr, x, x', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := ok_bind h
    obtain ⟨c, e, hc, rfl⟩ := gstep_ok hz
    rw [gather_keep ws cut l (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) _ _ h]
    exact hr r List.mem_cons_self _ _ _ _ hc

/-- The duty of the steps' moves, from one duty a run. -/
theorem steps_keep {P K : Type} (l : List (Step S P K))
    (hr : ∀ r ∈ runsOf l, ∀ n e c e₁, r.run.2 n e = .ok (c, e₁) → f e₁ = f e)
    (hq : ∀ s ∈ l, ∀ e e₁, s.behind e = .ok e₁ → f e₁ = f e) :
    ∀ m ∈ (movesOf l).map (·.move), MoveKeeps f m := by
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
  obtain ⟨s, hs, hm1⟩ := List.mem_flatMap.1 hm0
  simp only [Step.moves, List.mem_cons, List.mem_nil_iff, or_false] at hm1
  rcases hm1 with rfl | rfl
  · intro e c e₁ h
    rw [gather_eq] at h
    exact gather_keep f s.ws s.cut (s.runs.map (·.run)) (fun r hr' => by
      obtain ⟨r0, h0, rfl⟩ := List.mem_map.1 hr'
      exact hr r0 (List.mem_flatMap.2 ⟨s, hs, h0⟩)) ([], e) (c, e₁) h
  · exact hq s hs

/-- The one equation's block, in whatever dress. -/
theorem equation_keep {Cl : Type} (hset : ∀ s a, f (atS.set s a) = f s) (pw : Where)
    (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b₃.step ft s rs cols = .ok (s', k)) : f s' = f s := by
  obtain ⟨a0, out, _, _, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  rw [hs', hset]

/-- "Shut". -/
theorem shut_keep {Cl : Type} (hput : ∀ s L, f (s.putLink L) = f s) (p : Where) (piece ft : ℕ)
    (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : (shut (Cl := Cl) p piece).step ft s rs cols = .ok (s', k)) : f s' = f s := by
  obtain ⟨L, _, rfl⟩ := shut_inv p piece ft s rs cols s' k h
  exact hput s _

end

/-- A writing of the link's record leaves the deferred mark. -/
theorem failed_putLink (s : S) (L : LinkCtx) : (s.putLink L).failed = s.failed := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putLink, ho]
  | _ => rfl

/-- The lens's writing leaves the deferred mark. -/
theorem failed_set (s : S) (a : K9.Part) : (atS.set s a).failed = s.failed := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [atS, S.putLink, S.putFork, ho]
  | _ => rfl

section
variable {α β W Cl : Type} {F : Frame}

/-- **At the joining's three pieces f passes unturned.** -/
theorem join_keeps (f : S → β) (hset : ∀ s a, f (atS.set s a) = f s) {φ : S → α}
    {Ok : α × Option Pub9 → Prop} {Fu : S → Prop} {p pw : Where}
    {ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)} {d N : ℕ} {b₁ b₂ b₃ : Block S Cl}
    {pb pq pe : Piece (ckP .two) F S Cl W} {on0 on1 on2 on3 : S × F.E.Str → Prop}
    {tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E} {ctx : S × F.E.Str → W → Prop}
    (H : JoinAsks φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx)
    (hk : ∀ m ∈ ms₁ ++ ms₂, MoveKeeps f m.move) :
    (∀ a τ b, pb.ior.red.out a τ = some b → f b.1 = f a.1) ∧
      (∀ a τ b, pq.ior.red.out a τ = some b → f b.1 = f a.1) ∧
      ∀ a τ b, pe.ior.red.out a τ = some b → f b.1 = f a.1 := by
  have hk₁ : ∀ m ∈ ms₁.map (·.move), MoveKeeps f m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hk q (List.mem_append_left _ hq)
  have hk₂ : ∀ m ∈ ms₂.map (·.move), MoveKeeps f m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hk q (List.mem_append_right _ hq)
  refine ⟨fun a τ b hout => ?_, fun a τ b hout => ?_, fun a τ b hout => ?_⟩
  · obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact drawMoves_keep f hset p _ b₁ H.hb₁ hk₁ _ _ _ _ _ k hs
  · obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpq hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact isMoves_keep f hset _ b₂ H.hb₂ hk₂ _ _ _ _ _ k hs
  · obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpe hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact equation_keep f hset pw b₃ H.hb₃ _ _ _ _ _ k hs

/-- **A mark stays**, at the joining's three pieces. -/
theorem join_marks {φ : S → α} {Ok : α × Option Pub9 → Prop} {Fu : S → Prop} {p pw : Where}
    {ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)} {d N : ℕ} {b₁ b₂ b₃ : Block S Cl}
    {pb pq pe : Piece (ckP .two) F S Cl W} {on0 on1 on2 on3 : S × F.E.Str → Prop}
    {tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E} {ctx : S × F.E.Str → W → Prop}
    (H : JoinAsks φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx)
    (hk : ∀ m ∈ ms₁ ++ ms₂, MoveKeeps (·.failed) m.move) :
    (∀ a τ b, pb.ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none) ∧
      (∀ a τ b, pq.ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none) ∧
      ∀ a τ b, pe.ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none := by
  obtain ⟨h1, h2, h3⟩ := join_keeps (·.failed) failed_set H hk
  exact ⟨fun a τ b ho hm => by rw [h1 a τ b ho]; exact hm,
    fun a τ b ho hm => by rw [h2 a τ b ho]; exact hm,
    fun a τ b ho hm => by rw [h3 a τ b ho]; exact hm⟩

/-- And at a piece that holds "shut". -/
theorem shut_mark {C : CK} (p : Where) (piece : ℕ) (ps : Piece C F S Cl W)
    (hps : ps.b = below (shut p piece)) (a b : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT C ps.ds)) (hout : ps.ior.red.out a τ = some b)
    (hm : a.1.failed ≠ none) : b.1.failed ≠ none := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hps hout
  obtain ⟨k, hs⟩ := fold_one hfold
  rw [shut_keep (·.failed) failed_putLink p piece _ _ _ _ _ k hs]
  exact hm

/-- **The link's own check and the statement stay** along the first two pieces. -/
theorem join_doors {φ : S → α} {Ok : α × Option Pub9 → Prop} {Fu : S → Prop} {p pw : Where}
    {ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)} {d N : ℕ} {b₁ b₂ b₃ : Block S Cl}
    {pb pq pe : Piece (ckP .two) F S Cl W} {on0 on1 on2 on3 : S × F.E.Str → Prop}
    {tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E} {ctx : S × F.E.Str → W → Prop}
    (H : JoinAsks φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx) :
    (∀ a τ b, pb.ior.red.out a τ = some b →
      (atS.get? a.1).isSome = true ∧ KeepsDoor atS a.1 b.1) ∧
      ∀ a τ b, pq.ior.red.out a τ = some b → KeepsDoor atS a.1 b.1 := by
  have lens : ∀ s a, (atS.get? s).isSome = true →
      ∃ a', atS.get? (atS.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st := fun s a h => by
    obtain ⟨a', e0, _, e2, e3⟩ := atS_reads s a h
    exact ⟨a', e0, e2, e3⟩
  refine ⟨fun a τ b hout => ?_, fun a τ b hout => ?_⟩
  · obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact drawMoves_door atS lens p _ b₁ H.hb₁ (fun m hm => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      exact H.hkd q (List.mem_append_left _ hq)) F.ft _ _ _ _ k hs
  · obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpq hout
    obtain ⟨k, hs⟩ := fold_one hfold
    obtain ⟨rs', gs, hd⟩ := step_decide b₂ _ _ _ _ _ k hs
    obtain ⟨cls, hy⟩ := H.hb₂.dec _ _ _ _ hd
    exact moves_door atS lens _ (fun m hm => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      exact H.hkd q (List.mem_append_right _ hq)) _ _ _ hy

/-- **"inside" from the live check's layout and the public test.** -/
theorem inside_of_live (codes : Codes) (sh : OnBytes.Params.ReqShape)
    (layout : OnBytes.Params.ReqLayout) (hl : reqLayoutOk codes sh layout = true)
    (on2 : S × F.E.Str → Prop)
    (hlive : ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → a.L.check.rows.layout = layout) :
    ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl :=
  fun s hs a ha born name r hr =>
    inside_of_layoutOk codes sh layout hl born name r (by rw [← hlive s hs a ha]; exact hr)

end

/-- A writing of the ledger or of the test's record leaves the deferred mark. -/
theorem failed_puts (s : S) (tl : HTailF2) (G : Fork) :
    (s.putTl tl).failed = s.failed ∧ (s.putFork G).failed = s.failed := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putTl, S.putFork, ho]
  | _ => exact ⟨rfl, rfl⟩

theorem k8Run_failed (front : Nat) (e e₁ : S) (c : List Claim)
    (h : k8Run.2 front e = .ok (c, e₁)) : e₁.failed = e.failed := by
  obtain ⟨G, tl, funs, tl', F1, _, _, _, _, rfl⟩ := k8Run_ok front e e₁ c h
  rw [(failed_puts (e.putTl tl') tl' F1).2, (failed_puts e tl' F1).1]

theorem k8LsTail_failed (e e₁ : S) (h : k8LsTail e = .ok e₁) : e₁.failed = e.failed := by
  obtain ⟨G, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ h
  exact (failed_puts e _ G).1

theorem k8Tests_failed (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁) :
    e₁.failed = e.failed := by
  obtain ⟨G, tl, g, _, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  rw [(failed_puts (e.putTl tl) tl _).2, (failed_puts e tl G).1]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.join_doors
#print axioms VerifiableInference.Desc.K9L.inside_of_live
#print axioms VerifiableInference.Desc.K9L.k8Tests_failed
#print axioms VerifiableInference.Desc.K9L.steps_keep
#print axioms VerifiableInference.Desc.K9L.join_keeps
#print axioms VerifiableInference.Desc.K9L.join_marks
#print axioms VerifiableInference.Desc.K9L.shut_mark
