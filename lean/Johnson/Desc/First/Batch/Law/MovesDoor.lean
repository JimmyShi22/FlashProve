-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/MovesDoor.lean
(kind K9's soundness lemma): THEOREMS: FOUR HYPOTHESES OF k9_row_moves
(Law/RowMoves.lean) PAID DOWN TO ONE DUTY OF EACH MOVE: hdb, hgb (the data and "every open row
holds" are carried past the first piece), hN, inside (asked behind the first piece).
  KeepsDoor e e'   where K9's part is there at e, it is there at e', with the same walk's record
                   (L.check: the layout, the frame, the group's number) and the same statement
                   (d.st): all that the door reads beside the ledger.
  MoveDoor         THE DUTY: a function of claims, or a quiet move, keeps the door.
  move_door, moves_door, drawMoves_door   so a row of moves does, and a draw with moves behind it.
  dataAt_door, groupHolds_door            what follows for the data and for the open rows.
  onPost           the conditions at the three boundaries: a condition on0 in front; behind the
                   first piece: "reached from it by a yes of the first piece"; behind the second:
                   none. (The strongest that the pieces hand on: the rule of consequence weakens
                   them.)
  k9_row_moves_post   **k9_row_moves at these conditions**: hN and inside are asked IN FRONT of the
                   draw; hdb, hgb are gone: in their place hkd (MoveDoor of each move) and htabb
                   (the witness's tables are the same in front of and behind the first piece).
All other hypotheses are k9_row_moves' own, hpin under ctx first among them; Fx is its letter "the
state goes on from the fixed part" (Law/Moves.lean).

-/
import Johnson.Desc.First.Batch.Law.RowMoves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens Where)
open VerifiableInference.Desc.Sound
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {T : Type}

/-- All that the door reads beside the ledger stays. -/
def KeepsDoor (X : Lens T) (e e' : T) : Prop :=
  ∀ a, X.get? e = some a →
    ∃ a', X.get? e' = some a' ∧ a'.L.check = a.L.check ∧ a'.d.st = a.d.st

/-- The duty of a move. -/
def MoveDoor (X : Lens T) : Move T → Prop
  | .add g => ∀ e c e₁, g e = .ok (c, e₁) → KeepsDoor X e e₁
  | .quiet h => ∀ e e₁, h e = .ok e₁ → KeepsDoor X e e₁

theorem keepsDoor_trans (X : Lens T) {e e₁ e₂ : T} (h1 : KeepsDoor X e e₁)
    (h2 : KeepsDoor X e₁ e₂) : KeepsDoor X e e₂ := by
  intro a ha
  obtain ⟨a₁, ha₁, c1, d1⟩ := h1 a ha
  obtain ⟨a₂, ha₂, c2, d2⟩ := h2 a₁ ha₁
  exact ⟨a₂, ha₂, c2.trans c1, d2.trans d1⟩

section
variable (X : Lens T)
  (lens : ∀ s a, (X.get? s).isSome = true →
    ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
include lens

theorem move_door (m : Move T) (hm : MoveDoor X m) (e e' : T) (c : List Claim)
    (hy : MoveYes X m e e' c) : KeepsDoor X e e' := by
  cases m with
  | add g =>
    obtain ⟨e₁, s, G, hg, hs, _, rfl⟩ := hy
    intro a ha
    obtain ⟨a₁, ha₁, c1, d1⟩ := hm e c e₁ hg a ha
    have es : a₁ = s := Option.some.inj (ha₁.symm.trans hs)
    subst es
    obtain ⟨a', h', l', d'⟩ := lens e₁ { a₁ with F := G } (by simp [ha₁])
    have l2 : a'.L = a₁.L := l'
    have d2 : a'.d.st = a₁.d.st := d'
    exact ⟨a', h', by rw [l2, c1], d2.trans d1⟩
  | quiet h => exact hm e e' hy.1

theorem moves_door : ∀ (ms : List (Move T)), (∀ m ∈ ms, MoveDoor X m) →
    ∀ (e e' : T) (c : List Claim), MovesYes X ms e e' c → KeepsDoor X e e'
  | [], _, e, e', c, hy => by
    obtain ⟨rfl, _⟩ := hy
    exact fun a ha => ⟨a, ha, rfl, rfl⟩
  | m :: l, hms, e, e', c, hy => by
    obtain ⟨u, c₁, c₂, h1, h2, _⟩ := hy
    exact keepsDoor_trans X (move_door X lens m (hms m List.mem_cons_self) e u c₁ h1)
      (moves_door l (fun q hq => hms q (List.mem_cons_of_mem _ hq)) u e' c₂ h2)

/-- A draw with moves behind it keeps the door; and K9's part is there in front. -/
theorem drawMoves_door {Cl : Type} (p : Where) (ms : List (Move T)) (b : Block T Cl)
    (hb : DrawMoves X p ms b) (hms : ∀ m ∈ ms, MoveDoor X m) (ft : ℕ) (s : T)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : ℕ)
    (h : b.step ft s rs cols = .ok (s', k)) :
    (X.get? s).isSome = true ∧ KeepsDoor X s s' := by
  obtain ⟨r, x, a, o, cls, _, _, ha, ho, hy⟩ := hb ft s rs cols s' k h
  have hck : o.L.check = a.L.check := (drawnClean_ok _ _ _ _ _ _ _ ho).2.2.2.2.2.2.2.2.2.1
  refine ⟨by simp [ha], keepsDoor_trans X ?_ (moves_door X lens ms hms _ _ _ hy)⟩
  intro a0 ha0
  have e0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  subst e0
  obtain ⟨a', h', l', d'⟩ :=
    lens s { a0 with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  have l2 : a'.L = o.L := l'
  exact ⟨a', h', by rw [l2, hck], d'⟩

end

variable {P K W Cl : Type}

theorem dataAt_door [CommRing K] (X : Lens T) (e e' : T) (h : KeepsDoor X e e')
    (hs : (X.get? e).isSome = true) (tab : Nat → OnBytes.Part → Nat → K) :
    dataAt X e' tab = dataAt X e tab := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨a', ha', c, d⟩ := h a ha
  exact dataAt_of_same X e e' a a' ha ha' (by rw [c]) (by rw [c])
    (by rw [d]; exact SameBits.refl _) tab

theorem groupHolds_door [CommRing K] (X : Lens T) (ρ : Reading K) (N : Nat) (e e' : T)
    (h : KeepsDoor X e e') (hs : (X.get? e).isSome = true)
    (tab : Nat → OnBytes.Part → Nat → K) (hh : GroupHoldsAt X ρ N e' tab) :
    GroupHoldsAt X ρ N e tab := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨a', ha', c, d⟩ := h a ha
  exact groupHolds_of_same X ρ N e e' a a' ha ha' c d tab hh

variable [Field K] [Fintype K] [DecidableEq K] {F : Frame}

/-- The conditions at the three boundaries. -/
def onPost (on0 : T × F.E.Str → Prop) (pb : Piece (ckP .two) F T Cl W) (j : ℕ) :
    ℕ → T × F.E.Str → Prop := fun i b' =>
  if i = j then on0 b'
  else if i = j + 1 then ∃ a τ, on0 a ∧ pb.ior.red.out a τ = some b'
  else True

/-- **Kind K9's two pieces in a row, four hypotheses paid down to each move's duty.** -/
theorem k9_row_moves_post (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)
    (p pw : Where) (ms : List (Termed T P K)) (d N j : ℕ) (HF : FitsM X O Fx p)
    (hms : ∀ m ∈ ms, MoveOk ρ X O Fx m) (hkd : ∀ m ∈ ms, MoveDoor X m.move) (b : Block T Cl)
    (hbm : DrawMoves X p (ms.map (·.move)) b)
    (hend : ∀ s s' cls, O.good s → MovesYes X (ms.map (·.move)) s s' cls →
      O.behind s' ∧ O.full s')
    (hok : ∀ s y, O.ready s → Desc.TermsOk K (termsOf (O.fixed s) y ms 0) d)
    (pb pe : Piece (ckP .two) F T Cl W)
    (hpb : pb.b = below b) (hpe : pe.b = below (K9.oneEquation X pw))
    (hextb : ∀ a τ w, pb.ext a τ w = w) (hexte : ∀ a τ w, pe.ext a τ w = w)
    (on0 : T × F.E.Str → Prop)
    (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K) (ctx : T × F.E.Str → W → Prop)
    (hready : ∀ a, on0 a → O.ready a.1)
    (hpin : ∀ a w w', on0 a → ctx a w → ctx a w' → tabOf a w = tabOf a w')
    (hcb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → ctx b' w → ctx a w)
    (hce : ∀ a τ b' w, pe.ior.red.out a τ = some b' → ctx b' w → ctx a w)
    (htabb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → tabOf b' w = tabOf a w)
    (htab : ∀ a τ b' w, pe.ior.red.out a τ = some b' → tabOf b' w = tabOf a w)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (hN : ∀ s, on0 s → ∀ a, X.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (inside : ∀ s, on0 s → ∀ a, X.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl)
    (hlog : ∀ r ∈ pb.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ pb.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => ρ.val (E.ofTriple (toU3 a)))
    (herr : Err.le (allErr (fun _ _ => d) 0 pb.ds) pb.err) :
    EachGoodIn (onPost on0 pb j) (relM ρ X O ms N tabOf ctx j) j [pb, pe] := by
  have o0 : ∀ a, onPost on0 pb j j a ↔ on0 a := fun a => by simp [onPost]
  have o1 : ∀ a, onPost on0 pb j (j + 1) a ↔ ∃ a₀ τ, on0 a₀ ∧ pb.ior.red.out a₀ τ = some a :=
    fun a => by simp [onPost]
  have hdoor : ∀ a τ b', pb.ior.red.out a τ = some b' →
      (X.get? a.1).isSome = true ∧ KeepsDoor X a.1 b'.1 := by
    intro a τ b' hout
    obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact drawMoves_door X lens p _ b hbm (fun m hm => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      exact hkd q hq) F.ft _ _ _ _ k hs
  refine k9_row_moves ρ X O Fx p pw ms d N j HF hms b hbm hend hok pb pe hpb hpe hextb hexte
    (onPost on0 pb j) tabOf ctx (fun a ha => hready a ((o0 a).1 ha))
    (fun a τ b' ha hout => (o1 b').2 ⟨a, τ, (o0 a).1 ha, hout⟩)
    (fun _ _ _ _ _ => by
      unfold onPost
      rw [if_neg (by omega), if_neg (by omega)]
      trivial)
    (fun a w w' ha => hpin a w w' ((o0 a).1 ha))
    (fun a τ b' w ha => hcb a τ b' w ((o0 a).1 ha))
    (fun a τ b' w _ => hce a τ b' w) ?_ ?_ (fun a τ b' w _ => htab a τ b' w) lens ?_ ?_
    hlog hback hinj herr
  · intro a τ b' w ha hout
    obtain ⟨h1, h2⟩ := hdoor a τ b' hout
    rw [htabb a τ b' w ((o0 a).1 ha) hout]
    exact dataAt_door X a.1 b'.1 h2 h1 _
  · intro a τ b' w ha hout hh
    obtain ⟨h1, h2⟩ := hdoor a τ b' hout
    rw [htabb a τ b' w ((o0 a).1 ha) hout] at hh
    exact groupHolds_door X ρ N a.1 b'.1 h2 h1 _ hh
  · intro s hs a ha
    obtain ⟨a₀, τ, h0, hout⟩ := (o1 s).1 hs
    obtain ⟨h1, h2⟩ := hdoor a₀ τ s hout
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨a', ha', _, dd⟩ := h2 x hx
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    subst e
    rw [dd]
    exact hN a₀ h0 x hx
  · intro s hs a ha
    obtain ⟨a₀, τ, h0, hout⟩ := (o1 s).1 hs
    obtain ⟨h1, h2⟩ := hdoor a₀ τ s hout
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨a', ha', cc, _⟩ := h2 x hx
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    subst e
    rw [cc]
    exact inside a₀ h0 x hx

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.moves_door
#print axioms VerifiableInference.Desc.K9L.drawMoves_door
#print axioms VerifiableInference.Desc.K9L.k9_row_moves_post
