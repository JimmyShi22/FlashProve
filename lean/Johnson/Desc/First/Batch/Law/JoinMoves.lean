-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/JoinMoves.lean
(kind K9's soundness lemma; the law of a link on the road of moves): THEOREM: THE JOINING, IN MOVES:
the statement LinkJoin.InMoves (Johnson/Desc/First/Link/Law/LinkJoin.lean) IS PROVED: three pieces
in a row: the batching's (a draw with the moves ms1 behind it), that of the block behind it (the
quiet moves ms2), the one equation's (in whatever dress), are good between that file's conditions
onJ and relations relJ, the batching's at the cap 128.
HOW. The first piece: Law/Row3Tools.lean: goodInQ_real at the sentence "the moves ms2 return some
state t from here and the ledger's one sum at t is 0": by value_at over ms1 ++ ms2 the drawn element
is then a root of the terms' polynomial. The second: moves_goodIn: t is the state behind; a row of
quiet moves adds no claim. The third: equation_goodIn_yes. The data and the open rows are carried
along the first two by the door's duty of each move.
  reach_pays, reach_facts   "reached from a state with on0" (that file's at1, at2) as an instance of
                the two free conditions on1, on2: it pays hs1, hN and inside from the two facts at
                on0 (h01, h12 hold there by definition).
  inMoves       the theorem.
Not claimed: any clause of JoinAsks at a segment of the protocol.

-/
import Johnson.Desc.First.Link.Law.LinkJoin
import Johnson.Desc.First.Batch.Law.Row3Tools

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (onJ relJ at1 at2 JoinAsks InMoves)
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {α W Cl : Type} {F : Frame}

/-- **"Reached from a state with on0" pays what the second and the third piece's laws spend of their
conditions in front**: a state behind the first piece has K9's part, and it and a state behind the
second keep the door of a state with on0. -/
theorem reach_pays (p : Where) (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E))
    (b₁ b₂ : Block S Cl) (pb pq : Piece (ckP .two) F S Cl W) (on0 : S × F.E.Str → Prop)
    (hkd : ∀ m ∈ ms₁ ++ ms₂, MoveDoor atS m.move)
    (hb₁ : DrawMoves atS p (ms₁.map (·.move)) b₁) (hb₂ : IsMoves atS (ms₂.map (·.move)) b₂)
    (hpb : pb.b = below b₁) (hpq : pq.b = below b₂) :
    (∀ b, at1 on0 pb b → ∃ a₀, on0 a₀ ∧ (atS.get? a₀.1).isSome = true ∧
      KeepsDoor atS a₀.1 b.1 ∧ (atS.get? b.1).isSome = true) ∧
    ∀ s, at2 on0 pb pq s → ∃ a₀, on0 a₀ ∧ (atS.get? a₀.1).isSome = true ∧
      KeepsDoor atS a₀.1 s.1 := by
  have lens : ∀ s a, (atS.get? s).isSome = true →
      ∃ a', atS.get? (atS.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st := fun s a h => by
    obtain ⟨a', e0, _, e2, e3⟩ := atS_reads s a h
    exact ⟨a', e0, e2, e3⟩
  have hkd₁ : ∀ m ∈ ms₁.map (·.move), MoveDoor atS m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hkd q (List.mem_append_left _ hq)
  have hkd₂ : ∀ m ∈ ms₂.map (·.move), MoveDoor atS m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hkd q (List.mem_append_right _ hq)
  have part₁ : ∀ b, at1 on0 pb b → ∃ a₀, on0 a₀ ∧ (atS.get? a₀.1).isSome = true ∧
      KeepsDoor atS a₀.1 b.1 ∧ (atS.get? b.1).isSome = true := by
    rintro b ⟨a₀, τ, h0, hout⟩
    obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    obtain ⟨h1, h2⟩ := drawMoves_door atS lens p _ b₁ hb₁ hkd₁ F.ft _ _ _ _ k hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨x', hx', _⟩ := h2 x hx
    exact ⟨a₀, h0, h1, h2, by simp [hx']⟩
  refine ⟨part₁, ?_⟩
  rintro c ⟨b, τ', hb, hout⟩
  obtain ⟨a₀, h0, h1, h2, _⟩ := part₁ b hb
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨rs', gs, hd⟩ := step_decide b₂ _ _ _ _ _ k hs
  obtain ⟨cls, hy⟩ := hb₂.dec _ _ _ _ hd
  exact ⟨a₀, h0, h1, keepsDoor_trans atS h2 (moves_door atS lens _ hkd₂ _ _ _ hy)⟩

/-- So the three clauses hs1, hN, inside of JoinAsks hold at on1 := at1, on2 := at2, where the two
facts hold at on0. -/
theorem reach_facts (p : Where) (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (N : ℕ)
    (b₁ b₂ : Block S Cl) (pb pq : Piece (ckP .two) F S Cl W) (on0 : S × F.E.Str → Prop)
    (hkd : ∀ m ∈ ms₁ ++ ms₂, MoveDoor atS m.move)
    (hb₁ : DrawMoves atS p (ms₁.map (·.move)) b₁) (hb₂ : IsMoves atS (ms₂.map (·.move)) b₂)
    (hpb : pb.b = below b₁) (hpq : pq.b = below b₂)
    (hN : ∀ s, on0 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (inside : ∀ s, on0 s → ∀ a, atS.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl) :
    (∀ b, at1 on0 pb b → (atS.get? b.1).isSome = true) ∧
    (∀ s, at2 on0 pb pq s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N) ∧
    ∀ s, at2 on0 pb pq s → ∀ a, atS.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl := by
  obtain ⟨p1, p2⟩ := reach_pays p ms₁ ms₂ b₁ b₂ pb pq on0 hkd hb₁ hb₂ hpb hpq
  refine ⟨fun b hb => (p1 b hb).choose_spec.2.2.2, fun s hs a ha => ?_,
    fun s hs a ha born name r hr => ?_⟩
  · obtain ⟨a₀, h0, h1, h2⟩ := p2 s hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨a', ha', _, dd⟩ := h2 x hx
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    subst e
    rw [dd]
    exact hN a₀ h0 x hx
  · obtain ⟨a₀, h0, h1, h2⟩ := p2 s hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨a', ha', cc, _⟩ := h2 x hx
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    subst e
    rw [cc] at hr
    exact inside a₀ h0 x hx born name r hr

/-- **The joining, in moves.** -/
theorem inMoves : InMoves := by
  intro α W Cl F φ Ok Fu p pw ms₁ ms₂ d N j b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx H
  have HF := fitsM_atS (K := Cb.Gl.E) φ H.hφ Ok Fu p
  have lens : ∀ s a, (atS.get? s).isSome = true →
      ∃ a', atS.get? (atS.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st := fun s a h => by
    obtain ⟨a', e0, _, e2, e3⟩ := atS_reads s a h
    exact ⟨a', e0, e2, e3⟩
  have hkd₁ : ∀ m ∈ ms₁.map (·.move), MoveDoor atS m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.hkd q (List.mem_append_left _ hq)
  have hkd₂ : ∀ m ∈ ms₂.map (·.move), MoveDoor atS m := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.hkd q (List.mem_append_right _ hq)
  have hq₂ : ∀ m ∈ ms₂.map (·.move), ∃ h, m = .quiet h := fun m hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact H.quiet q hq
  -- the conditions and the relations at the four boundaries
  have o0 : onJ on0 on1 on2 on3 j j = on0 := by
    funext a
    simp [onJ]
  have o1 : onJ on0 on1 on2 on3 j (j + 1) = on1 := by
    funext a
    simp [onJ]
  have o2 : onJ on0 on1 on2 on3 j (j + 1 + 1) = on2 := by
    funext a
    unfold onJ
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have o3 : onJ on0 on1 on2 on3 j (j + 1 + 1 + 1) = on3 := by
    funext a
    unfold onJ
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have r0 : relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx j j = fun a w =>
      (∃ y, boundAt atS tabOf ctx a w y ∧
        ∀ x ∈ termsOf ((O9 (K := Cb.Gl.E) φ Ok Fu).fixed a.1) y (ms₁ ++ ms₂) 0, x.2 = 0) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabOf a w) := by
    funext a w
    simp [relJ]
  have r1 : relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx j (j + 1) = fun a w =>
      ((∃ t, MovesYes atS (ms₂.map (·.move)) a.1 t [] ∧
          oneK atS Reading.gl t t (dataAt atS a.1 (tabOf a w)) = 0) ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabOf a w)) ∧ ctx a w := by
    funext a w
    simp [relJ]
  have r2 : relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx j (j + 1 + 1) = fun a w =>
      (oneK atS Reading.gl a.1 a.1 (dataAt atS a.1 (tabOf a w)) = 0 ∧
        GroupHoldsAt atS Reading.gl N a.1 (tabOf a w)) ∧ ctx a w := by
    funext a w
    unfold relJ
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have r3 : relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx j (j + 1 + 1 + 1) = fun a w =>
      GroupHoldsAt atS Reading.gl N a.1 (tabOf a w) ∧ ctx a w := by
    funext a w
    unfold relJ
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- the door's duty along the first two pieces
  have hdoor₁ : ∀ a τ b', pb.ior.red.out a τ = some b' →
      (atS.get? a.1).isSome = true ∧ KeepsDoor atS a.1 b'.1 := by
    intro a τ b' hout
    obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact drawMoves_door atS lens p _ b₁ H.hb₁ hkd₁ F.ft _ _ _ _ k hs
  have hyes₂ : ∀ a τ b', pq.ior.red.out a τ = some b' →
      MovesYes atS (ms₂.map (·.move)) a.1 b'.1 [] := by
    intro a τ b' hout
    obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpq hout
    obtain ⟨k, hs⟩ := fold_one hfold
    obtain ⟨rs', gs, hd⟩ := step_decide b₂ _ _ _ _ _ k hs
    obtain ⟨cls, hy⟩ := H.hb₂.dec _ _ _ _ hd
    rw [movesYes_quiet atS _ hq₂ _ _ _ hy] at hy
    exact hy
  have hdoor₂ : ∀ a τ b', pq.ior.red.out a τ = some b' → KeepsDoor atS a.1 b'.1 :=
    fun a τ b' hout => moves_door atS lens _ hkd₂ _ _ _ (hyes₂ a τ b' hout)
  -- the numbers of the first piece
  have hlog : ∀ r ∈ pb.ds, r.entry.logN ≤ 64 := by
    intro r hr
    rw [H.hds, List.mem_singleton] at hr
    rw [hr]
    exact Nat.zero_le 64
  have hheld : AllHeldEx (fun _ _ => d) ((2 : ℝ≥0∞)⁻¹ ^ 128) 0 pb.ds := by
    rw [H.hds]
    exact (allHeldEx_one (fun _ _ => d) _ 0 (k9Round p) 0 (dsOf_k9Round p)).2
      (num_k9 d (k9Round p).entry.work H.hd)
  have herr : Err.le (allErr (fun _ _ => d) 0 pb.ds) pb.err := by
    rw [H.hcap]
    exact herr_cap d pb.ds hlog hheld
  refine ⟨?_, ?_, ?_, trivial⟩
  · rw [o0, o1, r0, r1]
    refine goodIn_conseq pb (goodIn_and pb
      (goodInQ_real (semOf Reading.gl atS (O9 φ Ok Fu)) b₁
        (fun q y => termsOf q y (ms₁ ++ ms₂) 0) d H.hok
        (fun s' y => ∃ t, MovesYes atS (ms₂.map (·.move)) s' t [] ∧
          oneK atS Reading.gl t t y = 0)
        (fun s rs cols s' k hr _ hs => by
          obtain ⟨r, x, a, o, cls, rfl, hx, ha, ho, hy⟩ := H.hb₁ _ s rs cols s' k hs
          refine ⟨x, by simp [hx], fun y hQ => ?_⟩
          obtain ⟨t, ht, h0⟩ := hQ
          have hv := value_at Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p HF (ms₁ ++ ms₂) H.hms
            H.hend s t a o x (cls ++ []) hr ha ho (by
              rw [List.map_append]
              exact movesYes_append atS _ _ _ _ _ _ _ hy ht) y
          exact hv.symm.trans h0)
        pb H.hpb H.hextb on0 on1 (boundAt atS tabOf ctx) H.hready H.h01
        (fun a w w' y y' ha h1 h2 => by rw [h1.2, h2.2, H.hpin a w w' ha h1.1 h2.1])
        (fun a τ b' w y ha hout hB => ⟨H.hcb a τ b' w ha hout hB.1, by
          obtain ⟨h1, h2⟩ := hdoor₁ a τ b' hout
          rw [hB.2, H.htabb a τ b' w ha hout]
          exact dataAt_door atS a.1 b'.1 h2 h1 _⟩)
        hlog (fun r hr => by
          rw [H.hbk] at hr
          exact nomatch hr) reading_inj herr)
      (fun a τ b' w ha hout hq => by
        rw [H.hextb]
        obtain ⟨h1, h2⟩ := hdoor₁ a τ b' hout
        rw [H.htabb a τ b' w ha hout] at hq
        exact groupHolds_door atS Reading.gl N a.1 b'.1 h2 h1 _ hq))
      (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)
      (fun b' w _ h => ⟨⟨_, ⟨h.2, rfl⟩, h.1.1⟩, h.1.2⟩)
  · rw [o1, o2, r1, r2]
    refine moves_goodIn atS (ms₂.map (·.move)) b₂ H.hb₂ pq H.hpq H.hextq _ _ _ _
      H.h12 (fun a τ b' w cls ha hout _ h => ?_)
    have hs := H.hs1 a ha
    have hk := hdoor₂ a τ b' hout
    have ht := H.htabq a τ b' w ha hout
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [ht] at h1 h2
    rw [dataAt_door atS a.1 b'.1 hk hs _] at h1
    exact ⟨⟨⟨b'.1, hyes₂ a τ b' hout, h1⟩, groupHolds_door atS Reading.gl N a.1 b'.1 hk hs _ h2⟩,
      H.hcq a τ b' w ha hout h3⟩
  · rw [o2, o3, r2, r3]
    exact goodIn_and pe (equation_goodIn_yes atS Reading.gl pw N b₃ H.hb₃ pe H.hpe H.hexte
      on2 on3 tabOf H.hon3 H.htab lens H.hN H.inside)
      (fun a τ b' w ha hout hq => by
        rw [H.hexte]
        exact H.hce a τ b' w ha hout hq)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.reach_pays
#print axioms VerifiableInference.Desc.K9L.reach_facts
#print axioms VerifiableInference.Desc.K9L.inMoves
