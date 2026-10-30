-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Row3Tools.lean
(kind K9's soundness lemma): TOOLS FOR A ROW OF THREE PIECES ON THE ROAD OF MOVES: the batching's
block (a draw with moves behind it), A BLOCK OF ITS OWN THAT HOLDS FURTHER MOVES, the one equation's
block. General in the state and the lens.
  goodInQ, goodInQ_real   the law of the draw's piece (Law/LawF.lean: goodInF) WITH A FREE SENTENCE
                Q BEHIND in the place of "the one sum at the state behind the block is 0". Asked of
                the block: a yes of its step and Q of the state behind make the drawn element a root
                of the terms' polynomial. The proof is goodInF's.
  value_at      from the draw's yes and a yes of A ROW OF MOVES from the state behind the draw to a
                state t, with "full" behind the last move: the ledger's one sum at t is the terms'
                polynomial at the drawn element. (Law/Moves.lean: valueF_moves without its block.)
  movesYes_quiet   a row of quiet moves adds no claim.
  step_decide   a yes of a block's step holds a yes of its decision.
  moves_goodIn  a piece whose block is a row of moves (Law/MovesRow.lean: IsMoves) is good, at any
                errors, between two relations of which the one behind gives the one in front along a
                yes of the moves.
  equation_goodIn_yes   the one equation's piece (Law/DoorFacts.lean: equation_goodIn') for ANY
                BLOCK OF WHOSE STEP A YES IS A YES OF THE ONE EQUATION's, with the same return: a
                dress, or a guard that only adds refusals.

-/
import Johnson.Desc.First.Batch.Law.RowMoves
import Johnson.Desc.First.Batch.Law.MovesRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens Where drawnClean)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err Doomed)

section
variable {S Cl Cb W P Y K : Type} {C : CK} {F : Frame}
variable [Field K] [Fintype K] [DecidableEq K]

/-- **The law of the draw's piece, with a free sentence behind.** -/
theorem goodInQ (X : LinkSem K S Cl P Y) (b : Block S Cb) (terms : P → Y → List (ℕ × K)) (d : ℕ)
    (hok : ∀ s y, X.ready s → Desc.TermsOk K (terms (X.fixed s) y) d) (Q : S → Y → Prop)
    (hval : ∀ s rs cols s' k, X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true →
      b.step F.ft s rs cols = .ok (s', k) →
      ∃ x, rs.flatMap (·.drawn.elems) = [x] ∧
        ∀ y, Q s' y → termsAt K (terms (X.fixed s) y) (X.rd x) = 0)
    (p : Piece C F S Cb W) (hb : p.b = below b) (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : S × F.E.Str → Prop) (Bnd : S × F.E.Str → W → Y → Prop)
    (hready : ∀ a, on a → X.ready a.1)
    (hhands : ∀ a τ b', on a → p.ior.red.out a τ = some b' → on' b')
    (huniq : ∀ a w w' y y', on a → Bnd a w y → Bnd a w' y' → y = y')
    (hcarry : ∀ a τ b' w y, on a → p.ior.red.out a τ = some b' → Bnd b' w y → Bnd a w y)
    (hreads : p.Reads X.rd d) :
    p.GoodIn on on' (fun a w => ∃ y, Bnd a w y ∧ ∀ x ∈ terms (X.fixed a.1) y, x.2 = 0)
      (fun b' w => ∃ y, Bnd b' w y ∧ Q b'.1 y) := by
  have hcard : ∀ a, (badAtF X terms on Bnd a).card ≤ d := by
    intro a
    unfold badAtF
    split
    · next h => exact badF_card_le _ d (hok a.1 _ (hready a h.1))
    · simp
  refine goodInOfBadFam S Cb W C F p on on' _ _
    (fun a => Classical.choose (hreads _ (hcard a) a.2)) ?_ ?_ ?_
  · intro a _
    exact (Classical.choose_spec (hreads _ (hcard a) a.2)).1
  · intro a τ b' ha _ hout
    exact hhands a τ b' ha hout
  · rintro a τ b' w ha hclean hout ⟨y, hB, hone⟩
    rw [hext]
    have hBa := hcarry a τ b' w y ha hout hB
    refine ⟨y, hBa, ?_⟩
    obtain ⟨hp, hw, hfold⟩ := Piece.out_below hb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    obtain ⟨x, hx, hv⟩ := hval _ _ _ _ _ (hready a ha) hw hs
    have hnb := (Classical.choose_spec (hreads _ (hcard a) a.2)).2 τ hclean hp x hx
    have hex : on a ∧ ∃ y, ∃ w, Bnd a w y := ⟨ha, y, w, hBa⟩
    have hy : Classical.choose hex.2 = y := by
      obtain ⟨w', hw'⟩ := Classical.choose_spec hex.2
      exact huniq a w' w _ _ ha hw' hBa
    unfold badAtF at hnb
    rw [dif_pos hex, hy] at hnb
    exact zero_of_root _ _ (hv y hone) hnb

/-- The same at the format's own kit of challenges, from the degree alone. -/
theorem goodInQ_real (X : LinkSem K S Cl P Y) (b : Block S Cb) (terms : P → Y → List (ℕ × K))
    (d : ℕ) (hok : ∀ s y, X.ready s → Desc.TermsOk K (terms (X.fixed s) y) d) (Q : S → Y → Prop)
    (hval : ∀ s rs cols s' k, X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true →
      b.step F.ft s rs cols = .ok (s', k) →
      ∃ x, rs.flatMap (·.drawn.elems) = [x] ∧
        ∀ y, Q s' y → termsAt K (terms (X.fixed s) y) (X.rd x) = 0)
    (p : Piece (ckP .two) F S Cb W) (hb : p.b = below b) (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : S × F.E.Str → Prop) (Bnd : S × F.E.Str → W → Y → Prop)
    (hready : ∀ a, on a → X.ready a.1)
    (hhands : ∀ a τ b', on a → p.ior.red.out a τ = some b' → on' b')
    (huniq : ∀ a w w' y y', on a → Bnd a w y → Bnd a w' y' → y = y')
    (hcarry : ∀ a τ b' w y, on a → p.ior.red.out a τ = some b' → Bnd b' w y → Bnd a w y)
    (hlog : ∀ r ∈ p.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ p.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => X.rd (toU3 a))
    (herr : Err.le (allErr (fun _ _ => d) 0 p.ds) p.err) :
    p.GoodIn on on' (fun a w => ∃ y, Bnd a w y ∧ ∀ x ∈ terms (X.fixed a.1) y, x.2 = 0)
      (fun b' w => ∃ y, Bnd b' w y ∧ Q b'.1 y) :=
  goodInQ X b terms d hok Q hval p hb hext on on' Bnd hready hhands huniq hcarry
    (reads_allErr p X.rd d hlog hback hinj herr)

end

section
variable {T P K : Type}

/-- **The one sum behind a row of moves is the terms' polynomial at the drawn element.** -/
theorem value_at [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)
    (p : Where) (H : FitsM X O Fx p) (ms : List (Termed T P K))
    (hms : ∀ m ∈ ms, MoveOk ρ X O Fx m)
    (hend : ∀ s s' cls, O.good s → MovesYes X (ms.map (·.move)) s s' cls →
      O.behind s' ∧ O.full s')
    (s t : T) (a : K9.Part) (o : K9.Drawn) (x : Fmt.Ext) (cls : List Claim) (hr : O.ready s)
    (ha : X.get? s = some a)
    (ho : drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o)
    (hy : MovesYes X (ms.map (·.move)) (X.set s { a with owed := o.owed, L := o.L, F := o.F }) t
      cls) (y : Bound K) :
    oneK X ρ t t y = termsAt K (termsOf (O.fixed s) y ms 0) (ρ.val (E.ofTriple x)) := by
  obtain ⟨d1, d2, d3, _, _, _, _, _, _, _, _, d12⟩ := drawnClean_ok _ _ _ _ _ _ _ ho
  obtain ⟨a₁, ha₁, hF⟩ := H.lens s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  have hF' : a₁.F = o.F := hF
  obtain ⟨f1, g1⟩ := H.atDraw s a o x hr ha ho
  obtain ⟨b', A⟩ := moves_adv ρ X O Fx p H (O.fixed s) ms hms _ t a₁ cls f1 g1 ha₁
    (by rw [hF']; exact d12) hy
  obtain ⟨_, e2⟩ := hend _ _ _ g1 hy
  have hsum := A.sum t y ⟨rfl, H.moreRefl t, rfl⟩ e2
  rw [hF', d2, d3] at hsum
  rw [← hsum, wsumK_eq X ρ t b' A.part]
  simp only [oneK, A.part]
  rw [A.total, hF', total_of_empty ρ _ o.F d1, zero_add, d2, d3, A.plan, hF']

/-- A row of quiet moves adds no claim. -/
theorem movesYes_quiet (X : Lens T) : ∀ (ms : List (Move T)), (∀ m ∈ ms, ∃ h, m = .quiet h) →
    ∀ (t t' : T) (cls : List Claim), MovesYes X ms t t' cls → cls = []
  | [], _, _, _, _, hy => hy.2
  | m :: l, hq, t, t', cls, hy => by
    obtain ⟨u, c, c', h1, h2, rfl⟩ := hy
    obtain ⟨h, rfl⟩ := hq m List.mem_cons_self
    have e1 : c = [] := h1.2
    rw [e1, movesYes_quiet X l (fun q hq' => hq q (List.mem_cons_of_mem _ hq')) u t' c' h2]
    rfl

end

section
variable {T W K Cl : Type} {C : CK} {F : Frame}

/-- A yes of a block's step holds a yes of its decision. -/
theorem step_decide (b : Block T Cl) (ft : ℕ) (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T)
    (k : ℕ) (h : b.step ft s rs cols = .ok (s', k)) : ∃ rs' gs, b.decide s rs' gs = .ok s' := by
  unfold Block.step at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨t, ht, h⟩ := ok_bind h
  have e : t = s' := congrArg Prod.fst (Except.ok.inj h)
  subst e
  exact ⟨_, _, ht⟩

/-- **A piece whose block is a row of moves is good**, at any errors, along a carry. -/
theorem moves_goodIn (X : Lens T) (ms : List (Move T)) (b : Block T Cl) (hbm : IsMoves X ms b)
    (p : Piece C F T Cl W) (hb : p.b = below b) (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop)
    (hhands : ∀ a τ b', on a → p.ior.red.out a τ = some b' → on' b')
    (hcarry : ∀ a τ b' w cls, on a → p.ior.red.out a τ = some b' → MovesYes X ms a.1 b'.1 cls →
      R' b' w → R a w) : p.GoodIn on on' R R' := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ b' hout => ⟨hhands a τ b' ha hout, ?_⟩
  intro w hw
  rw [hext]
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hstep⟩ := fold_one hfold
  obtain ⟨rs', gs, hd⟩ := step_decide b _ _ _ _ _ k hstep
  obtain ⟨cls, hy⟩ := hbm.dec _ _ _ _ hd
  exact hcarry a τ b' w cls ha hout hy hw

/-- **The one equation's piece, for any block of whose step a yes is a yes of the one equation's.**
-/
theorem equation_goodIn_yes [CommRing K] (X : Lens T) (ρ : Reading K) (pw : K9.Where) (N : Nat)
    (b₃ : Block T Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) X pw).step ft s rs cols = .ok x)
    (p : Piece C F T Cl W) (hb : p.b = below b₃) (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : T × F.E.Str → Prop) (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (hcarry : ∀ a τ b w, on a → p.ior.red.out a τ = some b → tabOf b w = tabOf a w)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (hN : ∀ s, on s → ∀ a, X.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (inside : ∀ s, on s → ∀ a, X.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ b ∈ r.blocks, Inside r b) :
    p.GoodIn on on'
      (fun a w => oneK X ρ a.1 a.1 (dataAt X a.1 (tabOf a w)) = 0 ∧
        GroupHoldsAt X ρ N a.1 (tabOf a w))
      (fun b w => GroupHoldsAt X ρ N b.1 (tabOf b w)) := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ b hout => ⟨hhands a τ b ha hout, ?_⟩
  intro w hw
  rw [hext]
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hstep0⟩ := fold_one hfold
  have hstep := hb₃ _ _ _ _ _ hstep0
  rw [hcarry a τ b w ha hout] at hw
  obtain ⟨a0, out, ha0, hdoor, _⟩ := oneEquation_inv X pw F.ft a.1 _ _ b.1 k hstep
  refine oneEquation_joint X ρ pw F.ft a.1 _ _ b.1 k N (tabOf a w) lens (fun a1 q G h1 hq => ?_)
    hstep hw
  have e : a1 = a0 := Option.some.inj (h1.symm.trans ha0)
  subst e
  exact door_facts _ _ _ _ _ out N (hN a ha a1 h1) (inside a ha a1 h1) hdoor q G hq

end

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.goodInQ_real
#print axioms VerifiableInference.Desc.K9L.value_at
#print axioms VerifiableInference.Desc.K9L.movesYes_quiet
#print axioms VerifiableInference.Desc.K9L.moves_goodIn
#print axioms VerifiableInference.Desc.K9L.equation_goodIn_yes
