-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsSeatedYes.lean: the lookup on the digits of a link's smallness test:
WHAT A YES OF THE SEATED BLOCK IS, AND WHAT IT TURNS: a yes of K3.theStated's value at the digits'
address is a yes of K3.block at the address's own arguments, at the front of the rounds shown, and
then a yes of K3.quietAt's step, or no step; so a yes of a piece that holds «below B'», B' any block
that narrows that value, leaves what SameBut names, and gives the lookup's promise behind from its
promise in front. Facts on the text: no premise on a filling, no letter of the table of joints.
Statements and proofs. A tie: no error term.

Main names.
  SameBut.trans.
  putFork_sameBut, headClaim_sameBut: laying a ledger where one is open, and laying the head's
    claim, turn nothing that SameBut names.
  k3OnOut_planClaims, k3OnOut_headClaim: nor what k3OnOut reads.
  theStated_yes_digits: WHAT A YES OF THE SEATED BLOCK IS.
  k3_digits_seated_turns: SameBut, and k3OnOut behind from k3OnIn in front, ACROSS THE STEP.
OBJECT. Desc.K3.theStated claim readers X codes shape a, at a.link = some i and a.piece = K3.pieceAt
X i true; K3.quietDigits, K3.quietHead.
USER. k3_digits_seated_leaves (K3DigitsSeatedLeaves.lean); k3_digits_row_seated_cut
(K3DigitsSeatedCut.lean).
LETTERS. claim, readers, X, codes, shape, a, B, B', i, x; q; u, v, τ.
IS IT EMPTY? The object's equations, hOk (a public Bool), hN, the piece's two, and a yes of the
piece. NOT TRIED AT A REAL PLACE.
(Where this and lean/THEOREM.md differ, the page holds.)

Limits. Nothing where the piece says no. SameBut says nothing of the rest of the open link's own
part: K3DigitsSeatedLeaves.lean says more.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsKeeps
import Johnson.Desc.First.Look.K3DigitsLookOut
import Johnson.Desc.First.Look.K3DigitsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

theorem SameBut.trans {s t u : Desc.First.S} (h : SameBut s t) (h' : SameBut t u) :
    SameBut s u where
  st := h'.st.trans h.st
  book := h'.book.trans h.book
  roots := h'.roots.trans h.roots
  rowsOwed := h'.rowsOwed.trans h.rowsOwed
  failed := h'.failed.trans h.failed
  check := h'.check.trans h.check
  out := h'.out.trans h.out
  req := h'.req.trans h.req
  link := h'.link.trans h.link
  sort := by
    rcases h.sort with ⟨a, b, e1, e2⟩ | ⟨a, b, e1, e2⟩ | ⟨a, b, e1, e2, o1, o2⟩ <;>
      rcases h'.sort with ⟨c, d, e3, e4⟩ | ⟨c, d, e3, e4⟩ | ⟨c, d, e3, e4, o3, o4⟩
    · exact Or.inl ⟨a, d, e1, e4⟩
    · rw [e2] at e3; cases e3
    · rw [e2] at e3; cases e3
    · rw [e2] at e3; cases e3
    · exact Or.inr (Or.inl ⟨a, d, e1, e4⟩)
    · rw [e2] at e3; cases e3
    · rw [e2] at e3; cases e3
    · rw [e2] at e3; cases e3
    · exact Or.inr (Or.inr ⟨a, d, e1, e4, o1, o4⟩)

/-- Laying a ledger where one is open turns nothing that SameBut names. -/
theorem putFork_sameBut (s : Desc.First.S) (F Gk : Fork) (hF : s.fork? = some F) :
    SameBut s (s.putFork Gk) := by
  cases hh : s.here with
  | between => simp [Desc.First.S.fork?, hh] at hF
  | fin _ => simp [Desc.First.S.fork?, hh] at hF
  | mem _ => simp [Desc.First.S.fork?, hh] at hF
  | lay a => constructor <;> simp [Desc.First.S.putFork, Desc.First.S.link?, hh]
  | att a => constructor <;> simp [Desc.First.S.putFork, Desc.First.S.link?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [Desc.First.S.fork?, hh, ho] at hF
    | true => constructor <;> simp [Desc.First.S.putFork, Desc.First.S.link?, hh, ho]

/-- Laying the head's claim turns nothing that SameBut names. -/
theorem headClaim_sameBut (s : Desc.First.S) (a : Desc.First.HeadOwn) (c : WsClaim)
    (ha : s.here = .head a) (ho : a.opened = true) :
    SameBut s { s with here := .head { a with claim := some c } } := by
  constructor <;> simp [Desc.First.S.link?, ha, ho]

/-- What the promise behind reads does not turn with the count of planned claims. -/
theorem k3OnOut_planClaims (p : Desc.First.Look.P) (s t : Desc.First.S) (F : Fork) (c : ℕ)
    (hF : s.fork? = some F) (hG : t.fork? = some { F with planClaimsF := c })
    (hh : Desc.K3.heardAt p.digits t = Desc.K3.heardAt p.digits s)
    (h : Desc.K3.k3OnOut p s = true) : Desc.K3.k3OnOut p t = true := by
  unfold Desc.K3.k3OnOut at h ⊢
  rw [hG, hh]
  rw [hF] at h
  cases hs : p.shape with
  | none =>
    rw [hs] at h
    cases h
  | some h₀ =>
    cases hg : Desc.K3.heardAt p.digits s with
    | none =>
      rw [hs, hg] at h
      cases h
    | some g =>
      rw [hs, hg] at h
      exact h

/-- Nor with the head's claim, at the digits. -/
theorem k3OnOut_headClaim (p : Desc.First.Look.P) (hdg : p.digits = true) (s : Desc.First.S)
    (a : Desc.First.HeadOwn) (c : WsClaim) (ha : s.here = .head a)
    (h : Desc.K3.k3OnOut p s = true) :
    Desc.K3.k3OnOut p { s with here := .head { a with claim := some c } } = true := by
  have e1 : ({ s with here := .head { a with claim := some c } } : Desc.First.S).fork? =
      s.fork? := by
    simp [Desc.First.S.fork?, ha]
  have e2 : Desc.K3.heardAt p.digits
      ({ s with here := .head { a with claim := some c } } : Desc.First.S) =
      Desc.K3.heardAt p.digits s := by
    rw [hdg]
    simp [Desc.K3.heardAt, Desc.First.S.tl?, ha]
  unfold Desc.K3.k3OnOut at h ⊢
  rw [e1, e2]
  exact h

theorem okRoundsE_take (rs : List Fmt.RoundView) (n : ℕ) (h : okRoundsE rs = true) :
    okRoundsE (rs.take n) = true := by
  unfold okRoundsE at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => h r (List.mem_of_mem_take hr)

section
variable {Cl : Type}

/-- **What a yes of the seated block is, at the digits' address.** -/
theorem theStated_yes_digits (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s c : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok c) :
    ∃ P sent laid n gs' s', placeAt X i true = some P ∧
      (Desc.K3.block (Desc.K3.seatDigits claim) a.piece laid sent P []).decide s (rs.take n) gs' =
        .ok s' ∧
      (c = s' ∨ ∃ f, Desc.K3.quietAt X i true = some f ∧ f s' = .ok c) := by
  obtain ⟨B₁, hB₁, -, e2, -, e4⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i', digits, P, sent, laid, hi', hpc', hP, -, -, -, r2, -, hpl⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  cases digits with
  | false => exact absurd (hpc'.symm.trans hpc) (pieceAt_neD X i)
  | true =>
    rw [e2] at hd
    rw [e4] at hOk
    rcases hW with ⟨-, rfl⟩ | ⟨f, hf, rfl⟩
    · rw [r2] at hd
      refine ⟨P, sent, laid, rs.length, gs, c, hP, ?_, Or.inl rfl⟩
      rw [List.take_length]
      exact Desc.K3.Law.blockVia_decide (hpl hOk) hd
    · have hOk' : b.planOk = true := by
        have h0 : (b.planOk && true) = true := hOk
        simpa using h0
      have hd' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
          (fun s' => f s') = .ok c := hd
      cases hb' : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
      | error e =>
        rw [hb'] at hd'
        cases hd'
      | ok s' =>
        rw [hb'] at hd'
        rw [r2] at hb'
        refine ⟨P, sent, laid, _, _, s', hP, Desc.K3.Law.blockVia_decide (hpl hOk') hb',
          Or.inr ⟨f, ?_, hd'⟩⟩
        simpa [hi, hpc] using hf

end

section
variable {Cl : Type} {Fr : Frame}

/-- **A yes of a piece that holds «below B'»**: nothing else turns; the promise behind holds. -/
theorem k3_digits_seated_turns {W : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B) (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (q : Piece (ckP .two) Fr Desc.First.S Cl W) (hq : q.b = below B') (hback : q.back = [])
    (u v : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds))
    (hout : q.ior.red.out u τ = some v) :
    SameBut u.1 v.1 ∧
      (Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 = true →
        Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) v.1 =
          true) := by
  obtain ⟨-, -, hw, cols, hd⟩ := piece_hears_below q B' hq hback u τ v hout
  obtain ⟨P', sent, laid, n, gs', s', hP, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc u.1 v.1 _ cols
      (hN.2 _ _ _ _ hd)
  have eP : P' = (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) := by
    unfold placeAt at hP
    rw [hlook] at hP
    exact (Option.some.inj hP).symm
  subst eP
  have hS := k3_digits_sameBut claim a.piece laid sent _ [] u.1 s' _ gs' hyes
  have hO : Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 =
      true →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) s' = true :=
    fun hIn => k3_digits_lookOut claim a.piece laid sent _ [] hsh rfl u.1 s' _ gs'
      (okRoundsE_take _ n hw) hyes hIn
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact ⟨hS, hO⟩
  · unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, ho, e⟩ := Desc.K3.quietHead_ok X s' v.1 hfs
      rw [e]
      exact ⟨hS.trans (headClaim_sameBut s' ah c ha ho),
        fun hIn => k3OnOut_headClaim _ rfl s' ah c ha (hO hIn)⟩
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, hF, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' v.1 hfs
         obtain ⟨F₂, hF₂, hG₂⟩ := Desc.K3.quietDigits_fork _ _ s' v.1 hfs
         obtain rfl : F = F₂ := Option.some.inj (hF.symm.trans hF₂)
         have hh : Desc.K3.heardAt true v.1 = Desc.K3.heardAt true s' := by
           rw [e]
           simp [Desc.K3.heardAt, tl_putFork]
         exact ⟨hS.trans (e ▸ putFork_sameBut s' F _ hF),
           fun hIn => k3OnOut_planClaims _ s' v.1 F _ hF hG₂ hh (hO hIn)⟩)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.theStated_yes_digits
#print axioms VerifiableInference.OnPublicFiles.k3_digits_seated_turns
