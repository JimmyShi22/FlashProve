-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/HeadClaim.lean: what the plain text of the head's claim on the weights returns; and so what that claim says at the typed record, in an index's own output matrix.

Johnson/Desc/First/Look/LookQuiet.lean writes the step behind the lookup on the digits at the head's link as a plain function, weightsClaim R lay : Except String WsClaim. Johnson/Road/HeadWeight.lean has
the like of the verifier program's routine, which runs in a context (weightsClaim_ok); nothing of that theorem is spent here. Its two DEFINITIONS avOf (the vector on the vocabulary, as a fold) and facKK
(the factor on the channels) are pure functions, and are used.
    weightsClaim_is    where the plain text returns, and the layout's last unit has the two groups x and kk: the claim is { ui := the last unit, f := [{ AV := avOf R ew }, facKK rs z o lamS] }, ew the
                       weights of the segment HD0's entries as the text reckons them (ewAt); and the checked token of every covered position is an entry of the vocabulary
    weightsClaim_head  at the reference parameters (SizedW; wsLayOf at kRef; lamS = 13): it is headClaim lay (avOf R ew) rs (HeadSays.lean)
    plain_head_says    so: at the record G, where the state's factors are that claim's, read, and the cells of W among the entries hold an index i's digit matrix, carried into the field:
                       the typed claim holds  ⇔  the sum over the vocabulary and the channels of avOf[v] * eq(rs, k) * i.index.val.H k v + (the mask entry) * be = sh
SPENT OF THE LIBRARY: OnBytes.Road.Hd.head_unit (Johnson/Road/HeadWeight.lean) · OnBytes.Road.getD_of_some (Johnson/Road/FormsKeysPan.lean) · the field d of SizedW: on pure functions and plain records.
ALSO SPENT: Johnson/Desc/First/Look/LookQuiet.lean (its definition weightsClaim).
Held by a run beside the proofs, at the small size alone: at the record that a stored proof leaves in front of the merge, the claim that the record carries is what the plain text returns and is the closed
form in avOf and facKK; with the coordinates turned round, or 1 added to AV[0], it is not. In that run the carried claim had been laid by a step that calls the verifier program's routine, not by the plain text: so that step's file says of itself; the step's text was not read.
Limits: one direction: from the text's return. What avOf's members are in closed form is OnBytes.Road.Hd.avOf_value's. That R is the run's record of a description's state is not said here. Identities alone: no
random step. On hiding nothing.

-/
import Johnson.Desc.First.Look.LookQuiet
import Johnson.Top.H0.K11Caller.HeadSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes
open OnBytes.Model (WsLay WsClaim WsGrp WsFac eqTab eqLow)
open OnBytes.Model (Reading WsShape wsLayOf wsClaimShape)
open OnBytes.Road (Numerals SizedW eqR shapeOf placeP)
open OnBytes.Road.Hd (facKK avOf avFold avStep head_unit askH)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (nV nD)
open Finset

/-- The rule for a loop over a list of numbers in Except. -/
theorem ex_forIn_list {β ε : Type} (f : ℕ → β → Except ε (ForInStep β)) (I : ℕ → β → Prop) (n : ℕ)
    (step : ∀ x b r, x < n → I x b → f x b = .ok r → ∃ b', r = ForInStep.yield b' ∧ I (x + 1) b') :
    ∀ (k s : ℕ) (b b' : β), s + k ≤ n → I s b → forIn (List.range' s k) b f = .ok b' → I (s + k) b'
  | 0, s, b, b', _, h0, h => by
    have e : b = b' := by simpa [pure, Except.pure] using h
    rw [← e]
    exact h0
  | k + 1, s, b, b', hk, h0, h => by
    rw [List.range'_succ, List.forIn_cons] at h
    cases hr : f s b with
    | error e =>
      rw [hr] at h
      cases h
    | ok r =>
      rw [hr] at h
      obtain ⟨b1, rfl, h1⟩ := step s b r (by omega) h0 hr
      have h2 := ex_forIn_list f I n step k (s + 1) b1 b' (by omega) h1 h
      rwa [show s + 1 + k = s + (k + 1) by omega] at h2

theorem ex_forIn_range {β ε : Type} (n : ℕ) (f : ℕ → β → Except ε (ForInStep β)) (I : ℕ → β → Prop)
    (step : ∀ x b r, x < n → I x b → f x b = .ok r → ∃ b', r = ForInStep.yield b' ∧ I (x + 1) b')
    {b b' : β} (h0 : I 0 b) (h : forIn [:n] b f = .ok b') : I n b' := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have e : List.range' ([:n] : Std.Legacy.Range).start ([:n] : Std.Legacy.Range).size ([:n] : Std.Legacy.Range).step = List.range' 0 n := by
    simp [Std.Legacy.Range.size]
  rw [e] at h
  have h3 := ex_forIn_list f I n step n 0 b b' (by omega) h0 h
  rwa [Nat.zero_add] at h3

theorem thr_bind {α β : Type} (e : String) (f : α → Except String β) (b : β) : ¬ ((throw e : Except String α) >>= f) = .ok b := by
  intro h
  cases h

theorem avFold_succ (on : Array Bool) (win : Array ℕ) (wx : E) (eH A0 : Array E) (t : ℕ) :
    avFold on win wx eH A0 (t + 1) = avStep on win wx eH (avFold on win wx eH A0 t) t := by
  unfold avFold
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The weights of the entries of the segment HD0, as the plain text reckons them. -/
def ewAt (R : Model.Head.Run) (q : ℕ) (g : Model.Seg) : Array E :=
  g.pos.map fun p => (eqTab (Model.Head.zjOf R.L R.x.g1 q)).getD p zeroE

/-- **What the plain text weightsClaim returns**, where the layout's last unit has the two groups x and kk. -/
theorem weightsClaim_is {R : Model.Head.Run} {lay : WsLay} {cl : WsClaim} (h : Look.weightsClaim R lay = .ok cl) {gx gk : WsGrp}
    (hg : (lay.U.getD (lay.U.size - 1) default).g = [gx, gk]) (hx : gx.name = "x") (hkk : gk.name = "kk") :
    ∃ q g, Model.Head.callNo R.L "HD0" = some q ∧ (R.L.calls.getD q default).seg? "HD0" = some g ∧
      cl = { ui := lay.U.size - 1, f := [{ AV := avOf R (ewAt R q g) }, facKK R.x.rs gk.z gk.o R.hp.lamS] } ∧
      ∀ t, t < R.h.T → R.cov.hOn.getD t false = true → R.x.win.getD t 0 < R.h.V := by
  unfold Look.weightsClaim at h
  dsimp only at h
  cases hq : Model.Head.callNo R.L "HD0" with
  | none =>
    rw [hq] at h
    exact absurd h (thr_bind _ _ _)
  | some q =>
    rw [hq] at h
    dsimp only at h
    rw [pure_bind] at h
    cases hs : (R.L.calls.getD q default).seg? "HD0" with
    | none =>
      rw [hs] at h
      exact absurd h (thr_bind _ _ _)
    | some g =>
      rw [hs] at h
      dsimp only at h
      rw [pure_bind] at h
      split at h
      · exact absurd h (thr_bind _ _ _)
      · rw [pure_bind, hg] at h
        have e1 : (gx.name == "x") = true := by rw [hx]; rfl
        have e2 : (gk.name == "x") = false := by rw [hkk]; decide
        have e3 : (gk.name == "kk") = true := by rw [hkk]; rfl
        simp only [List.forIn_cons, List.forIn_nil, e1, e2, e3, if_true, Bool.false_eq_true, if_false] at h
        generalize hL : (forIn [:R.h.T] _ _ : Except String (Array E)) = L at h
        cases L with
        | error e => simp [bind, Except.bind] at h
        | ok AV =>
          simp only [bind, Except.bind, pure, Except.pure, List.nil_append, List.cons_append] at h
          have hcl := (Except.ok.inj h).symm
          have hI := ex_forIn_range R.h.T _
            (fun t A => A = avFold R.cov.hOn R.x.win (Model.Head.wxOf R (ewAt R q g)) (eqTab R.x.tH.r)
                ((Array.range R.h.V).map fun v => subE zeroE (mulE (Model.Head.onSum R R.x.tH.r) ((ewAt R q g).getD v zeroE))) t ∧
              ∀ t', t' < t → R.cov.hOn.getD t' false = true → R.x.win.getD t' 0 < R.h.V)
            ?_ ⟨rfl, fun t' ht' => absurd ht' (Nat.not_lt_zero t')⟩ hL
          · exact ⟨q, g, rfl, hs, by rw [hcl, hI.1]; rfl, hI.2⟩
          · intro x b r _ hb hr
            obtain ⟨hb1, hb2⟩ := hb
            by_cases hon : R.cov.hOn.getD x false = true
            · rw [if_pos hon] at hr
              by_cases hv : R.x.win.getD x 0 < R.h.V
              · have hd : (!decide (R.x.win.getD x 0 < R.h.V)) = false := by rw [decide_eq_true hv]; rfl
                rw [if_neg (by rw [hd]; exact Bool.false_ne_true)] at hr
                refine ⟨_, (Except.ok.inj hr).symm, ?_, ?_⟩
                · rw [avFold_succ, ← hb1]
                  unfold avStep
                  rw [if_pos hon]
                  rfl
                · intro t' ht' h1
                  rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h2 | h2
                  · exact hb2 t' h2 h1
                  · rw [h2]
                    exact hv
              · have hd : (!decide (R.x.win.getD x 0 < R.h.V)) = true := by rw [decide_eq_false hv]; rfl
                rw [if_pos hd] at hr
                exact absurd hr (thr_bind _ _ _)
            · rw [if_neg hon] at hr
              refine ⟨_, (Except.ok.inj hr).symm, ?_, ?_⟩
              · rw [avFold_succ, ← hb1]
                unfold avStep
                rw [if_neg hon]
              · intro t' ht' h1
                rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h2 | h2
                · exact hb2 t' h2 h1
                · rw [h2] at h1
                  exact absurd h1 hon

/-- **At the reference parameters the plain text's claim is headClaim.** -/
theorem weightsClaim_head {s : WsShape} (Z : SizedW s ppref) {lay : WsLay} (h : wsLayOf s true kRef = .ok lay)
    {R : Model.Head.Run} {cl : WsClaim} (hk : Look.weightsClaim R lay = .ok cl) (hlam : R.hp.lamS = 13) :
    ∃ q g, Model.Head.callNo R.L "HD0" = some q ∧ (R.L.calls.getD q default).seg? "HD0" = some g ∧
      cl = headClaim lay (avOf R (ewAt R q g)) R.x.rs ∧
      ∀ t, t < R.h.T → R.cov.hOn.getD t false = true → R.x.win.getD t 0 < R.h.V := by
  obtain ⟨o, hu⟩ := head_unit h
  have hd : (shapeOf s true).d = 5120 := Z.d
  have hg : (lay.U.getD (lay.U.size - 1) default).g =
      placeP [WsLay.A_ "x" (shapeOf s true).V, WsLay.E_ "kk" 5120 false] kRef 0 := by
    rw [OnBytes.Road.getD_of_some hu default]
    unfold askH
    rw [hd]
    rfl
  obtain ⟨q, g, h1, h2, hcl, hw⟩ := weightsClaim_is hk hg rfl rfl
  refine ⟨q, g, h1, h2, ?_, hw⟩
  rw [hcl, hlam]
  rfl

/-- **What the plain text's claim says at the typed record, in an index's own output matrix.** -/
theorem plain_head_says {E' : Type} [Field E'] [Fintype E'] {ρ : Reading E'} (hρ : Numerals ρ) {s : WsShape} (Z : SizedW s ppref) (P : Place)
    (h : wsLayOf s true kRef = .ok P.lay) (a : Fin P.n) (T : Letters E' P) (st : T.St) (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    {R : Model.Head.Run} (hk : Look.weightsClaim R P.lay = .ok (cl a)) (hlam : R.hp.lamS = 13) (hs : 13 ≤ R.x.rs.size) (F : Fit ρ P T st cl)
    (i : Cm.Idx) (hW : ∀ rc : P.Cell, m (.inl rc) = ((i.mat rc.1.val rc.2.val : ℤ) : E')) :
    ∃ q g, Model.Head.callNo R.L "HD0" = some q ∧ (R.L.calls.getD q default).seg? "HD0" = some g ∧
      ((G P T).Cl st m a ↔
        ∑ v ∈ range nV, ∑ k ∈ range nD,
          ρ.val ((avOf R (ewAt R q g)).getD v zeroE) * eqR ρ R.x.rs 0 13 k * ((i.index.val.H k v : ℤ) : E') +
          m (.inr (T.nm a)) * (T.rd st).be a = (T.rd st).sh a) := by
  obtain ⟨q, g, h1, h2, hcl, -⟩ := weightsClaim_head Z h hk hlam
  exact ⟨q, g, h1, h2, G_head_says_idx hρ Z P h a T st m cl _ _ hs hcl F i hW⟩

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.weightsClaim_is
#print axioms VerifiableInference.Desc.First.K11Caller.weightsClaim_head
#print axioms VerifiableInference.Desc.First.K11Caller.plain_head_says
