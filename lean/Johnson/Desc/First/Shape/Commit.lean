-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Commit.lean: A COMMITMENT (a segment's later moment, the kind K1: each
link's reads and digits) AS A MEMBER OF THE FIRST CHAIN, ON THE CHAIN's SHAPE: one step, and its
two laws at the block's own decision (K1.commitAtS, Johnson/Desc/K1/AtS.lean). General laws;
nothing is evaluated.

  1 `stepG`, **`commitStep_sh`**: L3.commitStep around K1.laterOwn, behind the sending's return,
    and its step on shapes commute.
  2 `setLed_same`, `commitStepG`, **`commit_sq`**: where the sending
    returns, the member's decision and its step on the chain's shape commute.
  3 **`commitG`**: the sending's Bool (sendB, SendCore.lean), then the step. `laterOwn_inv`,
    `commit_inv`: a yes has the sending's return in it. **`commit_carries_strong`**: behind a yes
    commitStepG returns the shape behind. **`commit_carries`**: where the member says yes and
    commitG returns, it returns the shape behind. **`commit_returns`**: where commitG returns, the
    member says yes on two rounds in which no seed's factor is 0 and round 2 holds as many answers
    as the place counts, with that shape behind.

The step reads the shape alone: the marks "this array has a root" lie in the ledger's shape
(Parts.lean: TreeSh.rooted).

Limits. The bare block: the quiet steps that a description lays behind it by Block.andThen, the
guard on the mark and the comparison of the reply are not in it. The converse of commit_returns
fails by the sending's tests on the plan alone (K1.planOkOwn, the pads), which a yes does not give
back. The two premises on the rounds stand as in SendCore.lean. No state is shown at which commitG
returns. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Later

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState GPar groundG)
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh)

/-! ## 1 The commitment's step behind its sending -/

/-- L3.commitStep around K1.laterOwn, behind the sending, on shapes. L: the link's context in front;
Ld: the ledger's shape; h: the core BEHIND the sending. -/
def stepG (P : K1.Par) (n0 : Nat) (ts : List Nat) (L : LinkSh) (Ld : LedSh) (h : CoreSh) :
    Option (LinkSh × LedSh × CoreSh) :=
  if !(!L.handed && !L.done) then none
  else if !(L.link == L.check.link) then none
  else (laterG P n0 L.check h).bind fun x =>
    (commitAllG L ts Ld).bind fun rt' =>
      if ts.length == (L3.laidHere L.blank).length then
        some ({ L with check := x.1, moments := L.moments + 1 }, rt', x.2)
      else none

theorem commitStep_sh (P : K1.Par) (owed : Option Nat) (ts : List Nat) (x : L3.St (DState Unit))
    (rs : List Fmt.RoundView) (n0 : Nat) (d₁ : DState Unit)
    (hs : K1.decideSend P owed x.w rs = .ok (idsAt P n0, d₁)) :
    (L3.commitStep (K1.laterOwn P owed) ts x rs).toOption.map
        (fun y => (linkSh y.L, ledSh y.F, coreSh (coreOf y.w))) =
      stepG P n0 ts (linkSh x.L) (ledSh x.F) (coreSh (coreOf d₁)) := by
  have h1 := laterOwn_sh P owed x.L.check x.w d₁ rs n0 hs
  have h2 := commitAll_sh x.L ts x.F
  unfold L3.commitStep L3.commitFront stepG
  show _ = (if !(!x.L.handed && !x.L.done) then none
    else if !(x.L.link == x.L.check.link) then none
    else (laterG P n0 (checkSh x.L.check) (coreSh (coreOf d₁))).bind fun z =>
      (commitAllG (linkSh x.L) ts (ledSh x.F)).bind fun rt' =>
        if ts.length == (L3.laidHere x.L).length then
          some ({ linkSh x.L with check := z.1, moments := x.L.moments + 1 }, rt', z.2)
        else none)
  by_cases g1 : (!(!x.L.handed && !x.L.done)) = true
  · simp only [g1, if_true]
    rfl
  · by_cases g2 : (!(x.L.link == x.L.check.link)) = true
    · simp only [g1, g2, Bool.false_eq_true, if_false, if_true]
      rfl
    · simp only [g1, g2, Bool.false_eq_true, if_false]
      rw [← h1]
      cases hl : K1.laterOwn P owed x.L.check x.w rs with
      | error e => rfl
      | ok y =>
        obtain ⟨c', w'⟩ := y
        show (Except.toOption ((L3.commitBehind x.L c' x.F ts).bind fun q =>
          pure { x with L := q.1, F := q.2, w := w' })).map _ =
          ((commitAllG (linkSh x.L) ts (ledSh x.F)).bind fun rt' =>
            if ts.length == (L3.laidHere x.L).length then
              some ({ linkSh x.L with check := checkSh c', moments := x.L.moments + 1 }, rt',
                coreSh (coreOf w'))
            else none)
        unfold L3.commitBehind
        cases hf : ts.foldlM (L3.commitOne x.L) x.F with
        | error e =>
          rw [hf] at h2
          have hn : commitAllG (linkSh x.L) ts (ledSh x.F) = none := by
            cases hg : commitAllG (linkSh x.L) ts (ledSh x.F) with
            | none => rfl
            | some r => rw [hg] at h2; cases h2
          rw [hn]
          rfl
        | ok G =>
          rw [hf] at h2
          cases hg : commitAllG (linkSh x.L) ts (ledSh x.F) with
          | none => rw [hg] at h2; cases h2
          | some r =>
            rw [hg] at h2
            have e1 := Option.some.inj h2
            by_cases g3 : (ts.length == (L3.laidHere x.L).length) = true
            · simp only [bind, Except.bind, Option.bind, g3, if_true, pure, Except.pure]
              show some (linkSh { x.L with check := c', moments := x.L.moments + 1 }, ledSh G,
                coreSh (coreOf w')) = _
              rw [e1]
              rfl
            · simp only [bind, Except.bind, Option.bind, g3, Bool.false_eq_true, if_false]
              rfl

/-! ## 2 The member: a segment's later moment at the first chain's state -/

theorem setLed_same {a : ChainSh} {L : LedSh} (h : a.led = some L) : a.setLed L = a := by
  obtain ⟨a1, a2, a3, a4, rest⟩ := a
  change a4 = some L at h
  subst h
  rfl

/-- **K1's commitment behind its sending's guards, on the chain's shape.** -/
def commitStepG (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (a : ChainSh) :
    Option ChainSh :=
  match a.link, a.led, a.tl with
  | some L, some Ld, some _ =>
    if L.check.frame.link == link && L.check.frame.moment == moment &&
        ReqFrame.notices (L.check.frame.blank.atMoment L.check.frame.moment) == P.sent then
      match arrays with
      | none => none
      | some ts =>
        (stepG P a.core.st.oracles.length ts L Ld (sendCore P a.core)).map fun z =>
          (((a.setCore z.2.2).setRowsOwed none).setLink z.1).setLed z.2.1
    else none
  | _, _, _ => none

/-- **Where the sending returns, the member's decision and its step on the shape commute.** -/
theorem commit_sq (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (s : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (x : Array Nat × DState Unit)
    (hs : K1.decideSend P (K1.owedOf s) (K1.stateOf s ()) rs = .ok x) :
    ((K1.commitAtS (Cl := Unit) P link moment arrays).decide s rs gs).toOption.map chainSh =
      commitStepG P link moment arrays (chainSh s) := by
  obtain ⟨ids, d₁⟩ := x
  obtain ⟨hi, hcore, -, -⟩ := send_core hs
  have hi' : ids = idsAt P s.st.oracles.size := hi
  subst hi'
  have hcore' : coreSh (coreOf d₁) = sendCore P (chainSh s).core := hcore
  have hz : (chainSh s).core.st.oracles.length = s.st.oracles.size := Ground.Sh.orc_size s.st
  unfold commitStepG
  show _ = (match s.link?.map linkSh, s.fork?.map ledSh, s.tl?.map tailSh with
    | some L, some Ld, some _ => _
    | _, _, _ => none)
  show (Except.toOption (match s.link?, s.fork?, s.tl? with
    | some L, some F, some tl => _
    | _, _, _ => _)).map _ = _
  cases hL : s.link? with
  | none => rfl
  | some L =>
    cases hF : s.fork? with
    | none => rfl
    | some F =>
      cases hT : s.tl? with
      | none => rfl
      | some tl =>
        rw [hz, ← hcore']
        show (Except.toOption (((K1.commitOwn (Cl := Unit) P link moment arrays).decide
            ⟨K1.owedOf s, ⟨L, F, tl, K1.stateOf s ()⟩⟩ rs gs).map fun y =>
              ((K1.laid s y.held.w).putLink y.held.L).putFork y.held.F)).map _ =
          (if L.check.frame.link == link && L.check.frame.moment == moment &&
              ReqFrame.notices (L.check.frame.atMoment L.check.frame.moment) == P.sent then
            match arrays with
            | none => none
            | some ts =>
              (stepG P s.st.oracles.size ts (linkSh L) (ledSh F) (coreSh (coreOf d₁))).map
                fun z => ((((chainSh s).setCore z.2.2).setRowsOwed none).setLink z.1).setLed z.2.1
          else none)
        unfold K1.commitOwn
        simp only []
        by_cases g : (L.check.frame.link == link && L.check.frame.moment == moment &&
            ReqFrame.notices (L.check.frame.atMoment L.check.frame.moment) == P.sent) = true
        · simp only [g, if_true]
          cases arrays with
          | none => rfl
          | some ts =>
            have hq' : (L3.commitStep (K1.laterOwn P (K1.owedOf s)) ts
                ⟨L, F, tl, K1.stateOf s ()⟩ rs).toOption.map
                  (fun y => (linkSh y.L, ledSh y.F, coreSh (coreOf y.w))) =
                stepG P s.st.oracles.size ts (linkSh L) (ledSh F) (coreSh (coreOf d₁)) :=
              commitStep_sh P (K1.owedOf s) ts ⟨L, F, tl, K1.stateOf s ()⟩ rs
                s.st.oracles.size d₁ hs
            simp only []
            cases hc : L3.commitStep (K1.laterOwn P (K1.owedOf s)) ts
                ⟨L, F, tl, K1.stateOf s ()⟩ rs with
            | error e =>
              cases hg : stepG P s.st.oracles.size ts (linkSh L) (ledSh F)
                  (coreSh (coreOf d₁)) with
              | none => rfl
              | some z =>
                rw [hc, hg] at hq'
                exact absurd hq' (by simp [Except.toOption])
            | ok y =>
              cases hg : stepG P s.st.oracles.size ts (linkSh L) (ledSh F)
                  (coreSh (coreOf d₁)) with
              | none =>
                rw [hc, hg] at hq'
                exact absurd hq' (by simp [Except.toOption])
              | some z =>
                have h' := hq'
                rw [hc, hg] at h'
                obtain ⟨e1, e2, e3⟩ : linkSh y.L = z.1 ∧ ledSh y.F = z.2.1 ∧
                    coreSh (coreOf y.w) = z.2.2 := by
                  have := Option.some.inj h'
                  subst this
                  exact ⟨rfl, rfl, rfl⟩
                show some (chainSh (((K1.laid s y.w).putLink y.L).putFork y.F)) = _
                rw [chainSh_putFork, chainSh_putLink, chainSh_laid, e1, e2, e3]
                rfl
        · simp only [g, Bool.false_eq_true, if_false]
          rfl

/-! ## 3 The member's one step, and its two laws -/

/-- **K1's commitment on the chain's shape: the sending's Bool, then the step.** -/
def commitG (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (a : ChainSh) :
    Option ChainSh :=
  if sendB P a.rowsOwed a.core then commitStepG P link moment arrays a else none

/-- A later moment's yes has its sending's return in it. -/
theorem laterOwn_inv {P : K1.Par} {owed : Option Nat} {c : ChainCheck} {w : DState Unit}
    {rs : List Fmt.RoundView} {y : ChainCheck × DState Unit} (h : K1.laterOwn P owed c w rs = .ok y) :
    ∃ x, K1.decideSend P owed w rs = .ok x := by
  unfold K1.laterOwn at h
  simp only [] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases hd : K1.decideSend P owed w rs with
        | error e => rw [hd] at h; cases h
        | ok x => exact ⟨x, rfl⟩

theorem commit_inv {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s rs gs = .ok s') :
    ∃ x, K1.decideSend P (K1.owedOf s) (K1.stateOf s ()) rs = .ok x := by
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl _ _ _
    cases hb : (K1.commitOwn (Cl := Unit) P link moment arrays).decide
        ⟨K1.owedOf s, ⟨L, F, tl, K1.stateOf s ()⟩⟩ rs gs with
    | error e => simp [hb, Except.map] at h
    | ok y =>
      simp only [K1.commitOwn] at hb
      split at hb
      · split at hb
        · cases hb
        · rename_i ts
          cases h1 : L3.commitStep (K1.laterOwn P (K1.owedOf s)) ts
              ⟨L, F, tl, K1.stateOf s ()⟩ rs with
          | error e => simp [h1, Except.map] at hb
          | ok z =>
            simp only [L3.commitStep, bind, Except.bind] at h1
            cases h0 : L3.commitFront L with
            | error e => simp [h0] at h1
            | ok u =>
              simp only [h0] at h1
              cases h2 : K1.laterOwn P (K1.owedOf s) L.check (K1.stateOf s ()) rs with
              | error e => simp [h2] at h1
              | ok x => exact laterOwn_inv h2
      · cases hb
  · cases h

/-- **"Carries" at the member**, in the strong form but for the sending's tests on the plan: behind
a yes the step behind the sending's Bool returns the shape behind. -/
theorem commit_carries_strong {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s rs gs = .ok s') :
    commitStepG P link moment arrays (chainSh s) = some (chainSh s') := by
  obtain ⟨x, hx⟩ := commit_inv h
  rw [← commit_sq P link moment arrays s rs gs x hx, h]
  rfl

/-- **"Carries" at the member.** -/
theorem commit_carries {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {t : ChainSh}
    (h : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s rs gs = .ok s')
    (hg : commitG P link moment arrays (chainSh s) = some t) : t = chainSh s' := by
  unfold commitG at hg
  split at hg
  · rw [commit_carries_strong h] at hg
    exact (Option.some.inj hg).symm
  · cases hg

/-- **"Returns" at the member**: where the step on the shape returns, the member says yes on two
rounds in which no seed's factor is 0 and round 2 holds as many answers as the place counts. -/
theorem commit_returns {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {t : ChainSh}
    (hg : commitG P link moment arrays (chainSh s) = some t)
    (hz : ∀ x ∈ K1.seedsOf P r₁, isZeroE x.2 = false)
    (hn : (K1.answersIn r₂).length = P.answers) :
    ∃ s', (K1.commitAtS (Cl := Unit) P link moment arrays).decide s [r₁, r₂] gs = .ok s' ∧
      chainSh s' = t := by
  unfold commitG at hg
  split at hg
  · rename_i hB
    obtain ⟨x, hs⟩ := send_returns P s.rowsOwed (K1.stateOf s ()) r₁ r₂ hB hz hn
    have hq := commit_sq P link moment arrays s [r₁, r₂] gs x hs
    rw [hg] at hq
    cases hd : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s [r₁, r₂] gs with
    | error e => rw [hd] at hq; cases hq
    | ok s' =>
      rw [hd] at hq
      exact ⟨s', rfl, Option.some.inj hq⟩
  · cases hg

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.commit_inv
#print axioms VerifiableInference.Desc.First.Shape.commit_carries_strong
#print axioms VerifiableInference.Desc.First.Shape.commit_carries
#print axioms VerifiableInference.Desc.First.Shape.commit_returns
#print axioms VerifiableInference.Desc.First.Shape.commit_sq
#print axioms VerifiableInference.Desc.First.Shape.setLed_same
#print axioms VerifiableInference.Desc.First.Shape.commitStep_sh
#print axioms VerifiableInference.Desc.First.Shape.laterOwn_inv
