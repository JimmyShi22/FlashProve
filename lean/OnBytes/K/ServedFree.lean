-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ServedFree.lean: what the stage request finds, without the check of the proof file
(`requestFound`, OnBytes/K/Served.lean), is the same at two requests on which the program's tests of
sizes, of r and e and of ranges say the same.

The body of `requestFound` reads the request and the reply. This file follows each step and says
what of them it reads.

Main names:
  `ReqAlike T V P Q P' Q'`: two requests with their replies, as words: the same numbers of words;
    the same r and e; the same verdicts of the tests "the reply is 0 before the window's end", "the
    reply is below V", "every token is below V".
  `stFromCall_alike`, `coveredOf_alike`: both refuse with one name, or both return; the covered
    positions then have one count.
  `servedOf_alike`: the conditions of the standard form read r, e and that count alone.
  `itemStep`, `linksStep`: the steps on the item and on the links, their results thrown away.
  `linksStep_free`: whether the links are made does not hang on the covered positions.
  `afterCov`, `requestFound_eq`: the body in two halves. `afterCov_free`, `requestFound_free`: the
    findings are the same.

Asked in `requestFound_free`: `ReqAlike`; the two lengths in bytes give one verdict of the test on
whole words; the step on the item says the same of the two requests.

Limits: that the step on the item says the same is a hypothesis here. Nothing on the check of the
proof file, which does read the tokens. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.Served
import OnBytes.K.Tokens
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

/-- Two requests with their replies, as words, on which the program's tests of sizes, of r and e and
of ranges say the same. -/
structure ReqAlike (T V : Nat) (P Q P' Q' : Array UInt32) : Prop where
  sizeP : P.size = P'.size
  sizeQ : Q.size = Q'.size
  r : (P.getD T 0).toNat = (P'.getD T 0).toNat
  e : (P.getD (T + 1) 0).toNat = (P'.getD (T + 1) 0).toNat
  y0 : (decide ((P.getD (T + 1) 0).toNat < T) && (Q.getD 0 0).toNat != 0) =
    (decide ((P.getD (T + 1) 0).toNat < T) && (Q'.getD 0 0).toNat != 0)
  yV : decide ((Q.getD 0 0).toNat < V) = decide ((Q'.getD 0 0).toNat < V)
  tokV : ((P.extract 0 T).map (·.toNat)).all (fun v => decide (v < V)) =
    ((P'.extract 0 T).map (·.toNat)).all (fun v => decide (v < V))

/-- The reader of request and reply refuses both with one name, or returns on both, with one r and
one e. -/
theorem stFromCall_alike {T V : Nat} {P Q P' Q' : Array UInt32} (h : ReqAlike T V P Q P' Q') :
    (∃ n, Head.stFromCall P Q T = .error n ∧ Head.stFromCall P' Q' T = .error n) ∨
      (Head.stFromCall P Q T = .ok ⟨P, (P.getD T 0).toNat, (P.getD (T + 1) 0).toNat,
          (Q.getD 0 0).toNat⟩ ∧
        Head.stFromCall P' Q' T = .ok ⟨P', (P.getD T 0).toNat, (P.getD (T + 1) 0).toNat,
          (Q'.getD 0 0).toNat⟩) := by
  have e1 : P.isEmpty = P'.isEmpty := by simp [Array.isEmpty, h.sizeP]
  have e2 : Q.isEmpty = Q'.isEmpty := by simp [Array.isEmpty, h.sizeQ]
  unfold Head.stFromCall Head.needed
  dsimp only
  rw [← e1, ← e2, ← h.sizeP, ← h.sizeQ, ← h.r, ← h.e, ← h.y0]
  by_cases c1 : (!(P.isEmpty || Q.isEmpty)) = true
  · by_cases c2 : (!(P.size != T + 2 || Q.size != 1)) = true
    · by_cases c3 : (!(decide ((P.getD T 0).toNat ≥ (P.getD (T + 1) 0).toNat) ||
          decide ((P.getD (T + 1) 0).toNat > T) ||
          (decide ((P.getD (T + 1) 0).toNat < T) && (Q.getD 0 0).toNat != 0))) = true
      · right
        rw [if_pos c1, if_pos c2, if_pos c3]
        exact ⟨rfl, rfl⟩
      · left
        rw [if_pos c1, if_pos c2, if_neg c3]
        exact ⟨_, rfl, rfl⟩
    · left
      rw [if_pos c1, if_neg c2]
      exact ⟨_, rfl, rfl⟩
  · left
    rw [if_neg c1]
    exact ⟨_, rfl, rfl⟩

/-- The covered positions: both refused with one name, or both returned, with one count. The letters
r and e are read by nothing: the covered positions take r and e from the words. -/
theorem coveredOf_alike {T V : Nat} {P Q P' Q' : Array UInt32} (h : ReqAlike T V P Q P' Q')
    (r e : Nat) :
    (∃ n, Head.coveredOf ⟨P, r, e, (Q.getD 0 0).toNat⟩ T V = .error n ∧
        Head.coveredOf ⟨P', r, e, (Q'.getD 0 0).toNat⟩ T V = .error n) ∨
      (∃ cov cov', Head.coveredOf ⟨P, r, e, (Q.getD 0 0).toNat⟩ T V = .ok cov ∧
        Head.coveredOf ⟨P', r, e, (Q'.getD 0 0).toNat⟩ T V = .ok cov' ∧ cov.hRC = cov'.hRC) := by
  unfold Head.coveredOf Head.needed
  dsimp only
  rw [← h.yV, ← h.sizeP, ← h.tokV, ← h.r, ← h.e]
  by_cases c1 : decide ((Q.getD 0 0).toNat < V) = true
  · by_cases c2 : (P.size == T + 2) = true
    · by_cases c3 : (((P.extract 0 T).map (·.toNat)).all fun v => decide (v < V)) = true
      · by_cases c4 : (!(decide ((P.getD T 0).toNat ≥ (P.getD (T + 1) 0).toNat) ||
            decide ((P.getD (T + 1) 0).toNat > T))) = true
        · right
          rw [if_pos c1, if_pos c2, if_pos c3, if_pos c4]
          exact ⟨_, _, rfl, rfl, rfl⟩
        · left
          rw [if_pos c1, if_pos c2, if_pos c3, if_neg c4]
          exact ⟨_, rfl, rfl⟩
      · left
        rw [if_pos c1, if_pos c2, if_neg c3]
        exact ⟨_, rfl, rfl⟩
    · left
      rw [if_pos c1, if_neg c2]
      exact ⟨_, rfl, rfl⟩
  · left
    rw [if_neg c1]
    exact ⟨_, rfl, rfl⟩

/-- The conditions of the standard form read r, e and the count alone. -/
theorem servedOf_alike (C : Common) (o : Options) (b : Bool) {so so' : Head.StOwn}
    {cov cov' : Head.Covered} (hr : so.r = so'.r) (he : so.e = so'.e) (hc : cov.hRC = cov'.hRC) :
    servedOf C o b so cov = servedOf C o b so' cov' := by
  unfold servedOf
  rw [hr, he, hc]

/-- The two steps of the stage request on the item: the item is made, and it is compared with the
public part. -/
def itemStep (X : Public) (pol KL request : ByteArray) : Except Refused Unit :=
  named
    (match Proof.requestItem pol KL request with
    | some w => pure w
    | none => throw "internal-request-item") >>= fun item => named (statementHeld X item)

/-- The step on the links, its result thrown away. -/
def linksStep (X : Public) (cov : Head.Covered) : Except Refused Unit :=
  named (linksOf X cov) >>= fun _ => pure ()

/-- A step that has returned, its result thrown away. -/
theorem named_ok_step {α : Type} (a : α) :
    (named (.ok a : Except String α) >>= fun _ => (pure () : Except Refused Unit)) = pure () := rfl

/-- Whether the links are made does not hang on the covered positions: `listLinksH` refuses on the
numbers of plans alone. -/
theorem linksStep_free (X : Public) (cov cov' : Head.Covered) :
    linksStep X cov = linksStep X cov' := by
  unfold linksStep linksOf
  rw [OnBytes.L5.LinksOrder.listLinksH_fold, OnBytes.L5.LinksOrder.listLinksH_fold]
  simp only [Array.size_mapIdx]
  by_cases hc : (X.G.size != X.NGr || (X.p4 && (X.A.map attentionPlanOf).size != X.NGr)) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]
    exact (named_ok_step _).trans (named_ok_step _).symm

/-- Four steps in a row, of which the later ones do not read what the first and the third return,
grouped as two steps and a rest. -/
theorem regroup {ε α β γ : Type} (I : Except ε α) (s : α → Except ε Unit) (L : Except ε β)
    (k : Except ε γ) :
    (I >>= fun item => s item >>= fun _ => L >>= fun _ => k) =
      ((I >>= s) >>= fun _ => (L >>= fun _ => pure ()) >>= fun _ => k) := by
  cases I with
  | error _ => rfl
  | ok a =>
    show (s a >>= fun _ => L >>= fun _ => k) =
      (s a >>= fun _ => (L >>= fun _ => pure ()) >>= fun _ => k)
    cases s a with
    | error _ => rfl
    | ok _ =>
      cases L with
      | error _ => rfl
      | ok _ => rfl

/-- The body of `requestFound` behind the covered positions. -/
def afterCov (C : Common) (o : Options) (pol KL request : ByteArray) (hasLayout : Bool)
    (so : Head.StOwn) (cov : Head.Covered) : Except Refused Found := do
  let a ← named (C.acct C.chains.made.proof o.bits "request")
  let item ← named
    (match Proof.requestItem pol KL request with
    | some w => pure w
    | none => throw "internal-request-item")
  named (statementHeld C.X item)
  let _ ← named (linksOf C.X cov)
  named (workHeldH (Params.needsWork C.chains.made.proof) a.work)
  pure (lastLine (!C.X.p4) (askedBelowBar o.bits) (servedForm (servedOf C o hasLayout so cov))
      C.X.P.settings.lidb C.X.P.settings.nminH,
    acctWhole C.chains.made.sized.set
      (some (C.chains.made.key ++ [C.chains.made.entry] ++ C.chains.made.proof)), a.work)

/-- The body of `requestFound` in two halves, by unfolding. -/
theorem requestFound_eq (C : Common) (o : Options) (pol KL request y : ByteArray) (b : Bool) :
    requestFound C o pol KL request y b =
      (named (refuseIf (request.size % 4 != 0 || y.size % 4 != 0) "statement-required") >>=
        fun _ => named (Head.stFromCall (words32 request) (words32 y) C.X.T) >>=
        fun so => named (Head.coveredOf so C.X.T C.X.P.h.V) >>=
        fun cov => afterCov C o pol KL request b so cov) := rfl

/-- The second half is the same where the two steps and the conditions of the standard form are. -/
theorem afterCov_free (C : Common) (o : Options) (pol KL request request' : ByteArray) (b : Bool)
    {so so' : Head.StOwn} {cov cov' : Head.Covered}
    (hItem : itemStep C.X pol KL request = itemStep C.X pol KL request')
    (hLinks : linksStep C.X cov = linksStep C.X cov')
    (hs : servedOf C o b so cov = servedOf C o b so' cov') :
    afterCov C o pol KL request b so cov = afterCov C o pol KL request' b so' cov' := by
  unfold afterCov
  rw [hs]
  refine congrArg _ (funext fun a => ?_)
  refine (regroup _ _ _ _).trans (Eq.trans ?_ (regroup _ _ _ _).symm)
  show (itemStep C.X pol KL request >>= fun _ => linksStep C.X cov >>= fun _ => _) =
    (itemStep C.X pol KL request' >>= fun _ => linksStep C.X cov' >>= fun _ => _)
  rw [hItem, hLinks]

/-- What the stage request finds is the same at two requests that are alike, if the step on the item
says the same of them. -/
theorem requestFound_free (C : Common) (o : Options) (pol KL request y request' y' : ByteArray)
    (b : Bool)
    (h4 : (request.size % 4 != 0 || y.size % 4 != 0) =
      (request'.size % 4 != 0 || y'.size % 4 != 0))
    (h : ReqAlike C.X.T C.X.P.h.V (words32 request) (words32 y) (words32 request') (words32 y'))
    (hItem : itemStep C.X pol KL request = itemStep C.X pol KL request') :
    requestFound C o pol KL request y b = requestFound C o pol KL request' y' b := by
  rw [requestFound_eq, requestFound_eq, h4]
  refine congrArg _ (funext fun _ => ?_)
  rcases stFromCall_alike h with ⟨n, h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    rfl
  · rw [h1, h2]
    show (named (Head.coveredOf ⟨words32 request, _, _, _⟩ C.X.T C.X.P.h.V) >>=
        fun cov => afterCov C o pol KL request b _ cov) =
      (named (Head.coveredOf ⟨words32 request', _, _, _⟩ C.X.T C.X.P.h.V) >>=
        fun cov => afterCov C o pol KL request' b _ cov)
    rcases coveredOf_alike h ((words32 request).getD C.X.T 0).toNat
      ((words32 request).getD (C.X.T + 1) 0).toNat with ⟨n, g1, g2⟩ | ⟨cov, cov', g1, g2, g3⟩
    · rw [g1, g2]
      rfl
    · rw [g1, g2]
      exact afterCov_free C o pol KL request request' b hItem (linksStep_free C.X cov cov')
        (servedOf_alike C o b rfl rfl g3)

end OnBytes.K
