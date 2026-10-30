-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LeftTiesInScope.lean: THE NAMED PREMISE LeftTies
(Johnson/Desc/Kinds/Law/WeightTwinAt.lean: the weights that the program's claim on the committed
weights takes for the vocabulary are the text's) IN THE GOALS' SCOPE, and in the letters in which
the joining of the merge's sentence with the output head's asks it.

How. Johnson/Desc/Kinds/Law/LeftTiesPaid.lean (leftTies_of_place) pays LeftTies where the layout's
call number 0 is placed by the layout's own rule at three segments of the text's three lengths. In
scope that is so: Johnson/Goal/Meaning/HeadColsScope.lean (calls_six, cols_in_scope),
HeadCallsScope.lean (lines_in_scope, callNo_in_scope), HeadCondScope.lean (numbers_in_scope,
ok_in_scope).

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.InScope).
  call0_in_scope: the layout's call number 0, written out as a placed call.
  seg_third: the segment of a placed call of three segments under the third's name, where the first
      two have other names: decided on the names alone.
  seg_HD0_in_scope: so the segment "HD0" of call number 0 is its third.
  leftTies_in_scope: LeftTies at that segment, at a state at which the letters in front are read.
  g1_behind: behind an accept of the head's own sub-protocol the state holds, as what was heard, a
      value whose field g1 is what the lookup on the calls had heard in front.
  wa7_in_scope: THE CLAUSE: for all letters g, o', x, q, sg as the joining binds them.

Every letter under "there is": g1_behind: gk, X0, o: pinned by the reader lookHeard? in front, by
o.x, and by the state's field here behind.
What it does not say. Only in the goals' scope, at the full size. hd (an accept of the head's own
sub-protocol from s to s') and hK (KeptWFo s' sF: Johnson/Desc/Kinds/Law/WeightAtFo.lean; of it the
proof reads "both states stand in a head's segment" and "x is the same" alone) are premises: they
are two other clauses of the same structure. That the letters in front are read at s is a premise
of the clause itself. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.LeftTiesPaid
import Johnson.Desc.Kinds.Law.WeightAtFo
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Goal.Meaning.HeadColsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public)
open OnBytes.Model (place SegAsk CallD Fork)
open OnBytes.Model.Head (keyFloor)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K11Caller (ewAt)

/-! ## 1 The placed call -/

/-- The third segment of a placed call of three, by its name. -/
theorem seg_third (name kind : String) (a1 a2 a3 : SegAsk) (fl : ℕ) (n : String)
    (h1 : (a1.1 == n) = false) (h2 : (a2.1 == n) = false) (h3 : (a3.1 == n) = true) :
    (place name kind [a1, a2, a3] fl).seg? n =
      some ((place name kind [a1, a2, a3] fl).segs.getD 2 default) := by
  unfold CallD.seg?
  rw [OnBytes.Road.Hd.place_segs_eq]
  show List.find? _ [_, _, _] = some _
  rw [List.find?_cons_of_neg (by simpa using h1), List.find?_cons_of_neg (by simpa using h2),
    List.find?_cons_of_pos (by simpa using h3)]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- **The layout's call number 0 in scope.** -/
theorem call0_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    X.HLy.calls.getD 0 default = place "R16a" "R16"
      [("NF", X.hS.d, false), ("NFH", X.hS.d, false), ("HD0", X.HLy.JV, false)]
      (keyFloor X.hS - X.hS.lt) := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  obtain ⟨cs, hc, -, hL⟩ := (OnBytes.Road.Hd.admittedH_of_layout B.head).calls
  rw [hL, calls_six hc (lines_in_scope hZ hR h)]
  rfl

/-- **The segment "HD0" of call number 0 is its third.** -/
theorem seg_HD0_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    (X.HLy.calls.getD 0 default).seg? "HD0" =
      some ((X.HLy.calls.getD 0 default).segs.getD 2 default) := by
  rw [call0_in_scope hZ hR h]
  exact seg_third _ _ _ _ _ _ _ (show ("NF" == "HD0") = false by decide)
    (show ("NFH" == "HD0") = false by decide) (show ("HD0" == "HD0") = true by decide)

/-- **LeftTies in scope.** -/
theorem leftTies_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {s : S} {g : Given} {gk : OnBytes.Model.Forest.Heard}
    (cov : OnBytes.Model.Head.Covered) (x : OnBytes.Model.Head.Heard)
    (t : OnBytes.Model.Head.Tables)
    (hg : given (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) s = .ok g)
    (hgk : s.lookHeard? = some gk) (hx : x.g1 = gk) :
    LeftTies X g cov x t
      (ewAt (runAt X cov x t) 0 ((X.HLy.calls.getD 0 default).segs.getD 2 default)) := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have A := OnBytes.Road.Hd.admittedH_of_layout B.head
  have eJ : X.HLy.JV = @JV (sizesOf X.hS) := by
    rw [A.JV]
    rfl
  refine leftTies_of_place X cov x t hg hgk hx (ok_in_scope hZ hR h _)
    (cols_in_scope hZ hR h 0 (by decide)) _ _ _ _ (call0_in_scope hZ hR h) ?_
  show [X.hS.d, X.hS.d, X.HLy.JV] = _
  rw [eJ]
  rfl

/-! ## 2 What was heard, behind the head's own accept -/

/-- **Behind an accept of the head's own sub-protocol: what was heard holds, as g1, what the lookup
on the calls had heard in front.** -/
theorem g1_behind (hS : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (hd : (blockAt hS iU3 work l).decide s rs gs = .ok s') :
    ∃ (gk : OnBytes.Model.Forest.Heard) (X0 : OnBytes.Model.Head.Heard) (o : HeadOwn),
      s.lookHeard? = some gk ∧ s'.here = .head o ∧ o.x = some X0 ∧ X0.g1 = gk := by
  obtain ⟨a, F1, X0, Q, ha, hop, _, e⟩ := Came.decide_record hS iU3 work l hd
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf hS work)
      (seatAt hS iU3) s rs = .ok s' := hd
  obtain ⟨_, H, _, s1, s2, _, _, _, e2, e3⟩ := Came.decide_hands hd'
  obtain ⟨o1, gk, _, hl1, e4⟩ := setHeard_form hS iU3 e2
  have e5 : s' = s2 := e3
  have hh := (congrArg (·.here) e).symm.trans (congrArg (·.here) (e5.trans e4))
  have hh' := VerifiableInference.Desc.First.Here.head.inj hh
  have k1 : a.lookHeard = o1.lookHeard := congrArg (·.lookHeard) hh'
  have k2 := Option.some.inj (congrArg (·.x) hh')
  refine ⟨gk, X0, _, ?_, congrArg (·.here) e, rfl, ?_⟩
  · unfold S.lookHeard?
    rw [ha]
    show (if a.opened then a.lookHeard else none) = some gk
    rw [hop, k1, hl1]
    rfl
  · have k3 : X0 = _ := k2
    rw [k3]
    rfl

/-! ## 3 The clause -/

/-- **THE CLAUSE ON LeftTies, IN SCOPE, IN THE JOINING'S OWN LETTERS.** -/
theorem wa7_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {s s' sF : S} {rv : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (cov : OnBytes.Model.Head.Covered)
    (t : OnBytes.Model.Head.Tables)
    (hd : (blockAt X.hS (readsOf X) (workOf X) 24).decide s rv gs = .ok s') (hK : KeptWFo s' sF) :
    ∀ (g : Given) o' x q sg,
      given (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) s = .ok g →
      sF.here = .head o' → o'.x = some x → OnBytes.Model.Head.callNo X.HLy "HD0" = some q →
      (X.HLy.calls.getD q default).seg? "HD0" = some sg →
      LeftTies X g cov x t (ewAt (runAt X cov x t) q sg) := by
  intro g o' x q sg hg ho' hx hq hsg
  obtain rfl : 0 = q := Option.some.inj ((callNo_in_scope hZ hR h).2.symm.trans hq)
  obtain rfl := Option.some.inj ((seg_HD0_in_scope hZ hR h).symm.trans hsg)
  obtain ⟨gk, X0, o, hgk, ho, hX0, hg1⟩ := g1_behind _ _ _ _ hd
  obtain ⟨p, p', hp, hp', ex, _⟩ := hK
  obtain rfl : o = p := VerifiableInference.Desc.First.Here.head.inj (ho.symm.trans hp)
  obtain rfl : o' = p' := VerifiableInference.Desc.First.Here.head.inj (ho'.symm.trans hp')
  obtain rfl : X0 = x := Option.some.inj (hX0.symm.trans (ex.symm.trans hx))
  exact leftTies_in_scope hZ hR h cov X0 t hg hgk hg1

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.seg_third
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.call0_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.seg_HD0_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.leftTies_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.g1_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.wa7_in_scope
