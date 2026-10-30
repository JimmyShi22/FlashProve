-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Forward.lean: the honest side of the kind "lookup" (K3). The
forward pieces: each piece of the verifier's hearing of a lookup
(Johnson/Desc/First/Look/Via/Rounds.lean; Johnson/Desc/First/ProdV/Level.lean) returns, with these
values and these rounds left, where its rounds have the stated shape and its masked sumcheck's own
text returns on them. Theorems, with one structure and three small definitions.

Terms. Honest/K3/GLOSSARY.md ("hearing", "level", "sumcheck, masked sumcheck", "tie").

What is shown.
  `Quiet n r`: a round that sends nothing and samples n elements and nothing else.
  `bind_ret`, `ite_bind_ret`, `slot_ret`, `owe_ret`, `must_ret`, `pure_ret`, `of_ret`: the
    connectives of the verifier's text.
  `drawsV_ret`, `drawV_ret`: a round of samples.
  `sumV_ret`, `openV_ret`: a masked sumcheck with ends, and one left open: from `MaskedSum.whole` or
    `MaskedSum.hear` returning on just its own rounds.
  `level_ret`, `run_succ_ret`: a level of a product tree; a run, level by level.
  `foldlM_ret`: a fold of the text, by an invariant with a counter (for the tie's steps).
  `tieV_ret`: the tie, from its first step and its fold.
  `keysV_one_ret`: one part's key tree.
  `messagesV_intro`, `hearV_intro`: conditional (one part of keys): the whole hearing, from its
    pieces' results in order.

Hypotheses that remain. `slot_ret`, `owe_ret`, `must_ret` and `pure_ret` have none. The others but
the two on a round of samples take as hypotheses that the pieces beneath them return (`h`, `h1`,
`h2`, `hw`, `hh`; in `messagesV_intro` `e5` to `e16`, nine of them, in the order of the text).
Beside these:
  `q`: (in `drawsV_ret`, `drawV_ret`, `level_ret`) the round is `Quiet`.
  `hx`, `ha`: (in `sumV_ret`, `openV_ret`, `level_ret`) the rounds are as many as the call has; no
    position and no matrix entry is sampled in them. `hy`: (in `sumV_ret`, `level_ret`) the sample
    of Y is not 0.
  `hp`, `hsz`, `hslots`, `hlins`: (in `messagesV_intro`) one part of keys; the table side's last
    point has mu + d coordinates; the ledger's next slot has moved by the face's number of slots;
    there are as many rows as the face says.
  `hok`: (in `hearV_intro`) the face passes the verifier's tests.
  In `foldlM_ret`, without a name, in front of arrows: the invariant is kept by each step, and holds
    at the start.

Users. These theorems mirror `drawsV_spec`, `sumV_spec`, `level_seg` and their kin
(Honest/K3/HeardLaw.lean), which go from "it returns" to the values. With them a proof that the
whole hearing returns is a chain of rewrites. This file is imported by Honest/K3/Law/Index.lean and
Honest/K3/Parts/Forward.lean.

Limits. Nothing here says that a masked sumcheck's text returns: that is a hypothesis at every piece
(Johnson/Desc/Part/MaskedSumReady.lean says when it does). Nothing is said of what the values mean.
`messagesV_intro` is stated at one part of keys.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Forward
open OnBytes (E zeroE isZeroE mulE subE)
open OnBytes.Model (Fork Aff orderDefault eqTab)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV
  noVar leafVars bitsCall)
open VerifiableInference.Desc.First.ProdV (layBack levelVars stepDown LevelOut level turn Carried
  levelEnds elementsAlone run_succ)

local notation "vRoundsOf" => VerifiableInference.Desc.K3.roundsOf
local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {α β γ : Type}

/-- A round that sends nothing and samples n elements, no position and no matrix entry. -/
structure Quiet (n : Nat) (r : Fmt.RoundView) : Prop where
  vals : r.vals = []
  elems : r.drawn.elems.length = n
  poss : r.drawn.poss = []
  trits : r.drawn.trits = []

/-! ## The connectives -/

theorem bind_ret {x : Hr α} {f : α → Hr β} {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}
    (h : x F rs = some (a, G, rest)) : (x >>= f) F rs = f a G rest := by
  show Hr.andThen x f F rs = _
  simp only [Hr.andThen, h]

theorem ite_bind_ret {c : Prop} [Decidable c] {x y : Hr α} {k : α → Hr β} {F G : Fork}
    {rs rest : List Fmt.RoundView} {a : α} (h : (if c then x else y) F rs = some (a, G, rest)) :
    (if c then x >>= k else y >>= k) F rs = k a G rest := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢
    exact bind_ret h
  · rw [if_neg hc] at h ⊢
    exact bind_ret h

theorem pure_ret (a : α) (F : Fork) (rs : List Fmt.RoundView) : (pure a : Hr α) F rs = some (a, F, rs) :=
    rfl

theorem slot_ret (F : Fork) (rs : List Fmt.RoundView) : Hr.slot F rs = some (F.next, F, rs) := rfl

theorem owe_ret (what : String) (F : Fork) (rs : List Fmt.RoundView) :
    Hr.owe what F rs = some ((F.owe what).1, (F.owe what).2, rs) := rfl

theorem of_ret {x : VerifiableInference.Desc.First.ProdV.Hears α} {F : Fork} {rs : List Fmt.RoundView}
    {y : α × Fork × List Fmt.RoundView} (h : x F rs = some y) : Hr.of x F rs = some y := h

theorem must_ret (F : Fork) (rs : List Fmt.RoundView) : Hr.must true F rs = some ((), F, rs) := rfl

/-! ## A round of samples -/

theorem drawsV_ret {n : Nat} {r : Fmt.RoundView} (q : Quiet n r) (F : Fork) (rest : List Fmt.RoundView) :
    drawsV n F (r :: rest) = some ((r.drawn.elems.map E.ofTriple).toArray, F, rest) := by
  have ha : elementsAlone [r] = true := by simp [elementsAlone, q.poss, q.trits]
  have hr : MaskedSum.roundOf 0 n r = some ([], r.drawn.elems.map E.ofTriple) := by
    simp [MaskedSum.roundOf, MaskedSum.scalars, q.vals, q.elems]
  simp [drawsV, ha, hr]

theorem drawV_ret {r : Fmt.RoundView} (q : Quiet 1 r) (F : Fork) (rest : List Fmt.RoundView) :
    drawV F (r :: rest) = some (e1 r, F, rest) := by
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 q.elems
  unfold drawV
  rw [drawsV_ret q]
  simp [ht, e1]

/-! ## The masked sumchecks -/

theorem sumV_ret {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {x : List Fmt.RoundView} {h : MaskedSum.Heard} {row : Aff}
    (hw : MaskedSum.whole C k endTerm F x = some (h, row, G)) (hx : x.length = vRoundsOf k)
    (ha : elementsAlone x = true) (hy : isZeroE (h.r.getLastD zeroE) = false)
    (rest : List Fmt.RoundView) : sumV C k endTerm F (x ++ rest) = some ((h, row), G, rest) := by
  unfold sumV
  simp only [List.take_left' hx, List.drop_left' hx, ha, hw, hy, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]

theorem openV_ret {C : Aff} {vs : List MaskedSum.Var} {F G : Fork} {x : List Fmt.RoundView}
    {h : MaskedSum.Heard}
    (hh : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F x = some (h, G))
    (hx : x.length = vs.length + 1) (ha : elementsAlone x = true) (rest : List Fmt.RoundView) :
    openV C vs F (x ++ rest) = some (h, G, rest) := by
  simp [openV, List.take_left' hx, List.drop_left' hx, ha, hh]

/-! ## A level; a run -/

theorem level_ret {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {x : List Fmt.RoundView} {line : Fmt.RoundView} {h : MaskedSum.Heard} {row : Aff}
    (hw : MaskedSum.whole C { lead := 0, vs := levelVars m z order, ends := some levelEnds }
      (fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) F x = some (h, row, G))
    (hx : x.length = m + 3) (ha : elementsAlone x = true) (q : Quiet 1 line)
    (hy : isZeroE (h.r.getLastD zeroE) = false) (rest : List Fmt.RoundView) :
    level m z order C F (x ++ line :: rest) =
      some ({ r := layBack m order (h.r.take m), sL := h.sEnd, sR := h.sEnd + 1, xi := e1 line,
              row := row }, G, rest) := by
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 q.elems
  have h4 : (x ++ line :: rest).take (m + 4) = x ++ [line] := by
    have : x ++ line :: rest = (x ++ [line]) ++ rest := by simp
    rw [this]
    exact List.take_left' (by simp [hx])
  have ha4 : elementsAlone (x ++ [line]) = true := by
    unfold elementsAlone at ha ⊢
    simp [List.all_append, ha, q.poss, q.trits]
  have hr : MaskedSum.roundOf 0 1 line = some ([], [E.ofTriple t]) := by
    simp [MaskedSum.roundOf, MaskedSum.scalars, q.vals, ht]
  have he : e1 line = E.ofTriple t := by simp [e1, ht]
  unfold level
  simp only [h4, ha4, List.take_left' hx, List.drop_left' hx, hw, hr, hy, he, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

theorem run_succ_ret {m0 n : Nat} {orders : Nat → List Nat} {s s1 : Carried} {F F1 G : Fork}
    {rs r1 rest : List Fmt.RoundView} {o : LevelOut} (h1 : vRun m0 n orders s F rs = some (s1, F1, r1))
    (h2 : level (m0 + n) s1.point (orders (m0 + n)) s1.form F1 r1 = some (o, G, rest)) :
    vRun m0 (n + 1) orders s F rs =
      some ({ rows := s1.rows.push o.row, point := (stepDown o).1, form := (stepDown o).2 }, G,
        rest) := by
  rw [run_succ, h1]
  simp [turn, h2]

/-! ## A fold of the text -/

/-- A fold returns where each step leads from the invariant at its number to the invariant at the
next. -/
theorem foldlM_ret {f : β → γ → Hr β} (P : Nat → β → Fork → List Fmt.RoundView → Prop) :
    ∀ (l : List γ) (i : Nat) (s : β) (F : Fork) (rs : List Fmt.RoundView),
    (∀ j (hj : j < l.length) s F rs, P (i + j) s F rs →
      ∃ s' F' rs', f s l[j] F rs = some (s', F', rs') ∧ P (i + j + 1) s' F' rs') →
    P i s F rs → ∃ s' F' rs', l.foldlM f s F rs = some (s', F', rs') ∧ P (i + l.length) s' F' rs'
  | [], i, s, F, rs, _, h0 => ⟨s, F, rs, rfl, h0⟩
  | a :: l, i, s, F, rs, hstep, h0 => by
    obtain ⟨s1, F1, r1, e1', p1⟩ := hstep 0 (by simp) s F rs h0
    obtain ⟨s2, F2, r2, e2, p2⟩ := foldlM_ret P l (i + 1) s1 F1 r1
      (fun j hj s F rs hp => by
        have := hstep (j + 1) (by simpa using hj) s F rs (by
          rw [show i + (j + 1) = i + 1 + j by omega]
          exact hp)
        rw [show i + (j + 1) + 1 = i + 1 + j + 1 by omega] at this
        simpa using this) p1
    refine ⟨s2, F2, r2, ?_, by
      rw [show i + (a :: l).length = i + 1 + l.length by simp; omega]
      exact p2⟩
    show (f s a >>= fun s' => l.foldlM f s') F rs = _
    rw [bind_ret (by simpa using e1')]
    exact e2

/-- The step of the tie's fold, as `tieV` has it. -/
def tieStep (s : Array Aff × Nat × Array Nat) : Hr (Array Aff × Nat × Array Nat) := do
  let y ← sumV (Aff.slot s.2.1) (noVar 3 2) fun _ v =>
    mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE)
  pure (s.1.push y.2, y.1.sEnd, s.2.2.push (y.1.sEnd + 1))

/-- The tie, from its first step and its fold. -/
theorem tieV_ret {w : Nat} {a : E} {F F1 G : Fork} {rs r1 rest : List Fmt.RoundView}
    {x : MaskedSum.Heard × Aff} {s : Array Aff × Nat × Array Nat}
    (h1 : sumV (Aff.ofConst zeroE) (noVar 3 3) (fun _ v =>
      subE (v.getD 0 zeroE) (mulE a (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE))
        (v.getD 2 zeroE)))) F rs = some (x, F1, r1))
    (h2 : (List.range (w - 2)).foldlM (fun s _ => tieStep s)
      (#[x.2], x.1.sEnd + 1, #[x.1.sEnd + 2]) F1 r1 = some (s, G, rest)) :
    tieV w a F rs = some ((s.1, x.1.sEnd, s.2.2.push s.2.1), G, rest) := by
  unfold tieV
  refine (bind_ret h1).trans ?_
  refine (bind_ret h2).trans ?_
  rfl

/-- One part's key tree. -/
theorem keysV_one_ret {f : LFace} {v i : Nat} {C : Aff} {rows : Array Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {c : Carried}
    (h : vRun 0 v (f.orders i) { rows := rows, point := #[], form := C } F rs = some (c, G, rest)) :
    keysV f [(v, i)] [C] rows F rs = some ((c.rows, [(c.point, c.form)]), G, rest) := by
  unfold keysV
  refine (bind_ret (of_ret h)).trans ?_
  unfold keysV
  rfl

/-! ## The whole hearing, from its pieces' results in order -/

/-- The one claim on the planes' roots, as `messagesV` makes it: of the slots of the roots and
JOIN's point. -/
def joinForm (f : LFace) (sG : Array Nat) (rhoT : Array E) : Aff :=
  (List.range (2 ^ f.mu)).foldl
    (fun (c : Aff) j =>
      if j < f.planes then Aff.addMul c (Aff.slot (sG.getD j 0)) ((eqTab rhoT).getD j zeroE)
      else c + Aff.ofConst ((eqTab rhoT).getD j zeroE)) (Aff.ofConst zeroE)

/-- The ledger behind the three debts that the hearing lays first. -/
def owed3 (F : Fork) : Fork :=
  (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe "look-up-join").2

/-- **Conditional: at one part of keys. The lookup's rounds are heard**, where the pieces return one
after the other, each from the ledger and the rounds that the one in front has left, the table
side's last point has its size (`hsz`), and the two counts at the end hold (`hslots`, `hlins`). -/
theorem messagesV_intro (f : LFace) (v : Nat) (hp : f.parts = [v]) {F F5 F6 F7 F9 F10 F12 F14 F15
    F16 : Fork} {rs r5 r6 r7 r9 r10 r12 r14 r15 r16 : List Fmt.RoundView} {theta alpha : E}
    {rows : Array Aff} {sZ : Nat} {sG : Array Nat} {jo ze : Array E} {c table : Carried}
    {leaves : MaskedSum.Heard} {bits : MaskedSum.Heard × Aff}
    (e5 : (if f.shifted then drawV else pure zeroE : Hr E) (owed3 F) rs = some (theta, F5, r5))
    (e6 : drawV F5 r5 = some (alpha, F6, r6))
    (e7 : tieV f.planes (f.factor theta alpha) F6 r6 = some ((rows, sZ, sG), F7, r7))
    (e9 : drawsV f.mu F7 r7 = some (jo, F9, r9))
    (e10 : vRun 0 v (f.orders 0) { rows := rows, point := #[], form := Aff.slot sZ } F9 r9 =
      some (c, F10, r10))
    (e12 : vRun f.mu f.d orderDefault
      { rows := c.rows, point := jo.reverse, form := joinForm f sG jo.reverse } F10 r10 =
      some (table, F12, r12))
    (hsz : table.point.size = f.mu + f.d)
    (e14 : openV table.form (leafVars f table.point) F12 r12 = some (leaves, F14, r14))
    (e15 : drawsV (f.mu + f.d) F14 r14 = some (ze, F15, r15))
    (e16 : sumV (Aff.ofConst zeroE) (bitsCall ze.reverse.toList) (fun _ x =>
      subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)) F15 r15 =
      some (bits, F16, r16))
    (hslots : F16.next = F.next + f.slots) (hlins : (table.rows.push bits.2).size = f.lins) :
    messagesV f F rs = some
      ({ theta := theta, alpha := alpha, a := f.factor theta alpha
         rows := table.rows.push bits.2, leaves := leaves, sBit := bits.1.sEnd
         keys := [(c.point, c.form)], zb0 := leaves.r.toArray
         zb1 := (bits.1.r.take (f.mu + f.d)).toArray
         owedObjects := (F.owe "look-up-mask-claims").1
         owedPlanes := ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").1
         owedJoin :=
           (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe "look-up-join").1 },
        F16, r16) := by
  have e8 : partsV (f.parts.length - 1) rows (Aff.slot sZ) F7 r7 =
      some ((rows, [Aff.slot sZ]), F7, r7) := by
    rw [hp]
    rfl
  have e10' : keysV f f.parts.zipIdx [Aff.slot sZ] rows F9 r9 =
      some ((c.rows, [(c.point, c.form)]), F10, r10) := by
    rw [hp]
    exact keysV_one_ret e10
  unfold messagesV
  dsimp only
  refine (bind_ret (slot_ret _ _)).trans ?_
  refine (bind_ret (owe_ret _ _ _)).trans ?_
  refine (bind_ret (owe_ret _ _ _)).trans ?_
  refine (bind_ret (owe_ret _ _ _)).trans ?_
  refine (ite_bind_ret e5).trans ?_
  refine (bind_ret e6).trans ?_
  refine (bind_ret e7).trans ?_
  refine (bind_ret e8).trans ?_
  refine (bind_ret e9).trans ?_
  refine (bind_ret e10').trans ?_
  have m1 : ([(c.point, c.form)].length == f.parts.length) = true := by simp [hp]
  refine (bind_ret (by dsimp only; rw [m1]; exact must_ret _ _)).trans ?_
  refine (bind_ret (of_ret e12)).trans ?_
  have m2 : (table.point.size == f.mu + f.d) = true := by simp [hsz]
  refine (bind_ret (by rw [m2]; exact must_ret _ _)).trans ?_
  refine (bind_ret e14).trans ?_
  refine (bind_ret e15).trans ?_
  refine (bind_ret e16).trans ?_
  refine (bind_ret (slot_ret _ _)).trans ?_
  have m3 : (F16.next == F.next + f.slots && (table.rows.push bits.2).size == f.lins) = true := by
    simp [hslots, hlins]
  refine (bind_ret (by rw [m3]; exact must_ret _ _)).trans ?_
  rfl

/-- The same at a place: the face passes its tests and no round is left over. -/
theorem hearV_intro (f : LFace) (hok : f.ok = true) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : messagesV f F rs = some (g, G, [])) : hearV f F rs = some (g, G) := by
  simp [hearV, hok, h]

#print axioms ProofFile.Honest.K3.Forward.bind_ret
#print axioms ProofFile.Honest.K3.Forward.ite_bind_ret
#print axioms ProofFile.Honest.K3.Forward.pure_ret
#print axioms ProofFile.Honest.K3.Forward.slot_ret
#print axioms ProofFile.Honest.K3.Forward.owe_ret
#print axioms ProofFile.Honest.K3.Forward.of_ret
#print axioms ProofFile.Honest.K3.Forward.must_ret
#print axioms ProofFile.Honest.K3.Forward.drawsV_ret
#print axioms ProofFile.Honest.K3.Forward.drawV_ret
#print axioms ProofFile.Honest.K3.Forward.sumV_ret
#print axioms ProofFile.Honest.K3.Forward.openV_ret
#print axioms ProofFile.Honest.K3.Forward.level_ret
#print axioms ProofFile.Honest.K3.Forward.run_succ_ret
#print axioms ProofFile.Honest.K3.Forward.foldlM_ret
#print axioms ProofFile.Honest.K3.Forward.tieV_ret
#print axioms ProofFile.Honest.K3.Forward.keysV_one_ret
#print axioms ProofFile.Honest.K3.Forward.messagesV_intro
#print axioms ProofFile.Honest.K3.Forward.hearV_intro

end ProofFile.Honest.K3.Forward
