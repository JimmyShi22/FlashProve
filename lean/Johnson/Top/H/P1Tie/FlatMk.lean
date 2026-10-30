-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/P1Tie/FlatMk.lean: the flat functions of the masked sumcheck (OnBytes/K/Kc/Flat.lean)
on a tape that is written out: where the next rounds have the names and the numbers that a function
asks, it returns, and what it returns is written with the part's own functions
(Johnson/Desc/Part/MaskedSum4.lean: complete, valueAt), by Johnson/Top/H/P1Tie/Words.lean. Theorems.

The other direction (a function returns: so the tape was such) stands in
Johnson/Top/H/FlPort/PscRun.lean.
`pscAt`: the verifier program's record in the course of a sumcheck, with its variables and
challenges as lists.

Limits. Rounds in a variable that is summed at a point alone. Nothing is said where a function
refuses. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.P1Tie.Words
import Johnson.Top.H.Cut.CutWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Aff Fork Psc RoundForm)
open VerifiableInference.Desc.K3Cut (bindM mustM stepW)

/-! ## Steps on the tape -/

theorem onTapeM {α : Type} {g : Tape → Option (α × Tape)} {t u : Tape} {a : α}
    (h : g t = some (a, u)) (F : Fork) :
    Fl.onTape g F t = some (a, F, u) := by
  show (g t).map (fun x => (x.1, F, x.2)) = _
  rw [h]
  rfl

theorem changeM {f : Fork → Option Fork} {F G : Fork} (h : f F = some G) (t : Tape) :
    Fl.change f F t = some ((), G, t) := by
  show (f F).map (fun G => ((), G, t)) = _
  rw [h]
  rfl

theorem closeOne_mk (name : String) (nz w : Nat) (x : E) (t : Tape) :
    closeOne name nz (⟨some name, nz, w, [], [x]⟩ :: t) = some (x, t) := by
  simp [closeOne]

theorem emptyOn_mk (name : String) (w : Nat) (t : Tape) :
    Fl.emptyOn name (⟨some name, 0, w, [], []⟩ :: t) = some ((), t) := by
  simp [Fl.emptyOn, closeN]

theorem recvLoop_mk (nm : Option String) (z w : Nat) (d : List E) (t : Tape) :
    ∀ (xs : List E) (a : Array E) (s : List E),
    recvLoop xs.length a (⟨nm, z, w, xs ++ s, d⟩ :: t) =
      some ((a.toList ++ xs).toArray, ⟨nm, z, w, s, d⟩ :: t)
  | [], a, s => by
    show some (a, (⟨nm, z, w, s, d⟩ : FlatRound) :: t) =
      some ((a.toList ++ []).toArray, ⟨nm, z, w, s, d⟩ :: t)
    simp
  | x :: xs, a, s => by
    show recvLoop xs.length (a.push x) (⟨nm, z, w, xs ++ s, d⟩ :: t) = _
    rw [recvLoop_mk nm z w d t xs (a.push x) s]
    simp

theorem recvN_mk (nm : Option String) (z w : Nat) (d : List E) (t : Tape) (xs : List E) :
    recvN xs.length (⟨nm, z, w, xs, d⟩ :: t) = some (xs.toArray, ⟨nm, z, w, [], d⟩ :: t) := by
  have h := recvLoop_mk nm z w d t xs (Array.emptyWithCapacity xs.length) []
  rw [List.append_nil] at h
  unfold recvN
  rw [h]
  rfl

theorem readM (nm : Option String) (z w : Nat) (d : List E) (t : Tape) (xs : List E) (n : Nat)
    (hn : n = xs.length)
    (F : Fork) : Fl.read n F (⟨nm, z, w, xs, d⟩ :: t) =
      some (xs.toArray, F, ⟨nm, z, w, [], d⟩ :: t) := by
  subst hn
  exact onTapeM (recvN_mk nm z w d t xs) F

/-! ## The record in the course of a sumcheck -/

/-- `verify-on-bytes`'s record: begun; no row made; the variables and the challenges so far as
lists. -/
def pscAt (C : Aff) (T eps : E) (first : Nat) (vs : List Var) (r : List E) (c : E) (ended : Bool) :
    Psc :=
  { start := C, target := T, eps := eps, claim := c, first := first,
    vars := (vs.map Var.weight).toArray
    r := r.toArray, ended := ended, rowMade := false, started := true }

theorem psc_eq (h : Heard) (b : Bool) :
    h.psc b = pscAt h.start h.target h.eps h.first h.vars h.r h.claim b := rfl

theorem pscAt_push (C : Aff) (T eps : E) (first : Nat) (vs : List Var) (r : List E) (c c' z x : E)
    (d : Nat)
    (b b' : Bool) :
    ({ pscAt C T eps first vs r c b with
        claim := c', vars := (pscAt C T eps first vs r c b).vars.push
          (OnBytes.Psc.Weight.equality z d),
        r := (pscAt C T eps first vs r c b).r.push x, ended := b' } : Psc) =
      pscAt C T eps first (vs ++ [Var.point z d]) (r ++ [x]) c' b' := by
  simp [pscAt, Var.weight]

/-! ## The four functions -/

theorem pscBegin_mk {C : Aff} {F : Fork} {T : E} (mu eps : E) (w : Nat) (t : Tape)
    (hT : F.publicPart C = some T) :
    Fl.pscBegin C F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) =
      some (pscAt C T eps F.next [] [] (addE mu (mulE eps T)) false, { F with next := F.next + 1 },
        t) := by
  have h0 : Fl.publicPart C F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) =
      some (T, F, ⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) := by
    show (F.publicPart C).map _ = _
    rw [hT]
    rfl
  have h1 : Fl.pscBeginAt T F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) =
      some ({ target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T) },
        { F with next := F.next + 1 }, t) := by
    unfold Fl.pscBeginAt
    refine bindM (a := F.next) (F1 := { F with next := F.next + 1 })
      (t1 := ⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) rfl ?_
    refine bindM (a := mu) (F1 := { F with next := F.next + 1 })
      (t1 := ⟨some Model.RoundName.pscEpsilon.name, 0, w, [], [eps]⟩ :: t) rfl ?_
    refine bindM (onTapeM (closeOne_mk _ 0 w eps t) _) ?_
    rfl
  unfold Fl.pscBegin
  refine bindM h0 ?_
  refine bindM h1 ?_
  rfl

/-- One round in a variable that is summed at z, d coefficients. draw: how the round is closed. -/
theorem pscRound_mk (p : Psc) (z : E) (d : Nat) (hd : 2 ≤ d) (draw : Tape → Option (E × Tape))
    (nm : Option String)
    (nz w : Nat) (sent : List E) (x : E) (t : Tape) (F : Fork) (hs : sent.length + 1 = d)
    (hdraw : draw (⟨nm, nz, w, [], [x]⟩ :: t) = some (x, t)) :
    Fl.pscRound p (OnBytes.Psc.Weight.equality z d) draw F (⟨nm, nz, w, sent, [x]⟩ :: t) =
      some ((x, { p with claim := valueAt (complete (.point z d) sent p.claim) x,
                         vars := p.vars.push (OnBytes.Psc.Weight.equality z d), r := p.r.push x }),
        { F with next := F.next + (d - 1) }, t) := by
  unfold Fl.pscRound
  refine bindM (mustM (equality_held z d hd) _ _) ?_
  refine bindM (readM nm nz w [x] t sent _ (by show d - 1 = sent.length; omega) F) ?_
  refine bindM (mustM (by show (sent.toArray.size + 1 == d) = true; simp [hs]) _ _) ?_
  refine bindM (onTapeM hdraw F) ?_
  refine bindM (a := F.next) (F1 := { F with next := F.next + (d - 1) }) (t1 := t) rfl ?_
  rw [← complete_eq z p.claim sent d hs]
  rfl

theorem roundIn_mk (form : RoundForm) (degree : Nat) (C : Aff) (T eps : E) (first : Nat)
    (vs : List Var) (r : List E)
    (c z : E) (d : Nat) (hd : 2 ≤ d) (hw :
      form.weight z degree = some (OnBytes.Psc.Weight.equality z d)) (w : Nat)
    (sent : List E) (x : E) (t : Tape) (F : Fork) (hs : sent.length + 1 = d) :
    Fl.roundIn form (pscAt C T eps first vs r c false) z degree F
        (⟨some Model.RoundName.pscRound.name, 0, w, sent, [x]⟩ :: t) =
      some ((x, pscAt C T eps first (vs ++ [Var.point z d]) (r ++ [x])
        (valueAt (complete (.point z d) sent c) x) false),
        { F with next := F.next + (d - 1) }, t) := by
  rw [← pscAt_push C T eps first vs r c _ z x d false false]
  unfold Fl.roundIn
  refine bindM (mustM rfl _ _) ?_
  refine bindM (a := OnBytes.Psc.Weight.equality z d) (F1 := F)
    (t1 := ⟨some Model.RoundName.pscRound.name, 0, w, sent, [x]⟩ :: t) (by
      -- the test's older name is said first: the rewriting finds it whichever name Flat.lean bears
      show Fl.need (form.weight z degree) F _ = _
      rw [hw]
      rfl) ?_
  exact pscRound_mk _ z d hd _ _ 0 w sent x t F hs (closeOne_mk _ 0 w x t)

theorem weight_eq2 (z : E) : RoundForm.eq2.weight z 0 = some (OnBytes.Psc.Weight.equality z 3) :=
    rfl

theorem weight_eq (z : E) (deg : Nat) (h1 : 1 ≤ deg) (h2 : deg ≤ 64) :
    RoundForm.eq.weight z deg = some (OnBytes.Psc.Weight.equality z (deg + 1)) := by
  have h : RoundForm.eq.degreeOK deg = true := by
    simp [RoundForm.degreeOK, h1, h2]
  unfold RoundForm.weight
  rw [if_pos h]
  rfl

/-- The round in the further variable, then the end values. -/
theorem pscEnds_mk (C : Aff) (T eps : E) (first : Nat) (vs : List Var) (r : List E) (c : E)
    (dY n : Nat) (h1 : 1 ≤ dY)
    (h2 : 1 ≤ n) (w w' : Nat) (sentY vals : List E) (beta : E) (t : Tape) (F G : Fork)
      (hs : sentY.length = dY)
    (hv : vals.length = n)
    (hG : ({ F with next := F.next + dY + n } : Fork).hideRun (F.next + dY) vals.toArray beta =
      some G) :
    Fl.pscEnds (pscAt C T eps first vs r c false) dY n F
        (⟨some Model.RoundName.pscY.name, 1, w, sentY, [beta]⟩ ::
          ⟨some Model.RoundName.pscValues.name, 0, w', vals, []⟩ :: t) =
      some ((F.next + dY, pscAt C T eps first (vs ++ [Var.point zeroE (dY + 1)]) (r ++ [beta])
        (valueAt (complete (.point zeroE (dY + 1)) sentY c) beta) true), G, t) := by
  rw [← pscAt_push C T eps first vs r c _ zeroE beta (dY + 1) false true]
  unfold Fl.pscEnds
  refine bindM (mustM (by simp [pscAt, h1, h2]) _ _) ?_
  refine bindM (pscRound_mk _ zeroE (dY + 1) (by omega) _ _ 1 w sentY beta _ F (by omega)
    (closeOne_mk _ 1 w beta _)) ?_
  refine bindM (readM _ 0 w' [] t vals n hv.symm _) ?_
  refine bindM (mustM (by show (vals.toArray.size == n) = true; simp [hv]) _ _) ?_
  refine bindM (onTapeM (emptyOn_mk _ w' t) _) ?_
  refine bindM (a := F.next + dY) (F1 := { F with next := F.next + dY + n }) (t1 := t) rfl ?_
  refine bindM (changeM hG t) ?_
  rfl

/-- The row. -/
theorem pscRow_mk (h : Heard) (hp : ∀ v ∈ h.vars, v.isPoint = true) (hne : h.vars ≠ [])
    (hl : h.r.length = h.vars.length)
    (b : Bool) (S0 : E) (kept : Aff) (F G : Fork) (t : Tape)
    (hG : F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE)
      (subE zeroE oneE) = some G) :
    Fl.pscRow (h.psc b) S0 kept F t =
      some ((rowAff h S0 kept, { h.psc b with rowMade := true }), G, t) := by
  unfold Fl.pscRow
  refine bindM (mustM (by
    cases hv : h.vars with
    | nil => exact absurd hv hne
    | cons v vs => simp [Heard.psc, hv, hl]) _ _) ?_
  refine bindM (changeM (by rw [walk_eq h b hp]; exact hG) t) ?_
  rw [← rowForm_eq h b hp S0 kept]
  rfl

end VerifiableInference.Desc.Part.MaskedSum
