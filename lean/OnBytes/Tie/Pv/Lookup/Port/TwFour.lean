-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/TwFour.lean.
A lookup, and a lookup of several calls with its shift: four facts on one term, general in its
sizes, in one statement each.

The four facts: (1) the block is a typed reduction, one term, of which the other three speak; (2)
knowledge soundness alone, at the block's own joints and errors; (3) its rounds bear the entries of
the planner's list, in the sense of ShapeIs; (4) each error, as a share of its round's challenges,
is the quotient from which the planner computes that round's error.
In both statements the planner's own function stands in the premise: P is any plan with finish s sc
(planLookup ..) = .ok P, or finish s sc (planForest (forestSize h)) = .ok P.

Main statements.
  entN_sizes: the sizes of the challenge sets that the entries of TwPlan.entN say are TwErr.nN.
  lookup_four: for every finite field E, every record A of a lookup (LkAsmH), all short sumcheck
    blocks V, VC and each fixed tuple m of committed messages: Know of (A.baseK V VC).R from "every
    key is a row of the table" to "the claim on the keys and all rows hold", with the identity as
    extractor and the errors (A.baseK V VC).e; the rounds of that reduction's shape are the entries
    of P (OnBytes.G4.ShapeIs); and there is a list Q of (c, n, (a, kind)), one for each round, such
    that the c are the list of these very errors, the n are the sizes of the rounds' challenge sets,
    errOf s sc (a, kind) are P's errors, and c · b = a · n. Here b is bOf s.cardE kind
    (Cb/Pv/Lookup/Lists/TwErr.lean): |E| at kind 1, |E| - 1 at kind 2, else 1.
  forest_four: the same for the lookup of several calls on the record h of a forest
    (OnBytes.Model.Forest.Shape): KnowAt, all four fields, from "each call's keys lie in that call's
    table" to "the claim on the joint keys and all rows hold".
Premises, by name. Of the lookup: [CharP E p], A.H.lkb.Adm p, padsOK, A.n + 1 + 1 = 2 ^ A.w; A.oE =
Fin.revPerm (the closing binds its variables from the last to the first); A.w ≤ 6 (the forest:
A0.w = 5); s.cardE = Fintype.card E; that the planner does not refuse.
  Of the forest also: Port.OK h, h.NC ≤ p, h.v = A0.v' + 1, h.d = A0.d.
What is not claimed: that the planner does not refuse at given sizes; that A0 holds what belongs to
h; what ShapeIs lets through (it ties msg, drawE and drawNZ of an entry and nothing else: see
OnBytes/G4/RoundIs.lean); that the binary number errOf s sc (a, kind) is at least a / b; that the
kinds in Q are 0, 1 or 2 (at any other kind errOf divides by |E| - 1 while b is 1); anything on what
a verifier accepts (a block that rejects everything is among V, VC).
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Holes.HoleC
import OnBytes.Tie.Pv.Lookup.Lists.ShiftKLists
import OnBytes.Tie.Pv.Lookup.Lists.TwPlanOne
import OnBytes.Model.RoundSizes

set_option autoImplicit false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4 TwLaw
open OnBytes.Params (Setting Scope Planned finish planLookup planForest)

theorem size_rd0 (q wk : Nat) (name : String) (s k : Nat) : sizeOf q (rd wk name s k) = q ^ k := by
  simp [sizeOf, rd]
theorem size_rd1 (q wk : Nat) (name : String) (s : Nat) : sizeOf q (rd wk name s 1 1) = q - 1 := by
  simp [sizeOf, rd]
theorem size_none (q : Nat) (name : String) (s : Nat) : sizeOf q (rdNone name s) = 1 := by
  simp [sizeOf, rdNone]

theorem psc_sizes (q wk k g gY vals : Nat) : (pscN wk (List.replicate k g) true gY vals).map
    (sizeOf q) = pscV q k := by
  simp [pscN, pscV, size_rd0, size_rd1, size_none]

theorem psc_sizes0 (q wk gY vals : Nat) : (pscN wk [] true gY vals).map (sizeOf q) = pscV q 0 :=
  psc_sizes q wk 0 0 gY vals

/-- The sizes that the entries say are nN. -/
theorem entN_sizes (q wk v' d w n : Nat) : (entN wk v' d w n).map (sizeOf q) = nN v' d w n q := by
  have hc : (pscN wk (List.replicate d 2 ++ List.replicate w 1) false 0 0).map (sizeOf q) = [q] ++
      List.replicate d q ++ List.replicate w q := by
    simp [pscN, size_rd0, -List.replicate_append_replicate]
  simp only [entN, nN, List.map_append, List.map_flatMap, psc_sizes, psc_sizes0, hc, List.map_cons,
      List.map_nil, size_rd0, Nat.pow_one,
    TwLaw.flat_succ (fun _ => pscV q 0) n, List.append_assoc]

section
variable {E : Type} [Field E] [Fintype E] (V : ∀ (Y : PscPar E) Ex, TWhole.ShortK Y Ex)
    (VC : ∀ (Y : PscPar E) Ex, TWhole.ShortKC Y Ex)
  (Ex : ExtSpec)

/-- A lookup: the four facts of the head. -/
theorem lookup_four (A : LkAsmH E) (p : ℕ) [CharP E p] (Kc M Wp : Type)
    (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (hA : A.H.lkb.Adm p) (hP : padsOK (A.v' + 1) A.d A.pads = true) (hF : A.n + 1 + 1 = 2 ^ A.w)
        (ho : A.oE = Fin.revPerm) (hw : A.w ≤ 6)
    (s : Setting) (sc : Scope) (hq : s.cardE = Fintype.card E) (P : Planned)
    (hf : finish s sc (planLookup { v := A.v' + 1, d := A.d, mu := A.w }) = .ok P) (m : M) :
    (A.baseK V VC).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧ A.lk.inR a.1 (msg m))
      (fun b wp => R0.relR (b.1.1, b.2) (m, wp) ∧ A.lk.out id id b.1 (msg m))
      (fun _ _ wp => wp) (A.baseK V VC).e ∧
    ShapeIs E (A.baseK V VC : BkK A.St (TX A.St E A.J) Ex).R.shape (P.rounds.map (·.entry)) ∧
    ∃ Q : List Quad,
      Q.map (·.1) = TWhole.errList (A.baseK V VC : BkK A.St (TX A.St E A.J) Ex).e ∧
      Q.map (·.2.1) = (A.baseK V VC : BkK A.St (TX A.St E A.J) Ex).R.shape.map
          (fun r => Nat.card r.Chal) ∧
      Q.map (fun x => errOf s sc x.2.2) = P.rounds.map (·.error) ∧
      ∀ x ∈ Q, x.1 * bOf s.cardE x.2.2.2 = x.2.2.1 * x.2.1 := by
  have hn : 2 ^ A.w - 2 = A.n := by omega
  obtain ⟨f1, f2⟩ :=
    finish_all (s := s) (sc := sc) { v := A.v' + 1, d := A.d, mu := A.w } A.v' rfl rfl rfl hw hf
  have f1' : P.rounds.map (·.entry) = entN (s.workOf .field sc) A.v' A.d A.w A.n := by
    rw [f1]
    show [] ++ entN (s.workOf .field sc) A.v' A.d A.w (2 ^ A.w - 2) = _
    rw [hn, List.nil_append]
  have f2' : P.rounds.map (·.error) = (ratN A.v' A.d A.w A.n).map (errOf s sc) := by
    rw [f2]
    show ([] ++ ratN A.v' A.d A.w (2 ^ A.w - 2)).map (errOf s sc) = _
    rw [hn, List.nil_append]
  refine ⟨asmK_know E p A V VC Ex Kc M Wp R0 msg hA hP hF m, ?_, quadN A.v' A.d A.w A.n s.cardE, ?_,
      ?_, ?_, rule_all _ _ _ _ _⟩
  · rw [f1']
    exact asmV_shape_port V VC Ex A _ ho
  · rw [quad_c, hq]
    exact (asmV_eps_port V VC Ex A ho).symm
  · rw [quad_n, hq]
    refine Eq.trans ?_ (asmV_sizes V VC Ex A ho).symm
    rw [entN_sizes, Nat.card_eq_fintype_card]
  · rw [f2', ← quad_r A.v' A.d A.w A.n s.cardE, List.map_map]
    rfl

/-- A lookup of several calls, on the record of a forest: the four facts of the head. -/
theorem forest_four (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E) (h : OnBytes.Model.Forest.Shape)
    (T : St → ℕ → ℕ → E) (K : St → (A0.J → E) → ℕ → ℕ → E) (Kc M Wp : Type)
        (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E)
    (hOK : Port.OK h) (hp : h.NC ≤ p) (hv : h.v = A0.v' + 1) (hd : h.d = A0.d) (hA : A0.H.lkb.Adm p)
    (hP : padsOK (A0.v' + 1) A0.d A0.pads = true) (hF : A0.n + 1 + 1 = 2 ^ A0.w)
        (ho : A0.oE = Fin.revPerm) (hw : A0.w = 5)
    (s : Setting) (sc : Scope) (hq : s.cardE = Fintype.card E) (P : Planned)
    (hf : finish s sc (planForest (OnBytes.Model.forestSize h)) = .ok P) :
    TWhole.KnowAt ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := Ex)).R
      (Port.jIn h T K msg R0)
      (cj (ShiftQ.ride R0) msg Prod.fst (((Port.Q h T K).asmH A0).lk.out id id)
          (((Port.Q h T K).asmH A0).lk.out id id))
      (fun _ _ _ wp => wp) ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := Ex)).e ∧
    ShapeIs E ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := Ex)).R.shape
        (P.rounds.map (·.entry)) ∧
    ∃ Q : List Quad,
      Q.map (·.1) = TWhole.errList ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := Ex)).e ∧
      Q.map (·.2.1) = ((Port.Q h T K).allK A0 (Port.several h) V VC (Ex := Ex)).R.shape.map
          (fun r => Nat.card r.Chal) ∧
      Q.map (fun x => errOf s sc x.2.2) = P.rounds.map (·.error) ∧
      ∀ x ∈ Q, x.1 * bOf s.cardE x.2.2.2 = x.2.2.1 * x.2.1 := by
  have hn : A0.n = 30 := by rw [hw] at hF; omega
  have hs : OnBytes.Model.forestSize h = ⟨A0.v' + 1, A0.d, Port.several h⟩ := by
    unfold OnBytes.Model.forestSize Port.several
    rw [hv, hd]
  rw [hs] at hf
  obtain ⟨f1, f2⟩ := finish_forest (s := s) (sc := sc) A0.v' A0.d (Port.several h) hf
  have sh := allK_shape V VC Ex A0 (Port.Q h T K) (Port.several h) (s.workOf .field sc) ho
  have ep := allK_eps V VC Ex A0 (Port.Q h T K) (Port.several h) ho
  rw [hw, hn] at sh ep
  have hPd : (Port.Q h T K).d = A0.d := hd
  rw [hPd] at ep
  refine ⟨Cb.Fo.hC E p St A0 h T K V VC Ex Kc M Wp R0 msg hOK hp hv hd hA hP hF, ?_,
    shHead (Port.several h) (2 ^ A0.d, s.cardE, (2 ^ A0.d, 1)) ++ quadN A0.v' A0.d 5 30 s.cardE, ?_,
        ?_, ?_, ?_⟩
  · rw [f1]
    exact sh
  · rw [List.map_append, quad_c, hq, ep]
    cases Port.several h <;> rfl
  · rw [List.map_append, quad_n, shapeIs_sizes sh, List.map_append, entN_sizes,
      Nat.card_eq_fintype_card, hq]
    cases Port.several h with
    | false => rfl
    | true =>
      show [Fintype.card E] ++ _ = [sizeOf (Fintype.card E) (shiftN (s.workOf .field sc))] ++ _
      rw [show sizeOf (Fintype.card E) (shiftN (s.workOf .field sc)) = Fintype.card E ^ 1 from
          size_rd0 _ _ _ _ _, Nat.pow_one]
  · rw [f2, List.map_append, List.map_append, ← quad_r A0.v' A0.d 5 30 s.cardE, List.map_map]
    cases Port.several h <;> rfl
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · cases hS : Port.several h with
      | false => rw [hS] at hx; cases hx
      | true =>
        rw [hS] at hx
        obtain rfl : x = (2 ^ A0.d, s.cardE, (2 ^ A0.d, 1)) := by simpa [shHead] using hx
        exact ok_same _ _
    · exact rule_all _ _ _ _ _ x hx

end
end TwRound
