-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3RiderK6.lean: THE RIDER's LAW AT THE OUTPUT HEAD's TWO GUESTS, clip AND table, IN
K6's OWN LETTERS: the riders' clause in front of the lookup IS that kind's premise
CornerGuests; the riders' clause behind IS «the right-hand sides of the two last lines of its
K06OutStatement are 0». Whoever calls. Definitions, statements and proofs. NO SOUNDNESS OF ANY TEXT
THAT RUNS IS CLAIMED.

Why. K6's law of the head has two halves around the lookup: OUT (K06OutStatement: at the hidden
scalars and the sent reads clip | table are worth Σ_{t < T} eq zt t · clipAt | tableAt c (corner 0
t)) and BACK (K06BackStatement: … ∧ CornerGuests c ⇒ the relation on cells). «OUT's conclusion ⇒
BACK's premise» is the lookup's law; for the two guests it is the rider's
(Johnson/Top/H/K3RiderTail.lean: tail_good).

OBJECT: no text that runs: the library's lookup block with riders, at two arrays made of K6's
  record of cells.
USER: Johnson/Desc/First/Look/K3CallerHead.lean.
LETTERS: the caller c₀, cOf, the reading rdm: free.
Compiled with the whole library.


Main names:
  `wt_eqN`: K6's product of one factor a coordinate (Law/Corner.lean: wt) is the library's
    Blocks.eqN: THE ORDER OF THE BITS, HELD BY LEAN.
  `k6Arrs c₀ cOf rdm`: the two arrays: t ↦ the reading of clipAt | tableAt (cOf st m) (corner 0 t).
    cOf: THE ONE LETTER: K6's record of cells, off the state in front and the tuple of messages.
  `k6_good`: the rider's law at these two: Good, and the list of bad challenges is the plain
    lookup's.
  `k6_src`: the riders' clause in front ↔ CornerGuests (cOf a.1 m): as records (a canonical element
    that reads as 0 is 0: K6's eq_of_rd with okE_clipAt | okE_tableAt).
  `k6_tgt`: under IsTail (the text's zt, read, is the last lt places of zx of the typed point) and
    zt.size = lt: the riders' clause behind ↔ the two sums of K06OutStatement are 0, as records.
  `k6_tgt_of_out`: so: clip and table worth 0 at a world, with K06OutStatement's two last
    equations there, give the riders' clause behind.
Limits. Those of K3RiderTail.lean. cOf is a letter: at a closed caller it is to be «the integers
behind the committed symbols; Wh off the stored table, by the pin; the token: the reply that was
HEARD, in the state in front». That the arrays are free of the point is by type: cOf reads the state
in front and the messages. IsTail is a premise: it is owed by the kind "lookup". K6's statements
(K06Statement.lean) are taken as they stand at the sum above: if they turn, this file turns.
Not claimed: the soundness of any text that runs; anything on completeness or hiding.

-/
import Johnson.Top.H.K3RiderTailDeg
import Johnson.Desc.Kinds.Law.K06Statement
import Johnson.Desc.Kinds.Law.Lemma2a

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Fork Reading)
open Norm (lt ls d lPd T S2)
open VerifiableInference.OnPublicFiles
open Cb.LdLkp (TX)

/-- **K6's weight is the library's**: one factor a coordinate, that of the highest bit first. -/
theorem wt_eqN : ∀ (l : List K) (i : ℕ), wt l i = Blocks.eqN l.length 0 (Blocks.ofList l) i
  | [], i => by simp [wt, Blocks.eqN]
  | x :: xs, i => by
    have ih := wt_eqN xs i
    unfold Blocks.eqN at ih ⊢
    rw [List.length_cons, Finset.prod_range_succ', wt, ih, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    · have h1 : xs.length + 1 - 1 - (t + 1) = xs.length - 1 - t := by omega
      have h2 : Blocks.ofList (x :: xs) (0 + (t + 1)) = Blocks.ofList xs (0 + t) := by
        unfold Blocks.ofList
        rw [Nat.zero_add, Nat.zero_add, List.getD_cons_succ]
      rw [h1, h2]

/-- Under IsTail the library's equality weight at the typed point's stretch is the reading of part
4's eq at the text's array. -/
theorem eqN_of_isTail_eq {zt : Point} {pt : ℕ → K} {dT : ℕ} (h : IsTail Reading.gl zt pt dT)
    {t : ℕ} (ht : t < 2 ^ zt.size) :
    Blocks.eqN zt.size 0 (fun s => pt (dT - zt.size + s)) t = rd (eq zt t) := by
  rw [rd_eq, if_pos ht, wt_eqN, List.length_map, Array.length_toList]
  refine eqN_congr (fun s hs => ?_) t
  rw [Nat.zero_add]
  show pt (dT - zt.size + s) = (zt.toList.map rd).getD s 0
  rw [← h s hs, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases zt[s]? <;> rfl

variable [Sizes] [Policy] [Request] [Token]

section
variable (c₀ : LookupCCaller) (cOf : c₀.St₀ → c₀.Sg.Msg → Cells) (rdm : List c₀.Sg.O)

/-- **The two guests' arrays.** -/
def k6Arrs : List (List c₀.Sg.O × (c₀.St₀ → c₀.Sg.Msg → ℕ → Cb.Gl.E)) :=
  [(rdm, fun st m t => rd (clipAt (cOf st m) (corner 0 t))),
    (rdm, fun st m t => rd (tableAt (cOf st m) (corner 0 t)))]

/-- **THE RIDER's LAW AT THE TWO GUESTS.** -/
theorem k6_good (hc : FoNums.ok c₀.h = true) (hl : lt ≤ c₀.h.dT) :
    ((kLookupCR [riderOf c₀ (tailIds lt (k6Arrs c₀ cOf rdm))]).toKind.block
        (riderOf c₀ (tailIds lt (k6Arrs c₀ cOf rdm)))).Good ∧
      TWhole.errList ((kLookupCR [riderOf c₀ (tailIds lt (k6Arrs c₀ cOf rdm))]).ε
          (riderOf c₀ (tailIds lt (k6Arrs c₀ cOf rdm)))) =
        Cb.Fo.forEps (Fintype.card Cb.Gl.E) c₀.h :=
  tail_good lt (k6Arrs c₀ cOf rdm) hc hl

theorem rd_zero_iff {x : E} (hx : okE x = true) : rd x = 0 ↔ x = 0 :=
  ⟨fun h => eq_of_rd hx okE_zero (h.trans rd_zero.symm), fun h => by rw [h, rd_zero]⟩

/-- **THE RIDERS' CLAUSE IN FRONT IS CornerGuests.** -/
theorem k6_src (m : c₀.Sg.Msg) (a : c₀.St₀ × c₀.Ex.Str) :
    (riderOf c₀ (tailIds lt (k6Arrs c₀ cOf rdm))).src m a ↔ CornerGuests (cOf a.1 m) := by
  rw [tail_src]
  constructor
  · intro h t ht
    exact ⟨(rd_zero_iff (okE_clipAt _ _)).1 (h _ (List.mem_cons_self) t ht),
      (rd_zero_iff (okE_tableAt _ _)).1
        (h _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) t ht)⟩
  · intro h x hx t ht
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (rd_zero_iff (okE_clipAt _ _)).2 (h t ht).1
    · obtain rfl := List.mem_singleton.1 hx
      exact (rd_zero_iff (okE_tableAt _ _)).2 (h t ht).2

/-- The reading of a sum of K06OutStatement's shape. -/
theorem rd_outSum {zt : Point} {pt : ℕ → K} {dT : ℕ} (h : IsTail Reading.gl zt pt dT)
    (hz : zt.size = lt) (g : ℕ → E) :
    rd (∑ t < T, eq zt t * g t) =
      ∑ t ∈ Finset.range (2 ^ lt), Blocks.eqN lt 0 (fun s => pt (dT - lt + s)) t * rd (g t) := by
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < 2 ^ zt.size := by
    rw [hz]
    exact Finset.mem_range.1 ht
  rw [rd_mul, ← eqN_of_isTail_eq h ht', hz]

/-- **THE RIDERS' CLAUSE BEHIND IS: K06OutStatement's TWO SUMS ARE 0.** -/
theorem k6_tgt (m : c₀.Sg.Msg)
    (b : TX (c₀.St₀ × Cb.Gl.E) Cb.Gl.E (Option c₀.J₀) × c₀.Ex.Str) (zt : Point)
    (hz : zt.size = lt) (h : IsTail Reading.gl zt b.1.2.1.pt c₀.h.dT) :
    (riderOf c₀ (tailIds lt (k6Arrs c₀ cOf rdm))).tgt m b ↔
      (∑ t < T, eq zt t * clipAt (cOf b.1.1.1 m) (corner 0 t)) = 0 ∧
        (∑ t < T, eq zt t * tableAt (cOf b.1.1.1 m) (corner 0 t)) = 0 := by
  rw [tail_tgt, ← rd_zero_iff (okE_sumTo _ _), ← rd_zero_iff (okE_sumTo _ _), rd_outSum h hz,
    rd_outSum h hz]
  constructor
  · intro g
    have hc := g (rdm, fun st m t => rd (clipAt (cOf st m) (corner 0 t))) List.mem_cons_self
    have ht := g (rdm, fun st m t => rd (tableAt (cOf st m) (corner 0 t)))
      (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
    exact ⟨hc, ht⟩
  · intro g x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact g.1
    · obtain rfl := List.mem_singleton.1 hx
      exact g.2

/-- **From the head's OUT to the riders' clause behind**: v, w: what clip and table are worth in the
world at hand. -/
theorem k6_tgt_of_out (m : c₀.Sg.Msg)
    (b : TX (c₀.St₀ × Cb.Gl.E) Cb.Gl.E (Option c₀.J₀) × c₀.Ex.Str) (zt : Point)
    (hz : zt.size = lt) (h : IsTail Reading.gl zt b.1.2.1.pt c₀.h.dT) {v w : E} (hv : v = 0)
    (hw : w = 0) (ev : v = ∑ t < T, eq zt t * clipAt (cOf b.1.1.1 m) (corner 0 t))
    (ew : w = ∑ t < T, eq zt t * tableAt (cOf b.1.1.1 m) (corner 0 t)) :
    (riderOf c₀ (tailIds lt (k6Arrs c₀ cOf rdm))).tgt m b :=
  (k6_tgt c₀ cOf rdm m b zt hz h).2 ⟨ev.symm.trans hv, ew.symm.trans hw⟩

end

#print axioms wt_eqN
#print axioms k6_good
#print axioms k6_src
#print axioms k6_tgt
#print axioms k6_tgt_of_out

end VerifiableInference.Desc.Kinds.Head.Law
