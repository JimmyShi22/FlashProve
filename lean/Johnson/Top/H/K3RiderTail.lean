-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3RiderTail.lean: THE RIDER's LAW FOR IDENTITIES OVER THE POSITIONS: a family of
arrays g on the cube of lt bits, each tested at the LAST lt PLACES OF THE FIRST PART (zx) OF THE
LOOKUP's KEY POINT: «Σ_t eq(zt, t) · g t = 0 for each member, with zt drawn behind what g reads,
gives g = 0 on the cube, at the lookup's own errors». Whoever calls. Definitions, statements and
proofs. AN INSTANTIATION of the library's lookupCR_good through Johnson/Top/H/K3HostLaw.lean; no new
mathematics. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Why. Two kinds test identities over the positions at that stretch of the point: the layers' one-hot
rows (K4) and the output head's two lines clip and table (K6). Their files state their forms' worth
as a sum over the positions under the equality weights of the array zt THAT THE PROGRAM's TEXT HOLDS
(bytes: OnBytes.Model.eqOne). The library's rider speaks of Blocks.ext at coordinates of the typed
point. This file lays the two side by side, the order of the bits held by Lean (the library's
Fo.eqOne_blocks: coordinate number t goes with bit lt − 1 − t: the highest first).

OBJECT: no text that runs: the library's lookup block with riders, at identities over the positions.
USER: Johnson/Top/H/K3RiderTailDeg.lean, K3RiderK6.lean; Johnson/Desc/First/Look/K3CallerHead.lean.
LETTERS: the caller c, lt, the reads and the arrays g: all free.
Compiled with the whole library.

Main names:
  `tailPlaces h lt`: the places dT − lt, …, dT − 1 of the key point.
  `tailId c lt reads g`: the guest's identity (K3HostLaw.lean's GuestId) with these places.
  `tailId_lawful`: under FoNums.ok and lt ≤ dT the places are different places of the key point.
  `tail_good`: THE LAW: for every list of such identities the lookup with these riders is Good (the
    library's property of a block over the caller's signature: knowledge soundness among it), and
    ITS LIST OF BAD CHALLENGES IS THE PLAIN LOOKUP's (Cb.Fo.forEps): NO CHARGE IS ADDED.
  `tail_src`: the riders' clause in the joint IN FRONT: every array is 0 at every t < 2^lt.
  `tail_tgt`: their clause in the joint BEHIND: for every array Σ_{t < 2^lt} eqN lt 0 (the point's
    last lt places of zx) t · g t = 0.
  `IsTail ρ zt pt dT`: the text's array zt, read by ρ, is that stretch of the typed point.
  `tail_tgt_bytes`: under IsTail the clause behind is Σ_{t < 2^lt} ρ (eqOne zt t) · g t = 0: the
    shape of the kinds' right-hand sides.

THE ERROR, AS NUMBERS. A false member alone has at most one bad value in each round that draws one
of its lt places, none elsewhere [the library's doomed_rider at degree 1; here not cut down to the
lt rounds: its list has a 1 at every round that binds a place]. In the block it is taken under the
MAXIMUM with the lookup's own count in the same round (2 of |E| in a sumcheck's round; 1 of |E| at
the round LINE), at a fixed tuple of messages. So the block's list is forEps |E| h, with riders as
without; its sum is at most 2048 / 2^158 (Johnson/Desc/First/Look/K3CallerErr.lean).

Limits. Those of K3HostLaw.lean. g IS A LETTER: a function of the state in front and the tuple of
messages. That the messages which g reads stand sent when the lookup's first challenge is drawn is
not a notion of this statement: at a caller whose signature holds such messages alone (K3CallerAtt |
K3CallerLay.lean) it holds by type. IsTail is a premise: that the text's zt is that stretch of the
point is the tie of the text's hearing to the typed transcript. The maximum is taken at a fixed
tuple, for clauses on the statement and the tuple alone. RiderBites is owed.
Not claimed: the soundness of any text that runs; anything on completeness or hiding.

-/
import Johnson.Top.H.K3HostLaw
import OnBytes.Tie.Pv.Lookup.Ends.FoTailKf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole
open Cb.Fo Cb.Rider

/-- The last lt places of the first part of the key point. -/
def tailPlaces (h : Sh) (lt : ℕ) : List ℕ := (List.range lt).map fun t => h.dT - lt + t

theorem tailPlaces_len (h : Sh) (lt : ℕ) : (tailPlaces h lt).length = lt := by
  unfold tailPlaces
  rw [List.length_map, List.length_range]

theorem tailPlaces_getD (h : Sh) {lt t : ℕ} (ht : t < lt) :
    (tailPlaces h lt).getD t 0 = h.dT - lt + t := by
  unfold tailPlaces
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
  rfl

/-- **An identity over the positions, as a guest's identity.** -/
def tailId (c : LookupCCaller) (lt : ℕ) (reads : List c.Sg.O)
    (g : c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E) : GuestId c := ⟨tailPlaces c.h lt, reads, g⟩

theorem tailId_lawful {c : LookupCCaller} (hc : FoNums.ok c.h = true) {lt : ℕ}
    (hl : lt ≤ c.h.dT) (reads : List c.Sg.O) (g : c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E) :
    (tailId c lt reads g).Lawful := by
  refine ⟨?_, fun j hj => ?_⟩
  · show ((List.range lt).map fun t => c.h.dT - lt + t).Nodup
    refine (List.nodup_range (n := lt)).map_on fun t _ t' _ e => ?_
    exact Nat.add_left_cancel e
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hj
    have h1 : t < lt := List.mem_range.1 ht
    have h2 := ok_v hc
    have h3 : c.h.v = c.h.dT + c.h.rK := rfl
    omega

section
variable {c : LookupCCaller} (lt : ℕ)
  (gs : List (List c.Sg.O × (c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E)))

/-- The identities of a list of arrays, each with the messages that it names. -/
def tailIds : List (GuestId c) := gs.map fun x => tailId c lt x.1 x.2

/-- **THE RIDER's LAW.** -/
theorem tail_good (hc : FoNums.ok c.h = true) (hl : lt ≤ c.h.dT) :
    ((kLookupCR [riderOf c (tailIds lt gs)]).toKind.block (riderOf c (tailIds lt gs))).Good ∧
      errList ((kLookupCR [riderOf c (tailIds lt gs)]).ε (riderOf c (tailIds lt gs))) =
        forEps (Fintype.card Cb.Gl.E) c.h :=
  ⟨lookupCR_good [riderOf c (tailIds lt gs)] (riderOf_ok _ hc)
      (riderOf_sel fun G hG => by
        obtain ⟨x, _, rfl⟩ := List.mem_map.1 hG
        exact tailId_lawful hc hl x.1 x.2) _ (List.mem_singleton.2 rfl),
    forB_eps Cb.Gl.E c.h c.L V₀ V₀C c.Ex⟩

/-- What holds of every member of a list that is made by a map, place by place. -/
theorem forall_get_map {α β : Type} (f : α → β) (l : List α) (P : β → Prop) :
    (∀ i : Fin (l.map f).length, P ((l.map f).get i)) ↔ ∀ x ∈ l, P (f x) := by
  constructor
  · intro h x hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 (List.mem_map_of_mem (f := f) hx)
    rw [← hi]
    exact h i
  · intro h i
    obtain ⟨x, hx, e⟩ := List.mem_map.1 (List.get_mem (l.map f) i)
    rw [← e]
    exact h x hx

/-- **The riders' clause in front**: every array is 0 on the cube. -/
theorem tail_src (m : c.Sg.Msg) (a : c.St₀ × c.Ex.Str) :
    (riderOf c (tailIds lt gs)).src m a ↔ ∀ x ∈ gs, ∀ t < 2 ^ lt, x.2 a.1 m t = 0 := by
  rw [riderOf_src]
  refine (forall_get_map (fun x => tailId c lt x.1 x.2) gs
    fun G => ∀ X < 2 ^ G.places.length, G.cells a.1 m X = 0).trans ?_
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  show (∀ X < 2 ^ (tailPlaces c.h lt).length, x.2 a.1 m X = 0) ↔ _
  rw [tailPlaces_len]

/-- An identity's worth at a point: the sum over the cube under the equality weights of the point's
last lt places of zx. -/
theorem tailId_val (reads : List c.Sg.O) (g : c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E) (st : c.St₀)
    (m : c.Sg.Msg) (z : ℕ → Cb.Gl.E) :
    (tailId c lt reads g).val st m z =
      ∑ t ∈ Finset.range (2 ^ lt), Blocks.eqN lt 0 (fun t => z (c.h.dT - lt + t)) t * g st m t := by
  show Blocks.ext (tailPlaces c.h lt).length (g st m) (fun t => z ((tailPlaces c.h lt).getD t 0)) =
    _
  rw [tailPlaces_len,
    Blocks.ext_congr_point (z' := fun t => z (c.h.dT - lt + t))
      (fun t ht => by rw [tailPlaces_getD c.h ht]) (g st m)]
  rfl

/-- **The riders' clause behind.** -/
theorem tail_tgt (m : c.Sg.Msg)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) :
    (riderOf c (tailIds lt gs)).tgt m b ↔ ∀ x ∈ gs,
      ∑ t ∈ Finset.range (2 ^ lt),
        Blocks.eqN lt 0 (fun t => b.1.2.1.pt (c.h.dT - lt + t)) t * x.2 b.1.1.1 m t = 0 := by
  rw [riderOf_tgt]
  refine (forall_get_map (fun x => tailId c lt x.1 x.2) gs
    fun G => G.val b.1.1.1 m b.1.2.1.pt = 0).trans ?_
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  rw [tailId_val]

end

/-! ### the text's array of bytes -/

section Bytes
open OnBytes OnBytes.Model
variable (ρ : Reading Cb.Gl.E)

/-- **The text's array zt, read by ρ, is the last zt.size places of zx of the typed point.** -/
def IsTail (zt : Array OnBytes.E) (pt : ℕ → Cb.Gl.E) (dT : ℕ) : Prop :=
  ∀ t < zt.size, ρ.val (zt.getD t zeroE) = pt (dT - zt.size + t)

/-- Under IsTail the library's equality weight is the reading of the program's. -/
theorem eqN_of_isTail {zt : Array OnBytes.E} {pt : ℕ → Cb.Gl.E} {dT : ℕ} (h : IsTail ρ zt pt dT)
    (hz : zt.size ≤ 63) {t : ℕ} (ht : t < 2 ^ zt.size) :
    Blocks.eqN zt.size 0 (fun t => pt (dT - zt.size + t)) t = ρ.val (eqOne zt t) := by
  rw [Fo.eqOne_blocks ρ zt t (by
    unfold eqIndexOK
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hz, decide_eq_true ht⟩)]
  unfold Blocks.eqN
  refine Finset.prod_congr rfl fun s hs => ?_
  have hs' : s < zt.size := Finset.mem_range.1 hs
  have e : Blocks.ofList (Fo.rdL ρ zt) (0 + s) = pt (dT - zt.size + (0 + s)) := by
    rw [Nat.zero_add]
    show (Fo.rdL ρ zt).getD s 0 = _
    rw [← Fo.rdL_getD]
    exact h s hs'
  rw [e]

/-- **The riders' clause behind, in the program's equality weights.** -/
theorem tail_tgt_bytes {c : LookupCCaller}
    (gs : List (List c.Sg.O × (c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E))) (m : c.Sg.Msg)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) (zt : Array OnBytes.E)
    (hz : zt.size ≤ 63) (h : IsTail ρ zt b.1.2.1.pt c.h.dT) :
    (riderOf c (tailIds zt.size gs)).tgt m b ↔ ∀ x ∈ gs,
      ∑ t ∈ Finset.range (2 ^ zt.size), ρ.val (eqOne zt t) * x.2 b.1.1.1 m t = 0 := by
  rw [tail_tgt]
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  rw [Finset.sum_congr rfl fun t ht => by
    rw [eqN_of_isTail ρ h hz (Finset.mem_range.1 ht)]]

end Bytes

#print axioms tailId_lawful
#print axioms tail_good
#print axioms tail_src
#print axioms tail_tgt
#print axioms eqN_of_isTail
#print axioms tail_tgt_bytes

end VerifiableInference.OnPublicFiles
