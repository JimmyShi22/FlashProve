-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Step.lean: the relation that every stretch of the lookup keeps
between the flat function's state (ledger, tape, rows so far) and the course's stand; and the step
of Sim.lean in its words.

Main names:
  hs o k pat a b: the mask entries of hidden values whose pattern is pat (false: the next entry of
    the first message; true: of the second), from the entries number a and b on.
  Al: slot by slot, home is that list. Al.plain, Al.keys: a sumcheck's share is split off.
  RowsRel: row by row, the flat function's claim has the value of the course's row in every later
    ledger.
  Shp t u L: the tape t is rounds of the shapes L, then u.
  St: the relation. St.congr: it reads four fields of the stand.
  RC F a c: the form a reads as the course's claim c.
  step: one masked sumcheck keeps St.

Limits. One world W of mask entries; where the flat function returns.

-/
import Johnson.Desc.First.Look.KeyLaw.Sim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole)
open Lk6.PortSim (noClaim)
open Lk6.Mid (Dt Cs RowF pscC heardF slots eqPairsF)

/-! ## The hidden values' mask entries -/

def hs (o k : ℕ → Slot) : List Bool → ℕ → ℕ → List Slot
  | [], _, _ => []
  | false :: bs, a, b => o a :: hs o k bs (a + 1) b
  | true :: bs, a, b => k b :: hs o k bs a (b + 1)

theorem hs_length (o k : ℕ → Slot) : ∀ (pat : List Bool) (a b : ℕ), (hs o k pat a b).length =
    pat.length
  | [], _, _ => rfl
  | false :: bs, a, b => congrArg Nat.succ (hs_length o k bs (a + 1) b)
  | true :: bs, a, b => congrArg Nat.succ (hs_length o k bs a (b + 1))

theorem slots_succ (e : ℕ → Slot) (a n : ℕ) : slots e a (n + 1) = e a :: slots e (a + 1) n := by
  unfold slots
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by
    show e (a + (i + 1)) = e (a + 1 + i)
    congr 1; omega

theorem hs_own (o k : ℕ → Slot) (pat : List Bool) : ∀ (n a b : ℕ),
    hs o k (own n ++ pat) a b = slots o a n ++ hs o k pat (a + n) b
  | 0, a, b => rfl
  | n + 1, a, b => by
    show o a :: hs o k (own n ++ pat) (a + 1) b = _
    rw [hs_own o k pat n (a + 1) b, slots_succ, List.cons_append,
      show a + 1 + n = a + (n + 1) by omega]

theorem hs_two (o k : ℕ → Slot) (pat : List Bool) (a b : ℕ) :
    hs o k (true :: true :: pat) a b = slots k b 2 ++ hs o k pat a (b + 2) := rfl

section Align
variable (home : ℕ → Slot)

/-- Slot by slot, from the slot nx on, home is the list of the pattern's mask entries. -/
def Al (o k : ℕ → Slot) (pat : List Bool) (nx a b : ℕ) : Prop :=
  (List.range' nx pat.length).map home = hs o k pat a b

variable {home}

theorem Al.split {o k : ℕ → Slot} {p1 p2 : List Bool} {nx a b a' b' : ℕ} {L : List Slot}
    (h : Al home o k (p1 ++ p2) nx a b) (hL : hs o k (p1 ++ p2) a b = L ++ hs o k p2 a' b')
    (hl : L.length = p1.length) :
    (List.range' nx p1.length).map home = L ∧ Al home o k p2 (nx + p1.length) a' b' := by
  unfold Al at h ⊢
  rw [hL, List.length_append, ← List.range'_append_1, List.map_append] at h
  exact List.append_inj h (by simp [hl])

theorem own_length (n : ℕ) : (own n).length = n := List.length_replicate

theorem slots_length (e : ℕ → Slot) (a n : ℕ) : (slots e a n).length = n := by simp [slots]

theorem Al.plain {D : Dt} {pat : List Bool} {n nx : ℕ} {s : Cs}
    (h : Al home D.ms D.ix (own n ++ pat) nx s.own s.idx) :
    freshOf D false n s = (List.range' nx n).map home ∧
      Al home D.ms D.ix pat (nx + n) (s.own + n) s.idx := by
  obtain ⟨h1, h2⟩ := h.split (hs_own _ _ _ _ _ _) (by rw [slots_length, own_length])
  rw [own_length] at h1 h2
  exact ⟨h1.symm, h2⟩

theorem Al.keys {D : Dt} {pat : List Bool} {n nx : ℕ} {s : Cs} (hn : 2 ≤ n)
    (h : Al home D.ms D.ix ((own (n - 2) ++ [true, true]) ++ pat) nx s.own s.idx) :
    freshOf D true n s = (List.range' nx n).map home ∧
      Al home D.ms D.ix pat (nx + n) (s.own + (n - 2)) (s.idx + 2) := by
  have e : hs D.ms D.ix ((own (n - 2) ++ [true, true]) ++ pat) s.own s.idx =
      (slots D.ms s.own (n - 2) ++ slots D.ix s.idx 2) ++
        hs D.ms D.ix pat (s.own + (n - 2)) (s.idx + 2) := by
    rw [List.append_assoc, hs_own, List.append_assoc]
    rfl
  obtain ⟨h1, h2⟩ := h.split e (by simp [slots_length, own_length])
  have l : (own (n - 2) ++ [true, true]).length = n := by
    rw [List.length_append, own_length]; show n - 2 + 2 = n; omega
  rw [l] at h1 h2
  exact ⟨h1.symm, h2⟩

end Align

/-! ## Rows, shapes, the relation -/

variable (W : PscF.World) (home : ℕ → Slot)

/-- The flat function's claim a has the value of the course's row r in every later ledger. -/
def RowIs (F : Fork) (a : Aff) (r : RowF) : Prop :=
  r.maps = [] ∧ NoEnt a ∧ ∀ H, Later F H → hidV W home H a = W.form r.masks - r.target

def RowsRel (F : Fork) (as : List Aff) (rs : List RowF) : Prop := List.Forall₂ (RowIs W home F) as
    rs

/-- The form a reads as the course's claim c. -/
def RC (F : Fork) (a : Aff) (c : PscF.PointClaim) : Prop := Reads W home F a c.masks c.value

/-- The tape t is rounds of the shapes L, then u. -/
def Shp (t u : Tape) (L : List Shape) : Prop := ∃ ks, t.map key = ks ++ u.map key ∧ ks.map shK = L

variable {W home}

theorem RowsRel.later {F G : Fork} {as : List Aff} {rs : List RowF} (h : RowsRel W home F as rs)
    (l : Later F G) : RowsRel W home G as rs :=
  List.Forall₂.imp (fun _ _ x => ⟨x.1, x.2.1, fun H hH => x.2.2 H (l.trans hH)⟩) h

theorem RowsRel.snoc {F : Fork} {as : List Aff} {rs : List RowF} {a : Aff} {r : RowF}
    (h : RowsRel W home F as rs) (x : RowIs W home F a r) :
    RowsRel W home F (as ++ [a]) (rs ++ [r]) :=
  List.rel_append h (List.Forall₂.cons x List.Forall₂.nil)

theorem RC.later {F G : Fork} {a : Aff} {c : PscF.PointClaim} (h : RC W home F a c)
    (l : Later F G) : RC W home G a c := Reads.later h l

theorem Shp.refl (t : Tape) : Shp t t [] := ⟨[], rfl, rfl⟩

theorem Shp.trans {t u v : Tape} {L L' : List Shape} (h : Shp t u L) (h' : Shp u v L') :
    Shp t v (L ++ L') := by
  obtain ⟨ks, e1, e2⟩ := h
  obtain ⟨ks', e3, e4⟩ := h'
  exact ⟨ks ++ ks', by rw [e1, e3, List.append_assoc], by rw [List.map_append, e2, e4]⟩

variable (W home) (D : Dt)

/-- **The relation.** pat: the pattern of the hidden values that are still to come. rows: the flat
function's claims so far. -/
structure St (F : Fork) (t : Tape) (s : Cs) (pat : List Bool) (rows : List Aff) : Prop where
  base : Base F t s
  al : Al home D.ms D.ix pat F.next s.own s.idx
  rows : RowsRel W home F rows s.rows

variable {W home D}

theorem St.congr {F : Fork} {t : Tape} {s s' : Cs} {pat : List Bool} {rows : List Aff}
    (h : St W home D F t s pat rows) (h1 : s'.rounds = s.rounds) (h2 : s'.own = s.own)
    (h3 : s'.idx = s.idx) (h4 : s'.rows = s.rows) : St W home D F t s' pat rows :=
  ⟨⟨h.base.sized, h1.trans h.base.rounds⟩, by rw [h2, h3]; exact h.al, by rw [h4]; exact h.rows⟩

/-- **One masked sumcheck keeps the relation.** -/
theorem step {C : Aff} {zs : List E} {dY n : ℕ} {endTerm : List E → E} {F G : Fork}
    {t u : Tape} {w : Whole} {s : Cs} {c : PscF.Claim} {S : PscF.Summand}
    {keys : Bool} {place : List GE → List GE} {pat : List Bool} {rows : List Aff}
    (h : wholeStandIn C zs dY n endTerm F t = some (w, G, u))
    (hst : St W home D F t s
      ((if keys = true then own (1 + 2 * zs.length + dY + n - 2) ++ [true, true]
        else own (1 + 2 * zs.length + dY + n)) ++ pat) rows)
    (hcv : c.vars = zs.map fun z => PscF.Weight.equality (readE z) 3)
    (hC : Reads W home F C c.masks c.target) (hS1 : S.shown = n) (hS2 : S.degree = dY)
    (hn : 1 ≤ n)
    (hS3 : ∀ pt (y : List E), (S.coeffs pt (y.map readE)).headD 0 = readE (endTerm y)) :
    St W home D G u (pscC D c S keys 0 place s).2 pat (rows ++ [w.row]) ∧
      (pscC D c S keys 0 place s).1.point = place ((w.challenges.take zs.length).map readE) ∧
      w.challenges.length = zs.length + 1 ∧
      (∀ i < n, ((pscC D c S keys 0 place s).1.ends.getD i noClaim).point =
          (pscC D c S keys 0 place s).1.point ∧
        RC W home G (Aff.slot (w.sEnd + i)) ((pscC D c S keys 0 place s).1.ends.getD i noClaim)) ∧
      Later F G ∧ Shp t u (pscShape (List.replicate zs.length 2) (some (dY, n))) := by
  have hal : freshOf D keys (1 + 2 * zs.length + dY + n) s =
        (List.range' F.next (1 + 2 * zs.length + dY + n)).map home ∧
      Al home D.ms D.ix pat (F.next + (1 + 2 * zs.length + dY + n))
        (s.own + (if keys = true then 1 + 2 * zs.length + dY + n - 2
          else 1 + 2 * zs.length + dY + n)) (s.idx + (if keys = true then 2 else 0)) := by
    have := hst.al
    cases keys with
    | false => exact Al.plain this
    | true => exact Al.keys (by omega) this
  obtain ⟨o, row, beta, val, e, h1, h2, h3, h4, h5, h6, a, hs', sh⟩ :=
    whole_sim (place := place) D h hst.base hcv hC hS1 hS2 hn hS3 hal.1
  rw [e]
  refine ⟨⟨⟨hs', rfl⟩, ?_, ?_⟩, h1, h2, fun i hi => ?_, a.later, sh⟩
  · rw [a.next]; exact hal.2
  · exact (hst.rows.later a.later).snoc ⟨h4, h5, h6⟩
  · obtain ⟨x1, x2⟩ := h3 i hi
    show (o.ends.getD i noClaim).point = o.point ∧ RC W home G _ (o.ends.getD i noClaim)
    rw [x1]
    exact ⟨rfl, x2⟩

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.step
