-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Same.lean: kind K5: whether the claims' routines return depends on
public numbers and lengths alone: the readers.

Main names:
  `Same i i'`: two records of what the runs read (Johnson/Desc/First/Att/RunsP.lean: In) agree in
    what is public: the place's numbers (Geo) are one; the tables' first entries and lengths are
    one, and the two points ptM and ptD have one length; unit by unit: the call, the plane claim's
    number, isD, np, each piece's layer and head, the lengths of the inner point and of the
    sumcheck's challenges; of the division: the pieces' layers and heads, the call that holds wh,
    the lengths of zcW and zcH; of the maximum: the length of the first sumcheck's challenges. No
    field element, no form and no slot's number is compared.
  `rs_…`: each routine at i and at i' returns at both or at neither (`RS`,
    Johnson/Desc/First/Att/Claims/RS.lean).
Nothing of OnBytes is used but the types Aff and E.
Not claimed: that a routine returns anywhere; what it returns.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.RS

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP DivP MaxP Pts SumP TablesP Geo Ten CallG)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP)

variable {K : ℕ}

/-! ### lengths -/

theorem size_fold_push2 (f g : E → E) : ∀ (l : List E) (n : Array E),
    (l.foldl (fun n a => (n.push (f a)).push (g a)) n).size = n.size + 2 * l.length
  | [], n => by simp
  | a :: l, n => by
    rw [List.foldl_cons, size_fold_push2 f g l]
    simp only [Array.size_push, List.length_cons]
    omega

theorem eqTab_size (z : Array E) : (P.eqTab z).size = 2 ^ z.size := by
  unfold P.eqTab
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (t : Array E),
      (l.foldl (fun t zv => t.foldl (fun n a =>
        let hi := mulE a zv
        (n.push (subE a hi)).push hi) (Array.emptyWithCapacity (2 * t.size))) t).size
        = 2 ^ l.length * t.size := by
    intro l
    induction l with
    | nil => intro t; simp
    | cons zv l ih =>
      intro t
      rw [List.foldl_cons, ih, ← Array.foldl_toList]
      rw [size_fold_push2 (fun a => subE a (mulE a zv)) (fun a => mulE a zv)]
      have e0 : (Array.emptyWithCapacity (2 * t.size) : Array E).size = 0 := rfl
      rw [e0, List.length_cons, Array.length_toList (xs := t)]
      ring
  rw [key]
  simp

/-! ### what is public of what the runs read -/

/-- Piece by piece: one layer, one head. -/
def SameW (a b : Array W1) : Prop :=
  List.Forall₂ (fun w w' => w.lam = w'.lam ∧ w.a = w'.a) a.toList b.toList

structure SameT (t t' : TablesP) : Prop where
  ptM : t.ptM.size = t'.ptM.size
  ptD : t.ptD.size = t'.ptD.size
  tA : t.tA = t'.tA
  tVM : t.tVM = t'.tVM
  tVD : t.tVD = t'.tVD
  score : t.score = t'.score
  hW : t.hW = t'.hW
  hX : t.hX = t'.hX
  hE : t.hE = t'.hE
  hT : t.hT = t'.hT
  hPi : t.hPi = t'.hPi
  hR2 : t.hR2 = t'.hR2
  tO : t.tO = t'.tO
  qO : t.qO = t'.qO
  qVM : t.qVM = t'.qVM
  qVD : t.qVD = t'.qVD
  qF : t.qF = t'.qF
  qKx : t.qKx = t'.qKx
  tabLen : t.tabLen = t'.tabLen

structure SameRem (c c' : RemP) : Prop where
  call : c.call = c'.call
  z : c.z.size = c'.z.size
  isD : c.isD = c'.isD
  pw : SameW c.pw c'.pw
  np : c.np = c'.np

structure SameScore (k k' : ScoreP) : Prop where
  call : k.call = k'.call
  claim : k.claim = k'.claim
  pw : SameW k.pw k'.pw
  r : k.sc.r.size = k'.sc.r.size

structure SameDiv (d d' : DivP) : Prop where
  pwW : SameW d.pwW d'.pwW
  pwX : SameW d.pwX d'.pwX
  pwH : SameW d.pwH d'.pwH
  qWH : d.qWH = d'.qWH
  zcW : d.zcW.size = d'.zcW.size
  zcH : d.zcH.size = d'.zcH.size

structure SameP (p p' : Pts) : Prop where
  planes : List.Forall₂ SameRem p.planes.toList p'.planes.toList
  scores : List.Forall₂ SameScore p.scores.toList p'.scores.toList
  d : SameDiv p.d p'.d
  rF : p.x.scF.r.size = p'.x.scF.r.size

/-- **Two records of what the runs read agree in what is public.** -/
structure Same (i i' : In) : Prop where
  g : i.g = i'.g
  p : SameP i.p i'.p
  t : SameT i.t i'.t

/-! ### lists member by member -/

theorem forall₂_getElem? {α α' : Type} {R : α → α' → Prop} :
    ∀ {l : List α} {l' : List α'}, List.Forall₂ R l l' → ∀ n : ℕ, OptRel R l[n]? l'[n]?
  | _, _, .nil, _ => trivial
  | _, _, .cons h _, 0 => h
  | _, _, .cons _ hl, n + 1 => by
    simp only [List.getElem?_cons_succ]
    exact forall₂_getElem? hl n

theorem forall₂_zipIdx {α α' : Type} {R : α → α' → Prop} :
    ∀ {l : List α} {l' : List α'}, List.Forall₂ R l l' → ∀ n,
      List.Forall₂ (fun x x' => R x.1 x'.1 ∧ x.2 = x'.2) (l.zipIdx n) (l'.zipIdx n)
  | _, _, .nil, _ => .nil
  | _, _, .cons h hl, n => by
    simp only [List.zipIdx_cons]
    exact .cons ⟨h, rfl⟩ (forall₂_zipIdx hl (n + 1))

theorem sameW_getD {a b : Array W1} (h : SameW a b) (n : ℕ) :
    (a.getD n default).lam = (b.getD n default).lam ∧ (a.getD n default).a = (b.getD n default).a := by
  have := forall₂_getElem? h n
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← Array.getElem?_toList]
  cases h1 : a.toList[n]? <;> cases h2 : b.toList[n]? <;> rw [h1, h2] at this
  · exact ⟨rfl, rfl⟩
  · exact this.elim
  · exact this.elim
  · exact this

/-! ### the readers -/

theorem rs_uEnt (t t' x : ℕ) : RS K Any (P.Runs.uEnt t x) (P.Runs.uEnt t' x) := by
  unfold P.Runs.uEnt
  refine RS.bind RS.read fun a a' e => ?_
  subst e
  exact RS.bind (RS.mustAs _ _ rfl) fun _ _ _ => RS.pure trivial

variable {i i' : In}

theorem rs_u3at (H : Same i i') (t n : ℕ) : RS K Any (P.Runs.u3at i t n) (P.Runs.u3at i' t n) := by
  unfold P.Runs.u3at
  rw [H.t.tabLen]
  exact RS.bind (RS.mustAs _ _ rfl) fun _ _ _ => rs_uEnt _ _ _

theorem rs_weighted (n : ℕ) (w w' : Array E) (f f' : ℕ → W Aff) (hf : ∀ k, RS K Any (f k) (f' k)) :
    RS K Any (P.Runs.weighted n w f) (P.Runs.weighted n w' f') := by
  unfold P.Runs.weighted
  exact RS.foldlM1 (fun _ _ k _ => RS.bind (hf k) fun _ _ _ => RS.pure trivial) _ trivial

theorem rs_plane (H : Same i i') (t x lam a : ℕ) (z z' : Array E) (hz : z.size = z'.size)
    (isD : Bool) : RS K Any (P.Runs.plane i t x lam a z isD) (P.Runs.plane i' t x lam a z' isD) := by
  unfold P.Runs.plane
  dsimp only
  rw [H.g, eqTab_size, eqTab_size, Array.size_extract, Array.size_extract, hz]
  exact rs_weighted _ _ _ _ _ fun _ => rs_u3at H _ _

theorem rs_shV (H : Same i i') (t off nl J lam j : ℕ) :
    RS K Any (P.Runs.shV i t off nl J lam j) (P.Runs.shV i' t off nl J lam j) := by
  unfold P.Runs.shV
  rw [H.g]
  exact rs_weighted _ _ _ _ _ fun _ => rs_u3at H _ _

theorem rs_overG (H : Same i i') (zg zg' : Array E) (f f' : ℕ → W Aff)
    (hf : ∀ k, RS K Any (f k) (f' k)) : RS K Any (P.Runs.overG i zg f) (P.Runs.overG i' zg' f') := by
  unfold P.Runs.overG
  rw [H.g]
  exact rs_weighted _ _ _ _ _ hf

theorem rs_readDenominator (H : Same i i') (t : ℕ) (zg zg' : Array E) (lam a : ℕ) :
    RS K Any (P.Runs.readDenominator i t zg lam a) (P.Runs.readDenominator i' t zg' lam a) := by
  unfold P.Runs.readDenominator
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_shV H _ _ _ _ _ _

theorem rs_readMaximum (H : Same i i') (t : ℕ) (zg zg' : Array E) (lam a : ℕ) :
    RS K Any (P.Runs.readMaximum i t zg lam a) (P.Runs.readMaximum i' t zg' lam a) := by
  unfold P.Runs.readMaximum
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_shV H _ _ _ _ _ _

theorem rs_readIndexBit (H : Same i i') (t : ℕ) (zg zg' : Array E) (lam a k : ℕ) :
    RS K Any (P.Runs.readIndexBit i t zg lam a k) (P.Runs.readIndexBit i' t zg' lam a k) := by
  unfold P.Runs.readIndexBit
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_shV H _ _ _ _ _ _

theorem cutLast_rel (z z' : Array E) (hz : z.size = z'.size) (k : ℕ) :
    OptRel (fun c c' => c.1.size = c'.1.size) (P.cutLast z k) (P.cutLast z' k) := by
  unfold P.cutLast
  rw [hz]
  split
  · trivial
  · show (z.extract 0 (z'.size - k)).size = (z'.extract 0 (z'.size - k)).size
    rw [Array.size_extract, Array.size_extract, hz]

theorem rs_xl (H : Same i i') (t : ℕ) (X : Ten) (lam hd : ℕ) (zc zc' : Array E)
    (hz : zc.size = zc'.size) : RS K Any (P.Runs.xl i t X lam hd zc) (P.Runs.xl i' t X lam hd zc') := by
  unfold P.Runs.xl
  dsimp only
  rw [H.g]
  have hc := cutLast_rel (zc.extract 0 i'.g.ldh) (zc'.extract 0 i'.g.ldh)
    (by rw [Array.size_extract, Array.size_extract, hz]) i'.g.ls
  cases h1 : P.cutLast (zc.extract 0 i'.g.ldh) i'.g.ls <;>
    cases h2 : P.cutLast (zc'.extract 0 i'.g.ldh) i'.g.ls <;> rw [h1, h2] at hc
  · exact RS.refuse _ _
  · exact hc.elim
  · exact hc.elim
  · dsimp only
    cases P.headFeat X hd i'.g.dh with
    | none => exact RS.refuse _ _
    | some j0 =>
      dsimp only
      rw [eqTab_size, eqTab_size, hc]
      exact rs_weighted _ _ _ _ _ fun _ => rs_weighted _ _ _ _ _ fun _ => rs_u3at H _ _

theorem rs_readHead (H : Same i i') (t : ℕ) (X : Ten) (zg zg' zc zc' : Array E)
    (hz : zc.size = zc'.size) (lam a : ℕ) :
    RS K Any (P.Runs.readHead i t X zg zc lam a) (P.Runs.readHead i' t X zg' zc' lam a) := by
  unfold P.Runs.readHead
  refine rs_overG H _ _ _ _ fun g => ?_
  rw [H.g]
  exact rs_xl H _ _ _ _ _ _ hz

theorem rs_readGroup (H : Same i i') (t : ℕ) (X : Ten) (zg zg' zc zc' : Array E)
    (hz : zc.size = zc'.size) (lam : ℕ) :
    RS K Any (P.Runs.readGroup i t X zg zc lam) (P.Runs.readGroup i' t X zg' zc' lam) := by
  unfold P.Runs.readGroup
  exact rs_overG H _ _ _ _ fun g => rs_xl H _ _ _ _ _ _ hz

theorem rs_lessPieces (s s' : Aff) {pw pw' : Array W1} (hp : SameW pw pw') (f f' : W1 → W Aff)
    (hf : ∀ w w' : W1, w.lam = w'.lam → w.a = w'.a → RS K Any (f w) (f' w')) :
    RS K Any (P.Runs.lessPieces s pw f) (P.Runs.lessPieces s' pw' f') := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact RS.foldlM₂ (fun _ _ w w' _ h => RS.bind (hf w w' h.1 h.2) fun _ _ _ => RS.pure trivial)
    hp trivial

end K5Law
