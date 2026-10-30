-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/PlainSteps.lean: THE STEPS OF THE PLAIN CELLS AND THE BACK ROW DO NOT SEE
WHAT STANDS IN look AND lookHeard. pC, pF lay these two components anew. Keep: a step on a shape so
laid is the step on the shape, so laid behind. Drop: the step is the same. Blind: the step goes alike
at two shapes with one strip (Rel.lean). Nothing is evaluated.

Limits. Laws on steps at any letters; which letters stand at which record: PlainCells.lean. Nothing
on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rel
import Johnson.AtFull.Shape.TabLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9.Shape
open Johnson.Desc.First.Walk.Shape
open ProofFile.Honest.K10.YesFree

/-- A chain's shape with the two lookups' components laid anew. -/
def pC (l h : Option HeardAll) (a : ChainSh) : ChainSh :=
  ChainSh.mk a.marked a.here a.tl a.led a.tables a.rowsOwed a.core a.reply a.indexMasks a.pile
    a.atEnd a.check a.link l h a.own a.head a.att a.fin

/-- The same on the whole. -/
def pF (l h : Option HeardAll) (x : ShA) : ShA := (pC l h x.1, x.2)

section
variable (l h : Option HeardAll) (a : ChainSh)
theorem pC_marked : (pC l h a).marked = a.marked := rfl
theorem pC_here : (pC l h a).here = a.here := rfl
theorem pC_tl : (pC l h a).tl = a.tl := rfl
theorem pC_led : (pC l h a).led = a.led := rfl
theorem pC_rowsOwed : (pC l h a).rowsOwed = a.rowsOwed := rfl
theorem pC_core : (pC l h a).core = a.core := rfl
theorem pC_check : (pC l h a).check = a.check := rfl
theorem pC_link : (pC l h a).link = a.link := rfl
theorem pC_live : (pC l h a).live = a.live := rfl
end

theorem pF_fst (l h : Option HeardAll) (x : ShA) : (pF l h x).1 = pC l h x.1 := rfl
theorem pF_snd (l h : Option HeardAll) (x : ShA) : (pF l h x).2 = x.2 := rfl
theorem pF_mk (l h : Option HeardAll) (u : ChainSh) (F : FormsSh) :
    pF l h (u, F) = (pC l h u, F) := rfl

/-- The readers and setters, on a shape laid out. (Written as rfl, these equations ran Lean's kernel
out of time; why is not shown.) -/
macro "chain_eq" : tactic =>
  `(tactic| simp only [pC, pF, strip, enterSh, leaveSh, leaveAll, ChainSh.mk, ChainSh.marked,
    ChainSh.here, ChainSh.tl, ChainSh.led, ChainSh.tables, ChainSh.rowsOwed, ChainSh.core,
    ChainSh.reply, ChainSh.indexMasks, ChainSh.pile, ChainSh.atEnd, ChainSh.check, ChainSh.link,
    ChainSh.live, ChainSh.look, ChainSh.lookHeard, ChainSh.own, ChainSh.head, ChainSh.att,
    ChainSh.fin, ChainSh.setLink, ChainSh.setTl, ChainSh.setLed, ChainSh.setCore,
    ChainSh.setRowsOwed, ChainSh.setCheck, ChainSh.setHere, ChainSh.setPile, ChainSh.layTl,
    ChainSh.layLed, ChainSh.layTables, ChainSh.layLink, ChainSh.layLook, ChainSh.layLookHeard,
    ChainSh.layOwn, ChainSh.layHead, ChainSh.layAtt])

section
variable (l h : Option HeardAll)

theorem pC_setLink (a : ChainSh) (L : LinkSh) : (pC l h a).setLink L = pC l h (a.setLink L) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem pC_setTl (a : ChainSh) (t : TailSh) : (pC l h a).setTl t = pC l h (a.setTl t) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem pC_setLed (a : ChainSh) (L : LedSh) : (pC l h a).setLed L = pC l h (a.setLed L) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem pC_setCore (a : ChainSh) (c : VerifiableInference.Desc.Ground.Sh.CoreSh) :
    (pC l h a).setCore c = pC l h (a.setCore c) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem pC_setRowsOwed (a : ChainSh) (r : Option Nat) :
    (pC l h a).setRowsOwed r = pC l h (a.setRowsOwed r) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem pC_setCheck (a : ChainSh) (c : CheckSh) : (pC l h a).setCheck c = pC l h (a.setCheck c) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem pC_enter (n : Nat) (t : TailSh) (L : LedSh) (X : Johnson.Desc.First.Walk.LinkPub) (k : Nat)
    (a : ChainSh) : enterSh n t L X k (pC l h a) = pC l h (enterSh n t L X k a) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem leaveAll_pC (a : ChainSh) : leaveAll (pC l h a) = leaveAll a := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem leaveSh_pC (a : ChainSh) : leaveSh (pC l h a) = leaveSh a := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem pC_setPile (a : ChainSh) (p : List VerifiableInference.Desc.K13.Honest.RowSh) :
    (pC l h a).setPile p = pC l h (a.setPile p) := by
  obtain ⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩ := a
  chain_eq

theorem strip_pF (b : ShA) : strip (pF l h b) = pF (l.map stripH) (h.map stripH) b := by
  obtain ⟨⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩, F⟩ := b
  chain_eq

end

/-- A shape is its strip with its own two components laid back. -/
theorem pF_back (x : ShA) : pF x.1.look x.1.lookHeard (strip x) = x := by
  obtain ⟨⟨m, hh, tl, led, tb, ro, co, rp, im, pi, en, ck, lk, lo, lh, ow, hd, at', fi⟩, F⟩ := x
  chain_eq

/-- A step that keeps what stands in the two components, on the whole. -/
def Keep (f : ShA → Except String ShA) : Prop :=
  ∀ x l h, (f (pF l h x)).toOption = (f x).toOption.map (pF l h)

/-- A step that reads neither of the two components and clears both. -/
def Drop (f : ShA → Except String ShA) : Prop :=
  ∀ x l h, (f (pF l h x)).toOption = (f x).toOption

/-- **A step that goes alike at two shapes with one strip.** -/
def Blind (f : ShA → Except String ShA) : Prop :=
  ∀ x y, strip x = strip y → (f x).toOption.map strip = (f y).toOption.map strip

/-- The law behind Keep.blind, in letters. -/
theorem blind_of_keep {α κ : Type} (st : α → α) (put : κ → α → α) (get : α → κ) (mp : κ → κ)
    (h1 : ∀ k b, st (put k b) = put (mp k) b) (h2 : ∀ x, put (get x) (st x) = x)
    (h3 : ∀ x y, st x = st y → mp (get x) = mp (get y)) (f : α → Except String α)
    (hk : ∀ x k, (f (put k x)).toOption = (f x).toOption.map (put k)) (x y : α)
    (e : st x = st y) : (f x).toOption.map st = (f y).toOption.map st := by
  have kx := hk (st x) (get x)
  have ky := hk (st y) (get y)
  rw [h2] at kx ky
  rw [kx, ky, ← e]
  generalize (f (st x)).toOption = o
  cases o with
  | none => rfl
  | some b =>
    show some (st (put (get x) b)) = some (st (put (get y) b))
    rw [h1, h1, h3 x y e]

theorem strip_two (x y : ShA) (e : strip x = strip y) :
    (x.1.look.map stripH, x.1.lookHeard.map stripH) =
      (y.1.look.map stripH, y.1.lookHeard.map stripH) := by
  have e1 : x.1.look.map stripH = y.1.look.map stripH := congrArg (fun z : ShA => z.1.look) e
  have e2 : x.1.lookHeard.map stripH = y.1.lookHeard.map stripH :=
    congrArg (fun z : ShA => z.1.lookHeard) e
  rw [e1, e2]

/-- The two components as one letter. -/
def putK (k : Option HeardAll × Option HeardAll) (b : ShA) : ShA := pF k.1 k.2 b
def getK (x : ShA) : Option HeardAll × Option HeardAll := (x.1.look, x.1.lookHeard)
def mpK (k : Option HeardAll × Option HeardAll) : Option HeardAll × Option HeardAll :=
  (k.1.map stripH, k.2.map stripH)

theorem st_put (k : Option HeardAll × Option HeardAll) (b : ShA) :
    strip (putK k b) = putK (mpK k) b := by
  unfold putK mpK
  exact strip_pF _ _ _

theorem put_get (x : ShA) : putK (getK x) (strip x) = x := by
  unfold putK getK
  exact pF_back x

theorem mp_get (x y : ShA) (e : strip x = strip y) : mpK (getK x) = mpK (getK y) := by
  unfold mpK getK
  exact strip_two x y e

theorem Keep.blind {f : ShA → Except String ShA} (hk : Keep f) : Blind f :=
  blind_of_keep strip putK getK mpK st_put put_get mp_get f fun x k => by
    unfold putK
    exact hk x k.1 k.2

/-- At two shapes with one strip a step that clears returns the same. -/
theorem Drop.same {f : ShA → Except String ShA} (hk : Drop f) {x y : ShA} (e : strip x = strip y) :
    (f x).toOption = (f y).toOption := by
  have kx := hk (strip x) x.1.look x.1.lookHeard
  have ky := hk (strip y) y.1.look y.1.lookHeard
  rw [pF_back] at kx ky
  rw [kx, ky, e]

theorem keep_no (why : String) : Keep (noCell why).1 := fun _ _ _ => rfl
theorem drop_no (why : String) : Drop (noCell why).1 := fun _ _ _ => rfl

theorem toOption_map {α β ε : Type} (e : Except ε α) (f : α → β) :
    (e.map f).toOption = e.toOption.map f := by
  cases e <;> rfl

theorem toOption_optE {α β : Type} (g : α → Option β) (a : α) : (optE g a).toOption = g a := by
  unfold optE
  cases g a <;> rfl

/-- Keep on the chain's shape, in the two forms of a step. -/
def KeepE (G : ChainSh → Except String ChainSh) : Prop :=
  ∀ a l h, (G (pC l h a)).toOption = (G a).toOption.map (pC l h)
def KeepO (G : ChainSh → Option ChainSh) : Prop :=
  ∀ a l h, G (pC l h a) = (G a).map (pC l h)
/-- Keep on the whole, a step that may refuse. -/
def KeepP (G : ChainF → Option ChainF) : Prop :=
  ∀ x l h, G (pF l h x) = (G x).map (pF l h)

theorem keep_liftQ {G : ChainSh → Except String ChainSh} (hG : KeepE G) : Keep (liftQ G) := by
  intro x l h
  unfold liftQ
  rw [toOption_map, toOption_map, pF_fst, hG]
  cases (G x.1).toOption <;> rfl

theorem keep_optE {G : ChainF → Option ChainF} (hG : KeepP G) : Keep (optE G) := by
  intro x l h
  rw [toOption_optE, toOption_optE, hG]

theorem keepP_bind {F G : ChainF → Option ChainF} (hF : KeepP F) (hG : KeepP G) :
    KeepP fun x => (F x).bind G := by
  intro x l h
  show (F (pF l h x)).bind G = ((F x).bind G).map (pF l h)
  rw [hF]
  cases F x with
  | none => rfl
  | some y => exact hG y l h

theorem keepP_quiet {G : ChainSh → Except String ChainSh} (hG : KeepE G) :
    KeepP (Johnson.AtFull.Shape.quietE G) := by
  intro x l h
  show ((G (pC l h x.1)).toOption).map (·, x.2) = ((G x.1).toOption.map (·, x.2)).map (pF l h)
  rw [hG]
  cases (G x.1).toOption <;> rfl

/-! ## The steps, one by one -/

theorem keep_laid (n : Nat) : KeepE (laidGS n) := by
  intro a l h
  unfold laidGS Johnson.Desc.First.Walk.Shape.laidG
  rw [show laidB n (pC l h a) = laidB n a from rfl]
  simp only [pC_marked]
  split
  · rfl
  · split <;> rfl

theorem keep_shut : KeepE shutGS := by
  intro a l h
  unfold shutGS shutG
  simp only [pC_marked, pC_link]
  split
  · rfl
  · split
    · rw [pC_setLink]
      rfl
    · rfl

theorem keep_draw (p : VerifiableInference.Desc.First.K8.Par) : KeepE (drawStep p) := by
  intro a l h
  unfold drawStep drawGS VerifiableInference.Desc.First.K8.drawG
  rw [show VerifiableInference.Desc.First.K8.drawGuard p (pC l h a) =
    VerifiableInference.Desc.First.K8.drawGuard p a from rfl]
  simp only [pC_marked, pC_tl]
  split
  · rfl
  · split
    · rfl
    · split
      · rw [pC_setTl]
        rfl
      · rfl

theorem keep_commit (P : VerifiableInference.Desc.K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) : KeepO (commitGS P link moment arrays) := by
  intro a l h
  unfold commitGS commitG commitStepG
  simp only [pC_marked, pC_rowsOwed, pC_core, pC_link, pC_led, pC_tl, pC_setCore, pC_setRowsOwed,
    pC_setLink, pC_setLed]
  repeat' split
  all_goals first
    | rfl
    | (simp only [Option.map_map, Function.comp_def])

theorem keep_digits (P : VerifiableInference.Desc.K1.Par) (n : Nat) (dg : Option (List Nat)) :
    Keep (digitsA P n dg) := by
  intro x l h
  unfold digitsA
  rw [pF_fst, keep_commit]
  cases commitGS P n 2 dg x.1 <;> rfl

theorem keep_openLay (P : Johnson.Desc.First.Walk.LayPar) : KeepE (openLayG P) := by
  intro a l h
  unfold openLayG
  rw [show openB P.l P.X.kind (pC l h a) = openB P.l P.X.kind a from rfl]
  split
  · rw [pC_enter]
    rfl
  · rfl

theorem keep_openAtt (P : Johnson.Desc.First.Walk.AttPar) : KeepE (openAttG P) := by
  intro a l h
  unfold openAttG
  rw [show openB P.l P.X.kind (pC l h a) = openB P.l P.X.kind a from rfl]
  split
  · rw [pC_enter]
    rfl
  · rfl

theorem keep_linkU (p : VerifiableInference.Desc.First.K2.P2) : KeepP (linkU p) := by
  intro x l h
  unfold linkU
  simp only [pF_fst, pF_snd, pC_check, pC_core, pC_setCore, pC_setRowsOwed, pC_setCheck,
    Option.map_bind, Option.map_map, Function.comp_def, pF_mk]

theorem switchUL_zero {ft : Nat} {a : VerifiableInference.Desc.Place} {n : P1K2.Nums}
    {HP : VerifiableInference.Desc.First.K2.HeadPar} {x : ChainF} (h0 : x.1.here = 0) :
    switchUL ft a n HP x = linkU (k2PL ft a "" .link n) x := by
  unfold switchUL
  rw [h0]

/-- The switch at a link, with any step behind it. -/
theorem keep_switch (ft : Nat) (a : VerifiableInference.Desc.Place) (n : P1K2.Nums)
    (HP : VerifiableInference.Desc.First.K2.HeadPar) {Q : ChainF → Option ChainF} (hQ : KeepP Q) :
    Keep (optE fun y => if linkGd (k2PL ft a "" .link n) y then (switchUL ft a n HP y).bind Q
      else none) := by
  refine keep_optE ?_
  intro x l h
  show (if linkGd (k2PL ft a "" .link n) (pF l h x) = true then
      (switchUL ft a n HP (pF l h x)).bind Q else none) =
    (if linkGd (k2PL ft a "" .link n) x = true then (switchUL ft a n HP x).bind Q else none).map
      (pF l h)
  rw [show linkGd (k2PL ft a "" .link n) (pF l h x) = linkGd (k2PL ft a "" .link n) x from rfl]
  by_cases hg : linkGd (k2PL ft a "" .link n) x = true
  · rw [if_pos hg, if_pos hg]
    have h0 : x.1.here = 0 := by
      unfold linkGd at hg
      simp only [Bool.and_eq_true] at hg
      simpa using linkB_here hg.1.2
    rw [switchUL_zero h0, switchUL_zero (x := pF l h x) h0]
    exact keepP_bind (keep_linkU _) hQ x l h
  · rw [if_neg hg, if_neg hg]
    rfl

theorem keep_one : KeepE oneGS := by
  intro a l h
  unfold oneGS oneG
  rw [show owedSh (pC l h a) = owedSh a from rfl]
  simp only [pC_marked, pC_link, pC_led, pC_tl, pC_core, pC_setLed, pC_setCore, pC_setRowsOwed]
  repeat' split
  all_goals rfl

theorem keep_equation : Keep oneA := by
  intro x l h
  have e := keep_one x.1 l h
  unfold oneA
  rw [pF_fst, pF_snd, show eqFormsU (pC l h x.1) x.2 = eqFormsU x.1 x.2 from rfl]
  cases h1 : oneGS x.1 with
  | error w =>
    rw [h1] at e
    cases h2 : oneGS (pC l h x.1) with
    | error w' => rfl
    | ok b =>
      rw [h2] at e
      cases e
  | ok u =>
    rw [h1] at e
    cases h2 : oneGS (pC l h x.1) with
    | error w' =>
      rw [h2] at e
      cases e
    | ok b =>
      rw [h2] at e
      obtain rfl : b = pC l h u := Option.some.inj e
      cases eqFormsU x.1 x.2 <;> rfl

theorem keep_putLive (c : CheckSh) (a : ChainSh) (l h : Option HeardAll) :
    putLiveS (pC l h a) c = pC l h (putLiveS a c) := by
  unfold putLiveS
  simp only [pC_link, pC_setLink, pC_setCheck]
  split <;> rfl

theorem keep_closeGS (Q : VerifiableInference.Desc.First.Close.Par) (c : FormSh)
    (kept : List (Nat × FormSh)) (a : ChainSh) (l h : Option HeardAll) :
    closeGS Q c kept (pC l h a) = (closeGS Q c kept a).map (pC l h) := by
  unfold closeGS
  rw [show owedS (pC l h a) = owedS a from rfl]
  simp only [pC_marked, pC_live, pC_core, keep_putLive, pC_setCore, pC_setRowsOwed]
  repeat' split
  all_goals first
    | rfl
    | contradiction
    | simp only [Option.map_map, Function.comp_def]

theorem keep_closeGSM (Q : VerifiableInference.Desc.First.Close.Par) (fm : FormsSh) (a : ChainSh)
    (l h : Option HeardAll) :
    closeGSM Q fm (pC l h a) = (closeGSM Q fm a).map (pC l h) := by
  unfold closeGSM
  simp only [pC_live, pC_core, keep_closeGS]
  cases a.core.st.groups[a.live.frame.group]? with
  | none => rfl
  | some G =>
    simp only [Option.bind_some]
    cases batchedS fm a.core.st a.live.frame.group G <;> rfl

theorem keep_close (Q : VerifiableInference.Desc.First.Close.Par) : Keep (optE (closeGF Q)) := by
  refine keep_optE ?_
  intro x l h
  unfold closeGF
  rw [show closeValsF (pF l h x) = closeValsF x from rfl, pF_fst, pF_snd, keep_closeGSM,
    show formsBehindF (pC l h x.1) x.2 = formsBehindF x.1 x.2 from rfl]
  split
  · cases closeGSM Q x.2 x.1 <;> rfl
  · rfl

theorem drop_clearGL (X : Johnson.Desc.First.Walk.LinkPub) (lay : WsLay) (lin : Params.LinShape)
    {countsB : ChainSh → Bool} {leftSh : ChainSh → Option MergeSh}
    (hc : ∀ a l h, countsB (pC l h a) = countsB a) (hl : ∀ a l h, leftSh (pC l h a) = leftSh a) :
    Drop (liftQ (clearGL X lay lin countsB leftSh)) := by
  intro x l h
  unfold liftQ
  rw [toOption_map, toOption_map, pF_fst, pF_snd]
  unfold clearGL
  have e : clearB X countsB (pC l h x.1) = clearB X countsB x.1 := by
    funext C L
    unfold clearB
    rw [hc]
    rfl
  rw [e, hl]
  simp only [pC_link, pC_led, pC_core, pC_setCore, pC_setPile, leaveAll_pC,
    show (pC l h x.1).indexMasks = x.1.indexMasks from rfl, show (pC l h x.1).pile = x.1.pile from rfl]

theorem drop_clearAtt (X : Johnson.Desc.First.Walk.LinkPub) (nLin : Nat) :
    Drop (liftQ (clearAttG X nLin)) := by
  intro x l h
  unfold liftQ
  rw [toOption_map, toOption_map, pF_fst, pF_snd]
  unfold clearAttG
  rw [show clearAttB X nLin (pC l h x.1) = clearAttB X nLin x.1 from rfl, leaveSh_pC]

theorem drop_clearLay (X : Johnson.Desc.First.Walk.LinkPub) (lay : WsLay) (lin : Params.LinShape)
    (NM : Nat) : Drop (liftQ (clearLayGL X lay lin NM)) :=
  drop_clearGL X lay lin (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem drop_clearHead (X : Johnson.Desc.First.Walk.LinkPub) (lay : WsLay) (lin : Params.LinShape) :
    Drop (liftQ (clearHeadGL X lay lin)) :=
  drop_clearGL X lay lin (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.Keep.blind
#print axioms Johnson.AtFull.Shape.Scope.Drop.same
#print axioms Johnson.AtFull.Shape.Scope.keep_switch
#print axioms Johnson.AtFull.Shape.Scope.keep_close
#print axioms Johnson.AtFull.Shape.Scope.keep_equation
#print axioms Johnson.AtFull.Shape.Scope.drop_clearHead
