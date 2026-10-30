-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchFrames.lean: K9's 25 BATCHING MEMBERS OF THE PROOF FILE's OWN FIRST CHAIN,
IN THE FORM IN WHICH THE RULE FOR ACCEPTANCE CAN TAKE A MEMBER WHOSE SHAPE BEHIND HANGS ON VALUES:
"carries" WITH THE MEMBER's NAMED TESTS ON VALUES IN HAND, and Returns
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the reader shA of
Johnson/AtFull/Shape/FrameForm.lean. FOR EVERY RunsLaw OF THE LINK WITH ITS Bools: a bridge; it
builds on batch_named (BatchAtHead.lean). Nothing is evaluated.

Why not Carries. Some runs of claims lay a shape that hangs on a value's not being 0: from a bare
yes of the member no law "the step on the shape returns the shape behind" can hold. Under the runs'
own premises it does. That form is the frame's house's CarriesU
(Johnson/Desc/ProofFile/Honest/Thread/ShapeJ.lean). ITS TEXT IS WRITTEN OUT HERE (`CarriesV`), word
for word but for one letter's name: it was written out when that form was only offered, so that this
file stood on nothing that was only offered. No law in this seal or these lots ties the two.

  `RunLawB R`: BESIDE a RunLaw: its premise as a Bool: preB, and pays : preB n s = true → R.pre n s.
  `preAllB`, `preAllB_pays`: the runs' premises along the gathering, as one Bool: IT RUNS THE RUNS.
  **`batchV`**: THE MEMBER's NAMED TESTS AS ONE Bool OF (s, rs, gs): the ledger is empty; and, where
    the draw alone returns at (s, rs, gs), preAllB behind it.
  `Still`, `fold_still`, `batch_still`: the bare batching leaves the statement where every run does.
  `CarriesV`: that form's text.
  **`batch_frame`** (l < 25): Lk · p · w tied as in batch_named: for every RunsLaw R of Lk.hear and
    Lk.order, every B : ∀ o, RunLawB (R.law o), if every run of the order leaves the statement: for
    every ft, G with G ‹number› = liftQ (batchGS p.rows w.1 (fun o => (R.law o).runG) Lk.order) and
    vals with vals ‹number› = batchV p R B Lk.order: CarriesV and Returns at that member.

Limits. A BRIDGE: no RunsLaw of a link and no Bool for a run is laid here. IN batchV AND preAllB A
CLAUSE IS true WHERE SOMETHING REFUSES OR LACKS (no ledger: batchV's first; the draw refuses: its
second; a run refuses: all that preAllB would ask behind it): a yes does not say that the runs'
premises were asked. That batchV accepts at a state of a run is not shown. UNDER THE HEAD: that it
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the earlier hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchAtHead
import Johnson.AtFull.Shape.FrameLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim claimsInBy claimsInStep named roundsFit
  noDigest)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere Where atS drawAlone adds batch eachAtS
  ledgerEmpty addList)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)
open ProofFile.Honest (Shape Returns returns_seat)

/-! ## 1 The premises as Bools -/

/-- **Beside a RunLaw: its premise as a Bool.** -/
structure RunLawB {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run) where
  preB : Nat → S → Bool
  pays : ∀ n s, preB n s = true → R.pre n s

/-- The runs' premises along the gathering, as one Bool. It runs the runs. -/
def preAllB {bs : List (Block S Claim)} {order : List (Nat × String)} (R : RunsLaw bs order)
    (B : ∀ o, RunLawB (R.law o)) : List (Nat × String) → Nat → S → Bool
  | [], _, _ => true
  | o :: os, n, s =>
    (B o).preB n s &&
      match R.run o n s with
      | .ok y => preAllB R B os (n + y.1.length) y.2
      | .error _ => true

theorem preAllB_pays {bs : List (Block S Claim)} {order : List (Nat × String)}
    (R : RunsLaw bs order) (B : ∀ o, RunLawB (R.law o)) :
    ∀ (os : List (Nat × String)) (n : Nat) (s : S), preAllB R B os n s = true → PreAll R os n s
  | [], _, _, _ => trivial
  | o :: os, n, s, h => by
    have h' : ((B o).preB n s &&
      match R.run o n s with
      | .ok y => preAllB R B os (n + y.1.length) y.2
      | .error _ => true) = true := h
    rw [Bool.and_eq_true] at h'
    refine ⟨(B o).pays n s h'.1, fun cs s' hr => ?_⟩
    have h2 := h'.2
    rw [hr] at h2
    exact preAllB_pays R B os _ _ h2

/-- **THE MEMBER's NAMED TESTS AS ONE Bool.** -/
def batchV {bs : List (Block S Claim)} {order : List (Nat × String)} (p : Where)
    (R : RunsLaw bs order) (B : ∀ o, RunLawB (R.law o)) (os : List (Nat × String)) (s : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  (s.fork?.map ledgerEmpty).getD true &&
    match (drawAlone (Cl := Claim) atS p).decide s rs gs with
    | .ok s₁ => preAllB R B os 0 s₁
    | .error _ => true

/-! ## 2 The batching leaves the statement -/

/-- The second state has the first one's statement. -/
def Still (a b : S) : Prop := b.st = a.st

theorem fold_still (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) :
    ∀ (os : List (Nat × String)),
      (∀ o ∈ os, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
        ∀ n a cs a', run n a = .ok (cs, a') → Still a a') →
      ∀ (x y : List Claim × S), foldE (claimsInStep each bs) os (.ok x) = .ok y → Still x.2 y.2
  | [], _, x, y, h => by
    obtain rfl : x = y := Except.ok.inj h
    rfl
  | o :: os, hk, x, y, h => by
    rw [fold_cons] at h
    cases hs : claimsInStep each bs x o with
    | error e => rw [hs] at h; exact nomatch h
    | ok z =>
      rw [hs] at h
      have h2 := fold_still each bs os (fun o' ho' => hk o' (List.mem_cons_of_mem _ ho')) z y h
      have h1 : Still x.2 z.2 := by
        unfold claimsInStep at hs
        cases hl : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
        | none => rw [hl] at hs; exact nomatch hs
        | some run =>
          rw [hl] at hs
          have hn : named (o.2 ++ ": no such run") (some run) = .ok run := rfl
          rw [hn] at hs
          dsimp only [Except.bind] at hs
          cases hr : run x.1.length x.2 with
          | error e => rw [hr] at hs; exact nomatch hs
          | ok v =>
            rw [hr] at hs
            dsimp only at hs
            cases he : each o v.1 v.2 with
            | error e => rw [he] at hs; exact nomatch hs
            | ok _ =>
              rw [he] at hs
              obtain rfl := Except.ok.inj hs
              exact hk o (by simp) run hl x.1.length x.2 v.1 v.2 hr
      exact h2.trans h1

theorem batch_still (p : Where) (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String))
    (hk : ∀ o ∈ order, ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
      ∀ n a cs a', run n a = .ok (cs, a') → Still a a')
    (s t : S) (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (batch atS p (claimsInBy each bs order)).decide s [r] gs = .ok t) : Still s t := by
  have h' : ((drawAlone (Cl := Claim) atS p).decide s [r] gs >>= fun t₁ =>
    (adds (Cl := Claim) atS p p.piece "the segment's" (claimsInBy each bs order)).decide t₁ [] [])
      = .ok t := h
  obtain ⟨s₁, h1, h2⟩ := (ans_bind _ _ _).1 h'
  obtain ⟨P, chi, o, hP, -, -, rfl⟩ := (drawAlone_iff p s s₁ r gs).1 h1
  have h2' : (atS.part (atS.set s { P with owed := o.owed, L := o.L, F := o.F }) >>= fun s₀ =>
    VerifiableInference.Desc.need "K9.draw-has-run" s₀.L.handed >>= fun _ =>
      claimsInBy each bs order (atS.set s { P with owed := o.owed, L := o.L, F := o.F }) >>=
        fun x => atS.part x.2 >>= fun q => addList q.F x.1 >>= fun F =>
          (pure (atS.set x.2 { q with F := F }) : Except String S)) = .ok t := h2
  simp only [ans_bind] at h2'
  obtain ⟨-, -, -, -, x, hx, q, hq, F, -, e⟩ := h2'
  obtain rfl := Except.ok.inj e
  have k1 : Still (atS.set s { P with owed := o.owed, L := o.L, F := o.F }) x.2 :=
    fold_still each bs order hk ([], _) x hx
  have e1 : (atS.set s { P with owed := o.owed, L := o.L, F := o.F }).st = s.st :=
    (part_sh hP).2.2.2.2.2
  have e2 : q.d.st = x.2.st := (part_sh ((there_ok _ _ _).1 hq)).2.2.2.2.2
  show q.d.st = s.st
  rw [e2, ← e1]
  exact k1

/-! ## 3 The frame -/

/-- "Carries" with the member's named tests on values in hand: the text of the frame's house's form
CarriesU. A definition: a premise's form. -/
def CarriesV {Cl : Type} (bs : List (Block S Cl)) (ft : Nat) (Zs : Shape S) (b : Nat) : Prop :=
  ∀ blk, bs[b]? = some blk → ∀ s rs cols s' n t, blk.step ft s rs cols = .ok (s', n) →
    Zs.g b (Zs.sh s) = .ok t → Zs.vals b s (rs.map noDigest) (blk.shown ft rs cols) = true →
    t = Zs.sh s'

/-- Rounds that fit the batching's one declared round are one round, which drew one element. -/
theorem batch_fit {p : Where} {rs : List Fmt.RoundView}
    (h : roundsFit [{ entry := VerifiableInference.Desc.K9.entry p }] rs = true) :
    ∃ rd y, rs = [rd] ∧ rd.drawn.elems = [y] := by
  match rs, h with
  | [rd], h =>
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
    have hl : rd.drawn.elems.length = 1 := h.1.1.1.1.1.1.2
    match he : rd.drawn.elems, hl with
    | [y], _ => exact ⟨rd, y, rfl, he⟩
  | [], h => cases h
  | _ :: _ :: _, h => simp [roundsFit] at h

/-- What a yes of batchV gives. -/
theorem batchV_pays {bs : List (Block S Claim)} {order : List (Nat × String)} {p : Where}
    {R : RunsLaw bs order} {B : ∀ o, RunLawB (R.law o)} {os : List (Nat × String)} {s : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : batchV p R B os s rs gs = true) :
    (∀ F, s.fork? = some F → ledgerEmpty F = true) ∧
      ∀ s₁, (drawAlone (Cl := Claim) atS p).decide s rs gs = .ok s₁ → PreAll R os 0 s₁ := by
  unfold batchV at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun F hF => ?_, fun s₁ h₁ => ?_⟩
  · have h1 := h.1
    rw [hF] at h1
    exact h1
  · have h2 := h.2
    rw [h₁] at h2
    exact preAllB_pays R B os 0 s₁ h2

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem batch_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Lk : Link S ProofFile.Cl) (p : Where) (w : SegSort × Nat × TWhere),
      cF.links[l]? = some Lk ∧ IM.k9At Zp l = some p ∧ testsWhere Zp.p.X l 0 = some w ∧
      ∀ (R : RunsLaw Lk.hear Lk.order) (B : ∀ o, RunLawB (R.law o)),
        (∀ o ∈ Lk.order, ∀ n a cs a', R.run o n a = .ok (cs, a') → Still a a') →
        ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
          (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
          G (14 * l + Lk.hear.length + 2) =
            liftQ (batchGS p.rows w.1 (fun o => (R.law o).runG) Lk.order) →
          vals (14 * l + Lk.hear.length + 2) = batchV p R B Lk.order →
          CarriesV cF.blocksInOrder ft (firstZA G vals) (14 * l + Lk.hear.length + 2) ∧
            Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + Lk.hear.length + 2) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, w, T, eL, hp, -, -, -, -, hla, hflat, -, -, -, -, -, -, hw, -, -, -, -⟩ :=
    (IM.k9_of h.scope h.reads O).2 l hl
  obtain ⟨Lk₁, p₁, w₁, b₁, a1, a2, a3, a4, -, hN⟩ := batch_named h l hl
  obtain rfl : Lk = Lk₁ := Option.some.inj (eL.symm.trans a1)
  obtain rfl : p = p₁ := Option.some.inj (hp.symm.trans a2)
  obtain rfl : w = w₁ := Option.some.inj (hw.symm.trans a3)
  obtain rfl := Option.some.inj (hflat.symm.trans a4)
  have hrd : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).rounds =
      [{ entry := VerifiableInference.Desc.K9.entry p }] := IM.alone_rounds (hla _)
  refine ⟨Lk, p, w, eL, hp, hw, fun R B hst ft G vals hG hv => ?_⟩
  -- from the step on ShA, the Bool and rounds that fit: the member's yes, to that shape
  have key : ∀ (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (t : ShA),
      roundsFit (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).rounds rs = true →
      G (14 * l + Lk.hear.length + 2) (shA s) = .ok t →
      vals (14 * l + Lk.hear.length + 2) s (rs.map noDigest) gs = true →
      ∃ s', (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s (rs.map noDigest) gs =
        .ok s' ∧ t = shA s' := by
    intro s rs gs t hfit hg hvv
    rw [hrd] at hfit
    obtain ⟨rd, y, rfl, hy⟩ := batch_fit hfit
    rw [hG] at hg
    rw [hv] at hvv
    obtain ⟨v1, v2⟩ := batchV_pays hvv
    unfold liftQ at hg
    cases hu : batchGS p.rows w.1 (fun o => (R.law o).runG) Lk.order (shA s).1 with
    | error e => rw [hu] at hg; exact nomatch hg
    | ok u =>
      rw [hu] at hg
      obtain rfl := Except.ok.inj hg
      obtain ⟨s', hd, rfl⟩ := hN R s (noDigest rd) gs u hu ⟨y, hy⟩ v1 v2
      refine ⟨s', hd, ?_⟩
      have hb := ((IM.yes_alone (hla _) (by intro k; cases k) s s' [noDigest rd] gs).1 hd).1
      have hs : Still s s' := batch_still p Lk.each Lk.hear Lk.order
        (fun o ho run hl' n a cs a' hr => by
          obtain rfl : R.run o = run := Option.some.inj ((R.look o ho).symm.trans hl')
          exact hst o ho n a cs a' hr) s s' (noDigest rd) gs hb
      show (chainSh s', formsOf s.st) = (chainSh s', formsOf s'.st)
      rw [show s'.st = s.st from hs]
  constructor
  · intro blk hblk s rs cols s' n t hs hg hvv
    rw [hflat] at hblk
    obtain rfl := Option.some.inj hblk
    have h3 := (VerifiableInference.Desc.step_iff ft _ s s' rs cols n).1 hs
    obtain ⟨s'', hd, rfl⟩ := key s rs _ t h3.1.1 hg hvv
    obtain rfl : s'' = s' := Except.ok.inj (hd.symm.trans h3.2.1)
    rfl
  · refine returns_seat hflat fun rs cols hF s t hg hvv => ?_
    obtain ⟨s', hd, -⟩ := key s rs _ t hF.1 hg hvv
    exact ⟨s', hd⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.preAllB_pays
#print axioms Johnson.AtFull.Shape.fold_still
#print axioms Johnson.AtFull.Shape.batch_still
#print axioms Johnson.AtFull.Shape.batch_fit
#print axioms Johnson.AtFull.Shape.batchV_pays
#print axioms Johnson.AtFull.Shape.batch_frame
#print axioms Johnson.AtFull.Shape.RunLawB
#print axioms Johnson.AtFull.Shape.preAllB
#print axioms Johnson.AtFull.Shape.batchV
#print axioms Johnson.AtFull.Shape.Still
#print axioms Johnson.AtFull.Shape.CarriesV
