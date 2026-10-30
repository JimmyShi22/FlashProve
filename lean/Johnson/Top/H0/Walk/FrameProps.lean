-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameProps.lean: for each yes-or-no test of the link's frame's own text
(Johnson/Desc/First/Walk/Quiet, FirstQuiet, LinkZero, Frame, FrameZero.lean): a Prop of what it
checks, and a theorem that the text says yes just where the Prop holds. No block imports this file.

What the frame's tests read: the carried record S and the plan's letters. None reads a view, a
round or a column.

  Bool tests     firstDue [W0], laterDue [W6], closeDue [W7], finishDue [W8], firstRun [A],
                 samePlan [W4], weightsOut [C2], foldsOut [C3]; planPlain, planFlag, planAtt,
                 planLay, planLayZero (these five: the plan's numbers alone)
  Except tests   layFront [B W0 W2], front [W1 W2], back [W3 W4 W5], indexMasksAt [I1 I2 I3 I4],
                 attFirstQuiet [Q0], layFirstQuiet and layFirstQuietZero [Q0 G1 G2],
                 countsLay [N C0 C1 C2 C3], countsAtt [N C1 .. C6]
  The functions  openAtt, openLay, openLayZero [B A], clearWith [N; ROW]: a yes, unfolded to the
                 yes of each part; the entering's and the leaving's own forms (State.lean's
                 forms with a question mark) and the pending row's function stay as they are
                 named: they are other files' text

Not covered: the refusals S1, S2, S3 in Quiet.lean's two functions at the one Step type, which no
block calls.

Limits. These are equivalences between a text and a plainer sentence on the same arguments: no
soundness statement, nothing on an honest prover.

-/
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Props
open OnBytes OnBytes.Model
open VerifiableInference.Desc (need)
open VerifiableInference.Desc.First (S)

/-! ### the Bool tests -/

/-- [W0] not in a link, and a link is left. -/
def FirstDue (c : ChainCheck) : Prop := c.inLink = false ∧ c.frame.link < c.frame.shape.link.length
theorem firstDue_iff (c : ChainCheck) : firstDue c = true ↔ FirstDue c := by
  simp [firstDue, FirstDue]

/-- [W6] in a link, and the shape gives it a moment more. -/
def LaterDue (c : ChainCheck) : Prop := c.inLink = true ∧ c.moments < c.momentsDue
theorem laterDue_iff (c : ChainCheck) : laterDue c = true ↔ LaterDue c := by
  simp [laterDue, LaterDue]

/-- [W7] in a link, and all its moments have been received. -/
def CloseDue (c : ChainCheck) : Prop := c.inLink = true ∧ c.moments = c.momentsDue
theorem closeDue_iff (c : ChainCheck) : closeDue c = true ↔ CloseDue c := by
  simp [closeDue, CloseDue]

/-- [W8] not in a link, and every link is behind. -/
def FinishDue (c : ChainCheck) : Prop := c.inLink = false ∧ c.frame.link = c.frame.shape.link.length
theorem finishDue_iff (c : ChainCheck) : finishDue c = true ↔ FinishDue c := by
  simp [finishDue, FinishDue]

/-- [A] in a link, and just one moment has passed. -/
def FirstRun (c : ChainCheck) : Prop := c.inLink = true ∧ c.moments = 1
theorem firstRun_iff (c : ChainCheck) : firstRun c = true ↔ FirstRun c := by
  simp [firstRun, FirstRun]

/-- [W4] the same list of arrays; for each array of the list both forks have it, with the same rows
and columns. -/
def SamePlan (X : LinkPub) (F : Fork) (list : Tail2) : Prop :=
  list.nt = X.Tp.nt ∧ ∀ t, t < X.Tp.nt.size →
    ∃ a b, F.trees[t]? = some a ∧ X.Fp.trees[t]? = some b ∧ a.R = b.R ∧ a.K = b.K
theorem samePlan_iff (X : LinkPub) (F : Fork) (list : Tail2) : samePlan X F list = true ↔ SamePlan X
    F list := by
  unfold samePlan SamePlan
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine and_congr Iff.rfl (forall_congr' fun t => ?_)
  rw [List.mem_range]
  refine imp_congr Iff.rfl ?_
  cases h1 : F.trees[t]? <;> cases h2 : X.Fp.trees[t]? <;> simp

/-- [C2] as many marks as the plan has claims, and every mark is set. -/
def WeightsOut (F : Fork) : Prop := F.kapMapF.size = F.planClaimsF ∧ ∀ (i : Nat) (h : i <
    F.kapMapF.size), F.kapMapF[i] = true
theorem weightsOut_iff (F : Fork) : weightsOut F = true ↔ WeightsOut F := by
  simp [weightsOut, WeightsOut]

/-- [C3] as many marks as the record has matrices, and every mark is set. -/
def FoldsOut (tl : HTailF2) : Prop := tl.foldTakenF.size = tl.NM ∧ ∀ (i : Nat) (h : i <
    tl.foldTakenF.size), tl.foldTakenF[i] = true
theorem foldsOut_iff (tl : HTailF2) : foldsOut tl = true ↔ FoldsOut tl := by
  simp [foldsOut, FoldsOut]

/-- The plan: the request's shape has the link, and sends one plain scalar at the head's link, none
at any other. -/
def PlanPlain (shape : Params.ReqShape) (X : LinkPub) (l : Nat) : Prop :=
  ∃ k, shape.link[l]? = some k ∧ k.plain = (if X.kind = 2 then 1 else 0)
theorem planPlain_iff (shape : Params.ReqShape) (X : LinkPub) (l : Nat) : planPlain shape X l = true
    ↔ PlanPlain shape X l := by
  unfold planPlain PlanPlain
  cases h : shape.link[l]? <;> simp

/-- The plan: the record is of this kind, and it leaves a row just if the kind is not attention's.
-/
def PlanFlag (X : LinkPub) (kind : Nat) : Prop := X.kind = kind ∧ (X.fv = true ↔ kind ≠ 1)
theorem planFlag_iff (X : LinkPub) (kind : Nat) : planFlag X kind = true ↔ PlanFlag X kind := by
  unfold planFlag PlanFlag
  cases X.fv <;> by_cases h : kind = 1 <;> simp [h]

def PlanAtt (shape : Params.ReqShape) (P : AttPar) : Prop :=
  P.l ≠ 0 ∧ PlanPlain shape P.X P.l ∧ PlanFlag P.X 1
theorem planAtt_iff (shape : Params.ReqShape) (P : AttPar) : planAtt shape P = true ↔ PlanAtt shape
    P := by
  simp [planAtt, PlanAtt, planPlain_iff, planFlag_iff, and_assoc]

def PlanLay (shape : Params.ReqShape) (P : LayPar) : Prop :=
  P.l ≠ 0 ∧ PlanPlain shape P.X P.l ∧ P.l = (if P.p4 = true then 2 * P.g else P.g) ∧ P.X.Tp.nt =
      P.Tp.nt ∧ sizes P.X.Fp = sizes P.Fp ∧ PlanFlag P.X 0
theorem planLay_iff (shape : Params.ReqShape) (P : LayPar) : planLay shape P = true ↔ PlanLay shape
    P := by
  simp [planLay, PlanLay, planPlain_iff, planFlag_iff, and_assoc]

def PlanLayZero (shape : Params.ReqShape) (P : LayPar) : Prop :=
  P.l = 0 ∧ PlanPlain shape P.X 0 ∧ 0 = (if P.p4 = true then 2 * P.g else P.g) ∧ P.X.Tp.nt = P.Tp.nt
      ∧ sizes P.X.Fp = sizes P.Fp ∧ PlanFlag P.X 0
theorem planLayZero_iff (shape : Params.ReqShape) (P : LayPar) : planLayZero shape P = true ↔
    PlanLayZero shape P := by
  simp [planLayZero, PlanLayZero, planPlain_iff, planFlag_iff, and_assoc]

/-- What the tests on the plan give to "cleared": the flag, by the sort of link. -/
theorem planAtt_fv {shape : Params.ReqShape} {P : AttPar} (h : planAtt shape P = true) :
    P.X.fv = false := by
  have := ((planAtt_iff shape P).1 h).2.2.2
  cases hv : P.X.fv with
  | false => rfl
  | true => exact absurd rfl (this.1 hv)
theorem planLay_fv {shape : Params.ReqShape} {P : LayPar} (h : planLay shape P = true) :
    P.X.fv = true := ((planLay_iff shape P).1 h).2.2.2.2.2.2.2 (by decide)
theorem planLayZero_fv {shape : Params.ReqShape} {P : LayPar} (h : planLayZero shape P = true) :
    P.X.fv = true := ((planLayZero_iff shape P).1 h).2.2.2.2.2.2.2 (by decide)
theorem planFlag_head_fv {X : LinkPub} (h : planFlag X 2 = true) : X.fv = true :=
  ((planFlag_iff X 2).1 h).2.2 (by decide)

/-! ### the tests that refuse under a name -/

/-- [B W0 W2] no link is open in the record; a first call is due; the chain stands at link l. -/
def LayFront (l : Nat) (s : S) : Prop := s.atBetween = true ∧ FirstDue s.check ∧ s.check.frame.link
    = l
theorem layFront_iff {l : Nat} {s t : S} : layFront l s = .ok t ↔ t = s ∧ LayFront l s := by
  constructor
  · intro h
    obtain ⟨h0, h1, h2, h3⟩ := Law.layFront_ok h
    exact ⟨h0, h1, (firstDue_iff _).1 h2, h3⟩
  · rintro ⟨rfl, hB, hW, hL⟩
    simp [layFront, need, hB, (firstDue_iff _).2 hW, hL, bind, Except.bind, pure, Except.pure]

/-- [W1 W2] the number of plain scalars is the kind's; the walk stands at link l; what is laid. -/
def Front (X : LinkPub) (l : Nat) (check : ChainCheck) (out : Proof.LinksResult) (L : LinkCtx) (o :
    Proof.LinksResult) : Prop :=
  check.frame.plain.length = (if X.kind == 2 then 1 else 0) ∧ check.frame.link = l ∧
    L = { check := check, link := l, arrayOf := X.arrayOf, list := X.Tp } ∧ o = out
theorem front_iff {X : LinkPub} {l : Nat} {check : ChainCheck} {out o : Proof.LinksResult} {L :
    LinkCtx} :
    front X l check out = .ok (L, o) ↔ Front X l check out L o := by
  constructor
  · exact Law.front_ok
  · rintro ⟨h1, h2, rfl, rfl⟩
    subst h2
    simp [front, h1]

/-- [W3 W4 W5] handed and done; the plan's sizes; where the record leaves a row there is something
for it. -/
def Back (X : LinkPub) (o : Option WsForkOut) (C : LinkCtx) (F : Fork) (k : ChainCheck) (r : Option
    WsForkOut) : Prop :=
  C.handed = true ∧ C.done = true ∧ SamePlan X F C.list ∧ k = C.check ∧
    (X.fv = false → r = none) ∧ (X.fv = true → r = o ∧ o.isSome = true)
theorem back_iff {X : LinkPub} {o r : Option WsForkOut} {C : LinkCtx} {F : Fork} {k : ChainCheck} :
    back X o C F = .ok (k, r) ↔ Back X o C F k r := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Law.back_ok h
    exact ⟨h1, h2, (samePlan_iff _ _ _).1 h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, rfl, h5, h6⟩
    have h3' := (samePlan_iff _ _ _).2 h3
    cases h4 : X.fv
    · simp [back, h1, h2, h3', h4, h5 h4]
    · obtain ⟨rfl, ho⟩ := h6 h4
      cases r
      · simp at ho
      · simp [back, h1, h2, h3', h4]

/-- [I1 I2 I3 I4] just one message at the chain's start; it is in the statement; it has a ledger;
the ledger has room. -/
def IndexMasksAt (room : Nat) (check : ChainCheck) (os : Array Oracle) (im : Nat) : Prop :=
  check.frame.atStart.size = 1 ∧ check.frame.atStart[0]? = some im ∧
    ∃ x l, os[im]? = some x ∧ x.ledger = some l ∧ room ≤ (if l.closed then 0 else l.left)
theorem indexMasksAt_iff {room im : Nat} {check : ChainCheck} {os : Array Oracle} :
    indexMasksAt room check os = .ok im ↔ IndexMasksAt room check os im := by
  constructor
  · exact Law.indexMasksAt_ok
  · rintro ⟨h1, h2, x, l, h3, h4, h5⟩
    simp only [indexMasksAt, h2, h3, h4]
    simp [h1, h5]

/-- [Q0] not link 0; front says yes; what is laid. -/
def AttFirstQuiet (X : LinkPub) (l ns : Nat) (tl₀ : HTailF2) (check : ChainCheck) (out :
    Proof.LinksResult) (a : AttStart) : Prop :=
  l ≠ 0 ∧ Front X l check out a.L a.out ∧ a.F = startFork X ns ∧
    a.tl = { tl₀ with funClosed := false, foldDrawn := 0 }
theorem attFirstQuiet_iff {X : LinkPub} {l ns : Nat} {tl₀ : HTailF2} {check : ChainCheck} {out :
    Proof.LinksResult} {a : AttStart} :
    attFirstQuiet X l ns tl₀ check out = .ok a ↔ AttFirstQuiet X l ns tl₀ check out a := by
  unfold attFirstQuiet AttFirstQuiet
  rw [← front_iff]
  obtain ⟨aL, ao, aF, atl⟩ := a
  by_cases hl : l = 0
  · simp [hl]
  · cases hf : front X l check out with
    | error e => simp [hl]
    | ok p => obtain ⟨L, o⟩ := p; simp [hl]; constructor <;> (rintro ⟨h1, h2, h3, h4⟩; simp_all)

/-- [Q0 G1 G2] not link 0; front says yes; the link is the group's; the list and the sizes are the
plan's; what is laid. -/
def LayTests (X : LinkPub) (p4 : Bool) (g : Nat) (Tp : Tail2) (Fp : Fork) (ns : Nat) (a : LayStart)
    : Prop :=
  a.L.link = (if p4 = true then 2 * g else g) ∧ a.L.list.nt = Tp.nt ∧ sizes X.Fp = sizes Fp ∧ a.F =
      startFork X ns
def LayFirstQuiet (X : LinkPub) (l : Nat) (p4 : Bool) (g : Nat) (Tp : Tail2) (Fp : Fork) (ns : Nat)
    (check : ChainCheck) (out : Proof.LinksResult) (a : LayStart) : Prop :=
  l ≠ 0 ∧ Front X l check out a.L a.out ∧ LayTests X p4 g Tp Fp ns a
theorem layFirstQuiet_iff {X : LinkPub} {l : Nat} {p4 : Bool} {g : Nat} {Tp : Tail2} {Fp : Fork} {ns
    : Nat} {check : ChainCheck} {out : Proof.LinksResult} {a : LayStart} :
    layFirstQuiet X l p4 g Tp Fp ns check out = .ok a ↔ LayFirstQuiet X l p4 g Tp Fp ns check out a
        := by
  unfold layFirstQuiet LayFirstQuiet LayTests
  rw [← front_iff]
  obtain ⟨aL, ao, aF⟩ := a
  by_cases hl : l = 0
  · simp [hl]
  · cases hf : front X l check out with
    | error e => simp [hl]
    | ok p =>
      obtain ⟨L, o⟩ := p
      by_cases h1 : L.link = (if p4 = true then 2 * g else g) <;> by_cases h2 : L.list.nt = Tp.nt
          <;> by_cases h3 : sizes X.Fp = sizes Fp <;>
        simp [hl, h1, h2, h3] <;> (try constructor) <;> (try (intro h; simp_all))

/-- Link 0: [I1 … I4], then front at link 0 with the message's number laid in, then [G1 G2]. -/
def LayFirstQuietZero (X : LinkPub) (p4 : Bool) (g : Nat) (Tp : Tail2) (Fp : Fork) (ns room : Nat)
    (check : ChainCheck) (out : Proof.LinksResult) (os : Array Oracle) (a : LayStart) : Prop :=
  ∃ im, IndexMasksAt room check os im ∧ Front X 0 check { out with indexMasks := im } a.L a.out ∧
      LayTests X p4 g Tp Fp ns a
theorem layFirstQuietZero_iff {X : LinkPub} {p4 : Bool} {g : Nat} {Tp : Tail2} {Fp : Fork} {ns room
    : Nat} {check : ChainCheck} {out : Proof.LinksResult} {os : Array Oracle} {a : LayStart} :
    layFirstQuietZero X p4 g Tp Fp ns room check out os = .ok a ↔ LayFirstQuietZero X p4 g Tp Fp ns
        room check out os a := by
  unfold layFirstQuietZero LayFirstQuietZero LayTests
  simp only [← front_iff, ← indexMasksAt_iff]
  obtain ⟨aL, ao, aF⟩ := a
  cases hi : indexMasksAt room check os with
  | error e => simp
  | ok im =>
    cases hf : front X 0 check { out with indexMasks := im } with
    | error e => simp [hf]
    | ok p =>
      obtain ⟨L, o⟩ := p
      by_cases h1 : L.link = (if p4 = true then 2 * g else g) <;> by_cases h2 : L.list.nt = Tp.nt
          <;> by_cases h3 : sizes X.Fp = sizes Fp <;>
        simp [hf, h1, h2, h3] <;> (try constructor) <;> (try (intro h; simp_all))

/-- [N C0 C1 C2 C3] a layers' link is open; its counts. -/
def CountsLay (NM : Nat) (s : S) : Prop :=
  ∃ a, s.here = .lay a ∧ a.tl.NM = NM ∧ a.F.nClaim = a.F.planClaimsF ∧ WeightsOut a.F ∧ FoldsOut
      a.tl
theorem countsLay_iff {NM : Nat} {s : S} : countsLay NM s = .ok () ↔ CountsLay NM s := by
  unfold countsLay CountsLay
  simp only [← weightsOut_iff, ← foldsOut_iff]
  split
  · rename_i a h
    cases h0 : (a.tl.NM == NM) <;> cases h1 : (a.F.nClaim == a.F.planClaimsF) <;> cases h2 :
        weightsOut a.F <;> cases h3 : foldsOut a.tl <;>
      simp [need, bind, Except.bind] <;> simp_all
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_exists]
    intro a ha
    exact h a ha.1

/-- [N C1 … C6] an attention link is open; its counts. -/
def CountsAtt (nLin : Nat) (s : S) : Prop :=
  ∃ a, s.here = .att a ∧ a.F.nClaim = a.F.planClaimsF ∧ WeightsOut a.F ∧ FoldsOut a.tl ∧ a.F.nClaim
      = nLin ∧ a.tl.foldDrawn = 1 ∧ a.tl.heard.isSome = true
theorem countsAtt_iff {nLin : Nat} {s : S} : countsAtt nLin s = .ok () ↔ CountsAtt nLin s := by
  unfold countsAtt CountsAtt
  simp only [← weightsOut_iff, ← foldsOut_iff]
  split
  · rename_i a h
    cases h1 : (a.F.nClaim == a.F.planClaimsF) <;> cases h2 : weightsOut a.F <;> cases h3 : foldsOut
        a.tl <;> cases h4 : (a.F.nClaim == nLin) <;>
      cases h5 : (a.tl.foldDrawn == 1) <;> cases h6 : a.tl.heard.isSome <;>
      simp [need, bind, Except.bind] <;> simp_all
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_exists]
    intro a ha
    exact h a ha.1

/-! ### the frame's three functions: a yes, unfolded to the yes of each part -/

theorem openAtt_iff {P : AttPar} {s t : S} : openAtt P s = .ok t ↔
    s.atBetween = true ∧ FirstRun s.check ∧ ∃ a, AttFirstQuiet P.X P.l P.ns P.tl₀ s.check s.out a ∧
      S.enterAtt? { s with out := a.out } a.L a.F a.tl = .ok t := by
  unfold openAtt
  simp only [← firstRun_iff, ← attFirstQuiet_iff]
  cases hB : s.atBetween <;> cases hA : firstRun s.check <;> cases hq : attFirstQuiet P.X P.l P.ns
      P.tl₀ s.check s.out <;>
    simp [need, bind, Except.bind]

theorem openLay_iff {P : LayPar} {s t : S} : openLay P s = .ok t ↔
    s.atBetween = true ∧ FirstRun s.check ∧ ∃ a, LayFirstQuiet P.X P.l P.p4 P.g P.Tp P.Fp P.ns
        s.check s.out a ∧
      S.enterLay? { s with out := a.out } a.L a.F P.tl₀ = .ok t := by
  unfold openLay
  simp only [← firstRun_iff, ← layFirstQuiet_iff]
  cases hB : s.atBetween <;> cases hA : firstRun s.check <;> cases hq : layFirstQuiet P.X P.l P.p4
      P.g P.Tp P.Fp P.ns s.check s.out <;>
    simp [need, bind, Except.bind]

theorem openLayZero_iff {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S} : openLayZero P fvs
    kCol s = .ok t ↔
    s.atBetween = true ∧ FirstRun s.check ∧
      ∃ a, LayFirstQuietZero P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol) s.check s.out
          s.st.oracles a ∧
        S.enterLay? { s with out := a.out } a.L a.F P.tl₀ = .ok t := by
  unfold openLayZero
  simp only [← firstRun_iff, ← layFirstQuietZero_iff]
  cases hB : s.atBetween <;> cases hA : firstRun s.check <;>
    cases hq : layFirstQuietZero P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol) s.check s.out
        s.st.oracles <;>
    simp [need, bind, Except.bind]

/-- [N; ROW] a link with its fork is open; the counts say yes; back says yes; where a row is left
the row's function says yes; the leaving's own form says yes. -/
theorem clearWith_iff {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {row : RowFn} {s t : S} :
    clearWith X counts left row s = .ok t ↔
    ∃ C F, s.link? = some C ∧ s.fork? = some F ∧ counts s = .ok () ∧ ∃ k r, Back X (left s) C F k r
        ∧
      ((r = none ∧ s.leaveLink? = .ok t) ∨
       ∃ w q os, r = some w ∧ row s.out.indexMasks w X.NCL s.st.oracles = .ok (q, os) ∧
        ({ s with out := pendingKept s.out q, st := { s.st with oracles := os } } : S).leaveLink? =
            .ok t) := by
  unfold clearWith
  simp only [← back_iff]
  cases hC : s.link? <;> cases hF : s.fork? <;> try simp
  rename_i C F
  cases hc : counts s <;> simp [bind, Except.bind]
  cases hb : back X (left s) C F with
  | error e => simp
  | ok p =>
    obtain ⟨k, r⟩ := p
    cases r with
    | none => simp [and_assoc]
    | some w =>
      cases hr : row s.out.indexMasks w X.NCL s.st.oracles with
      | error e => simp [hr, and_assoc]
      | ok p => obtain ⟨q, os⟩ := p; simp [hr, and_assoc]

#print axioms firstDue_iff
#print axioms laterDue_iff
#print axioms closeDue_iff
#print axioms finishDue_iff
#print axioms firstRun_iff
#print axioms samePlan_iff
#print axioms weightsOut_iff
#print axioms foldsOut_iff
#print axioms planPlain_iff
#print axioms planFlag_iff
#print axioms planAtt_fv
#print axioms planLay_fv
#print axioms planLayZero_fv
#print axioms planFlag_head_fv
#print axioms planAtt_iff
#print axioms planLay_iff
#print axioms planLayZero_iff
#print axioms layFront_iff
#print axioms front_iff
#print axioms back_iff
#print axioms indexMasksAt_iff
#print axioms attFirstQuiet_iff
#print axioms layFirstQuiet_iff
#print axioms layFirstQuietZero_iff
#print axioms countsLay_iff
#print axioms countsAtt_iff
#print axioms openAtt_iff
#print axioms openLay_iff
#print axioms openLayZero_iff
#print axioms clearWith_iff

end Johnson.Desc.First.Walk.Props
