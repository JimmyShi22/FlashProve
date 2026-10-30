-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/DoorKeeps.lean: THE CODE SWITCH AT A SEATED BLOCK: WHAT THE WAY OUT OF THE
DOOR MUST KEEP, SO THAT THE LAW SPEAKS OF THE RECORD THAT THE CHAIN CARRIES.
WHENCE. A text of this project, taken over and turned in
three things alone: the type of the letter strs, at both places where
it is bound (it reads the record too, as in LawAt.lean); one import more (GoodAt.lean); one
theorem more at the end (`doorKeeps_of`).

Why. The law at a seated block (`k2_leads_seated`, SeatedAt.lean; as one sentence `K02LawOf`,
SitsLaw.lean) ends at "there are t, t' with enter a.1 = .ok t, leave a.1 t' = .ok a'.1 and `K2Q` at
(t, a.2), (t', a'.2)": t' is the record that the kind's block made INSIDE the door. The chain
carries a'.1. t is a function of a.1 (enter is one); t' is not one of a'.1. Here it is shown what
`K2Q` reads of t', and that a way out which keeps just that lets the law end at a'.1 itself.

Main names:
  `Kept t' s'`: the two statements have the same tables (`K2.SameTables`: codes, number of messages,
    each message's shape and stored sample rows), and group by group the same open rows. It is, to
    the letter, the conclusion of `K2.first_keeps` (Johnson/Top/H0/K2Hears/RowsKept.lean).
  `formsAt_kept`, `ansAt_kept`, `newSmp_kept`: the reading of a new member's sample off a record
    (BehindPaid.lean) reads the stored sample rows alone.
  `rb_kept`: what stands behind (`lawRb`, LawAt.lean) reads of the RECORD behind the groups' open
    rows alone.
  `ReadKept`: NAMED PREMISE on the three letters of `fbOf` (oldB, strB, carB): they give the same at
    two records that are `Kept`.
  `fbOf_kept`, `k2Q_kept`: so `K2Q` at (t', y) gives `K2Q` at (s', y).
  `KeepsOut leave`: every yes of the way out keeps. `keepsOut_same` (a way out that hands back what
    it is handed), `KeepsOut.then` (one step, then a way out that keeps), `headOpenQ_kept`
    ("H.1.quiet"), `finishBehindQ_kept` ("F.0.quiet").
  `leads_out`: THE RULE: a `Reduction.Leads` towards the door's sentence, through a way out that
    keeps, is one towards "there is t with enter a.1 = .ok t and `K2Q` at (t, a.2), a'".
  `doorKeeps_of`: a way out that keeps, and letters with `ReadKept`, meet `DoorKeeps` (GoodAt.lean):
    the premise on the way out of the law in the form that the rule of composition asks
    (`k2_goodIn_seated`).
Limits. ONE DIRECTION, as SeatedAt.lean. Nothing on the way in: t stays enter's value. `ReadKept` is
shown of no letters here (constant letters meet it). The guards of a seat and a joined block of the
frames' lot lie in roots beside the library: `keepsOut_same` and `KeepsOut.then` are made for them;
they are not called at them here. No member. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.SitsLaw
import Johnson.Top.H0.K2Caller.GoodAt
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands

/-- **What a way out must keep** of the record t' that the kind's block made, in the record s' that
it hands on. -/
def Kept (t' s' : Rec) : Prop :=
  K2.SameTables t'.st s'.st ∧
    ∀ i : Nat, (s'.st.groups[i]?).map (·.rows) = (t'.st.groups[i]?).map (·.rows)

theorem Kept.refl (t : Rec) : Kept t t := ⟨K2.SameTables.refl _, fun _ => rfl⟩

theorem Kept.trans {a b c : Rec} (h : Kept a b) (k : Kept b c) : Kept a c :=
  ⟨h.1.trans k.1, fun i => (k.2 i).trans (h.2 i)⟩

/-- Two records with one statement. -/
theorem kept_of_st {t' s' : Rec} (h : s'.st = t'.st) : Kept t' s' := by
  unfold Kept
  rw [h]
  exact ⟨K2.SameTables.refl _, fun _ => rfl⟩

/-! ### The reading of a new member's sample reads the stored sample rows alone -/

theorem formsAt_kept (cs : Codes) (sh : OracleShape) {A B : Statement} (T : K2.SameTables A B)
    (o : Nat) : K2.formsAt cs sh B o = K2.formsAt cs sh A o := by
  have h := T.samples o
  unfold K2.formsAt
  cases hA : A.oracles[o]? with
  | none =>
    cases hB : B.oracles[o]? with
    | none => rfl
    | some b =>
      rw [hA, hB] at h
      cases h
  | some a =>
    cases hB : B.oracles[o]? with
    | none =>
      rw [hA, hB] at h
      cases h
    | some b =>
      rw [hA, hB] at h
      have e : b.sampleRows = a.sampleRows := Option.some.inj h
      show (b.sampleRows[0]?).map _ = (a.sampleRows[0]?).map _
      rw [e]

theorem ansAt_kept {A B : Statement} (T : K2.SameTables A B) (o : Nat) :
    K2.ansAt B o = K2.ansAt A o := by
  have h := T.samples o
  unfold K2.ansAt
  cases hA : A.oracles[o]? with
  | none =>
    cases hB : B.oracles[o]? with
    | none => rfl
    | some b =>
      rw [hA, hB] at h
      cases h
  | some a =>
    cases hB : B.oracles[o]? with
    | none =>
      rw [hA, hB] at h
      cases h
    | some b =>
      rw [hA, hB] at h
      have e : b.sampleRows = a.sampleRows := Option.some.inj h
      show (b.sampleRows[0]?).map _ = (a.sampleRows[0]?).map _
      rw [e]

theorem newSmp_kept {r : SwRow} (n0 : ℕ) {t' s' : Rec} (h : Kept t' s') (o : Fin r.l.length) :
    newSmp (r := r) n0 s' o = newSmp (r := r) n0 t' o := by
  unfold newSmp
  rw [formsAt_kept r.cs (r.l.get o).1 h.1 (n0 + o.val), ansAt_kept h.1 (n0 + o.val)]

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)

/-- **What stands behind reads of the record behind the groups' open rows alone.** -/
theorem rb_kept (p : K2.P2) (Yt : Type) (a : Rec × Yt) {t' s' : Rec} (h : Kept t' s')
    (b : TB X iJ iQ) (wt) (hw : lawRb X iJ iQ p Yt a (s', b) wt) :
    lawRb X iJ iQ p Yt a (t', b) wt := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨h1, ?_, h3⟩
  intro fx hfx G0 G' h0 hG' x hx
  have e : (s'.st.groups[fx.f.group]?).map (·.rows) = some G'.rows := by
    have e0 : (t'.st.groups[fx.f.group]?).map (·.rows) = some G'.rows := by
      have hG'' : t'.st.groups[fx.f.group]? = some G' := hG'
      rw [hG'']
      rfl
    exact (h.2 fx.f.group).trans e0
  obtain ⟨G'', hG'', eR⟩ := Option.map_eq_some_iff.1 e
  exact h2 fx hfx G0 G'' h0 hG'' x (by rw [eR]; exact hx)

variable {F : Frame}

/-- **The named premise on the three letters of `fbOf`**: at two records that are `Kept` they give
the same. -/
def ReadKept (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str) : Prop :=
  ∀ (t' s' : Rec) (y : F.E.Str), Kept t' s' →
    oldB (s', y) = oldB (t', y) ∧ strB (s', y) = strB (t', y) ∧ carB (s', y) = carB (t', y)

theorem fbOf_kept (n0 : ℕ) (b₀ : TB X iJ iQ)
    (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str) (hL : ReadKept X iJ iQ oldB strB carB)
    {t' s' : Rec} (h : Kept t' s') (y : F.E.Str) :
    fbOf X iJ iQ n0 b₀ oldB strB carB (s', y) = fbOf X iJ iQ n0 b₀ oldB strB carB (t', y) := by
  obtain ⟨e1, e2, e3⟩ := hL t' s' y h
  have e4 : newSmp (r := r) n0 s' = newSmp (r := r) n0 t' := funext fun o => newSmp_kept n0 h o
  unfold fbOf
  rw [e1, e2, e3]
  show _ = _
  simp only [e4]

variable (p : K2.P2)
  (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

/-- **What the law leads to, at the record that the chain carries.** -/
theorem k2Q_kept (fb : Rec × F.E.Str → TB X iJ iQ) (a : Rec × F.E.Str) {t' s' : Rec}
    (h : Kept t' s') (y : F.E.Str) (hfb : fb (s', y) = fb (t', y))
    (hq : K2Q X iJ iQ p strs inX fb a (t', y)) : K2Q X iJ iQ p strs inX fb a (s', y) := by
  intro wt hw
  have hw' : lawRb X iJ iQ p F.E.Str a (s', fb (t', y)) wt := hfb ▸ hw
  exact hq wt (rb_kept X iJ iQ p F.E.Str a h _ wt hw')

end

/-! ### Ways out that keep -/

/-- Every yes of the way out keeps. -/
def KeepsOut (leave : Rec → Rec → Except String Rec) : Prop :=
  ∀ s t' s', leave s t' = .ok s' → Kept t' s'

/-- A way out that hands back what it is handed (a guard). -/
theorem keepsOut_same {leave : Rec → Rec → Except String Rec}
    (h : ∀ s t' s', leave s t' = .ok s' → s' = t') : KeepsOut leave := fun s t' s' e => by
  rw [h s t' s' e]
  exact Kept.refl _

/-- One step that keeps, then a way out that keeps. -/
theorem KeepsOut.then {q : Rec → Except String Rec} {leave : Rec → Rec → Except String Rec}
    (hq : ∀ t m, q t = .ok m → Kept t m) (hl : KeepsOut leave) :
    KeepsOut fun s t => (q t).bind (leave s) := fun s t' s' e => by
  have e' : (q t').bind (leave s) = .ok s' := e
  cases hm : q t' with
  | error x =>
    rw [hm] at e'
    cases e'
  | ok m =>
    rw [hm] at e'
    exact (hq t' m hm).trans (hl s m s' e')

/-- "H.1.quiet" keeps: its statement is `firstBehind`'s. -/
theorem headOpenQ_kept {P : K2.HeadPar} {t m : Rec} (h : K2.headOpenQ P t = .ok m) : Kept t m := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (K2.headOpenQ_iff P t m).1 h
  have e : m.st = st := by rw [k.out']
  unfold Kept
  rw [e]
  exact K2.first_keeps k.behind

/-- "F.0.quiet" keeps: it leaves the statement. -/
theorem finishBehindQ_kept {t m : Rec} (h : K2.finishBehindQ t = .ok m) : Kept t m := by
  obtain ⟨a, x, _, _, rfl⟩ := (K2.finishBehindQ_iff t m).1 h
  exact Kept.refl _

/-! ### The rule -/

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {F : Frame} (p : K2.P2)
  (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

/-- **Through a way out that keeps, the law ends at the record that the chain carries.** -/
theorem leads_out (K : Reduction (Rec × F.E.Str) (Rec × F.E.Str))
    (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hk : KeepsOut leave) (fb : Rec × F.E.Str → TB X iJ iQ)
    (hfb : ∀ (t' s' : Rec) (y : F.E.Str), Kept t' s' → fb (s', y) = fb (t', y))
    (on : Rec × F.E.Str → Prop) (ε : Err K.shape)
    (h : K.Leads on
      (fun a a' => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok a'.1 ∧
        K2Q X iJ iQ p strs inX fb (t, a.2) (t', a'.2)) ε) :
    K.Leads on
      (fun a a' => ∃ t, enter a.1 = .ok t ∧ K2Q X iJ iQ p strs inX fb (t, a.2) a') ε :=
  h.conseq (fun _ ha => ha) fun a _ a' _ _ ⟨t, t', e1, e2, q⟩ =>
    ⟨t, e1, k2Q_kept X iJ iQ p strs inX fb (t, a.2) (hk a.1 t' a'.1 e2) a'.2
      (hfb t' a'.1 a'.2 (hk a.1 t' a'.1 e2)) q⟩

end

/-! ### For the form that the rule of composition asks -/

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  {F : Frame} (p : K2.P2)

/-- **A way out that keeps meets `DoorKeeps`**, at the reading `fbOf` with letters that read no
more of a record than is kept. -/
theorem doorKeeps_of {leave : Rec → Rec → Except String Rec} (hk : KeepsOut leave) (n0 : ℕ)
    (b₀ : TB X iJ iQ) (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str) (hL : ReadKept X iJ iQ oldB strB carB) :
    DoorKeeps (F := F) X iJ iQ p leave (fbOf X iJ iQ n0 b₀ oldB strB carB) :=
  fun s t' s' y e =>
    ⟨by
      rw [fbOf_kept X iJ iQ n0 b₀ oldB strB carB hL (hk s t' s' e) y]
      exact ⟨fun _ => rfl, fun _ => rfl, rfl, rfl⟩,
    fun a bb wt hw => rb_kept X iJ iQ p F.E.Str a (hk s t' s' e) bb wt hw⟩

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.newSmp_kept
#print axioms VerifiableInference.Desc.First.K2Caller.rb_kept
#print axioms VerifiableInference.Desc.First.K2Caller.fbOf_kept
#print axioms VerifiableInference.Desc.First.K2Caller.k2Q_kept
#print axioms VerifiableInference.Desc.First.K2Caller.keepsOut_same
#print axioms VerifiableInference.Desc.First.K2Caller.KeepsOut.then
#print axioms VerifiableInference.Desc.First.K2Caller.headOpenQ_kept
#print axioms VerifiableInference.Desc.First.K2Caller.finishBehindQ_kept
#print axioms VerifiableInference.Desc.First.K2Caller.leads_out
#print axioms VerifiableInference.Desc.First.K2Caller.doorKeeps_of
